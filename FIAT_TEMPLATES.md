# Templates with bounds certificates: scope, completeness, measurements

Status of 2026-10-06. Companion to [FIELD_TEMPLATES_VS_RUST.md](FIELD_TEMPLATES_VS_RUST.md),
which compares the printed Rust with the Rust ecosystem. Paths under `Haxc/`, `bench/` and
`scripts/` are in the development repository; other paths are in this package.

## Principle

The template method applies to any computation that is straight-line word arithmetic
generated from an algebraic template, with a bounds certificate checked per instance. It
therefore covers prime fields, lattice transforms and codecs, GHASH, extension towers, RSA
moduli and isogeny primes. It does not cover control flow or bit-logic permutations
(Keccak, ChaCha, AES rounds): those have no algebraic template whose instances differ only
in parameters and bounds.

A template is a Lean function from a parameter record to a `Com` program, with one
denotation theorem over every record. An instance proves nothing new except its
certificate, a decided statement that the word bounds hold:

- intervals: `boundsOk` and `denote_eq_denoteZ_of_boundsOk` (`VIR/ComRangeExact.lean`),
  which identify the word program with its integer denotation when no word overflows;
- schedules: `SchedOk` (`VIR/NegacyclicNttTemplate.lean`), decided per NTT parameter set;
- field records: `LimbParams` with `noCarryOk` for the no-carry block
  (`Algebraic/FieldLimbs/MontNoCarry.lean`), and `FieldTemplate.route_abi_denote`
  (`Haxc/FieldRoute.lean`) for the assembled route.

At the bytes, each family has one theorem over its records (`field_correct_bytes`,
`Haxc/FieldBytes.lean`; `ntt_correct_bytes`, `Haxc/NttBytes.lean`; `ec_correct_bytes`,
`Haxc/EcBytes.lean`) whose only per-instance hypothesis is acceptance by `compileJ`
(`Haxc/BackHalf.lean`), the decided gate of `backend_correct`. An instance cell below is
therefore a theorem together with the result of running the gate.

## Completeness against the fiat acceptance

Verdicts are from `compileJ` as run by the executables `field-bytes-emit` and
`mpn-bytes-emit` and recorded in `scripts/acceptance-registry.tsv` (columns `accepted`,
`bytes`, `ct`), or from probes of the gate where a row says so. The `compileJ` and
`compileOf` calls the executables run are the hypotheses of the theorems named in the
cells (`Haxc/FieldBytesEmitMain.lean`). The `ct` column is the result of the byte-level
constant-time checker on the accepted bytes (`ctGateB`, `Haxc/CTPub.lean`), with `%rsp` and
the array pointers public and the limb contents and scalar words secret; `-` means that no
result is recorded.

### Fields (F1): Montgomery multiply, square, add, subtract

Theorem names are `<prime>_<op>_correct_bytes` in `Haxc/FieldInstances.lean`; sizes are the
registry rows `field/<prime>_<op>`.

| prime | mul | sqr | add | sub |
|---|---|---|---|---|
| P-256 | 3541 B | 3529 B | 510 B | 451 B |
| secp256k1 | 3691 B | 3701 B | 457 B | 414 B |
| P-384 | 7211 B | 7072 B | 731 B | 678 B |
| BN254 | 3813 B | 3823 B | 508 B | 472 B |
| BLS12-381 | 7418 B | 7309 B | 767 B | 713 B |

All 20 programs are accepted; the `ct` column of the 20 rows is `-`. Constant time of the
field chain at the five primes is `nfChainF_ct_<prime>` and
`nfChainF_ct_of_levelCheck'_<prime>` (`Haxc/FieldBlocksCT.lean`), with no hypothesis on the
blocks of the template (`blocksCheck_<prime>`): two runs whose source leak traces agree
have equal leak traces of the route program the chain returns. Conformance: 69 arms over
the 20 cells, 0 mismatches against GMP and the peers (`bench/field_bytes/README.md`,
objects of 2026-10-04 18:02). The interleaved multiply `Mont.mulBlkRoute`
(`mulBlkRoute_denote`, `MontCIOS.lean`) selects `mulBlkI` from six limbs; the P-384 and
BLS12-381 sizes are those of this block. The no-carry block `mulBlkNC` has the lowest
instruction count at BN254 and
BLS12-381 and is refused by `encodeLfundefBytesChecked` (unfused `MUL`/`MULXHI` pairs;
row candidate NC-FUSE).

### Lattice, symmetric, EC, mpn, towers (F3) and the prime-ir front (F4)

| kernel | op | theorem | accepted at the bytes; size; `ct` |
|---|---|---|---|
| ML-KEM NTT | forward | `mlkem_ntt_correct_bytes` (signed 16-bit arm), `mlkem_ntt_correct_bytes_wide` (64-bit arm), `Haxc/NttInstances.lean` | no registry row; the signed 16-bit arm is deferred on narrow arithmetic (below); the gate is not run on the 64-bit arm |
| ML-KEM | basemul | `mlkem_basemul_correct_bytes` (`Haxc/LatticeRoute.lean`) | no registry row; deferred on narrow arithmetic (below), as is ML-DSA pointwise |
| Poseidon2 BabyBear, width 16 | permutation | `bb_poseidon2_correct_bytes` (`Haxc/Poseidon2Bytes.lean`), tied to `permute_bbParams_eq`; conditional: its `compileJ` hypothesis holds for no instance, because `plantBlk` binds 128-bit values. The 64-bit block `plantBlk64` (`plantBlk64_denote`) and the chain `bbPermChain64` (`bbPermProg64_spec'`) are in `VIR/NarrowFieldPlant64.lean` | no registry row; no route and no bytes theorem over `bbPermChain64` |
| P-256 Jacobian | add | `p256_jacAdd_correct_bytes`, `p256_jacAddC_correct_bytes` (`Haxc/EcInstances.lean`) | `ec/p256_jacAdd`: not accepted; `compileJ` refuses the route of `p256_jacAddC_correct_bytes` at all three coordinates; the refusing conjunct is not localised |
| P-256 Jacobian | double | `p256_jacDbl_correct_bytes`, `p256_jacDblC_correct_bytes` | `ec/p256_jacDbl`: not accepted; the gate evaluation of coordinate x of the route of `p256_jacDblC_correct_bytes` does not finish within eight minutes in the executable; no result |
| mpn, n = 4 | add_n, sub_n, mul_1, addmul_1 | `mpn_add_n_bytes_correct`, `mpn_sub_n_bytes_correct`, `mpn_mul_1_bytes_correct`, `mpn_addmul_1_bytes_correct` (`Haxc/MpnBytes.lean`, every n) | accepted: 301 B, 359 B, 369 B, 499 B; `ct` yes on all four |
| mpn, n = 8 | all four | the same four theorems | accepted: 534 B, 623 B, 614 B, 992 B; `ct` yes on all four |
| Fp2 at BN254 | mul, sqr | `bn254_fp2_mul_correct_bytes`, `bn254_fp2_sqr_correct_bytes` (`Haxc/TowerRoute.lean`) | `tower/bn254_fp2_mul`: accepted, 13 720 B, `ct` yes; `tower/bn254_fp2_sqr`: accepted, 9008 B, `ct` yes |
| Fp2 at BLS12-381 | mul, sqr | `bls12381_fp2_mul_correct_bytes`, `bls12381_fp2_sqr_correct_bytes` (`Haxc/TowerRoute.lean`) | no registry row; the executable does not run the gate on these routes |
| Solinas 2^255−19 | mul, sqr | none | accepted by probe: 2452 B, 2399 B; deferred (D3, below) |
| Solinas 2^521−1 | mul, sqr | none | accepted by probe: 10 018 B, 10 189 B; outside the F1 prime list |
| prime-ir `fe_mul_add`, P-256 | front to bytes | `fieldFront_accepts_p256` (`Haxc/FieldFrontP256.lean`), `impArgsNF_sound` (`Hax/ImpToNF.lean`), `fe_mul_add_bytes_p256` (`Haxc/FieldInstances.lean`) | `primeir/fe_mul_add_p256`: accepted, 3901 B, `ct` yes; the accepted call is the `compileOf` hypothesis of `fe_mul_add_bytes_p256` |
| counted loop of field multiplications, P-256 | front | `powLoop_front_accepts` (`Haxc/FieldLowerChain.lean`): `fieldChainFront` returns a program on `powLoopBody` | no registry row; the bytes route is deferred on the loop gate (below) |

The Solinas figures come from route definitions inlined while `FieldRoute` was stale; the
dispatcher `fieldTemplateOf` reaches the Solinas arm only at 2^521−1, and sends 2^255−19 to
the unsaturated arm (`unsatReprs`).

## Measured ratios (F2)

Target (decision D1, 2026-10-04): ours/fiat-C ≤ 1.25 for mul and sqr at the five primes;
a slow proven hand kernel retires when the template bytes measure within 1.1 of it. F2 is
recorded, not gated.

Objects with `mulBlkRoute` and `mulLoadBody` (run of 2026-10-05, `bench/field_bytes/results/summary.md`,
conformance all arms pass; the ratios are not remeasured on the objects of 2026-10-06),
latency / throughput:

| prime | op | ours/peer | peer |
|---|---|---|---|
| P-256 | mul | 1.54 / 1.54 | fiat C |
| P-256 | sqr | 1.60 / 1.54 | fiat C |
| secp256k1 | mul | 1.55 / 1.58 | fiat C |
| secp256k1 | sqr | 1.70 / 1.66 | fiat C |
| P-384 | mul | 1.16 / 1.15 | fiat C |
| P-384 | sqr | 1.18 / 1.15 | fiat C |
| BN254 | mul | 1.54 / 1.59 | fiat/bedrock2 C |
| BN254 | sqr | 1.55 / 1.64 | fiat/bedrock2 C |
| BLS12-381 | mul | 2.93 / 2.97 | blst (no fiat C arm) |

The D1 target holds at P-384 only; the six-limb CIOS block (`mulBlkRoute`) moved P-384
from 1.33 to 1.18. The P-256 multiply has 791 instructions and nine stack reloads of
`%r14`. LOAD-AT-USE (`mulLoadBody`, below six limbs) loads each row word of the second
factor at its row; it moved the four-limb ratios by 0.03–0.12 and left the nine reloads:
four are the per-row reload of the operand pointer and three the spilled reduction word,
and `LprogGpRealloc` cannot promote either across a `MULX`, which ends its runs. At six
limbs the same body measured 1.37 at P-384, so the CIOS block stays there.
No proven hand kernel is within 1.1, so no retirement applies.

Earlier rounds, `bench/field_bytes/README.md`, TSC ticks, ours/peer (above 1: ours slower),
latency / throughput:

| prime | op | 2026-10-04 01:30 (first objects) | 2026-10-04 18:10 (dead-write pass) | peer |
|---|---|---|---|---|
| P-256 | mul | 1.62 / 1.59 | 1.54 / 1.54 | fiat C |
| P-256 | sqr | 1.73 / 1.72 | 1.74 / 1.65 | fiat C |
| secp256k1 | mul | 1.65 / – | 1.62 / 1.62 | fiat C |
| secp256k1 | sqr | – | 1.66 / 1.71 | fiat C |
| P-384 | mul | 1.39 / – | 1.33 / 1.33 | fiat C |
| P-384 | sqr | – | 1.33 / 1.34 | fiat C |
| BN254 | mul | – | 1.59 / 1.61 | fiat/bedrock2 C |
| BN254 | sqr | – | 1.58 / 1.66 | fiat/bedrock2 C |
| BLS12-381 | mul, sqr | – | no fiat C arm in the tree | – |

Against the fastest hand kernels (round of 2026-10-04 18:10, latency): BN254 mul 3.01,
sqr 3.09; BLS12-381 mul 3.24, sqr 3.27. The 1.1 retirement threshold is not met at any
prime. The first round's gap analysis for P-256 mul counted 96 `bt` and 80 `setb` (carries
leave the flags at every limb), 268 stack operands, 20 pointer reloads and 28 dead `imul`;
the dead-write pass removed the last.

The printed Rust (a different artifact, 2026-10-03, `bench/fiat_rust_compare/README.md`)
measures 0.68–1.18 of fiat-crypto's Rust for mul and sqr at P-256, secp256k1 and P-384
([FIELD_TEMPLATES_VS_RUST.md](FIELD_TEMPLATES_VS_RUST.md)).

## Size of the template layer

Counted on 2026-10-05 with `wc -l` over the files named, from each repository root:

| part | files | lines |
|---|---|---|
| field templates | `CatCrypt/Crypto/SecureCompilation/Algebraic/FieldLimbs/*.lean` (13 files) | 8 227 |
| other families | `VIR/{TowerDialect,TowerToLimbs,NegacyclicNttTemplate,NegacyclicNttWord,NegacyclicNttWordSigned,RoundCodec,NarrowField,BasemulWord,PointwiseAcc,Gf2Dialect,Gf2Aggregate,RowLazy,Poseidon2Word}.lean` | 12 241 |
| limb lowering | `Algebraic/FieldToJasminLimbs*.lean` (4 files) | 1 324 |
| routes (development repository) | `Haxc/{FieldRoute,FieldChain,RouteChain,TowerRoute,LatticeRoute}.lean` | 2 245 |
| instances (development repository) | `Haxc/{FieldInstances,NttInstances,Poseidon2Bytes,EcInstances,MpnBytes,FieldFrontP256}.lean` | 1 488 |

Templates: 20 468 lines; with lowering and routes, 24 037. This corrects the earlier
estimate of "about 30 000 lines of per-instance code against 6 000 of template" (2026-10-03).
The inventory of 2026-10-03 found 61 072 lines in about 275 per-instance modules, 27 136 of
them inside a headline, `SurfaceDeps` or emit closure, and about 2 550 lines whose
statements a template instance already proves; the template side was then about 17 900
lines.

Two corrections concern the AUCurves peers.

- A1. `bench/framework/VERIFIED_PEER_CLASSIFICATION.md:41` lists AUCurves as verified. Its
  safegcd inverse is a hand-written Rust port of libsecp256k1's `secp256k1_modinv64`, and
  the convergence bound is an `Axiom` in Rocq; the row should read "partially verified",
  as the libsecp256k1 row below it does. Applied 2026-10-05.
- A2. The BN254 and BLS12-381 towers adopted from AUCurves are hand-edited away from what
  the Rocq chain proves (BN254: 99 lines in three regions; BLS12-381: `Fp2_mul`,
  `Fp2_square`, `Fp2_inv`). The docstrings of the adopting axioms (`Vale/BN254.lean`, the
  BLS12-381 tower arm) state this since 2026-10-05.

## Deferrals

| item | date | reason or refusing gate | row candidate |
|---|---|---|---|
| carries in flags (CF-1 to CF-6, CARRY-FUSE) | 2026-10-04 | design D2 decided only when reopened | CARRY-IN-FLAGS |
| poly1305 3×44 | 2026-10-04 | `UnsatParams` has one limb width, so the fold sits at bit 132 and the freeze precondition X < 2p fails; poly1305 has a Solinas route | UNSAT-TOPWIDTH (top-limb width `bTop`) |
| Falcon, Goldilocks | 2026-10-04 | out of scope | – |
| towers above Fp2 | 2026-10-03 | out of scope | – |
| mpn with variable n | 2026-10-03 | out of scope | – |
| GHASH at the bytes | 2026-10-04 | out of scope; template and theorem exist (`ghashAggJ_denote_ghashFold`) | – |
| 2^255−19 at the bytes | 2026-10-04 (D3) | unsaturated arm has no x86 lowering of `reg 128`; Solinas arm accepted by probe | WIDE-LEGAL if wanted |
| e-graph stage of the field chain | 2026-10-04 | identity of `aegraphOptField` at a symbolic modulus unproved | – |
| P-256 Jacobian addition and doubling at the bytes | 2026-10-06 | `compileJ` refuses the addition at all three coordinates, and the refusing conjunct of `jGateB` is not localised; the gate evaluation of the doubling does not finish within the executable's time | localisation of the refusing conjunct; a gate evaluation that terminates on the doubling |
| narrow arithmetic (ML-KEM basemul, NTT signed 16-bit arm, ML-DSA pointwise) | 2026-10-06 | the exporter writes only the width 64 into a mnemonic, and the decoder `decodeLinstr` has no 32-bit ALU or shift form for the gate to decode to; width typing across arithmetic without shifts exists (`typeStep`, `wTyped_step`, `X86Backend/NarrowTyping.lean`) | LANE-NARROW-ARITH-2: 32-bit decoder forms, width typing of shifts |
| Poseidon2 BabyBear at the bytes | 2026-10-06 | the 128-bit bindings of `plantBlk` have no machine form in the checked encoder; the width gate `comWidthsOk` refuses them in `renderOwnedCom` (`renderOwnedCom_refuse`), and a printer call outside that gate renders an untagged 128-bit operation at 32 bits; `bbPermChain64` has no route | a route and a bytes theorem over `bbPermChain64` |
| counted loop of field multiplications at the bytes | 2026-10-06 | `compileJ` accepts a looped program through `v1LoopB`, whose route covers no carry chain and no cell access; the loop gate `v1LoopWB` (`Haxc/BackHalfW.lean`) is not a gate of `compileJ`; the checked encoder refuses the compare of a spilled counter with an immediate (P-256 loop at four limbs, evaluated on the printed body) | LOOP-GATE-W; CMP-SPILL-IMM |
| Fp2 at BLS12-381 at the bytes | 2026-10-06 | the gate is not run: no arm of the executable, no registry row | a registry row |

Of the instances with a bytes theorem, the field cells, the mpn programs at n = 4 and
n = 8, the Fp2 routes at BN254 and the prime-ir `fe_mul_add` at P-256 have an accepted
program; the P-256 Jacobian routes, the lattice routes, Poseidon2 and the Fp2 routes at
BLS12-381 have none.
