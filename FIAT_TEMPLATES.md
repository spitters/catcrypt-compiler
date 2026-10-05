# Templates with bounds certificates: scope, completeness, measurements

Status of 2026-10-05. Companion to [FIELD_TEMPLATES_VS_RUST.md](FIELD_TEMPLATES_VS_RUST.md),
which compares the printed Rust with the Rust ecosystem. Paths under `Haxc/` and `bench/`
are in the development repository; other paths are in this package.

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
therefore a theorem plus an acceptance verdict of the gate.

## Completeness against the fiat acceptance

Verdicts are from `compileJ` as run by the executables `field-bytes-emit` and
`mpn-bytes-emit`, or by probes of the gate. Byte sizes for the field cells are
`bench/field_bytes/acceptance.tsv` (objects of 2026-10-04 after the dead-write pass).
"Built" means the module built at a commit; "(unbuilt, 2026-10-05)" means the theorem is
in source with no build. `Haxc/FieldInstances.lean` was edited after its last build
(sqr and BN254/BLS12-381 cells added, routes restated as chain runs), so all field cells
await one build.

### Fields (F1): Montgomery multiply, square, add, subtract

Theorem names are `<prime>_<op>_correct_bytes` in `Haxc/FieldInstances.lean`.

| prime | mul | sqr | add | sub |
|---|---|---|---|---|
| P-256 | built; 3534 B | (unbuilt, 2026-10-05); 3546 B | built; 510 B | built; 451 B |
| secp256k1 | built; 3699 B | (unbuilt, 2026-10-05); 3697 B | built; 457 B | built; 414 B |
| P-384 | built; 8485 B | (unbuilt, 2026-10-05); 8401 B | built; 731 B | built; 678 B |
| BN254 | (unbuilt, 2026-10-05); 3818 B | (unbuilt, 2026-10-05); 3791 B | (unbuilt, 2026-10-05); 508 B | (unbuilt, 2026-10-05); 472 B |
| BLS12-381 | (unbuilt, 2026-10-05); 8611 B | (unbuilt, 2026-10-05); 8819 B | (unbuilt, 2026-10-05); 767 B | (unbuilt, 2026-10-05); 713 B |

All 20 programs are accepted. Conformance: 69 arms over the 20 cells, 0 mismatches against
GMP and the peers (`bench/field_bytes/README.md`, objects of 2026-10-04 18:02). The
interleaved multiply `Mont.mulBlkRoute` (`mulBlkRoute_denote`, `MontCIOS.lean`; uncommitted,
unbuilt) selects `mulBlkI` from six limbs and shrinks P-384 mul to 7211 B and BLS12-381 mul
to 7418 B. The no-carry block `mulBlkNC` has the lowest instruction count at BN254 and
BLS12-381 and is refused by `encodeLfundefBytesChecked` (unfused `MUL`/`MULXHI` pairs;
row candidate NC-FUSE).

### Lattice, symmetric, EC, mpn, towers (F3) and the prime-ir front (F4)

| kernel | op | theorem | gate verdict |
|---|---|---|---|
| ML-KEM NTT | forward | `mlkem_ntt_correct_bytes` (signed 16-bit arm), `mlkem_ntt_correct_bytes_wide` (64-bit arm), `Haxc/NttInstances.lean`; built | not run; the signed 16-bit arm is expected to be refused like basemul (`widenProg` lane casts), unmeasured |
| ML-KEM | basemul | `mlkem_basemul_correct_bytes` (`Haxc/LatticeRoute.lean`); (unbuilt, 2026-10-05) | refused at `encodeLfundefBytesChecked`: 20 of 104 instructions are `TRUNC`/`ZEROEXT`; ML-DSA pointwise refused at the same gate |
| Poseidon2 BabyBear, width 16 | permutation | `bb_poseidon2_correct_bytes` (`Haxc/Poseidon2Bytes.lean`), tied to `permute_bbParams_eq`; (unbuilt, 2026-10-05), statement error at line 103 open | not run; same `widenProg` casts as the lattice routes, refusal expected, unmeasured |
| P-256 Jacobian | add | `p256_jacAdd_correct_bytes`, `p256_jacAddC_correct_bytes` (`Haxc/EcInstances.lean`); (unbuilt, 2026-10-05) | not recorded |
| P-256 Jacobian | double | `p256_jacDbl_correct_bytes`, `p256_jacDblC_correct_bytes`; (unbuilt, 2026-10-05) | refused at `printedAddrWB` inside `cellRouteB` (37 742 B encoded); sub-check not isolated |
| mpn, n = 4 | add_n, mul_1, addmul_1 | `mpn_add_n_bytes_correct`, `mpn_mul_1_bytes_correct`, `mpn_addmul_1_bytes_correct` (`Haxc/MpnBytes.lean`, every n); built | accepted: 301 B, 369 B, 499 B (mul_1 and addmul_1 after the dead-write pass) |
| mpn, n = 4 | sub_n | `mpn_sub_n_bytes_correct`; built | refused at `printedAddrWB`: the 1-bit borrow (`MOV`, `XOR` on width 1) has no decoder shape |
| mpn, n = 8 | all four | the same four theorems | refused at `ownedCheckMC` and `printedAddrWB`: the both-spilled store arm of `legalizeMemStore` (`LEA` then store through the spilled base); sub_n also the 1-bit borrow |
| Fp2 at BN254 | mul, sqr | `bn254_fp2_mul_correct_bytes`, `bn254_fp2_sqr_correct_bytes` (`Haxc/TowerRoute.lean`); (unbuilt, 2026-10-05) | refused at `jGateB` → `printedAddrWB` → `decodableLcmd`: spill slots as destinations of `ADCX`/`CMOV` (1222 and 811 instructions) |
| Fp2 at BLS12-381 | mul, sqr | `bls12381_fp2_mul_correct_bytes`, `bls12381_fp2_sqr_correct_bytes`; (unbuilt, 2026-10-05) | refused earlier, at `encodeLfundefBytesChecked`; cause unmeasured |
| Solinas 2^255−19 | mul, sqr | none | accepted by probe: 2452 B, 2399 B; deferred (D3, below) |
| Solinas 2^521−1 | mul, sqr | none | accepted by probe: 10 018 B, 10 189 B; outside the F1 prime list |
| prime-ir `fe_mul_add`, P-256 | front | `fieldFront_accepts_p256` (`Haxc/FieldFrontP256.lean`), `impArgsNF_sound` (`Hax/ImpToNF.lean`, uncommitted); (unbuilt, 2026-10-05) | `fe_mul_add_bytes_p256` (built) stays conditional on acceptance of the compiled program |

The Solinas figures come from route definitions inlined while `FieldRoute` was stale; the
dispatcher `fieldTemplateOf` reaches the Solinas arm only at 2^521−1, and sends 2^255−19 to
the unsaturated arm (`unsatReprs`).

## Measured ratios (F2)

Target (decision D1, 2026-10-04): ours/fiat-C ≤ 1.25 for mul and sqr at the five primes;
a slow proven hand kernel retires when the template bytes measure within 1.1 of it. F2 is
recorded, not gated.

Current objects (with `mulBlkRoute` and `mulLoadBody`; run of 2026-10-05, `bench/field_bytes/results/summary.md`,
conformance all arms pass), latency / throughput:

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
| spill-induced forms | 2026-10-05 | `printedAddrWB`/`decodableLcmd`: spill slot as ALU destination, both-spilled indexed store (P-256 doubling, Fp2, mpn n = 8) | SPILL-DEST-SHAPES, or LOAD-AT-USE (decided by FIAT-MEASURE-1) |
| lane casts | 2026-10-05 | `TRUNC`/`ZEROEXT` unencodable (basemul, pointwise; NTT 16-bit arm and Poseidon2 expected) | LANE-CAST-ENC |
| 1-bit borrow | 2026-10-05 | `printedAddrWB`: width-1 `MOV`/`XOR` (mpn sub_n) | MPN-BIT1-SHAPES |

The refusals of the EC doubling, the Fp2 routes and mpn at n = 8 share one cause: forms the
register allocator produces after spilling, which the decoder shapes do not cover. One
back-end row on these shapes, or fewer spills at the source, would address all three.
