# Templates with bounds certificates: method, instances, measurements

Companion to [FIELD_TEMPLATES_VS_RUST.md](FIELD_TEMPLATES_VS_RUST.md), which compares the
printed Rust with the Rust ecosystem. Paths under `Haxc/`, `bench/` and `scripts/` are in
the development repository; other paths are in this package, and a path under `VIR/`,
`Algebraic/` or `X86Backend/` is relative to `CatCrypt/Crypto/SecureCompilation/`.

## Principle

The template method applies to straight-line word arithmetic generated from an algebraic
template, with a bounds certificate checked per instance. The families with a template
are prime fields, lattice transforms and codecs, GHASH, extension towers, RSA moduli and
isogeny primes.

A template is a Lean function from a parameter record to a `Com` program, with one
denotation theorem over every record. An instance adds its certificate, a decided
statement that the word bounds hold:

- intervals:
  [`boundsOk`](CatCrypt/Crypto/SecureCompilation/VIR/ComRangeExact.lean) and
  [`denote_eq_denoteZ_of_boundsOk`](CatCrypt/Crypto/SecureCompilation/VIR/ComRangeExact.lean),
  which identify the word program with its integer denotation for a program accepted by
  `boundsOk`;
- schedules:
  [`SchedOk`](CatCrypt/Crypto/SecureCompilation/VIR/NegacyclicNttTemplate.lean), decided
  per NTT parameter set;
- field records:
  [`LimbParams`](CatCrypt/Crypto/SecureCompilation/Algebraic/FieldLimbs/Mont.lean) with
  [`noCarryOk`](CatCrypt/Crypto/SecureCompilation/Algebraic/FieldLimbs/MontNoCarry.lean)
  for the no-carry block, and `FieldTemplate.route_abi_denote` (`Haxc/FieldRoute.lean`)
  for the assembled route.

At the bytes, the field and EC families have one theorem each over their records
(`field_correct_bytes`, `Haxc/FieldBytes.lean`; `ec_correct_bytes`, `Haxc/EcBytes.lean`);
the NTT byte theorems were removed. The per-instance hypothesis is acceptance by
`compileJ` (`Haxc/BackHalf.lean`), the earlier back half, with the decided gate of
`backend_correct`; the compiler `compileA` uses the region back half `compileRegion`, and
the byte theorems keep the hypothesis on `compileJ` until they are restated over the
region back half (plan row B2). For a result
`(P', bytes)` of `compileJ` on the route program of the instance, the theorem gives a
halting run of the decoded bytes from which the layout reads back the value of the
template. An instance with an accepted program is therefore a theorem together with the
result of running the gate.

## Instances at the bytes

The executables `field-bytes-emit` and `mpn-bytes-emit` run the earlier back half `compileJ` and record each
accepted program in `scripts/acceptance-registry.tsv` (columns `accepted`, `bytes`,
`ct`). The `compileJ` and `compileOf` calls the executables run are the hypotheses of the
theorems named below (`Haxc/FieldBytesEmitMain.lean`). The `ct` column is the result of
the byte-level constant-time checker on the accepted bytes (`ctGateB`, `Haxc/CTPub.lean`),
with `%rsp` and the array pointers public and the limb contents and scalar words secret.

### Fields (F1): Montgomery multiply, square, add, subtract

At each of the primes P-256, secp256k1, P-384, BN254 and BLS12-381, the theorem
`<prime>_<op>_correct_bytes` in `Haxc/FieldInstances.lean` states that, for a result of the
back half on the program of the operation, the decoded bytes halt in a state from which the
layout reads back the Montgomery limbs of the product, square, sum or difference. For each
of the five primes, `nfChainF_ct_<prime>` and `nfChainF_ct_of_levelCheck'_<prime>`
(`Haxc/FieldBlocksCT.lean`) state constant time of the field chain: two runs whose source
leak traces agree have equal leak traces of the route program the chain returns. The
decided check `blocksCheck_<prime>` discharges the hypothesis on the blocks of the
template. The interleaved multiply `Mont.mulBlkRoute` selects `mulBlkI` from six limbs and
denotes the Montgomery form of the product at every limb count
([`mulBlkRoute_denote`](CatCrypt/Crypto/SecureCompilation/Algebraic/FieldLimbs/MontCIOS.lean)).

### Lattice, symmetric, EC, mpn, towers (F3) and the prime-ir front (F4)

Instances with an accepted program. Each theorem holds for the result of `compileJ`, or
of `compileOf` for the prime-ir row, that the registry row records.

| Statement proved | Programs | Registry row: size, `ct` | Lean names |
|---|---|---|---|
| The decoded bytes halt in a state from which the layout reads back `n + 1` words: the sum with its carry, the difference with its borrow, the product by one word with its high word, or that product added to the destination | `mpn_add_n`, `mpn_sub_n`, `mpn_mul_1`, `mpn_addmul_1` at every `n`; accepted at `n = 4` and `n = 8` | `n = 4`: 301 B, 359 B, 369 B, 499 B; `n = 8`: 534 B, 623 B, 614 B, 992 B; `ct` yes on all eight | `mpn_add_n_bytes_correct`, `mpn_sub_n_bytes_correct`, `mpn_mul_1_bytes_correct`, `mpn_addmul_1_bytes_correct` (`Haxc/MpnBytes.lean`) |
| The field front accepts the surface function, and the decoded bytes halt in a state from which the layout reads back the Montgomery limbs of `fe_mul_add a b c` | prime-ir `fe_mul_add` at P-256, from the surface function to the bytes | `primeir/fe_mul_add_p256`: 3901 B, `ct` yes | `fieldFront_accepts_p256` (`Haxc/FieldFrontP256.lean`), [`impArgsNF_sound`](CatCrypt/Crypto/Hax/ImpToNF.lean), `fe_mul_add_bytes_p256` (`Haxc/FieldInstances.lean`) |

Theorems over every program the gate accepts. The hypothesis of each is the equation
that `compileJ` returns `(P', bytes)` on the route program named.

| Statement proved | Programs | Lean names |
|---|---|---|
| The decoded bytes halt in a state from which the layout reads back the Montgomery limbs of one coordinate of the Jacobian sum, for affine, on-curve, distinct inputs, or of the Jacobian double | Jacobian addition and doubling at every Montgomery record and curve | `ec_correct_bytes`, `ec_dbl_correct_bytes` (`Haxc/EcBytes.lean`) |
| Every value of a source run of the body is read back from a halting run of the decoded bytes | a function over the field accepted by the front `fieldChainFront`, at every limb count and modulus record | `fieldChain_correct_auto` (`Haxc/FieldLowerChain.lean`) |
| The program of the front is constant time at every fuel when the level check `fieldFrontLeakCT` accepts the lowered program, which a counted loop passes when its trip count is public | a function over the field accepted by the front `fieldRegionFront` | `fieldRegionFront_nfCT` (`Haxc/FieldLoopCT.lean`) |

Results at the template level, over `Com` programs:

| Statement proved | Programs | Lean names |
|---|---|---|
| The 64-bit Plantard block denotes the word function `plantW`, and the permutation built on it maps input lanes at most `p + 64` that represent `x` with the factor `−2 ^ 64` to output lanes at most `p + 64` that represent the Poseidon2 permutation of `x` | Poseidon2 over BabyBear at width 16, on the chain `bbPermChain64` | [`plantBlk64_denote`](CatCrypt/Crypto/SecureCompilation/VIR/NarrowFieldPlant64.lean), [`bbPermProg64_spec'`](CatCrypt/Crypto/SecureCompilation/VIR/NarrowFieldPlant64.lean) |
| The lowered aggregated loop at the powers of `h` computes the GHASH fold of the blocks of the groups below the count, in group order, at every fuel | GHASH, four-block aggregation | [`ghashAggJ_denote_ghashFold`](CatCrypt/Crypto/SecureCompilation/VIR/Gf2Aggregate.lean) |
| A step of the address machine preserves the width map of a body | every body, across every instruction of the address machine | [`wTyped_step`](CatCrypt/Crypto/SecureCompilation/X86Backend/NarrowTyping.lean) |
| For a program rejected by the width gate `comWidthsOk`, the printer `renderOwnedCom` returns the one-line text `# UNHANDLED-WIDTH` and prints no instruction | every `Com jasminDialect` program handed to the owned exporter | [`renderOwnedCom_refuse`](CatCrypt/Crypto/SecureCompilation/X86Backend/LprogOptPipeline.lean) |

Poseidon2 is a kernel: the compiler links it under the callee contract and does not
compile it, and it has no byte theorem.

Probes of the gate accept the multiply and square of the Solinas arm at 2^255−19
(2452 B, 2399 B) and at 2^521−1 (10 018 B, 10 189 B). The dispatcher `fieldTemplateOf`
tries the unsaturated arm (`unsatReprs`) first and selects it at 2^255−19; it selects
the Solinas arm at 2^521−1.

## Measured ratios (F2)

The target is ours/fiat-C ≤ 1.25 for mul and sqr at the five primes; a proven hand kernel
retires when the template bytes measure within 1.1 of it. The table gives the ratio
ours/peer as latency / throughput, measured on the objects with `mulBlkRoute` and
`mulLoadBody` (`bench/field_bytes/results/summary.md`; every conformance arm passes).

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
| BLS12-381 | mul | 2.93 / 2.97 | blst |

The ratio is within the target at P-384, where the route selects the six-limb CIOS block
`mulBlkI`. Below six limbs the route uses `mulLoadBody`, which loads each row word of
the second factor at its row; at six limbs `mulLoadBody` measures 1.37 at P-384, against
1.16 to 1.18 for the CIOS block. The P-256 multiply has 791 instructions and nine stack
reloads of `%r14`: four reload the operand pointer, one per row, and three reload the
spilled reduction word.

Against the fastest hand kernels the latency ratios are 3.01 (mul) and 3.09 (sqr) at
BN254 and 3.24 (mul) and 3.27 (sqr) at BLS12-381, measured on the objects of the
dead-write pass (`bench/field_bytes/README.md`).

The printed Rust (`bench/fiat_rust_compare/README.md`) measures 0.68–1.18 of
fiat-crypto's Rust for mul and sqr at P-256, secp256k1 and P-384
([FIELD_TEMPLATES_VS_RUST.md](FIELD_TEMPLATES_VS_RUST.md)).

## Size of the template layer

Line counts are those of `wc -l` over the files named, from each repository root:

| part | files | lines |
|---|---|---|
| field templates | `CatCrypt/Crypto/SecureCompilation/Algebraic/FieldLimbs/*.lean` (13 files) | 8 227 |
| other families | `VIR/{TowerDialect,TowerToLimbs,NegacyclicNttTemplate,NegacyclicNttWord,NegacyclicNttWordSigned,RoundCodec,NarrowField,BasemulWord,PointwiseAcc,Gf2Dialect,Gf2Aggregate,RowLazy,Poseidon2Word}.lean` | 12 241 |
| limb lowering | `Algebraic/FieldToJasminLimbs*.lean` (4 files) | 1 324 |
| routes (development repository) | `Haxc/{FieldRoute,FieldChain,RouteChain,LatticeRoute}.lean` | 1 705 |
| instances (development repository) | `Haxc/{FieldInstances,MpnBytes,FieldFrontP256}.lean` | 1 103 |

Templates: 20 468 lines; with lowering and routes, 23 497.
