# Templates with bounds certificates

Companion to [FIELD_TEMPLATES_VS_RUST.md](FIELD_TEMPLATES_VS_RUST.md), which compares the
printed Rust with the Rust ecosystem. A path under `Haxc/`, `VIR/`, `Algebraic/` or
`X86Backend/` is relative to `CatCrypt/Crypto/SecureCompilation/`.

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

At the bytes, the field family has one theorem over its records
(`field_correct_bytes`, `Haxc/FieldBytes.lean`). The per-instance hypothesis is acceptance by the
region back half `compileRegion` (`Haxc/RegionBackend.lean`), the back half of the compiler
`compileA`, with the decided gate of `compileRegion_correct`. For a result `(P', bytes)` of
`compileRegion` on the route program of the instance, the theorem gives a halting run of
the decoded bytes from which the layout reads back the value of the template. An instance
with an accepted program is therefore a theorem together with the result of running the
gate.

## Instances at the bytes

The hypothesis of each theorem below is that `compileRegion` returns a result on the
route program of the instance. The instances are kernels, which programs compiled by
`compileA` call as linked functions. The byte-level constant-time checker `ctGateB`
(`Haxc/CTPub.lean`) decides constant time of accepted bytes with `%rsp` and the array
pointers public and the limb contents and scalar words secret.

### Fields: Montgomery multiply, square, add, subtract

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

### mpn, the prime-ir front, lattice, symmetric and towers

Instances with an accepted program. Each theorem holds for a result of `compileRegion` on
the route program of the instance, after the field front for the prime-ir row.

| Statement proved | Programs | Lean names |
|---|---|---|
| The decoded bytes halt in a state from which the layout reads back `n + 1` words: the sum with its carry, the difference with its borrow, the product by one word with its high word, or that product added to the destination | `mpn_add_n`, `mpn_sub_n`, `mpn_mul_1`, `mpn_addmul_1` at every `n`; accepted at `n = 4` and `n = 8` | `mpn_add_n_bytes_correct`, `mpn_sub_n_bytes_correct`, `mpn_mul_1_bytes_correct`, `mpn_addmul_1_bytes_correct` (`Haxc/MpnBytes.lean`) |
| The field front accepts the surface function, and the decoded bytes halt in a state from which the layout reads back the Montgomery limbs of `fe_mul_add a b c` | prime-ir `fe_mul_add` at P-256, from the surface function to the bytes | `fieldFront_accepts_p256` (`Haxc/FieldFrontP256.lean`), [`impArgsNF_sound`](CatCrypt/Crypto/Hax/ImpToNF.lean), `fe_mul_add_bytes_p256` (`Haxc/FieldInstances.lean`) |

Theorems over every program the gate accepts. The hypothesis of each is the equation
that `compileRegion` returns `(P', bytes)` on the route program named.

| Statement proved | Programs | Lean names |
|---|---|---|
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
compile it.

The dispatcher `fieldTemplateOf` (`Haxc/FieldCorrect.lean`) tries the unsaturated arm
(`unsatReprs`, `Haxc/FieldRouteUnsat.lean`) before the Solinas arm.

## Printed Rust

[FIELD_TEMPLATES_VS_RUST.md](FIELD_TEMPLATES_VS_RUST.md) compares the printed Rust of the
field templates with fiat-crypto's Rust and the other Rust field crates.

## Size of the template layer

Line counts are those of `wc -l` over the files named:

| part | files | lines |
|---|---|---|
| field templates | `Algebraic/FieldLimbs/*.lean` (13 files) | 8 251 |
| other families | `VIR/{TowerDialect,TowerToLimbs,NegacyclicNttTemplate,NegacyclicNttWord,NegacyclicNttWordSigned,RoundCodec,NarrowField,BasemulWord,PointwiseAcc,Gf2Dialect,Gf2Aggregate,RowLazy,Poseidon2Word}.lean` | 12 405 |
| limb lowering | `Algebraic/FieldToJasminLimbs*.lean` (4 files) | 1 575 |
| routes | `Haxc/{FieldRoute,RouteChain}.lean` | 669 |
| instances | `Haxc/{FieldInstances,MpnBytes,FieldFrontP256}.lean` | 1 097 |

Templates: 20 656 lines; with lowering and routes, 22 900.
