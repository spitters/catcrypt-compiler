# CatCrypt VIR dialect map

This file records which `VIR.Dialect` has a lowering path to bytes, which exists to
agree with an upstream IR, and how a program reaches x86. Read it before adding a
dialect or routing a primitive through the compiler. Paths are relative to
`CatCrypt/Crypto/SecureCompilation/`; declarations are cited by name.

The algebraic tier follows the crypto dialects of fractalyze/prime-ir, an MLIR IR
for prime-field and elliptic-curve arithmetic. prime-ir stops at MLIR; CatCrypt
continues through a jasmin lowering to an x86/ELF backend, with a constant-time and
leakage framework. The op-by-op correspondence is the table in the section on
prime-ir crypto op dialects below.

## Tiers

```
HIGH  algebraic   fieldDialect  modArithDialect  polyDialect  ecDialect  tensorExtDialect
MID   lowering    catCryptDialect  thirDialect  latticeDialect  arith/memref/vector/func
LOW   target      jasminDialect → Lprog → x86 / ELF bytes;  scf, memref (x86) → x86Dialect
```

In this package no `Com`-level lowering connects the HIGH tier to jasmin: the graph
at the end of this file lists `fieldDialect`, `modArithDialect`, `fpDialect`,
`polyDialect` and `ecDialect` under "No path". The MID dialects lower into
`jasminDialect`. The substrate is `jasminDialect`: its
`regArith` ops carry word arithmetic, `stackLoad`/`stackStore` and the `Lprog` ABI
carry memory, and `vsimd`/`vpackZMM` carry packed vector arithmetic. The neutral
dialects `arithDialect`, `memrefDialect`, `vectorDialect` and `funcDialect`
(`Dialects/`) each lower into it, and `scfDialect` and the machine-level
`memrefDialect` (`X86Backend/`) lower into `x86Dialect`.

## One dialect per program

`Com` is indexed by a single dialect (`inductive Com` in `VIR/Core.lean`), so a
program draws its ops from one `d`. An op defined in a dialect of its own cannot
appear in a program beside an op from any other. MLIR carries no such restriction:
a module holds ops from many dialects while passes lower them one at a time.

Two consequences shape this map:

- The agreement layer mirrors upstream's decomposition and therefore carries no
  programs. `mlirArithDialect`, `mlirMemrefDialect`, `mlirVectorDialect` and
  `mlirScfDialect` model four MLIR core dialects, and nothing can be written across
  them.
- `catCryptDialect` carries 54 ops spanning what MLIR splits four ways: word
  arithmetic (`arith`), `memrefGet`/`memrefSet` and their dynamic variants
  (`memref`), `vsimd`/`vpshufdC`/`vsha256rnds2` and the other packed ops (`vector`),
  plus pairs, sums, sampling and `extCall`, in one op inductive.

A dialect's op set is therefore not free to match upstream: matching costs the
ability to write programs. Folding an op into a dialect that already carries
programs lets it appear beside other ops; a lowering lets it reach bytes. The
folded ops and their agreement theorems are in `VIR/FoldedOpAgreement.lean`.

A tagged op-union over a shared type alphabet, delegating per tag, combines two
dialects: `VIR/MlirArithScfSum.lean` for `arith ⊕ scf`, which share `CryptoTy`, and
`VIR/FieldCmpSum.lean` for `fieldDialect` and `cmpDialect`, over the alphabet
`FieldCmpTy` built for the pair. `VIR/DialectCoproduct.lean` gives the disjoint sum
`Dialect.sum`, in which values do not flow between the summands.
`ComParametricityTransport.LoweringData` and its `fundamental` lemma reduce the
denotation preservation of a structural lowering to three leaf obligations
(`VarTransports`, `OpLowerTransports`, `MapValExtends`).

## `Com`-program transports to bytes

| edge | pass | denotation preservation |
|---|---|---|
| `latticeDialect → jasminDialect` | `lowerLatticeToJasmin` (`VIR/LatticeToJasmin.lean`) | `lowerLatticeToJasmin_denote_eq_uncond` (`VIR/LatticeToJasminDenoteUncond.lean`), for every program. In `latticeDialect` (the `.bits` instance of `latticeDialectG`) `ntt` and `invntt` denote the identity and `basemul` pointwise multiplication, so the theorem is about that model. |
| `thirDialect → jasminDialect` | `lowerThir` (`VIR/ThirDialect.lean`) | `lowerThir_denote`, for every program |
| `thirDialect → catCryptDialect` | `lowerThirToCatCrypt` (`VIR/ThirToCatCryptDialect.lean`), `lowerThirToCrypto` (`ThirToCryptoDialect.lean`); partial | `lowerThirToCatCrypt_denote`, `lowerThirToCrypto_denote`, whenever the lowering returns a program |
| `catCryptDialect → jasminDialect` | `cryptoDialectToJasminCom` (`VIR/DialectToJasminCom.lean`); partial | `cryptoDialectToJasminCom_denote_eq'` (`VIR/DialectToJasminComCorrect.lean`), whenever the lowering returns a program |
| `arithDialect`, `memrefDialect`, `vectorDialect`, `funcDialect` `→ jasminDialect` | `lowerArithToJasmin`, `lowerMemrefToJasmin`, `lowerVectorToJasmin`, `lowerFuncToJasmin` (`Dialects/*ToJasmin.lean`) | `lowerArithToJasmin_denote`, `lowerMemrefToJasmin_denote`, `lowerVectorToJasmin_denote`, `lowerFuncToJasmin_denote` (`Dialects/*ToJasminDenote.lean`), for every program |
| `scfDialect → x86Dialect` | `lowerScfFor` (`X86Backend/ScfDialect.lean`), op level | `scfFor_lowering_denote` |
| `memrefDialect → x86Dialect` (`X86Backend/MemrefDialect.lean`) | `lowerMLoad`, `lowerMStore`, op level | `mLoad_lowering_denote`, `mStore_lowering_denote` |
| `jasminDialect → Lprog → x86/ELF` | `Com.toLprogPhysAbi` (`VIR/JasminLprogExport.lean`), then `renderLprogAtt` (`X86Backend/LprogAsmPrinter.lean`) or `compileComToElf` (`X86Backend/CompileComToElf.lean`) | `toLprogPhysAbi_faithful_uniform` (`X86Backend/ToLprogFaithfulAssembled.lean`) for `UniformRegArith` programs under its hypotheses; the package README states the fragment |

## Agreement layers

These dialects carry `rfl` theorems showing that their ops match the named upstream
MLIR dialects. They have no lowering to bytes. The `translate` functions of
`VIR/MlirArithDialect.lean`, `VIR/MlirMemrefDialect.lean` and
`VIR/MlirPolynomialDialect.lean` map `catCryptDialect` and `latticeDialect` programs
into them.

| correspondence dialect | corresponds to | file |
|---|---|---|
| `mlirArithDialect` | `jasminDialect` scalar ops | `VIR/MlirArithDialect.lean` |
| `mlirMemrefDialect` | `jasminDialect` memory ops and `Lprog` ABI | `VIR/MlirMemrefDialect.lean` |
| `mlirVectorDialect` | element-wise lane arithmetic, as in the packed ops of `jasminDialect` | `VIR/MlirVectorDialect.lean` |
| `mlirScfDialect` | `Lprog` control flow and loop emit | `VIR/MlirScfDialect.lean` |
| `mlirPolynomialDialect` | `polyDialect` | `VIR/MlirPolynomialDialect.lean` |
| `mlirArithScfDialect` | combined arith and scf agreement | `VIR/MlirArithScfSum.lean` |

## prime-ir crypto op dialects

Each dialect below gives prime-ir crypto ops a `VIR.Dialect` op with a denotation.
The prime-ir op names are those the modules' docstrings cite.

| dialect | prime-ir op(s) | file |
|---|---|---|
| `derivedDialect` | `field.double`, `field.square`, `field.powui`, `mod_arith.double`, `mod_arith.square` | `VIR/FieldDerivedOps.lean` |
| `cmpDialect` | `field.cmp`, `mod_arith.cmp`, `elliptic_curve.cmp`, `elliptic_curve.is_zero` (with a per-op `publicData` constant-time flag) | `VIR/FieldEcCmpOps.lean` |
| `modArithMontDialect` | `mod_arith.to_mont`, `mod_arith.from_mont`, `mod_arith.mont_square` | `VIR/ModArithMontOps.lean` |
| `modArithDialect` (folded op `montInverse`) | `mod_arith.mont_inverse` | `VIR/ModArithMontInverse.lean`, `VIR/FoldedOpAgreement.lean` |
| `ecConvertDialect` | `elliptic_curve.convert_point_type` (affine ↔ Jacobian) | `VIR/EcConvertOps.lean` |
| `tensorExtDialect` | `tensor_ext.bit_reverse` | `VIR/TensorExtDialect.lean` |
| `pairingCheckDialect` | `elliptic_curve.pairing_check` (`gtIsOne`, `pairingCheck2`, with a `publicData` flag) | `VIR/EcPairingCheckOps.lean`, `VIR/EcPairingCheckLowering.lean`, `VIR/Fp12Gt.lean` |

`VIR/FoldedOpAgreement.lean` places seven ops in the two dialects that carry
programs: `montInverse` and the coefficient-vector and bitcast reinterprets
(`polyToTensor`, `polyFromTensor`, `residueEncode`, `residueDecode`) in
`modArithDialect`, and `fieldDouble`/`fieldSquare` in `fieldDialect`. Each agreement
theorem (`montInverse_agrees`, `fieldSquare_agrees` and siblings) holds by `rfl`.
`fieldPow` stays in `derivedDialect`.

A dialect's value type decides which lowerings can exist:

| dialect | value type | lowering |
|---|---|---|
| `derivedDialect` | `ZMod p` | `lowerDerivedToField` (`VIR/DerivedToFieldLowering.lean`), total, to `fieldDialect` |
| `ecDialect` | `ECPoint p = Option (ZMod p × ZMod p)` | none; see below |
| `modArithMontDialect` | `ℤ` | none; the target denotes `ZMod p` |
| `ecConvertDialect` | affine and Jacobian coordinate tuples | per coordinate (`VIR/EcConvertToFieldLowering.lean`), one `Com fieldDialect` schedule per output coordinate; not a `Com → Com` edge |
| `pairingCheckDialect` | `Fp12Val p` | op level: `pairingCheck2_lower_denote` states that `pairingCheck2` denotes `gtIsOneF` of an `ext12Mul` product schedule in `fieldDialect` |
| `cmpDialect` | booleans | `cmpLowering` into the shared-alphabet dialect `fieldCmpDialect` (`VIR/FieldCmpSum.lean`) |
| `tensorExtDialect` | `Fin (2^k) → BitVec 64` | none |

`fieldDialect` itself has no lowering to jasmin in this package, so none of these
lowerings reaches bytes.

`ecDialect` has a front: `CompileFromHaxPrimeIrFrontEc.lean` recognises a hax
`point_add` or `point_double` call node and emits a single-op `Com ecDialect` leaf,
and
`VIR/EllipticCurveLowering.lean` carries the chord and tangent schedules in `ZMod p`.
A total `Com ecDialect → Com fieldDialect` does not exist: most `ECOp`s map points to
points, `.point p` denotes `ECPoint p` with a point at infinity, and `fieldDialect`
has no type for it. The schedule theorems record the same limit:
`padd_lowers_to_schedule` assumes `x₁ ≠ x₂` and `pdbl_lowers_to_schedule` assumes
`y ≠ -y`, both on affine inputs. `EllipticCurveLowering.lower_denote_preserved` is
`rfl` against an identity `realise`; the content is in the `*_lowers_to_schedule`
theorems and their hypotheses. For twisted Edwards coordinates,
`VIR/EcEdwardsAffineDialect.lean` proves `edAdd_faithful`, which carries the
coordinate-pair add onto `EdwardsParams.add` with no hypothesis on the operands.

No theorem here states that the pairing-check product schedule equals a
mathematical Tate or Weil pairing.

## Non-dialect and scaffolding

- There is no NTT-specific dialect. The ML-KEM NTT text is
  `VIR/LatticeNttEmit.lean`'s `emitMlkemNttFull16wayJazz`, a string renderer that no
  theorem relates to the transform. The module's 4-way butterfly kernels have a
  semantics (`runNtt4way` over `ntt4wayBody`), and
  `mlkem_ntt_4way_denotation_preserves` states that they compute Cooley–Tukey
  butterflies in wrapping word arithmetic.
  `latticeNttMul_compile_correct`
  (`VIR/CompilerCorrectness.lean`) concerns the `.bits` lattice model described in
  the transport table.
- `NamedSSA` (`ComBuilder.lean`) is a builder, not a dialect: it resolves
  level-named SSA into de Bruijn `Com jasminDialect`, and `FieldEmitGoldenGf256`,
  `FieldEmitGoldenMul`, `FieldEmitGoldenReduces` and `RelationalFrontEC` use it. A
  `Com` written with it is a builder `Com` at the jasmin tier.
- `toyDialect`, `smokeDialect`, `pilot`, and the coproduct examples `numDialect`,
  `flagDialect`, `mixedDialect` are test and example scaffolding.
- `latticeDialectG` is a family: `latticeDialect` and `realLatticeDialect` are its
  `.bits` and `.poly` instances, with one type alphabet, one op set, one
  `DialectSignature` and two `TyDenote` instances (`Fin n → BitVec 16` and
  `CPolynomial (ZMod q)`). The lowering to jasmin is on the `.bits` instance; the
  `.poly` instance is the specification view and reaches nothing.

## Reading the lowering graph

- There are two byte sinks, `jasminDialect` and `x86Dialect`. `Com (x86Dialect w)`
  over `JState w` is the machine level. `scfDialect` lowers into `x86Dialect`
  (`lowerScfFor`, `scfFor_lowering_denote`) without passing through jasmin.
- "No path" reports `Com`-level edges only. A denotation theorem can tie a dialect
  to a backend where no lowering function does. `tileDialect` is such a case:
  `VIR/TileDialectModelTie.lean` proves its op denotation equal to the per-lane
  semantics of `TileBackend/TileModel.lean` (`evalTileOp`), and
  `TileBackend/ComToTileIR.lean` emits `cuda_tile` MLIR text from tile programs.
  `TileBackend/ZmmArithBridgeCom.lean` and `TileBackend/VectorBackendBridgeCom.lean`
  express the packed lane arithmetic as `Com jasminDialect` programs over `vpackZMM`
  and `vsimd` ops.
- The prime-ir family reads as unreachable although `ecDialect` has a front, as the
  section above describes.

## Front-end landing (hax → IR)

- ANF scalar: `hax ImpExpr → impExprToThir → Thir → thirToJasmin → Com jasminDialect`
  (`ThirToComFront.lean`; `compileFromHax` in `CompileFromHax.lean`, with
  `compileFromHax_denote`).
- Loops and arrays: `hax ImpExpr → haxToLowCT → LowCT → catCryptDialect / lattice`
  (`CatCrypt/Crypto/Hax/HaxToLowCT.lean`; `PipelineMap.lean`).
- Routed THIR: `Thir → Com thirDialect → lowerThir → Com jasminDialect`
  (`CompileFromHaxDialect.lean`: `thirToThirCom_denote`,
  `thirToJasminViaThir_denote`). `compileFromHax` uses `thirToJasmin` directly.
- THIR into `catCryptDialect`: `lowerThirToCatCrypt` and `lowerThirToCrypto`, and the
  composite `thirToJasminViaCatCrypt` (`VIR/ThirToJasminViaCatCrypt.lean`,
  `thirToJasminViaCatCrypt_denote`) and its fallback form
  `compileThirViaCatCryptOrFlat` (`VIR/ThirToJasminViaCatCryptOrFlat.lean`).
  `ThirFrontProbe.lean` is a one-op instance of the same edge.

Multi-op `fieldDialect` and `polyDialect` programs are written in Lean or produced
by the relational fronts (`RelationalCompileHigh.lean`,
`PolyRelationalCompileHigh.lean`). From hax, `CompileFromHaxPrimeIrField.lean` and
`CompileFromHaxPrimeIrFront.lean` emit a recognized `Field` call as a single-op
`Com fieldDialect` leaf, and `CompileFromHaxPrimeIrFrontEc.lean` does the same for
`ecDialect`.

## Lowering graph

An edge is a `def` whose type takes a `Com A` program to a `Com B` program (possibly
under `Option`), a `LoweringData A B` record, or an op-level lowering with a
preservation theorem. Wrappers that only apply one of these to a fixed program are
not listed. The table covers the modules of this package.

### Lowering edges

| from | to | via |
|---|---|---|
| `arithDialect` | `jasminDialect` | `lowerArithToJasmin` |
| `catCryptDialect` | `jasminDialect` | `cryptoDialectToJasminCom` |
| `catCryptDialect` | `mlirArithDialect` | `MlirArithDialect.translate` |
| `catCryptDialect` | `mlirMemrefDialect` | `MlirMemrefDialect.translate` |
| `cmpDialect` | `fieldCmpDialect` | `cmpLowering` |
| `derivedDialect` | `fieldDialect` | `lowerDerivedToField` |
| `fieldDialect` | `fieldCmpDialect` | `fieldLowering` |
| `fpDialect` | `modArithDialect` | `lowerFieldToModArith` |
| `funcDialect` | `jasminDialect` | `lowerFuncToJasmin` |
| `latticeDialect` | `jasminDialect` | `lowerLatticeToJasmin`, `latticeLoweringData` |
| `latticeDialect` | `mlirPolynomialDialect` | `MlirPolynomialDialect.translate` |
| `memrefDialect` (`Dialects/Memref.lean`) | `jasminDialect` | `lowerMemrefToJasmin` |
| `memrefDialect` (`X86Backend/MemrefDialect.lean`) | `x86Dialect` | op level: `lowerMLoad`, `lowerMStore` |
| `scfDialect` | `x86Dialect` | op level: `lowerScfFor` |
| `thirDialect` | `catCryptDialect` | `lowerThirToCatCrypt`, `lowerThirToCrypto` |
| `thirDialect` | `jasminDialect` | `lowerThir`, `thirToJasminViaCatCrypt`, `compileThirViaCatCryptOrFlat` |
| `vectorDialect` | `jasminDialect` | `lowerVectorToJasmin` |

### Reaches `jasminDialect` or `x86Dialect`

- `arithDialect`
- `catCryptDialect`
- `funcDialect`
- `latticeDialect`
- `memrefDialect` (both)
- `scfDialect`
- `thirDialect`
- `vectorDialect`

### No path to `jasminDialect` or `x86Dialect`

- `cmpDialect`
- `derivedDialect`
- `ecConvertDialect`
- `ecDialect`
- `edAffDialect`
- `fieldCmpDialect`
- `fieldDialect`
- `flagDialect`
- `fpDialect`
- `mixedDialect`
- `mlirArithDialect`
- `mlirArithScfDialect`
- `mlirMemrefDialect`
- `mlirPolynomialDialect`
- `mlirScfDialect`
- `mlirVectorDialect`
- `modArithDialect`
- `modArithMontDialect`
- `numDialect`
- `pairingCheckDialect`
- `pilot`
- `polyDialect`
- `quantumDialect`
- `realLatticeDialect`
- `smokeDialect`
- `tensorExtDialect`
- `tileDialect`
- `toyDialect`
