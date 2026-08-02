# CatCrypt VIR dialect map

This file records which `VIR.Dialect` carries emit traffic, which exists only to
agree with an upstream IR, and how a program reaches x86. Read it before adding a
dialect or routing a primitive through the compiler.

The algebraic tier mirrors the crypto dialects of fractalyze/prime-ir, an MLIR IR
for prime-field and elliptic-curve arithmetic. The two differ at the bottom:
prime-ir stops at MLIR and hands off to LLVM, while CatCrypt continues through a
verified jasmin lowering to an x86/ELF backend, with a constant-time and leakage
framework prime-ir does not carry. The development repository tracks the op-by-op
correspondence separately, pinned to a prime-ir release.

## The three tiers

```
HIGH  crypto / algebraic   Field  ModArith  Poly  EllipticCurve  TensorExt   (prime-ir aligned)
                                   |  (Com-transports, denote-preserving)
MID   substrate            jasminDialect  +  vec128Dialect / ymm256Dialect
                                   |  (Com.toLprogPhysAbi → renderLprogAtt)
LOW   target               Lprog  →  x86 / ELF bytes
```

`jasminDialect` is the substrate. Its scalar word ops play the part of `arith`,
its memory ops and the Lprog ABI play `memref`, the Lprog labels and jumps and
the loop emit play `scf`, and `vec128Dialect`/`ymm256Dialect` play `vector`.
There is no separate `arith`/`memref`/`scf`/`vector` substrate: jasmin carries
that traffic, with the verified backend beneath it.

## One dialect per program

`Com` is indexed by a single dialect — `inductive Com (d : Dialect) … : Ctxt d →
d.Ty → Type` (`VIR/Core.lean:137`) — so a program draws its ops from one `d`. An
op defined in a dialect of its own cannot appear in a program beside an op from
any other.

MLIR carries no such restriction; mixing is its premise. A module holds ops from
many dialects while passes lower them one at a time, so intermediate modules are
multi-dialect by construction. One prime-ir rewrite file,
`EllipticCurveToField.cpp`, emits `field` at 29 sites, `tensor` at 19, `arith` at
10 and `func` at 3, into a single module.

Two consequences shape this map:

- The agreement layer mirrors upstream's decomposition and therefore carries no
  programs. `mlirArithDialect`, `mlirMemrefDialect`, `mlirVectorDialect` and
  `mlirScfDialect` model four distinct MLIR core dialects accurately, and nothing
  can be written across them.
- The spine merged instead. `catCryptDialect` carries 54 ops spanning what MLIR
  splits four ways: word arithmetic (`arith`), `memrefGet`/`memrefSet` and the
  dynamic variants (`memref`), `vsimd`/`vpshufdC`/`vsha256rnds2` and the rest
  (`vector`), plus pairs, sums, sampling and `extCall`. It is the union those four
  would form, written as one op inductive.

A dialect's op set is therefore not free to match upstream: matching costs the
ability to write programs. This is the argument for folding an op-dialect into one
that already carries traffic rather than giving it a lowering. A lowering lets the
op reach bytes; folding lets it appear beside other ops at all.

Where two dialects share a `Ty`, the tagged op-union delegating per tag is the
established alternative — `MlirArithScfSum.lean` does this for `arith ⊕ scf`,
which the `Cif` lowering needs because an `arith.cmpi` must feed an `scf.if`
inside one `Com`. Where the `Ty`s differ, a coproduct needs an injection
`Com d → Com (d ⊕ e)`; `ComParametricityTransport.LoweringData` and its
`fundamental` lemma already reduce such an injection's denotation-preservation to
three leaf obligations, so the cost is defining the injection rather than proving
it.

## The `Com`-program transport spine (these reach bytes)

| edge | pass | denote-preservation | file:line |
|---|---|---|---|
| `fieldDialect → jasminDialect` (prime-field 1:1) | `fieldComToJasmin : LoweringData` (`= fieldFpDescent.comp modArithToJasmin`) | `fieldComToJasmin_denote` | `FieldDescent.lean:597,622` |
| `latticeDialect → jasminDialect` | `lowerLatticeToJasmin` | `lowerLatticeToJasmin_denote_eq_uncond` | `LatticeToJasminDenoteUncond.lean:161` |
| `thirDialect → jasminDialect` | `lowerThir` | `lowerThir_denote` | `ThirDialect.lean:438,517` |
| `catCryptDialect → jasminDialect` | `cryptoDialectToJasminCom` | `cryptoDialectToJasminCom_denote_eq` | `DialectToJasminCom.lean:190`; `…Correct.lean:56` |
| `jasminDialect → Lprog → x86/ELF` | `Com.toLprogPhysAbi` → `renderLprogAtt` / `compileComToElf` | print/run-faithful (virtual `Lprog`); RA+two-addr legalization KAT-gated (see x86 note) | `JasminLprogExport.lean:2256`; `CompileComToElf.lean` |

The `ec`/`poly`/`modArith` chain (`curveChainDenote`, `extChainDenote`,
`polyChainDenote`, in the development tree — it reaches curve-specific migrations
that the compiler package excludes) is op-level `rfl`
realisation (`lower_denote_preserved := rfl`) composed by transitivity over
abstract values, not a `Com`-program transport. The transport seams are the table
above; `field-prime` and `lattice` are the arms with a full `Com → jasmin → ELF`
path.

## Agreement layers

These dialects carry `rfl` theorems showing our ops match the named upstream MLIR
dialects. They have no lowering out and no emit traffic, and they exist to
substantiate the MLIR-alignment claim. Each duplicates a dialect that does carry
traffic:

| correspondence dialect | duplicates | file |
|---|---|---|
| `mlirArithDialect` | `jasminDialect` scalar ops | `MlirArithDialect.lean` |
| `mlirMemrefDialect` | `jasminDialect` memory / Lprog ABI | `MlirMemrefDialect.lean` |
| `mlirVectorDialect` | `vec128Dialect` / `ymm256Dialect` | `MlirVectorDialect.lean` |
| `mlirScfDialect` | Lprog control flow + loop emit | `MlirScfDialect.lean` |
| `mlirPolynomialDialect` | `polyDialect` (self-documents "THEORY artifact, no lowering out") | `MlirPolynomialDialect.lean` |
| `mlirArithScfDialect` | combined arith+scf agreement | `MlirArithScfSum.lean` |

### prime-ir crypto op dialects

prime-ir is `fractalyze/prime-ir`, an external MLIR dialect stack (C++/TableGen)
for prime-field and elliptic-curve arithmetic. It stops at MLIR; CatCrypt lowers
to bytes. What it closes is the op-factoring axis, and each dialect below gives one
of its crypto ops a first-class `VIR.Dialect` op with a verified denotation.

**Lineage.** The names arrive at two removes. `mod_arith`, `tensor_ext` and
`polynomial` are dialects of **HEIR**, Google's homomorphic-encryption MLIR
compiler (`github.com/google/heir`); prime-ir reuses them, and CatCrypt's
`modArithDialect` / `tensorExtDialect` / `mlirPolynomialDialect` inherit them from
there. `field`, `elliptic_curve` and the point kinds are prime-ir's own.

**Granularity.** Op granularity is where the two designs diverge, and it accounts
for the unreachable column below. prime-ir has six dialects — `Field`, `ModArith`,
`EllipticCurve`, `Poly`, `TensorExt`, `ArithExt` — and twelve conversion passes,
so each of its dialects lowers out. Its `Field` dialect alone holds fifteen ops:
`Add Sub Mul Negate Inverse Constant Cmp Bitcast Double Square PowUI ToMont
FromMont ExtToCoeffs ExtFromCoeffs`. CatCrypt spreads those fifteen across six
dialects — `fieldDialect`, `derivedDialect`, `cmpDialect`, `modArithMontDialect`,
`montInverseDialect`, `structDialect` — so each needs a lowering of its own where
each prime-ir op inherits its dialect's. `tensorExtDialect` is the group's one
dialect-level correspondence: prime-ir's `TensorExt` is a dialect, and it holds
exactly one op, `bit_reverse`.

An op-dialect can also be folded back as an op of a dialect that already reaches
bytes: `cmp` and `bitcast` into `fieldDialect`, `mont_inverse` into
`modArithDialect`, `convert_point_type` into `ecDialect`. That costs a new case in
every `match` over the receiving op type. Lowering adds an edge, folding removes a
node, and neither is the default — decide per dialect.

**Points as coordinates.** prime-ir has no abstract group type. `PointKind` is
`Affine(2)`, `Jacobian(3)`, `XYZZ(4)`, `EdAffine(2)`, `EdExtended(4)` — coordinate
tuples — and the group identity is a sentinel coordinate value: short-Weierstrass
affine `(0,0)`, Edwards affine `(0,1)`, Edwards extended `(0,c,c,0)`.
`ConvertIsZero` is then field compares and an `arith.andi`. The formulas live
outside the pass: `PointCodeGenBase<Kind>` re-instantiates the `zk_dtypes`
point-operation templates at a `FieldCodeGen` type, so the C++ that computes on
field elements emits `field.*` ops instead. Their lowering is total because the
source type is already the target representation, and nothing checks the
coordinate schedule against a group law. `EcEdwardsAffineDialect.lean` takes the
representation and adds that check: `edAdd_faithful` carries the pair onto
`EdwardsParams.add` with no hypothesis, which holds over Edwards because the
unified addition law is complete.

**What each one needs.** A dialect's value type settles whether a total lowering
can exist, so the table records it:

| dialect | value type | lowering |
|---|---|---|
| `derivedDialect` | `ZMod p` | **done** — `DerivedToFieldLowering.lean`, total, whole-program |
| `ecDialect` | `ECPoint p = Option (ZMod p × ZMod p)` | **blocked** — see below |
| `modArithMontDialect` | `ℤ` | **blocked** — target denotes `ZMod p`; needs a range invariant, not a type map |
| `ecConvertDialect` | affine / jacobian tuples | **per-coordinate** — `EcConvertToFieldLowering.lean`; not a `Com → Com` edge, because one affine pair has no single `fieldDialect` type |
| `pairingCheckDialect` | `Fp12Val p` | GT product ties to `FieldOp.ext12Mul`; the `gtIsOne` tail is a predicate |
| `cmpDialect` | booleans | no target type; carries a CT-hazard flag |
| `tensorExtDialect` | `Fin (2^k) → BitVec 64` | no matching target type |

`ecDialect` has a complete front. `CompileFromHaxPrimeIrFrontEc` recognises a hax
`point_add` or `point_double` call and builds a `Com ecDialect`,
`EcLadderSelectCT` supplies a leakage analysis, and `EllipticCurveLowering.lean`
carries the chord, tangent and Edwards schedules in `ZMod p`. A total
`Com ecDialect → Com fieldDialect` is nevertheless impossible: almost every `ECOp`
maps points to points, `.point p` denotes `ECPoint p` with a point at infinity,
and `fieldDialect` has no type for that. The schedule theorems record the same
limit — `padd_lowers_to_schedule` assumes `x₁ ≠ x₂` and `pdbl_lowers_to_schedule`
assumes `y ≠ -y`, both on `ECPoint.aff` inputs. Closing it needs an
infinity-carrying target type, or a source fragment restricted to distinct affine
points that carries the side condition along. Wiring alone will not do it.

`EllipticCurveLowering.lower_denote_preserved` is `rfl` against an identity
`realise`, so it proves less than its name suggests. The content sits in the
`*_lowers_to_schedule` theorems and their hypotheses.

Which prime-ir op each one factors:

| dialect | factors prime-ir op(s) | file |
|---|---|---|
| `derivedDialect` | `field.double` / `field.square` / `field.powui` (+ `mod_arith.double` / `mod_arith.square`) | `FieldDerivedOps.lean` |
| `cmpDialect` | `field.cmp` / `mod_arith.cmp` / `elliptic_curve.cmp` / `elliptic_curve.is_zero` (carries a per-op `publicData` CT-hazard flag) | `FieldEcCmpOps.lean` |
| `modArithMontDialect` | `mod_arith.to_mont` / `mod_arith.from_mont` / `mod_arith.mont_square` | `ModArithMontOps.lean` |
| `montInverseDialect` | `mod_arith.mont_inverse` | `ModArithMontInverse.lean` |
| `ecConvertDialect` | `elliptic_curve.convert_point_type` (affine ↔ jacobian) | `EcConvertOps.lean` |
| `tensorExtDialect` | `tensor_ext.bit_reverse` | `TensorExtDialect.lean` |
| `pairingCheckDialect` | `elliptic_curve.pairing_check` (`gtIsOne` / `pairingCheck2`; carries a `publicData` CT-hazard flag) — **NOT correspondence-only**, see below | `EcPairingCheckOps.lean` / `EcPairingCheckLowering.lean` / `Fp12Gt.lean` |

`pairingCheckDialect` is the exception in this table. Its GT product lowers onto
`FieldOp.ext12Mul` (`EcPairingCheckLowering.lean`, `pairingCheck2_lower_denote`)
and rides the `extChainDenote_fp12` chain down through `Fp6`
and `ModArith` to x86 bytes. Only its equality tail stays at the bit layer:
`gtIsOne`, the `== 1` test from `Fp12Gt.lean`, is a `cmp`-style predicate. Its GT
inputs come from the proven tower-level `BLS12381PairingTowerEmit.pairingEmit`
(finalExp ∘ miller). Nothing here claims the schedule equals the mathematical
Tate or Weil pairing.

## Redundant / non-dialect

- **`nttDialect`, `nttLayerDialect`, `nttFoldDialect`** — absent, and not to be
  reintroduced. They were optimizer-local NTT denotation experiments
  (`Optimizer/Lattice/Ntt*ComDenote.lean`) whose denotations were never proved
  equal to the rendered kernel, and they duplicated the bytes-tied NTT
  verification (`polyDialect` lowering, `latticeNttMul_compile_correct`). Only a
  rot-guard aggregator imported them. The NTT emit is `LatticeNttEmit`'s
  `emitMlkemNttFull16wayJazz`, and the NTT tie is `latticeDialect`/`polyDialect`.
- **`NamedSSA`** (`ComBuilder.lean`) — a builder, not a dialect. It resolves
  level-named SSA into de-Bruijn `Com jasminDialect`, targeting the bottom tier,
  which makes it a leaf-kernel authoring convenience used by `FieldEmitGolden*`
  and `RelationalFrontEC*`. Routing a front end through it bypasses the algebraic
  tier entirely.
- **`toyDialect`, `smokeDialect`, `pilot`** — test scaffolding.
- **`latticeDialectG`** — a family, not a dialect. `latticeDialect` and
  `realLatticeDialect` are its `.bits` and `.poly` instantiations: one type
  alphabet, one set of op tags, one `DialectSignature`, two `TyDenote` instances
  (`Fin n → BitVec 16` and `CPolynomial (ZMod q)`). The lowering to jasmin is on
  the `.bits` instantiation, and the `.poly` one is the specification view, so the
  generated graph shows the family and `realLatticeDialect` as reaching nothing.

## Reading the generated graph

`scripts/gen-lowering-graph.sh` derives the graph below from source (`--check` in
CI, `--write` to regenerate). Three points about it invite misreading:

- **Two byte sinks, `jasminDialect` and `x86Dialect`.** Jasmin is a waypoint; the
  x86 backend continues past it, and `Com (x86Dialect w)` over `JState w` is the
  level `ElfObject` serialises. `scfDialect` lowers straight into `x86Dialect`
  (`lowerScfFor`, with `scfFor_lowering_denote`) without touching jasmin, so it
  sits on the emit path.
- **"No path" reports `Com`-level edges only.** A denotation theorem can tie a
  dialect to a live backend where no lowering function does, and such a dialect
  produces bytes while reading as unreachable. `tileDialect` is the case to know:
  `TileDialectModelTie` proves its denotation equals `TileBackend.TileModel`'s
  `evalTileOp`, and `TileBackend/ComToTileIR` emits CUDA tile IR from those ops.
  The SIMD emit reaching our own bytes takes a separate route —
  `ZmmArithBridgeCom` and `VectorBackendBridgeCom` build `Com jasminDialect`
  directly and prove it equal to the same tile and vector model. Tiles are in use;
  the tile dialect is off the jasmin route.
- **The prime-ir family reads as unreachable while having fronts**, as the section
  above describes.

## Front-end landing (hax → IR)

Two ingestion lanes, both terminating at or near jasmin. The algebraic tier is fed
by hand or relationally rather than from hax, and that gap is recorded below:

- **ANF scalar:** `hax ImpExpr → impExprToThir → Thir → thirToJasmin → Com jasminDialect`
  (`ThirToComFront.lean`; entry `CompileFromHax.lean:73`).
- **loops/arrays:** `hax ImpExpr → haxToLowCT → LowCT → catCryptDialect / lattice`
  (`Hax/HaxToLowCT.lean`; `PipelineMap.lean`).
- A second, uniform THIR route `Thir → Com thirDialect → lowerThir → jasmin`
  (`CompileFromHaxDialect.lean`, ~25 `*ThirEmit` kernels) is live but
  secondary; it has not displaced `thirToJasmin` in `compileFromHax`.

The algebraic dialects `fieldDialect` and `polyDialect` are fed either by
hand-authored `Com fieldDialect` on the scheme side, or by the
relational front (`RelationalCompileHigh.lean`, `spec → Com fieldDialect`), and
then descend through the spine above. The hand-authored feed is interim. A
hand-written `Com` paired with a hand-written spec proves nothing about the
source, so each such kernel is to be rerouted through `RelationalCompile` or a
front as coverage reaches it.

Carrying hax up into the algebraic tier — an edge from `thir`/`ImpExpr` to
`field`/`catCrypt` — is the outstanding piece. `ThirFrontProbe.lean` is the
smallest witness that it is reachable, and the memory backend already supports
it: `stackStore` and `stackLoad` have a faithful emitting x86 backend in
`JasminLsemGeneralFaithfulMem`.

<!-- BEGIN GENERATED lowering-graph -->

_Generated by `scripts/gen-lowering-graph.sh`. Do not edit by hand._

### Lowering edges (a `def` taking `Com A` to `Com B`)

| from | to | via |
|---|---|---|
| \`arithDialect\` | \`jasminDialect\` | \`lowerArithToJasmin\` |
| \`catCryptDialect\` | \`jasminDialect\` | \`blake2bGJazzA\` |
| \`catCryptDialect\` | \`jasminDialect\` | \`chacha20QRJazzA\` |
| \`catCryptDialect\` | \`jasminDialect\` | \`cryptoDialectToJasminCom\` |
| \`catCryptDialect\` | \`jasminDialect\` | \`reduceFrontCom\` |
| \`catCryptDialect\` | \`jasminDialect\` | \`regPassA1prime\` |
| \`catCryptDialect\` | \`jasminDialect\` | \`sha256Sigma0Jazz\` |
| \`catCryptDialect\` | \`jasminDialect\` | \`sha512Sigma0Jazz\` |
| \`catCryptDialect\` | \`jasminDialect\` | \`subFrontCom\` |
| \`catCryptDialect\` | \`jasminDialect\` | \`toJasmin\` |
| \`catCryptDialect\` | \`jasminDialect\` | \`toJasmin4\` |
| \`catCryptDialect\` | \`jasminDialect\` | \`vProg\` |
| \`catCryptDialect\` | \`mlirArithDialect\` | \`translate\` |
| \`catCryptDialect\` | \`mlirMemrefDialect\` | \`translate\` |
| \`derivedDialect\` | \`fieldDialect\` | \`lowerDerivedToField\` |
| \`fieldDialect\` | \`derivedDialect\` | \`op-level lowering\` |
| \`fieldDialect\` | \`jasminDialect\` | \`fieldComToJasmin\` |
| \`fieldDialect\` | \`jasminDialect\` | \`lowerComK\` |
| \`fieldDialect\` | \`jasminDialect\` | \`lowerComRBB\` |
| \`fieldDialect\` | \`jasminDialect\` | \`op-level lowering\` |
| \`fieldDialect\` | \`jasminDialect\` | \`translBB\` |
| \`fieldDialect\` | \`modArithDialect\` | \`fieldFpDescent\` |
| \`fpDialect\` | \`modArithDialect\` | \`lowerFieldToModArith\` |
| \`funcDialect\` | \`jasminDialect\` | \`lowerFuncToJasmin\` |
| \`latticeDialect\` | \`jasminDialect\` | \`latticeLoweringData\` |
| \`latticeDialect\` | \`jasminDialect\` | \`lowerLatticeToJasmin\` |
| \`latticeDialect\` | \`mlirPolynomialDialect\` | \`translate\` |
| \`memrefDialect\` | \`jasminDialect\` | \`lowerMemrefToJasmin\` |
| \`memrefDialect\` | \`x86Dialect\` | \`op-level lowering\` |
| \`modArithDialect\` | \`jasminDialect\` | \`modArithToJasmin\` |
| \`scfDialect\` | \`x86Dialect\` | \`op-level lowering\` |
| \`thirDialect\` | \`catCryptDialect\` | \`lowerThirToCatCrypt\` |
| \`thirDialect\` | \`catCryptDialect\` | \`lowerThirToCrypto\` |
| \`thirDialect\` | \`fieldDialect\` | \`lowerThirToField\` |
| \`thirDialect\` | \`jasminDialect\` | \`compileThirViaCatCryptOrFlat\` |
| \`thirDialect\` | \`jasminDialect\` | \`lowerThir\` |
| \`thirDialect\` | \`jasminDialect\` | \`thirToJasminViaCatCrypt\` |
| \`thirDialect\` | \`jasminDialect\` | \`thirToJasminViaField\` |
| \`vectorDialect\` | \`jasminDialect\` | \`lowerVectorToJasmin\` |

### Reaches bytes via `jasminDialect or x86Dialect` (transitively) — the emit spine

- `arithDialect`
- `catCryptDialect`
- `derivedDialect`
- `fieldDialect`
- `fpDialect`
- `funcDialect`
- `latticeDialect`
- `memrefDialect`
- `modArithDialect`
- `scfDialect`
- `thirDialect`
- `vectorDialect`

### No path to `jasminDialect or x86Dialect` — correspondence / theory layers

- `cmpDialect`
- `ecConvertDialect`
- `ecDialect`
- `edAffDialect`
- `ladderDialect`
- `latticeDialectG`
- `mlirArithDialect`
- `mlirArithScfDialect`
- `mlirMemrefDialect`
- `mlirPolynomialDialect`
- `mlirScfDialect`
- `mlirVectorDialect`
- `modArithMontDialect`
- `montInverseDialect`
- `pairingCheckDialect`
- `pilot`
- `polyDialect`
- `quantumDialect`
- `realLatticeDialect`
- `smokeDialect`
- `structDialect`
- `tensorExtDialect`
- `tileDialect`
- `toyDialect`

<!-- END GENERATED lowering-graph -->
