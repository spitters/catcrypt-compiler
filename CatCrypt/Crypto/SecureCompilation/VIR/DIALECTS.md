# CatCrypt VIR dialect map

This file records which `VIR.Dialect` has a lowering path to bytes, which exists to
agree with an upstream IR, and how a program reaches x86. Read it before adding a
dialect or routing a primitive through the compiler. Paths are relative to
`CatCrypt/Crypto/SecureCompilation/`; declarations are cited by name. A dialect
or module of the dev package is marked "(dev)"; the generated block names that tree
`SSProve-lean`.

The algebraic tier follows the crypto dialects of fractalyze/prime-ir, an MLIR IR
for prime-field and elliptic-curve arithmetic. prime-ir stops at MLIR; CatCrypt
continues through a jasmin lowering to an x86/ELF backend, with a constant-time and
leakage framework. The op-by-op correspondence is the table in the section on
prime-ir crypto op dialects below.

## Tiers

```
FRONT     normal form  nfDialect  (structured: NFProg nfDialect)
HIGH      algebraic    fieldDialect  modArithDialect  polyDialect  ecDialect  ringDialect
                       tensorExtDialect  ladderDialect (dev)
MID       lowering     catCryptDialect  thirDialect  latticeDialect  arith/memref/vector/func
LOW       target       jasminDialect → Lprog → x86 / ELF bytes;  scf, memref (x86) → x86Dialect
```

`nfDialect` (`VIR/NFDialect.lean`) is the value-semantic dialect of the hax normal
form; its programs are `NFProg nfDialect` and reach bytes through the structured
layer (next section). Two HIGH-tier dialects reach jasmin at the `Com` level, each on
a fragment: `fieldDialect`, through `lowerK` (`Algebraic/FieldToJasminWord.lean`) on
the `GoodW p` fragment at a `SingleWordField p` and through the limb templates
`fieldComOf` (`Algebraic/FieldToJasminLimbs.lean`); and `modArithDialect`, through
`loweringA` (`Algebraic/ModArithToJasminLimbsMont4.lean`, four 64-bit limbs at a
`Mont4Prime`). `fpDialect` reaches bytes through `lowerFieldToModArith` into
`modArithDialect`. `ringDialect`, `polyDialect`, `ecDialect`, `tensorExtDialect` and
`ladderDialect` have no path. The MID dialects lower into `jasminDialect`. The
substrate is `jasminDialect`: its `regArith` ops carry word arithmetic,
`stackLoad`/`stackStore` and the `Lprog` ABI carry memory, and `vsimd`/`vpackZMM`
carry packed vector arithmetic. The neutral dialects `arithDialect`,
`memrefDialect`, `vectorDialect` and `funcDialect` (`Dialects/`) each lower into it,
and `scfDialect` and the machine-level `memrefDialect` (`X86Backend/`) lower into
`x86Dialect`.

## Structured layer

`Com d` (`VIR/Core.lean`) is straight-line. Loops and branches over a dialect `d`
are `NFProg d` (`VIR/NFProg.lean`): `forLoop` (counted, carried tuple), `ifThenElse`
(results), `whileLoop` (exit flag), with `Com d` as the straight-line pieces. A
dialect admits `NFProg` when it has `HasWord64` and `HasBoolBit` instances:
`nfDialect`, `catCryptDialect` and `jasminDialect` (`VIR/NFProgJasmin.lean`) have
both, and `quantumDialect` has `HasBoolBit` only. `ComL`
(`VIR/JasminLprogExport/ExportLoops.lean`) is the loop form of the jasmin export.
`ComR` (`VIR/Regions.lean`), `mlirScfDialect`, the `ScfProg` of
`MLIRBackend/ComToVeir.lean` and the ladder fold of `ladderDialect` are older
structured forms.

`NFProg.map` and `NFProg.map?` (`VIR/NFProgMap.lean`) carry a block lowering
(`BlockLoweringData`, or the partial `PartialBlockLowering`) from `Com` to `NFProg`,
with `map_denote` and `map?_denote`; `VIR/BlockLoweringExtend.lean` extends a block
lowering to a sum of op sets, and `VIR/DialectOpSum.lean` gives the op-union
`Dialect.opSum` with its injections `inl`, `inr` as `LoweringData`. These are
generic in their dialects and contribute no edge between named dialects.

Regions, read as morphisms. A region body `NFProg d (cs ++ Γ) cs'` denotes a Kleisli
arrow of `Option` (`NFProg.denote`), and the three region operators are `List.foldlM`
over the trip indices, the fuel-bounded `whileIter` and the branch. The dialect is the
region's import interface and `DialectDenote d` its stateless handler; `NFProg.map?`
inlines a block per op as a package link inlines an oracle; `Dialect.opSum` is the sum
of interfaces and `BlockLoweringData.extendId` the whiskering of a lowering by the
identity on the other summand. The analogy with state-separating packages stops at
state: a region persists nothing across iterations (carried values are explicit
arguments), the lowering side condition `OpsCommute` is naturality of a re-encoding
rather than disjointness of state, and the leak run is a writer over the
non-commutative monoid of event lists, so its Kleisli category is premonoidal and the
quiet-kind hypothesis of the e-graph stages is centrality in it. The one law the
region operators satisfy and every lowering proof uses is relational congruence,
stated once in `VIR/NFProgRel.lean` (`foldlM_rel`, `whileIter_rel`, `ite_rel`,
`denote_forLoop_rel`, `denote_ifThenElse_rel`, `denote_whileLoop_rel`, with forward
and leak-writer forms).
`VIR/DialectCategory.lean` checks the presentation: regions form a category
(`RegionCtx d`, morphisms `NFPre`, composition `append`) with a functor to the
Kleisli category of `Option`; block lowerings compose with a right identity
unconditionally, with a left identity under `HeadVar` and associatively under
`SpliceNatural` (the lowering commutes with splicing), so they form a category only
on the natural lowerings; `opSum` has a copairing and `extendId` is the copairing of
`L ∘ inl` with `inr`; `Dialect.sum` has no copairing for block lowerings.
`VIR/DialectCategoryTemplate.lean` removes the side conditions on template
lowerings: a lowering given by an op template (`BlockLoweringData.ofTemplate`, a
block per op over the op's arguments, instantiated by renaming) is natural under
renaming (`spliceNatural_ofTemplate`, `headVar_ofTemplate`), so template lowerings
form a category (`Category TemplateDialect`) closed under composition, `extendId`,
`copair` and the sum injections; `catToJasmin` and the MOD-2 witness are templates.
This naturality under injective renamings is the de Bruijn form of nominal
equivariance.

| edge | pass | denotation preservation | reaches bytes |
|---|---|---|---|
| hax `ImpExpr` → `NFProg nfDialect` | `impToNF` (`CatCrypt/Crypto/Hax/ImpToNF.lean`) | `impToNF_sound` | front |
| `NFProg nfDialect` → `NFProg catCryptDialect` | `nfToCat` (`CatCrypt/Crypto/Hax/NFToCat.lean`); refuses `ifThenElse`, `whileLoop` and literal trip counts | `nfToCat_sound` | yes, through the next rows |
| `NFProg catCryptDialect` → `NFProg jasminDialect` → `ComL` | `catToJasmin : PartialBlockLowering catCryptDialect jasminDialect` under `NFProg.map?`, then `nfToComLVia` (`VIR/NFProgCatToJasmin.lean`) | `catToJasmin_map?_denote`, `nfToComLVia_denote`; `nfToComLVia_agrees` relates it to `nfToComL` | yes, through `ComL.toLprogPhysAbi` |
| `NFProg catCryptDialect` → `ComL` | `nfToComL` (`VIR/NFProgToComL.lean`; one carried value, straight-line body) | `nfToComL_denote` | yes, through `ComL.toLprogPhysAbi` |
| `NFProg nfDialect` → `Com jasminDialect` or `ComL` | `nfChain` (dev `Haxc/NFChain.lean`): `nfToCat`, `NFProg.map?` at `catToJasmin`, `lowerSelects`, `exportNF` | `nfChain_denote` | yes: `backend_correct` (dev `Haxc/BackHalf.lean`) on the programs `compileJ` accepts; `haxc_correct_auto` (dev `Haxc/ComposeV1.lean`) end to end |

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
- `catCryptDialect` carries 56 op constructors spanning what MLIR splits four ways:
  word arithmetic (`arith`), `memrefGet`/`memrefSet` and their dynamic variants
  (`memref`), `vsimd`/`vpshufdC`/`vsha256rnds2` and the other packed ops
  (`vector`), plus pairs, sums, sampling and `extCall`, in one op inductive.

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
| `fieldDialect → jasminDialect` | `lowerK` (`Algebraic/FieldToJasminWord.lean`); `fieldComOf` (`Algebraic/FieldToJasminLimbs.lean`) over the Montgomery and Solinas limb templates | `fieldToJasminWord_denote` on `GoodW p`; `fieldToJasminLimbs_denote` on the template's coverage |
| `fieldDialect → modArithDialect` | `lowering` (`VIR/FieldToModArithMont.lean`), a `BlockLoweringData`; `loweringAt` between the representation-indexed variants `fieldDialectAt ρ` and `modArithDialectAt` | `fieldToModArithMont_denote`, `loweringAt_denote` |
| `modArithDialect → jasminDialect` | `loweringA` (`Algebraic/ModArithToJasminLimbsMont4.lean`), a `MultiBlockLoweringData` over four 64-bit limbs at a `Mont4Prime` | `modArithToJasminLimbsMont4_denote` on the `GoodA` fragment; `fieldToJasminViaModArith_denote` for the two-stage descent from `fieldDialect` |
| `fpDialect → modArithDialect` | `lowerFieldToModArith` (`VIR/FieldToModArithLowering.lean`), a `LoweringData` | `fpVarTransports`, `fpOpLowerTransports` and the `fundamental` lemma of `ComParametricityTransport` |
| `jasminDialect → Lprog → x86/ELF` | `Com.toLprogPhysAbi` (`VIR/JasminLprogExport.lean`), `ComL.toLprogPhysAbi` (`VIR/JasminLprogExport/ExportPhysAbi.lean`), then `renderLprogAtt` (`X86Backend/LprogAsmPrinter.lean`) or `compileComToElf` (`X86Backend/CompileComToElf.lean`) | `toLprogPhysAbi_faithful_uniform` (`X86Backend/ToLprogFaithfulAssembled.lean`) for `UniformRegArith` programs under its hypotheses; on the hax route, `backend_correct` (dev `Haxc/BackHalf.lean`) for the programs `compileJ` accepts |

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
| `mlirScfDialect` | `Lprog` control flow and loop emit (an older structured form) | `VIR/MlirScfDialect.lean` |
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
| `ringDialect` | `ring.*` on RNS `!ring.rq`: `add`, `sub`, `negate`, `mul`, `automorphism`, `rescale`, `base_convert`, `from_tensor`, `to_tensor`, `from_limbs`, `to_limb`, and `ntt`, `intt`, `basemul` (14 op constructors) | `VIR/RingDialect.lean` |
| `edAffDialect` | `elliptic_curve.add/double/negate` and `convert_point_type` on `ed_affine` and `ed_extended` | `VIR/EcEdwardsAffineDialect.lean` |
| `pairingCheckDialect` | `elliptic_curve.pairing_check` (`gtIsOne`, `pairingCheck2`, with a `publicData` flag) | `VIR/EcPairingCheckOps.lean`, `VIR/EcPairingCheckLowering.lean`, `VIR/Fp12Gt.lean` |
| `ladderDialect` (dev) | `arith.select` over `fp p` and `point p` (`fSelect`, `pSelect`) and the ladder's point double and add (`ldDbl`, `ldAddP`) | dev `VIR/EcLadderSelectDialect.lean` |

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
| `ringDialect` | residue arrays `(i : Fin L) → Fin n → ZMod (ms.get i)` | none |
| `ladderDialect` (dev) | `Bool`, `ZMod p`, `ECPoint p` | none; the ladder loop is a `List.foldl` of `ladderStepCom` (`ladderLoop_eq_smul`) |

`fieldDialect` reaches jasmin through `Algebraic/FieldToJasminWord.lean` and
`Algebraic/FieldToJasminLimbs.lean`. `lowerK F : Com fieldDialect Γ t → Com
jasminDialect (mapCtxW Γ) (mapTyW t)` is defined for a `SingleWordField p`;
`fieldToJasminWord_denote` carries the denotation for a program covered by
`GoodW p` (`fAdd`, `fSub`, `fNeg`, `fMul`, `fConst`, `fCopy`, `fieldDouble`,
`fieldSquare`); `lowerK_scalar` places the result in `UniformScalarArith 64` and
`lowerK_exportFaithful` gives the
`ComLsemExportFaithful` precondition of the `toLprogPhysAbi` export.
`Algebraic/Poseidon2BabyBearCompile.lean` takes that route to bytes for the whole
Poseidon2 permutation. `SingleWordField p` requires `2 * p ≤ 2^63`; moduli above
that bound go through the multi-limb templates of `fieldComOf` or through
`modArithDialect` and `loweringA`.

`ecDialect` has a front: `CompileFromHaxPrimeIrFrontEc.lean` recognises a hax
`point_add` or `point_double` call node and emits a single-op `Com ecDialect` leaf,
and `VIR/EllipticCurveLowering.lean` carries the chord and tangent schedules in `ZMod p`.
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
  butterflies in wrapping word arithmetic. `latticeNttMul_compile_correct`
  (`VIR/CompilerCorrectness.lean`) concerns the `.bits` lattice model described in
  the transport table. `ringDialect` carries `ntt`, `intt` and `basemul` ops with no
  lowering.
- `NamedSSA` (`ComBuilder.lean`) is a builder, not a dialect: it resolves
  level-named SSA into de Bruijn `Com jasminDialect`, and `FieldEmitGoldenGf256`,
  `FieldEmitGoldenMul`, `FieldEmitGoldenReduces` and `RelationalFrontEC` use it. A
  `Com` written with it is a builder `Com` at the jasmin tier.
- `toyDialect`, `smokeDialect`, `pilot`, `wordDialect`, `dwDialect`, `srcDialect`,
  `tgtDialect`, `testDialect`, and the coproduct examples `numDialect`,
  `flagDialect`, `mixedDialect` are test and example scaffolding.
- `latticeDialectG` is a family: `latticeDialect` and `realLatticeDialect` are its
  `.bits` and `.poly` instances, with one type alphabet, one op set, one
  `DialectSignature` and two `TyDenote` instances (`Fin n → BitVec 16` and
  `CPolynomial (ZMod q)`). The lowering to jasmin is on the `.bits` instance; the
  `.poly` instance is the specification view and reaches nothing.
- `fieldDialectAt`, `fieldDialectTower`, `modArithDialectAt` and `ecDialectAt` are
  representation-annotated variants of `fieldDialect`, `modArithDialect` and
  `ecDialect`. `annotate…Com` and `unannotate…Com` re-index programs between a
  variant and its base dialect (`denote_annotateFieldCom`,
  `denote_unannotateFieldCom` and siblings), so a variant reaches bytes exactly
  when its base dialect does.

## Reading the lowering graph

- There are two byte sinks, `jasminDialect` and `x86Dialect`. `Com (x86Dialect w)`
  over `JState w` is the machine level. `scfDialect` lowers into `x86Dialect`
  (`lowerScfFor`, `scfFor_lowering_denote`) without passing through jasmin.
- The generator reads three kinds of edge, each from the type of the lowering: a
  lowering record `R A B` (a structure declared over `(d d' : Dialect)`), a function
  from a program at `A` to a program at `B` (`Com`, `NFProg`, `ComR`, and `ComL` or
  `RouteProg` at `jasminDialect`), and an op-level `lower…` with a preservation
  theorem over a builder of the source program. It does not check that a record or
  function edge has a preservation theorem, and it does not see the fragment on
  which a theorem holds; the transport tables above give both.
- "No path" reports such edges only. A denotation theorem can tie a dialect to a
  backend where no lowering function does. `tileDialect` is such a case:
  `VIR/TileDialectModelTie.lean` proves its op denotation equal to the per-lane
  semantics of `TileBackend/TileModel.lean` (`evalTileOp`), and
  `TileBackend/ComToTileIR.lean` emits `cuda_tile` MLIR text from tile programs.
  `TileBackend/ZmmArithBridgeCom.lean` and `TileBackend/VectorBackendBridgeCom.lean`
  express the packed lane arithmetic as `Com jasminDialect` programs over `vpackZMM`
  and `vsimd` ops.
- The prime-ir family other than `fieldDialect`, `modArithDialect`, `fpDialect`
  and `derivedDialect` reads as unreachable although `ecDialect` has a front, as the
  section above describes; the per-coordinate and per-op schedules of
  `ecConvertDialect` and `pairingCheckDialect` are not `Com`-to-`Com` edges.

## Front-end landing (hax → IR)

- Structured route (the hax compiler): `hax ImpExpr → impToNF → NFProg nfDialect →
  nfToCat → NFProg catCryptDialect → nfChain → RouteProg → compileJ → bytes`
  (dev `Haxc/NFFront.lean`, `Haxc/ComposeV1.lean`: `haxc_correct_auto`).
- ANF scalar: `hax ImpExpr → impExprToThir → Thir → thirToJasmin → Com jasminDialect`
  (`ThirToComFront.lean`; `compileFromHax` in `CompileFromHax.lean`, with
  `compileFromHax_denote`).
- Loops and arrays (older route): `hax ImpExpr → haxToLowCT → LowCT →
  catCryptDialect / ComL` (`CatCrypt/Crypto/Hax/HaxToLowCT.lean`; `PipelineMap.lean`;
  the `Dialects/TranslateDialect*` translators); the dev table route `Haxc.compile`
  (`Haxc/Compile.lean`, with `haxc_correct` in `Haxc/Correct.lean`) uses it.
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

## Reach by dialect

"Bytes" means a chain of lowering edges to `jasminDialect` or `x86Dialect`, each
with its preservation theorem; a qualifier names the fragment. The generated block
below gives the edges this table rests on.

| dialect | reaches bytes | how |
|---|---|---|
| `jasminDialect` | sink | `Com.toLprogPhysAbi`, `ComL.toLprogPhysAbi` |
| `x86Dialect` | sink | machine level |
| `nfDialect` | yes, through `NFProg` | `nfToCat`, then `nfToComL`, `nfToComLVia` or (dev) `nfChain` and `compileJ` (fragment: counted loops whose trip count is a variable, no branch or exit-flag loop; `nfToComL` takes one carried value) |
| `catCryptDialect` | yes | `cryptoDialectToJasminCom` (partial); `nfToComL`, `nfToComLVia` for `NFProg catCryptDialect` |
| `thirDialect` | yes | `lowerThir`, `thirToJasminViaCatCrypt` |
| `latticeDialect` | yes | `lowerLatticeToJasmin`, `latticeLoweringData` |
| `arithDialect`, `memrefDialect`, `vectorDialect`, `funcDialect` | yes | `Dialects/*ToJasmin.lean`; machine-level `memrefDialect` by `lowerMLoad`, `lowerMStore` |
| `scfDialect` | yes (machine level) | `lowerScfFor` |
| `fieldDialect` | yes, on a fragment | `lowerK` (`GoodW p`, `SingleWordField p`), `fieldComOf` (template coverage), or through `modArithDialect` |
| `modArithDialect` | yes, on a fragment | `loweringA` (`GoodA` at a `Mont4Prime`) |
| `fpDialect` | yes, on the fragment of `modArithDialect` | `lowerFieldToModArith`, then `loweringA` |
| `derivedDialect` | yes, on the fragment of `fieldDialect` | `lowerDerivedToField`, then `fieldDialect` |
| `fieldDialectAt`, `fieldDialectTower`, `modArithDialectAt` | as their base dialect | `unannotateFieldCom`, `unannotateTowerCom`, `unannotateCom` |
| `ringDialect` | no | none |
| `ladderDialect` (dev) | no | none |
| `ecDialect`, `ecDialectAt`, `ecConvertDialect`, `edAffDialect`, `pairingCheckDialect` | no | schedules into `fieldDialect` per op or per coordinate, not `Com → Com` |
| `cmpDialect`, `fieldCmpDialect` | no | `cmpLowering`, `fieldLowering` into `fieldCmpDialect`, which has no outgoing edge |
| `modArithMontDialect`, `polyDialect`, `tensorExtDialect`, `tileDialect`, `quantumDialect` | no | none |
| `natKernelDialect` | no | its target is the Lean kernel: `natKernelFn%` emits a Lean term, validated per program against `FlatProg.run`; (dev) `arithDialect` lowers into it |
| `mlirArithDialect`, `mlirMemrefDialect`, `mlirVectorDialect`, `mlirScfDialect`, `mlirPolynomialDialect`, `mlirArithScfDialect` | no | agreement layers |
| `latticeDialectG`, `realLatticeDialect` | no | family and specification instance |
| `toyDialect`, `smokeDialect`, `pilot`, `numDialect`, `flagDialect`, `mixedDialect`, `wordDialect`, `dwDialect`, `srcDialect`, `tgtDialect`, `testDialect` | no | scaffolding |

## Lowering graph

The block below is generated from the compiler and dev trees. From
the dev tree:

```
scripts/gen-lowering-graph.sh --check ../catcrypt-compiler .
scripts/gen-lowering-graph.sh --write ../catcrypt-compiler .
```

<!-- BEGIN GENERATED lowering-graph -->

_Generated by `scripts/gen-lowering-graph.sh` from the trees catcrypt-compiler, SSProve-lean (roots `CatCrypt`, excluding `CatCrypt/Quantum`). Do not edit by hand._

### Lowering edges

Kind `record`: a lowering record `R A B`; `signature`: a function from a program at `A` to a program at `B`; `op level`: a `lower…` definition with a preservation theorem over a source builder. Paths are relative to `CatCrypt/Crypto/SecureCompilation/` where they lie under it.

| from | to | via | kind | file |
|---|---|---|---|---|
| `arithDialect` | `jasminDialect` | `lowerArithToJasmin` | signature | `Dialects/ArithToJasmin.lean` |
| `arithDialect` | `natKernelDialect` | `lowerCom` | signature | `VIR/Dialects/ArithToNatKernel.lean (SSProve-lean)` |
| `arithDialect` | `natKernelDialect` | `lowering` | record | `VIR/Dialects/ArithToNatKernel.lean (SSProve-lean)` |
| `catCryptDialect` | `jasminDialect` | `catToJasmin` | record | `VIR/NFProgCatToJasmin.lean` |
| `catCryptDialect` | `jasminDialect` | `cryptoDialectToJasminCom` | signature | `VIR/DialectToJasminCom.lean` |
| `catCryptDialect` | `jasminDialect` | `nfToComLAt` | signature | `VIR/NFProgToComL.lean` |
| `catCryptDialect` | `jasminDialect` | `nfToComL` | signature | `VIR/NFProgToComL.lean` |
| `catCryptDialect` | `jasminDialect` | `nfToComLVia` | signature | `VIR/NFProgCatToJasmin.lean` |
| `catCryptDialect` | `jasminDialect` | `toJasmin4` | signature | `Secp256k1PointOpFront.lean` |
| `catCryptDialect` | `jasminDialect` | `toJasmin` | signature | `Bn254TowerFrontEmit.lean` |
| `catCryptDialect` | `jasminDialect` | `toJasmin` | signature | `Mersenne31FrontEmit.lean` |
| `catCryptDialect` | `jasminDialect` | `toJasmin` | signature | `Secp256k1PointOpFront.lean` |
| `catCryptDialect` | `jasminDialect` | `toJasminF` | signature | `Secp256k1PointOpFrontFramed.lean` |
| `catCryptDialect` | `mlirArithDialect` | `translate` | signature | `VIR/MlirArithDialect.lean` |
| `catCryptDialect` | `mlirMemrefDialect` | `translate` | signature | `VIR/MlirMemrefDialect.lean` |
| `cmpDialect` | `fieldCmpDialect` | `cmpLowering` | record | `VIR/FieldCmpSum.lean` |
| `derivedDialect` | `fieldDialect` | `lowerDerivedToField` | signature | `VIR/DerivedToFieldLowering.lean` |
| `derivedDialect` | `fieldDialect` | `lowering` | record | `VIR/DerivedToFieldLowering.lean` |
| `dwDialect` | `wordDialect` | `dwLowering` | record | `VIR/MultiBlockLoweringToy.lean` |
| `ecDialectAt` | `ecDialect` | `unannotateEcCom` | signature | `VIR/EllipticCurveDialect.lean` |
| `ecDialect` | `ecDialectAt` | `annotateEcCom` | signature | `VIR/EllipticCurveDialect.lean` |
| `fieldDialectAt` | `fieldDialect` | `unannotateFieldCom` | signature | `VIR/FieldDialect.lean` |
| `fieldDialectAt` | `modArithDialectAt` | `loweringAt` | signature | `VIR/FieldToModArithMont.lean` |
| `fieldDialect` | `fieldCmpDialect` | `fieldLowering` | record | `VIR/FieldCmpSum.lean` |
| `fieldDialect` | `fieldDialectAt` | `annotateFieldCom` | signature | `VIR/FieldDialect.lean` |
| `fieldDialect` | `fieldDialectTower` | `annotateTowerCom` | signature | `VIR/FieldDialect.lean` |
| `fieldDialect` | `jasminDialect` | `bbBL` | record | `CatCrypt/Crypto/Poseidon2/FieldDescentBB.lean (SSProve-lean)` |
| `fieldDialect` | `jasminDialect` | `bbMont32BL` | record | `CatCrypt/Crypto/Poseidon2/FieldDescentBBMont32.lean (SSProve-lean)` |
| `fieldDialect` | `jasminDialect` | `blockL` | record | `VIR/FieldDialectBlockDescentBB.lean (SSProve-lean)` |
| `fieldDialect` | `jasminDialect` | `compileField` | signature | `Haxc/FieldRoute.lean (SSProve-lean)` |
| `fieldDialect` | `jasminDialect` | `compileFieldS` | signature | `Haxc/FieldRoute.lean (SSProve-lean)` |
| `fieldDialect` | `jasminDialect` | `fieldCom` | signature | `Algebraic/FieldToJasminLimbs.lean` |
| `fieldDialect` | `jasminDialect` | `fieldComOf` | signature | `Algebraic/FieldToJasminLimbs.lean` |
| `fieldDialect` | `jasminDialect` | `fieldComToJasmin` | record | `FieldDescent.lean (SSProve-lean)` |
| `fieldDialect` | `jasminDialect` | `lowerBlockF` | op level | `CatCrypt/Crypto/Poseidon2/FieldDescentBB.lean (SSProve-lean)` |
| `fieldDialect` | `jasminDialect` | `lowerComKMC` | signature | `CatCrypt/Crypto/Poseidon2/FieldDescentBBMont32.lean (SSProve-lean)` |
| `fieldDialect` | `jasminDialect` | `lowerComKM` | signature | `CatCrypt/Crypto/Poseidon2/FieldDescentBBMont32.lean (SSProve-lean)` |
| `fieldDialect` | `jasminDialect` | `lowerComK` | signature | `CatCrypt/Crypto/Poseidon2/FieldDescentBB.lean (SSProve-lean)` |
| `fieldDialect` | `jasminDialect` | `lowering` | record | `Algebraic/FieldToJasminWord.lean` |
| `fieldDialect` | `jasminDialect` | `loweringL` | record | `Algebraic/FieldToJasminLimbs25519.lean` |
| `fieldDialect` | `jasminDialect` | `loweringL` | record | `Algebraic/FieldToJasminLimbs.lean` |
| `fieldDialect` | `jasminDialect` | `loweringL` | record | `Algebraic/FieldToJasminLimbsMont4.lean` |
| `fieldDialect` | `jasminDialect` | `loweringL` | record | `Algebraic/FieldToJasminLimbsSolinas.lean` |
| `fieldDialect` | `jasminDialect` | `loweringOf` | record | `Algebraic/FieldToJasminLimbs.lean` |
| `fieldDialect` | `jasminDialect` | `lowerK` | signature | `Algebraic/FieldToJasminWord.lean` |
| `fieldDialect` | `jasminDialect` | `translBBMont32` | signature | `CatCrypt/Crypto/Poseidon2/FieldDescentBBMont32.lean (SSProve-lean)` |
| `fieldDialect` | `jasminDialect` | `translBB` | signature | `CatCrypt/Crypto/Poseidon2/FieldDescentBB.lean (SSProve-lean)` |
| `fieldDialect` | `modArithDialect` | `fieldFpDescent` | record | `FieldDescent.lean (SSProve-lean)` |
| `fieldDialect` | `modArithDialect` | `lowering` | record | `VIR/FieldToModArithMont.lean` |
| `fieldDialectTower` | `fieldDialect` | `unannotateTowerCom` | signature | `VIR/FieldDialect.lean` |
| `fpDialect` | `modArithDialect` | `lowerFieldToModArith` | record | `VIR/FieldToModArithLowering.lean` |
| `funcDialect` | `jasminDialect` | `lowerFuncToJasmin` | signature | `Dialects/FuncToJasmin.lean` |
| `latticeDialect` | `jasminDialect` | `latticeLoweringData` | record | `VIR/CompilerGeneric.lean` |
| `latticeDialect` | `jasminDialect` | `lowerLatticeToJasmin` | signature | `VIR/LatticeToJasmin.lean` |
| `latticeDialect` | `mlirPolynomialDialect` | `translate` | signature | `VIR/MlirPolynomialDialect.lean` |
| `memrefDialect` | `jasminDialect` | `byteRolledForLoopN` | signature | `Dialects/ByteMemrefRolledLoop.lean` |
| `memrefDialect` | `jasminDialect` | `lowerMemrefToJasmin` | signature | `Dialects/MemrefToJasmin.lean` |
| `memrefDialect` | `x86Dialect` | `lowerMLoad, lowerMStore` | op level | `X86Backend/MemrefDialect.lean` |
| `modArithDialectAt` | `modArithDialect` | `unannotateCom` | signature | `VIR/ModArithDialect.lean` |
| `modArithDialect` | `jasminDialect` | `loweringA` | record | `Algebraic/ModArithToJasminLimbsMont4.lean` |
| `modArithDialect` | `jasminDialect` | `modArithToJasmin` | record | `FieldDescent.lean (SSProve-lean)` |
| `modArithDialect` | `modArithDialectAt` | `annotateCom` | signature | `VIR/ModArithDialect.lean` |
| `nfDialect` | `catCryptDialect` | `nfToCat` | signature | `CatCrypt/Crypto/Hax/NFToCat.lean` |
| `nfDialect` | `fieldDialect` | `nfToField` | signature | `Haxc/FieldCorrect.lean (SSProve-lean)` |
| `nfDialect` | `jasminDialect` | `nfChain` | signature | `Haxc/NFChain.lean (SSProve-lean)` |
| `scfDialect` | `x86Dialect` | `lowerScfFor` | op level | `X86Backend/ScfDialect.lean` |
| `srcDialect` | `tgtDialect` | `lowering` | record | `VIR/BlockLoweringExtendWitness.lean` |
| `thirDialect` | `catCryptDialect` | `lowerThirToCatCrypt` | signature | `VIR/ThirToCatCryptDialect.lean` |
| `thirDialect` | `catCryptDialect` | `lowerThirToCrypto` | signature | `ThirToCryptoDialect.lean` |
| `thirDialect` | `fieldDialect` | `lowerThirToField` | signature | `VIR/ThirToFieldDialect.lean (SSProve-lean)` |
| `thirDialect` | `jasminDialect` | `compileThirViaCatCryptOrFlat` | signature | `VIR/ThirToJasminViaCatCryptOrFlat.lean` |
| `thirDialect` | `jasminDialect` | `lowerThir` | signature | `VIR/ThirDialect.lean` |
| `thirDialect` | `jasminDialect` | `thirToJasminViaCatCrypt` | signature | `VIR/ThirToJasminViaCatCrypt.lean` |
| `thirDialect` | `jasminDialect` | `thirToJasminViaField` | signature | `VIR/ThirToFieldDialect.lean (SSProve-lean)` |
| `vectorDialect` | `jasminDialect` | `lowerVectorToJasmin` | signature | `Dialects/VectorToJasmin.lean` |

### Reaches bytes through `jasminDialect` or `x86Dialect`

- `arithDialect`
- `catCryptDialect`
- `derivedDialect`
- `fieldDialect`
- `fieldDialectAt`
- `fieldDialectTower`
- `fpDialect`
- `funcDialect`
- `latticeDialect`
- `memrefDialect`
- `modArithDialect`
- `modArithDialectAt`
- `nfDialect`
- `scfDialect`
- `thirDialect`
- `vectorDialect`

### No path to `jasminDialect` or `x86Dialect`

- `cmpDialect`
- `dwDialect`
- `ecConvertDialect`
- `ecDialect`
- `ecDialectAt`
- `edAffDialect`
- `fieldCmpDialect`
- `flagDialect`
- `ladderDialect` (SSProve-lean)
- `latticeDialectG`
- `mixedDialect`
- `mlirArithDialect`
- `mlirArithScfDialect`
- `mlirMemrefDialect`
- `mlirPolynomialDialect`
- `mlirScfDialect`
- `mlirVectorDialect`
- `modArithMontDialect`
- `natKernelDialect`
- `numDialect`
- `pairingCheckDialect`
- `pilot`
- `polyDialect`
- `quantumDialect`
- `realLatticeDialect`
- `ringDialect`
- `smokeDialect`
- `srcDialect`
- `tensorExtDialect`
- `testDialect`
- `tgtDialect`
- `tileDialect`
- `toyDialect`
- `wordDialect`

<!-- END GENERATED lowering-graph -->
