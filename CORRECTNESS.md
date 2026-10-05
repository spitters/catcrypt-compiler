# Correctness methods: descent, ascent, transfer

A correctness theorem about code in the CatCrypt workspace is proved by one of three
techniques or by a composition of them. A program that a technique cannot express
leads to an extension of that technique (a front construct, an ascent rule, a
registered relation), so every proof stays within the three.

| Technique | Direction | Judgement | Proves |
|---|---|---|---|
| Descent | source to bytes | simulation of each pass | the emitted code has the denotation of its source |
| Ascent | given code to a Lean function | `Corres`, `FnCorres` | the given code computes a stated Lean function |
| Transfer | across a representation | `Related`, `Param` | a fact about abstract values holds of their representations, or conversely |

The workspace builds against two siblings of this package, the development repository
(CatCrypt) and the ParamTransfer package. Paths below are relative to this package
unless the text names another package.

The operation semantics that these theorems are stated over, compared with LLVM, MLIR
`arith` and Rust at every layer, are in
[SEMANTICS.md](CatCrypt/Crypto/SecureCompilation/VIR/SEMANTICS.md).

## Descent: the verified compiler

Descent generates code from a source and proves each lowering a simulation. The
source is therefore the specification: correctness is equivalence to the source (the
Rust reference for extracted code), and known-answer tests are regressions. The chain
runs from the front through `LowCT`, the SSA dialects, `Com jasminDialect` and
`Lprog` to the owned x86, AArch64 and RISC-V encoders. The intended source is
orchestration: Rust above the field interface, with field operations as primeIR calls
and limb-level or bit-level kernels as calls to optimised implementations whose
correctness is a template theorem or an ascent theorem ([ASCENT.md](ASCENT.md)).

A template theorem covers straight-line word arithmetic generated from an algebraic
template: one denotation theorem over every parameter record, a bounds certificate decided
per instance (`boundsOk` with `denote_eq_denoteZ_of_boundsOk`, `SchedOk`), and one bytes
theorem per family (`field_correct_bytes`, `ntt_correct_bytes`, `ec_correct_bytes`) whose
only per-instance hypothesis is acceptance by the decided gate of `backend_correct`. The
method reaches fields, lattices, GHASH, towers, RSA and isogeny moduli, and not control
flow or bit-logic permutations. [FIAT_TEMPLATES.md](FIAT_TEMPLATES.md) gives the instance
table with gate verdicts, the measured ratios against fiat-crypto, the size of the
template layer and the dated deferrals.

- The hax front in `CatCrypt/Crypto/Hax/` lowers hax-lean's `ImpExpr` to `LowCT`
  (`haxToLowCT_simulates_program` and its array, tower and literal variants). The
  typed entry point `haxFrontT` (development repository,
  `CatCrypt/Crypto/Hax/HaxFrontT.lean`, `haxFrontT_simulates`) places each name by
  its type. Early exits lower to exit-flag form. `scalarizeExitIn`
  (`CatCrypt/Crypto/Hax/HaxToLowCTExitWordOps.lean`) replaces marshalled word calls by
  scalar assignments and unsigned comparisons by their signed forms. `placedUse`
  (`CatCrypt/Crypto/Hax/HaxToLowCTPlaced.lean`) checks that every name is used in the
  heap of its placement. [HAX_RUST.md](HAX_RUST.md) gives the procedures.
- In the Jasmin `.jinc` importer (`CatCrypt/Crypto/Jasmin/`), `JincParser` and
  `JincToCom` read the straight-line fragment, `JincElab` elaborates it to
  `Com jasminDialect`, and `JincToLowCT` emits `for` and `while` as the loop nodes
  `RFor` and `RWhileNz`. `JincInline` partially evaluates a Jasmin source unit
  (inlining, constant folding, scalar replacement of register arrays).
  `importFunRolled` keeps a loop over an affine counter rolled, as a loop over a
  run-time trip index. `JincInline` carries no simulation theorem, so the correctness
  theorem of an imported leaf concerns the `LowCT` or `Com` that the import produces.
  `KeccakJincImport` takes formosa-keccak's Keccak-f[1600] through this path.
- The scalar front's denotation theorems (`transU_denote`, `frontLoopBodyJ_denote`)
  assume the coverage fragment `IsCoveredSCtl`. `coveredB` and
  `isCoveredSCtl_of_coveredB` (`CatCrypt/Crypto/SecureCompilation/Dialects/CoveredSCtlDecide.lean`)
  discharge it by `decide`.
- The end-to-end theorems are `rustToJasminCom_endToEnd_unconditional`
  (`VIR/CompilerCorrectnessExtracted.lean`), `robustCompilation_source_to_x86`
  (`VIR/RobustCompilationPipeline.lean`; value correctness, no constant-time
  conjunct), and the straight-line demonstrations `com_x86_e2e`, `com_arm_e2e` and
  `com_riscv_e2e`. The three demonstrations compile a straight-line, register-only
  `Com` through the `ScalarTarget` instruction selection (`ScalarLin.lean`), which has
  no memory, flags or loops and is not the selection the owned exporters run.
  [HEADLINES.md](HEADLINES.md) states each with its hypotheses.
- The hax compiler `haxc` (development repository,
  `CatCrypt/Crypto/SecureCompilation/Haxc/`; its layout type `AbiLayout` is in this
  package) composes the hax front, the route to the Jasmin dialect, the export to
  `Lprog`, the owned back end and the encoder, and ends at decoded x86 bytes run by the
  address machine `aMachine`. Its general theorems quantify over every extraction the
  compiler accepts. `haxc_correct_auto` (`ComposeV1.lean`) and, for a result that pairs
  an array with one of its words, `haxc_correct_auto_tuple` (`ComposeTuple.lean`) state
  that every run of the source reading to a value is matched by a halting run on the
  decoded bytes that reads the value back. `haxc_correct_auto_ct_regions`
  (`ComposeCT.lean`) and `haxc_correct_auto_tuple_ct_regions` add constant time of the
  decoded program over runs from entry states that agree on the public data of the
  layout. The instances are `mpn_and_n_correct_auto` and
  `mpn_and_n_correct_auto_ct_regions` (`AndNCorrect.lean`, `AndNCorrectCT.lean`),
  `ltu_correct_auto` and `ltu_correct_auto_ct` (`LtuCorrect.lean`, `LtuCorrectCT.lean`),
  and `mpn_mul_1_correct_auto` and `mpn_mul_1_correct_auto_ct_regions`
  (`Mul1Correct.lean`, `Mul1CorrectCT.lean`).
- On `Lprog`, `LprogGpRealloc` re-allocates general-purpose
  registers with an untrusted allocator whose decisions a checked pass validates.
  `ConstIndexFold` rewrites each register-indexed load and store with a known index
  into displacement form (`gatherPrinted_constIndexFoldBody`). Two passes have a
  constant-time module: `LprogGpReallocCT` shows that the re-allocation introduces no
  register-indexed access, and `ConstIndexFoldCT` that the fold and the dead-move
  elimination leave the `runBlock` leakage trace unchanged. `OptimizeBasicBlocksCT`
  gives a body on which copy propagation followed by the gather introduces a
  secret-indexed load. `TwoAddrLegalize` and the post-pass `fuseMulHiLprog` have no
  constant-time module. `X86Backend/DecodedCT.lean` checks constant time at the
  shipped bytes.
- The tactic `kernel_rfl` (`CatCrypt/Tactic/KernelRfl.lean`) proves a straight-line
  `semScalar` run lemma by one kernel evaluation of `ScalarStraightRun.runProg`.
  `word_bound` (CatCrypt-core, `CatCryptCore/Tactics/WordBound.lean`) closes
  word-bound side goals.

[HEADLINES.md](HEADLINES.md) and [NAVIGATION.md](NAVIGATION.md) record the status and
open work, as do `COMPILER_ROADMAP.md` ("Where we are") and `JINC_IMPORT.md` in the
development repository.

### Routes as runs of certified pass chains

`VIR/PassChain.lean` defines a chain `Chain P Q` of named steps, its run (the
composite of the steps in `Option`), a certificate `Cert c S T` with one step
certificate per step against semantics `S` and `T`, and `PassChain.Cert.sound`: when
the run of `c` on `p` returns `q`, inputs related by the certificate give outputs
related by it. `PassChain.Cert.ct` is the leakage form. Each high-tier route of `haxc`
is defined as the run of a chain, and the denotation theorem of the route is
`Cert.sound` of the chain's certificate. The modules are in the development repository
(`Haxc.*`); the shared pieces `comSemOf`, `routeSem`, `straightStep` and
`straightCert` are in `Haxc.RouteChain`. As of 2026-10-05 every row except `nfChain`
is source that no build has checked.

| Route (module) | Chain and its steps | Certificate and `Cert.sound` consumer | Route theorem |
|---|---|---|---|
| `nfChain` (`Haxc.NFChain`) | `nfChain`: output-type check, `dceStep`, `nfToCatStep`, `aegraphStep catRules`, `mapStep catToJasmin`, `lowerSelectsStep`, `aegraphStep jasminRules`, `exportStep` | `nfChainCert`, `nfChain_denote` | `haxc_correct_auto` |
| `compileField P` (`Haxc.FieldRoute`) | `fieldChainId P` = `limbChainVia (Step.id _) (GoodVB P) (fieldCom P)`: optimisation slot, limb step, identity, `straightStep` | `limbChainViaCert`, `limbChainVia_denote` | `compileField_denote` |
| `compileFieldS S` (`Haxc.FieldRoute`) | `fieldChainSId S` = `limbChainVia (Step.id _) (GoodLB S) (fieldComOf (lowerOpL S))` | `limbChainViaCert`, `limbChainVia_denote` | `compileFieldS_denote` |
| `jacAddRoute`, `jacDblRoute` (`Haxc.EcRoute`) | `.get` of the run of `fieldChainId P` on `jacAddProg`, `jacDblProg` | through `compileField_denote` | `p256_jacAdd_correct_bytes`, `p256_jacDbl_correct_bytes` and the `C` variants (`Haxc.EcInstances`), with the compile hypothesis |
| `nttRoute`, `inttRoute` (`Haxc.NttRoute`) | `.get` of the run of `lanesChainId N` = `lanesChainVia (Step.id _)`: optimisation slot, `lanesStep`, `straightStep` | `lanesChainViaCert`, `lanesChainVia_denote` | `nttRoute_denote`, `inttRoute_denote` |
| `nttRouteOf A` (`Haxc.NttRouteSel`) | `.get` of the run of `lanesChain N pure`: value numbering `gvnMR pure`, lane lowering, `straightStep` | `lanesChainCert`, `lanesChain_denote` | `nttRouteOf_denote` |
| `bbPermRoute` (`Haxc.Poseidon2Bytes`) | `.get` of the run of `lanesChainId 16` on `widenProg 32 16` of the BabyBear permutation | `lanesChainViaCert`, `lanesChainVia_denote` | `bb_poseidon2_correct_bytes`, whose statement does not yet elaborate |
| `latticeRoute`, `basemulRoute`, `pointwiseRoute`, `accRoute` (`Haxc.LatticeRoute`) | `.get` of the run of `lanesChain M pure`; a non-square program is zero-padded to square | `lanesChainCert`, `lanesChain_denote` | `basemulRoute_denote`, `pointwiseRoute_denote`, `accRoute_denote`; `mlkem_basemul_correct_bytes` with the compile hypothesis |
| `towerRoute P N` (`Haxc.TowerRoute`) | `towerChain P N`: identity, `towerStep` (`towerCom` under `towerGoodB`), identity, `straightStep` | `towerChainCert`, `towerChain_denote` | `fp2_mul_correct_bytes`, `fp2_sqr_correct_bytes`; instances at BN254 and BLS12-381 with the compile hypothesis |

The optimisation slot of the field chains is the identity step. The e-graph stage
`aegraphOptField` leaves every tested program unchanged, but its equality with the
input at a symbolic modulus is not proved, so it stays out of the field route.

A route theorem that keeps the compile hypothesis is a theorem about the programs the
back half accepts; for these routes `compileJ` refuses the following.

- Jacobian doubling at P-256 (`jacDblRouteC`): refused at the image gate
  `printedAddrWB` inside the cell route; the sub-check that fails is not yet isolated.
- `Fp2` multiplication and squaring at BN254: refused at `decodableLcmd` inside
  `printedAddrWB`, because spill slots appear as destinations of `ADCX` and `CMOV`;
  at BLS12-381 the refusal is earlier, at `encodeLfundefBytesChecked`.
- The ML-KEM base multiplication (and the ML-DSA pointwise product): refused at
  `encodeLfundefBytesChecked`, whose encoder has no case for the `TRUNC` and
  `ZEROEXT` lane casts that `widenProg` introduces. The same refusal is expected, not
  measured, for the signed 16-bit NTT arm and for `bbPermRoute`.

### Proofs, checks and translation validation in `haxc`

The proved legs are the typed hax front (`haxFrontT_simulates_hax64W`), the route
from `LowCT` to the Jasmin dialect (`straightCompile_denote`, `loopCompile_denote`),
the export of a straight chain (`straight_export_faithful_abi`) and the decode
equation of the encoder (`DecodeLayout.decodeLprog_encodeLfundefBytes`). The other
legs are checks that run inside the compiler, in two classes.

- Class D: a decidable predicate on one program, with a soundness theorem. It is the
  side condition of a proved pass.
- Class V: a check of the output of an unproved transformation against its input.
  The design permits class V only for register allocation.

| Leg | Class | Proved | Missing |
|---|---|---|---|
| Front checks `haxFrontTOk`, `frontScalOk`/`frontArrOk`, `coveredGuardedB`, `loopTripOK`, the printer precondition `twoAddrOK` (`bodyTiedOk`) | D | a soundness lemma beside each check | — |
| Block optimiser `optimizeLprogBasicBlocks` | V, under `ownedCheckMC` | `optimizeBasicBlocks_straight_stateStore` (straight-line, `lsemStraight`, store image) | a statement at `lsemFuelMemF` with memory, flags and labels |
| Constant-index fold `foldIndexedLprog` | V, under `ownedCheckMC` | `foldInstr_lower`, `KEnv.Holds.stepK`, `foldCore_gather`, `gatherPrinted_constIndexFoldBody` (on `runBlock` over `JInstr`); checker completeness `foldIndexed_ownedCheckM_complete` | transport to `lsemFuelMemF` on `LinstrRM`; bodies of more than one block |
| Two-address form `twoAddrBody` | V, under `ownedCheckMC`; D once its theorem is at `lsemFuelMemF` | `twoAddrBody_lsemStraight`; checker completeness `twoAddr_ownedCheckM_complete` under `twoAddrRouteWF` | the three patterns `twoAddrRouteWF` excludes (an R15 output, a commutative operation with `b = d`, an immediate first source); the statement at `lsemFuelMemF` |
| Register allocation `reallocLprog` | V, the permitted validation | `ownedCheckM_sound`, `ownedCheckMC_sound` | — |
| Decode leg of the scalar straight route: `lineCheck` / `lineTVCheck` in `straightGateB` (development repository, `Haxc.BackHalf`) | V: the chain against the decoded line of the printed body | for array results, the image gate `v1StraightB` with `v1Straight_bytes` over `printedAddr_sim`; `DecodePrinted.printedLine_sim`, not used by the gate | evidence that `v1StraightB` accepts every program the line checks accept, after which the line checks leave the gate |
| Loop export certificate `comLCertNB` (`routeCertB`) and `exportCertJB` | V: a certificate, per program, of a fixed export function | `exportCertJB_sound`, `singleLoopJ_export_faithful_gate`, `ExportCertGate.singleLoop_export_faithful_gate` | completeness on a fragment predicate, which makes the leg class D; the do-while arm `ComLJ.whileRegs` has an export and no certificate, and `compileLoopJ` refuses it |
| Image gates `imgGateBW`, `printedAddrWB`, `physImgB` (the physical half of the register-allocation pair) | D | `image_addr_simBW`, `printedAddr_simW`, `printedAddr_sim` | completeness; a refusal does not name its cause |
| `decodableLcmd`, `decodesToB` on the printed body | D | `decodeLprog_of_decodesToB` | completeness on the encoder's image |
| Index bounds `idxInvCheckB` (abstract interpretation of one body) | D | `runIdxOk_of_idxInvCheckB` | — |
| Constant-time byte gate `ctGateR` in `compileACTR` (development repository, `Haxc.ComposeCT`) | D on the output bytes; the constant-time conjunct is checked, not preserved | `ctGateR_sound`; leak preservation of single passes: `foldInstr_lower_leak`, `gatherPrinted_constIndexFoldBody_leak`, `ownedCheckML_sound_leak`, `route_bytes_ct` | leak preservation of the block optimiser and the fold at `lsemFuelMemF`, and their composition into the source-to-bytes statement |

On the image routes (`ImageAddrRoute.routeB`, `ImageStraightCells.straightCellB`) one
call of `ownedCheckMC` compares the reference chain with the image of the printed body;
on the scalar straight route `lineTVCheck` calls `ownedCheckM` on the same pair. The
printed body is the output of the export, the post-pass `fuseMulHiLprog` and the owned
back end `ownedLprog`, so this one check accepts or refuses the combined output of the
block optimiser, the constant-index fold, the two-address form, the post-pass and
register allocation. The reference side applies the fusion as `fuseMulHiRM`, whose run is proved
(`fuseMulHi_lsemFuelMemF_pre`).

Translation validation outside register allocation, as the compiler stands: the three
owned back-end passes and the post-pass `fuseMulHiLprog`, which reach the theorems only
through the register-allocation check; the decode leg of the scalar straight route; and
the loop export certificate, until its completeness is proved. The constant-time
conjunct of the `_ct_regions` theorems is a verified static analysis of the decoded
bytes (`ctGateR_sound`), not a preservation result. A failed check makes the compiler
return `none`, so the theorems cover exactly the programs it accepts.

The design keeps one translation validation, the check of the pair before and after
register allocation. The block optimiser, the fold and the two-address form are to
carry preservation theorems at `lsemFuelMemF`; the general decode simulation is to
replace `lineCheck` and `lineTVCheck`; the loop export certificate is to carry a
completeness theorem; and constant time is to be derived from the source through
per-pass leakage transformers.

### Reference semantics of prime-ir calls

The hax interpreter reads a prime-ir field call under the builtin table
`primeirBuiltins p` (`CatCrypt/Hax/PrimeirBuiltins.lean`), which interprets the heads
`mul`, `add`, `sub`, `neg`, `square`, `double` and `inv` on integer arguments modulo
`p`. The extraction emits bare method names, so an integer `mul`, `add` or `sub` and
the field operation of the same name share a head. The field route's theorem
`field_correct_auto` (development repository, `Haxc.FieldCorrect`) is stated against
`primeirBuiltins p`; it is a theorem about the intended semantics only for functions
whose integer-typed calls with these names are field calls. The name table
`defaultFieldTable` (`CatCrypt/Hax/PrimeirNames.lean`) lists the qualified names
beside the bare ones.

## Ascent: correspondence from given code to a specification

Ascent takes existing code, extracted or shipped, and proves a correspondence from
its runs to a Lean function. A second, ordinary proof equates that function with the
handwritten specification. Ascent has two instances, which share one calculus in the
style of AutoCorres.

- In the ascent on extracted Rust (the library `HaxAscent`, which depends only on Lean,
  Std, Batteries and hax-lean; judgement and generator in `HaxAscent/Ascent/`, index
  [CatCrypt/Hax/AGENTS.md](CatCrypt/Hax/AGENTS.md)), `FnCorres bi e entry G f` relates
  the `denote'` run of an `ImpExpr` literal under the builtin table `bi` to a shallow
  function `f`. The generator `Hax.Ascent.Gen.ascendFn` produces `f` and its
  correspondence with no hand-written loop specification. The entry point
  `hax_ascend Ns` runs the generator over a whole haxpipeT extraction and declares
  `Ns.HaxGen.f.gen`, `Ns.HaxGen.f.corres` and `Ns.HaxGen.f.corres_full` per function.
  `#hax_coverage Ns` reports per function. For one literal, the entry points are
  `ascend_reified` and `hax_corres`. A function generic over a trait is monomorphised at
  the extraction's instances (`Monomorphise.lean`, `fnCorres_monomorphise_iff`), and
  `hax_ascend` declares `Ns.HaxGen.f.corres_generic` for the generic literal. The
  executable `lake exe asc-cover` (development repository) counts, for each
  extraction, the functions that the descent fronts accept and the generator proves.
- In the ascent on `LowCT`, x86 and RV64
  (`CatCrypt/Crypto/SecureCompilation/Ascent/`), the judgements `Corres`, `CorresJ` and
  `CorresR` relate a `LowCT` command, an x86 block or an RV64 block to a function on words,
  integers or field elements. `CorresIsa` is the same judgement at the instruction-set
  interpreter `Isa.lsemFuelMemF` (x86-64, AArch64, RV64); `corresIsa_x86_of_corresJ` and
  `corresIsa_arm_of_corresJ` transport a `CorresJ` result to it for blocks whose
  registers and memory do not depend on the flags. Its tactics are `ascend!`, `ascend_expr!`,
  `corres_solve_scalar`, `corres_sym`, `corres_sym_rv` and `mont_bound`.
  [ASCENT.md](ASCENT.md) is the guide, [ASCENT_REFERENCE.md](ASCENT_REFERENCE.md) the
  reference, and [CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md) the
  procedure for third-party machine code.
  [ASCENT_OVERVIEW_HIGHLEVEL.md](ASCENT_OVERVIEW_HIGHLEVEL.md) gives the design, its
  categorical form and its relation to verification-condition generation;
  [ASCENT_OVERVIEW_LEAN.md](ASCENT_OVERVIEW_LEAN.md) maps it to the declarations.

## Transfer: parametricity across representations

Transfer moves a proved statement across a registered relation between an abstract
value and its representation (`ZMod p` and limbs, `UScalar` and in-range `Int`, a
group and its bytes). The engine is the ParamTransfer package (namespace
`Transfer`), a port of Trocq's graded parametricity with `Param (m n) A B`,
`Related enc a b` and `RelatedBinOp`. Its tactics are `param_transfer` and `#transfer`,
which transfer statements and terms; `param_solve` and `rcongr`, which prove a
`Related` goal by descent through registered squares; and `param_auto`, the
coordinating cascade. The package's `README.md` and `TACTICS.md` document them.

A guarded square has a side condition that constrains the abstract operands, such as
`b ≤ a` at `a - b`; a total square is a guarded square with guard `True`. The engine
registers guarded squares as `RelatedBinOpOn`, `RelatedUnOpOn` and `RelatedRelOn`
(ParamTransfer `Transfer/Base/RelatedOn.lean`). The tactic `param_guard` composes
them and discharges each guard with `transfer_guard_disch` or leaves it as a goal.

In the development repository, `CatCrypt/Crypto/Bridges/Transfer/README.md` indexes
the relations the workspace registers. Its entries for hax-extracted integer code are
`HaxIntTransfer`, `HaxPrimeWord` and `RustMWordTransfer`. In this package,
`CatCrypt/Crypto/Bridges/Transfer/CompilerRegistry.lean` registers the compiler's
preservation lemmas, and `VIR/ParamDescent.lean` and `VIR/ParamDialectTransport.lean`
certify dialect-lowering squares by `param_solve`.

`TRANSFER_BOUNDARY.md` in the development repository uses "transfer" for a different
claim: a security game instantiated over an emitted primitive.

## Choosing a technique

| Situation | Technique |
|---|---|
| New kernel or Rust code that the compiler emits | descent; the source is the specification |
| Extracted Rust function `f` against a handwritten specification | ascent on `ImpExpr` (`hax_ascend`), then equate the generated function with the specification |
| Existing machine code (hand-written, CryptOpt, s2n-bignum) | ascent on x86 |
| Specification and code differ in representation | transfer, after ascent or descent |
| A proved fact needed at another representation | transfer |

For an extracted function `f`, the procedure has four steps: extract with haxpipeT
(`--emit-certified`, or `--emit-classes` for trait-generic code), run
`hax_ascend Ns`, read `#hax_coverage Ns`, and prove `Ns.HaxGen.f.gen` equal to the
specification. The last step uses transfer where the specification is stated over
`ZMod p` or `Int` and the code over words. When the generator reports a function as
failed, the report names the construct, leaf or loop that needs a new rule. Passing
the same extraction through the hax front also yields the emitted bytes, and
`asc-cover` reports which functions both techniques reach.

## Composition of the techniques

The welds are in `CatCrypt/Crypto/SecureCompilation/Ascent/`:

- Over one `LowCT` command, `LegWeld.legWeld` joins the descent refinement
  `RRefines spec c`, the ascent square `Corres SRwordNT P fa c` and the emit leg
  `rustToJasminCom_endToEnd_unconditional`. Its conclusion is that the emitted Jasmin
  program denotes the source step's output.
- `CorresDescentX86.corres_of_refines_x86` turns a relational-compiler result
  `Refines spec frag` into a forward simulation of the compiled x86 block;
  `CorresDescentRiscv.corres_of_refines_riscv` is the RV64 form.
- `PipelineWeld.feSub_raw_source_to_bytes` composes hax-lean's `pipeline_correct` with
  the `feSub` source tower, from the raw extracted `ImpExpr` to bytes.
- The ascent on `ImpExpr` and the compiler's theorems for the machine code meet at a
  common Lean function for one extracted function, `maj` of the Hash_DRBG extraction (in
  the development tree): `maj_corresJ_of_fnCorres` gives, for every `f` with
  `FnCorres` for the extracted body, a `CorresJ` result at the block decoded from the
  shipped bytes, and `maj_corresIsa_of_fnCorres` a `CorresIsa x86Isa` result for the
  export's straight-line chain over virtual registers. Both use
  `fnCorres_enc_unique` (`HaxAscent/Ascent/FnCorresUnique.lean`). No other extracted
  function, and no loop, has such a composition
  ([CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md#the-ascent-against-a-hax-reference)).

Transfer enters both other techniques as a proof step: descent certifies dialect
lowerings by `param_solve`, and an ascent result over words reaches a specification
over `ZMod p` through a registered relation.

## Trust ledger

A headline theorem rests on Lean's three foundational axioms (`propext`,
`Classical.choice`, `Quot.sound`) and on the further entries of the declared trust
base, `scripts/headlines_trust_base.txt` in the development repository. Every
`native_decide` entry trusts the Lean code generator on one closed computation. The
table lists the further entries and the row of the project plan that removes each.

| Entries | Content | Headlines that use them | Removed by |
|---|---|---|---|
| `CatCrypt.Util.ed25519L_prime`, `p25519_prime`, `secp256k1N_prime` | primality of the three published constants; the sources (`CatCrypt/Crypto/Util/ScalarFieldVerified.lean`, `CatCrypt/Crypto/Util/X25519Verified.lean`) declare them as theorems from the Pratt certificates in `CatCrypt/Crypto/Util/*PrimeCert.lean`, which `PrattCertificate.pratt_prime` checks by kernel `decide` | none in the recorded baseline | the entries leave the trust base at the next regeneration of the baseline that confirms they resolve to theorems |
| `Ed25519PointAddDecode.paShipped_instrOk` | every instruction of the shipped `ed25519_point_add` block lies in the decoder's covered set | `ed25519_point_add_bytes` | TV1a/TV1b: the decode equation and the general decode simulation for every encodable body, applied through R-ENC |
| `pa_footP1`–`pa_footP10`, `scr_foot1`–`scr_foot8`, `scm_foot1`–`scm_foot9` | memory-footprint scans of the canonical parts of the three shipped Ed25519 blocks | `ed25519_point_add_bytes`, `ed25519_sc_reduce_shipped`, `ed25519_sc_muladd_shipped` | R-ENC: one encoder, with the shipped Ed25519 results re-derived through `Lprog` |

No module of `Haxc/` uses `native_decide` except the route-selector check of each
instance (`and_frontScalOk`, `ltu_frontScalOk`, `mul1_frontScalOk`); those three checks
are not in the trust base, and the instances are not headlines.
