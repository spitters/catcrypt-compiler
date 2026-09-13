# The ascent

The ascent is the abstraction leg of the CatCrypt compiler. It proves that a program
at one of the compiler's low levels computes a Lean specification. Three kinds of
program are covered:

- a `LowCT` command, run by the scalar denotation `semScalar`, or by `semU`, which
  also denotes the `while` loop;
- an x86 instruction list, run by `runBlock : JState 64 → List (JInstr 64) → JState 64`,
  the Lean transcription of Jasmin's x86 semantics, with registers, memory and flags;
- an RV64 instruction list, run by `runRBlock64`.

The central judgment is a forward simulation. From a concrete state related to an
abstract state that satisfies a precondition, the program runs to a concrete state
related to the image of the abstract state under an abstract step. The descent goes the
other way: a verified lowering (`RustSubsetToLowCT.lower`, or the relational compiler
`RelationalCompile`) produces a program from a source or a specification together with
a refinement proof. The two legs meet in `legWeld`, which combines the refinement of
`RustSubsetToLowCT`, the front's jasmin program and an ascent correspondence for one
`LowCT` term.

The calculus follows AutoCorres (Greenaway, Andronick, Klein, ITP 2012; Greenaway, Lim,
Andronick, Klein, PLDI 2014): a correspondence relation, word abstraction from machine
words to rings, heap abstraction, and type strengthening to the weakest result monad.
Its design and vocabulary follow Sebastian Graf's AutoCorres2-in-Lean port,
[sgraf812/ascent](https://github.com/sgraf812/ascent); [PROVENANCE.md](PROVENANCE.md)
records what the package takes from it.

The modules are in `CatCrypt/Crypto/SecureCompilation/Ascent/`, namespace
`CatCrypt.Crypto.SecureCompilation.Ascent`. The contributor guide, with the full module
map, naming conventions and the choice of tactic, is
[Ascent/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Ascent/AGENTS.md).

## Layers

Each row names the modules of a layer and the declarations that carry it. Paths are
relative to `CatCrypt/Crypto/SecureCompilation/Ascent/`.

| Layer | Modules | Main declarations |
|---|---|---|
| Correspondence relations | `Corres`, `WhileTop`, `While`, `RunBlockCorres`, `CorresRiscv`, `CorresGeneric`, `Exit` | `Corres` over `semScalar` with `corres_seq`, `corres_weaken`; `CorresU` over `semU`; `CorresWhile`; `CorresJ` over `runBlock` with `corresJ_append`, `corresJ_loop`; `CorresR` over `runRBlock64`; `CorresM`, the machine-generic form, with `corres_eq_corresM`, `corresJ_eq_corresM`, `corresR_eq_corresM`; `CorresE`, `CorresUE` for bodies that throw |
| Value abstraction | `Corres`, `ExprLeaf`, `HeapAbs`, `StoreRefinement`, `MultiLimb`, `MlkemFieldLeaf`, `Width32Leaf`, `Phases` | `wEnc : BitVec 64 → ZMod 2^64` and the ParamTransfer squares `wEncAdd`, `wEncSub`, `wEncMul`; `SRword`, `SRwordNT`, `SRwordBV`; `ValueAbs` with `SRof`, `SRcarryOf` and the instance theorems `srwordNT_iff_srof`, `srcarry_iff_srcarryOf`; `fqEnc` and `CorresH`; `corres_WA`, `AbsProg` |
| Leaves over `LowCT` | `Corres`, `ExprLeaf`, `CorresScalar`, `BitwiseOrNot`, `RotateLeaf`, `SelectLeaf`, `ArrStoreLeaf`, `ArrLoadLeaf`, `MlkemFieldLeaf` | `corres_setScalar`, `corres_setScalar_NT`, `corres_setExpr` (arithmetic into `ZMod 2^64`), `corres_setExprBitwise`, `corres_setExprWord` (the `srcClean` word algebra over `BitVec 64`), `corres_setExprOr`, `corres_rotl`, `corres_ctSelect`, `corres_arrStore`, `corres_arrLoad`, `corres_setExpr_fqAdd` |
| Control and early exit | `Control`, `While`, `WhileTop`, `MlkemPolyFoldCorres`, `Exit` | `corres_for`, `corres_if`, `corres_for_indexed`, `polyAdd_fold_corres`, `corres_while`, `corresU_while`, `pipeline_exceptProg`, `whileExit_sim`, `corresU_while_exit` |
| Automation and total abstraction | `Ascend`, `AscendDecide`, `AscendMeta`, `Guards`, `Strengthen`, `CorresSolver`, `CorresAttr`, `CorresX86Solver`, `CorresRiscvLeaves`, `CorresRiscvSolver`, `CorresScalar`, `MontBounds`, `InvariantSchemas` | `ascend_sound`, `ascend_expr_sound`, `ascend_bitwise_sound` and the tactics `ascend!`, `ascend_meta`; `ascendG`, `ascendG_sound`; `tsLowCT_sound`, `tsHax_sound`, `Kernel.tsLevel`; the solvers `corres_solve`, `corres_solve_x86`, `corres_solve_rv`, `corres_solve_scalar`; `mont_bound` |
| Machine-level leaves and value results | `RunBlockCorres`, `EcMultiLimbCapstone`, `EcMultiLimbMul`, `MpnAdxCorres`, `FieldReduce`, `CorresX86Solver`, `CorresRiscvLeaves`, `Capstone`, `CapstoneField`, `EcMultiLimbEmit` | `corresJ_sbb`, `corresJ_adc`, `srcarryLimbs_recompose`; `sbbLimbs_spec`, `corresJ_sbbChain`; `mulLimbs_spec`, `corresJ_adxBlock`; `mpnAdd_runBlock`, `mpnSub_runBlock`; `montRedc_spec`, `corresJ_montRedc4Block`; `corresJ_movX` … `corresJ_mulxX`; `corresR_add` … `corresR_slli`; `sbbChain_emit_realizes_abstract_CF` |
| Ties between machines, and program logics | `CorresBridge`, `CorresBridgeArith`, `CorresBridgeArithComplete`, `CorresBridgeMem`, `CorresBridgeMemStore`, `CorresBridgeCtrl`, `CorresMachineTie`, `CorresMachineTieFragments`, `JasminComRunBlockTie`, `JasminComRunBlockSeq`, `JasminComRunBlockRealloc`, `XrunRunBlockTie`, `CorresHoare`, `RunBlockMvcgen`, `RunBlockMvcgenMorphism`, `JStateSepLogic` | `corresJ_forget_to_corres`, `coRefine`; `arith_middle_tie_seq_nonTmp`, `mem_store_middle_tie_full`, `for_middle_tie_gen`; `SimTie`, `simTie_seq`; `lowerBlock_tie`, `lowerBlockR_tie`; `xrun_runBlock_tie`; `corresJ_iff_triple`, `runBlockM_triple_iff`, `Spec.wp_theta`, `RunBlockTriple.frame` |
| Descent contracts in the ascent's shape | `CorresDescent`, `CorresDescentX86`, `CorresDescentRiscv`, `XrunRunBlockTie` | `frefines_ret`; `CorresMPost`, `corres_of_refines_x86`; `corresR_of_refines`; `corres_of_refines_x86_runBlock` |
| Welds to the emit leg and to sources | `EmitBridge`, `FeSubEndToEnd`, `FeAddEndToEnd`, `KeystoneControl`, `CondKernelCapstone`, `ArrStoreEmit`, `MlkemPolyAddCapstone`, `LegWeld`, `LegWeldDemo`, `FeSubSourceTower`, `LoopSourceLeaf`, `LoopSourceTower`, `PipelineWeld`, `SourceBridge`, `CorresScalar` | `keystone_emit`, `keystone_emit_NT`; `legWeld`, `legWeld_lower`; `feSub_source_to_bytes_tower`, `feAdd_source_to_bytes_tower`; `feSub_raw_source_to_bytes`, `feSubImp_raw_source_to_bytes`; `corresScalar_frontDenote_two` |
| Demonstrations | `Demos/*` | see below |

## Entry points

A reader new to the ascent can take these declarations in order.

1. `Corres` and `corres_seq` in
   [Corres.lean](CatCrypt/Crypto/SecureCompilation/Ascent/Corres.lean): the
   correspondence over `semScalar` and its sequencing rule.
2. `corres_setExpr` and `SRwordNT` in
   [ExprLeaf.lean](CatCrypt/Crypto/SecureCompilation/Ascent/ExprLeaf.lean): the
   arithmetic value leaf and the state relation that ignores the lowering's
   temporaries.
3. `ascend_expr_sound` in
   [Ascend.lean](CatCrypt/Crypto/SecureCompilation/Ascent/Ascend.lean), and the
   tactic `ascend_meta` in
   [AscendMeta.lean](CatCrypt/Crypto/SecureCompilation/Ascent/AscendMeta.lean): a
   straight-line kernel lifted to its word specification without manual composition.
4. `ascendG_sound` in
   [Guards.lean](CatCrypt/Crypto/SecureCompilation/Ascent/Guards.lean) and
   `tsLowCT_sound` in
   [Strengthen.lean](CatCrypt/Crypto/SecureCompilation/Ascent/Strengthen.lean): the
   total abstraction of every `LowCT` command under guards, and the choice of result
   monad.
5. `CorresJ` and `corresJ_sbb` in
   [RunBlockCorres.lean](CatCrypt/Crypto/SecureCompilation/Ascent/RunBlockCorres.lean),
   then `mpnAdd_runBlock` in
   [MpnAdxCorres.lean](CatCrypt/Crypto/SecureCompilation/Ascent/MpnAdxCorres.lean): a
   carry chain over any number of limbs against the integer sum.
6. `corres_of_refines_x86_runBlock` in
   [XrunRunBlockTie.lean](CatCrypt/Crypto/SecureCompilation/Ascent/XrunRunBlockTie.lean):
   a descent refinement read as a correspondence on the machine of the `CorresJ`
   leaves.
7. `legWeld` in [LegWeld.lean](CatCrypt/Crypto/SecureCompilation/Ascent/LegWeld.lean)
   and its instance `feSub_source_to_bytes_tower` in
   [FeSubSourceTower.lean](CatCrypt/Crypto/SecureCompilation/Ascent/FeSubSourceTower.lean):
   the weld traced below.

The demonstrations under `Ascent/Demos/` each state a small route end to end:

| Module | Route | Main declarations |
|---|---|---|
| [Demos/Decide](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Decide.lean) | a `LowCT` kernel to `asemWExpr` / `asemWBV` by the deciding tactics | `arithK_expr`, `bitK_bitwise`, `bitK_solve` |
| [Demos/Scalar](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Scalar.lean) | `corres_solve_scalar` over word kernels, and the weld to the front's `Com catCryptDialect` | `qrFrag_refines`, `xor_rotl_refines`, `qrClosed_frontDenote` |
| [Demos/X86StraightLine](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/X86StraightLine.lean) | `corres_solve_x86` over carry chains and over `x86Target.compile` output | `sbb3_refines`, `mulx_adcx_refines`, `compiled_refines` |
| [Demos/Riscv](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Riscv.lean) | `corres_solve_rv` over an add with materialised carry | `addCarry_ascends` |
| [Demos/LeanSourceX86](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/LeanSourceX86.lean) | a Lean function through the descent to x86, and the same block through the solver | `add_descent_x86`, `add_descent_solver` |
| [Demos/LeanSourceRiscv](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/LeanSourceRiscv.lean) | the RV64 twin | `add_descent_riscv` |
| [Demos/HeapAbs](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/HeapAbs.lean) | an `n`-limb add over the generic value abstraction | `feAddN_capstone`, `feAdd4_capstone_field` |
| [Demos/SourceToBytes](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/SourceToBytes.lean) | the closed capstones at their values | `feSub_value`, `feAdd_value` |
| [Demos/EarlyExit](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/EarlyExit.lean) | a search loop with `return`, an `ImpExpr` term written in Lean in the shape of an extraction, read as an exception program | `searchU_except_found`, `searchU_word_found` |
| [Demos/Strengthen](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Strengthen.lean) | the result monad chosen per kernel | `feSubC_ts_refines`, `qrFrag_ts_refines`, `searchU_ts_refines` |

## A worked path: `feSub_source_to_bytes_tower`

The kernel is `r0 := a0 - b0` with the inputs written as the literals
`av = 1634760805` and `bv = 857760878`. The theorem is

```lean
theorem feSub_source_to_bytes_tower (N : Nat) (leafSpec : LeafSpec) :
    feJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy feSubSourceWord
      ∧ wEnc feSubSourceWord
          = ((av : Nat) : ZMod (2 ^ 64)) - ((bv : Nat) : ZMod (2 ^ 64))
```

It is one application of `legWeld_lower`. The arguments are assembled as follows.

1. Source. `feSubSrc : RustSrc` ([FeSubSourceTower.lean](CatCrypt/Crypto/SecureCompilation/Ascent/FeSubSourceTower.lean))
   writes the two literals and assigns `r0 := a0 - b0`. `feSubSrc_ifFree` places it in
   the fragment of the verified lowering `RustSubsetToLowCT.lower`.
2. Descent refinement. `legWeld_lower` obtains `RRefines (RustSrc.exec feSubSrc) (lower feSubSrc)`
   from `lowerRefines` and moves it to the front's spelling `feSubC` along
   `feSubC_litNorm : LitNorm (lower feSubSrc) feSubC`, which rewrites literal expression
   assignments to literal assignments.
3. Run. `feSubC_run : AdeqRun feSubC frs0 frsF` records that each literal is a `u64`
   and that the subtraction is in range at the state it reads.
4. Scoping. `feSubC_readsOK` states that every read of `feSubC` follows a write, and
   `feSubC_out` that `r0` is written.
5. Front. The facts `fHTrans`, `fHName`, `fHRet` and `fHCom` of
   [FeSubEndToEnd.lean](CatCrypt/Crypto/SecureCompilation/Ascent/FeSubEndToEnd.lean) form a
   `FrontOut feSubC "r0"`: `translateDialectControl VarMap.empty feSubC` succeeds, `r0`
   resolves to a word slot, the continuation closed at that slot is `fCom`, and
   `cryptoDialectToJasminCom fCom = some feJcom`.
6. Ascent. `feSub_corres : Corres SRwordNT (fun _ => True) faSub feSubC` is `corres_seq`
   over two `corres_setScalar_NT` leaves and `feSub_ascends`
   ([CapstoneField.lean](CatCrypt/Crypto/SecureCompilation/Ascent/CapstoneField.lean)),
   which is `corres_setExpr` at a subtraction. `faSub_at_r0` evaluates the abstract
   step at `r0`.
7. Weld. Inside `legWeld` ([LegWeld.lean](CatCrypt/Crypto/SecureCompilation/Ascent/LegWeld.lean)),
   `agreeRun` matches the `RustExec` run of the refinement with a `semScalar` run twice:
   from the empty environment, where it supplies the premises of the emit theorem
   `rustToJasminCom_endToEnd_unconditional`
   (`CatCrypt/Crypto/SecureCompilation/VIR/CompilerCorrectnessExtracted.lean`),
   and from the environment `derivedEnv rs` that reflects the entry state, where it
   identifies the word the ascent's relation reads at `r0`.

`feSub_value` ([Demos/SourceToBytes.lean](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/SourceToBytes.lean))
evaluates the second conjunct to `776999927`. `LegWeldDemo.lean` applies the same weld
to `r0 := a0 + b0 - c0` and is the template for a new closed kernel.

## Scope

This section states what the capstones prove and where they stop, with the theorem
names at which each boundary can be checked.

`bash scripts/ascent-corpus.sh` lists, from the declaration text of the tracked files, the kernels of the package (closed `LowCT` values, `reifyLowCT%` kernels, and `ImpExpr` terms with an exit-lowering theorem), which of them an ascent correspondence names (single-store correspondences in a separate column), and which a closed capstone reaches, one that takes no emit, denotation or correspondence equation as a hypothesis; its header states the method.

### The source-to-bytes capstones end at a `Com jasminDialect` denotation

`legWeld`, `legWeld_lower`, `feSub_endToEnd`, `feAdd_endToEnd`,
`feSub_source_to_bytes_tower`, `feAdd_source_to_bytes_tower`, `demo_source_to_bytes`,
`feSub_value`, `feAdd_value`, `feSub_raw_source_to_bytes`,
`feSubImp_raw_source_to_bytes`, `keystone_emit`, `keystone_emit_NT`,
`keystone_emit_arr`, `keystone_emit_fq`, `welding` and `welding_program` conclude an
equation `jcom.denote (ctMapValD .nil) = ctTransTy val` for a program
`jcom : Com jasminDialect …` produced by `cryptoDialectToJasminCom`. The word "bytes" in
these names and their docstrings refers to that denotation. No ascent theorem reads
the output of the owned x86 lowering (`toLprogPhysAbi`) or of an instruction encoder.

The machine-level ascent results are stated over instruction-list semantics: `runBlock`
over `JInstr 64` (`CorresJ`), `xrun` / `x86Target.runOps` over the `Instr 64` lists of
the `ScalarLinX86Demo` target (`corres_of_refines_x86`), `runRBlock64` over `RInst64`
(`CorresR`), and `lsemStraightMem` over `LinstrRM` for the `sbb`-chain lowering
`sbbChainL` defined in `EcMultiLimbEmit` (`sbbChain_emit_realizes_abstract_CF`).

### The emit welds apply to kernels without inputs

`legWeld` takes `hReads : readsOK (fun _ => False) c`, so every read in `c` follows a
write in `c`, and it closes the front at `VarMap.empty` and the jasmin program at the
empty valuation. `F.jcom.denote (ctMapValD .nil)` is therefore a constant, and the
conclusion is a statement about one input-free kernel. `corres_emit_weld` and the `keystone_*` welds require
the same through `hAgree`: the word at the readout name is the same for every entry
environment. Every instance in the package fixes its inputs as literals:
`feSub_source_to_bytes_tower` and `feAdd_source_to_bytes_tower` at `av` and `bv`,
`demo_source_to_bytes` at `dav`, `dbv` and `dcv`, and `qrClosed_frontDenote_val`, which
concludes `qrCom.denote .nil = 393216#64`.

The weld at a nonempty entry valuation is `corresScalar_frontDenote` in
`CorresScalar.lean`. Its conclusion is over `Com catCryptDialect Γ`, one lowering above
`Com jasminDialect`, and the package contains no instance of it.

### The raw hax source is joined to the capstone by its output word

`feSub_raw_source_to_bytes e hNoLoops hNoEE hBridge` is a conjunction of three facts.
The first is hax-lean's `pipeline_correct` applied to `hBridge`, a statement about `e`.
The second and third are `feSub_source_to_bytes_tower`, which does not mention `e`.
`feJcom` is the front's translation of the `LowCT` term `feSubC`, not of a hax term,
and no theorem in the package relates `feSubImp` or any other `Hax.ImpExpr` to
`feSubC`. The hypothesis `hBridge : haxOutcomeWord (Hax.denote bi fuel e env).1 = some feSubSourceWord`
identifies only the output word, so every `e` whose reference run ends in a `uint`
value with the word `776999927` satisfies it.

`feSubImp_raw_source_to_bytes` discharges `hBridge` by evaluation (`feSubImp_word`) at
`Hax.widthAwareBuiltins`. `feSub_raw_source_to_bytes'` fixes `Hax.defaultBuiltins`,
whose `sub` accepts only `int` arguments, while `haxOutcomeWord` reads only `uint`
values; its `hBridge` therefore fails for a kernel whose result is computed by `sub` at
that table.

### Simulations from hax source do not reach the arithmetic kernels

`haxToLowCT` lowers a builtin call to a leaf call (`RCall`, or `RCallSwap` for a
two-component result) or, for `array_update` and `index`, to `RArrStore` and
`RArrLoad`. It produces `RScalarSetExpr` only for the index shift of a `forFold` with
a nonzero start. The program-level simulation
`haxToLowCT_simulates_program` (`CatCrypt/Crypto/Hax/HaxToLowCTSim_Program.lean`) takes
`FullSimPreconds`, whose field `leafScalar` states that no builtin result decodes as a
scalar. It therefore does not reach the `RScalarSetExpr` kernels that `legWeld` and the
value leaves abstract. `raw_source_to_bytes_of_program` and `welding_program` are stated
for arbitrary programs and have no instance in the package.

`haxToLowCT_simulates_full` (`HaxToLowCTSim_Main_Full.lean`) takes five universally
quantified call-side hypotheses, each refuted in `HaxToLowCTSim_Program.lean` by
`hScalarFresh_all_unsat`, `hDestBoundAll_unsat`, `hArgsEnvAll_unsat`,
`hArgsBoundAll_unsat` and `hArgsFreshAll_unsat`. No ascent theorem uses it:
`EmitBridge.welding` takes its `RustExec` premise as a hypothesis, and
`welding_program` supplies that premise from `haxToLowCT_simulates_program`.

The exit-flag lowering `haxToLowCTK` (`CatCrypt/Crypto/Hax/HaxToLowCTExit.lean`), with
scalar operations enabled, lowers `let x = op(a, b)` for `add`, `sub` and the unsigned
comparisons to `RScalarSetExpr`. `haxToLowCTFn_simulates`
(`CatCrypt/Crypto/Hax/HaxToLowCTSim_Exit.lean`) proves that the lowered function
simulates `Hax.denote'` on the fragment `exitSimOk` under `ScalarOpsSound`, which
`scalarOpsSound_noOverflow64_width` discharges for hax-lean's width tables with
overflowing `add` and `sub` refused. No ascent module uses this simulation. Its loops
lower to `RWhileNz`, which `semScalar` does not denote and the emit fragment
`IsCoveredSCtl` does not contain.

### The array and loop source towers

`arrKernel_source_to_rustexec_program` (`LoopSourceTower.lean`) takes the array-store
step of the program-level simulation, `hArrUpd`, as a hypothesis, and `arrKernel`
exercises no other construct. `ProgramSimArms_of_vacuity` discharges that step only for
a builtin table that does not implement `array_update`. The source preimage of a
bounded `RFor` is `RustSrc.forN`: `loopSrc_source_preimage` (`LoopSourceLeaf.lean`)
conjoins the descent refinement, the ascent correspondence and the `RFor` shape of the
lowered loop, and no theorem fuses the first two into an emit conclusion. From hax
source, `haxToLowCT` lowers only `.forFold` to `RFor`, and the evaluation of `.forFold`
is `none` (`loop_forFold_source_vacuous`).

### Welds that take the emit equation as a hypothesis

`corres_emit_weld`, `keystone_setScalar`, `keystone_if`, `keystone_for`, `loop_keystone_emit`,
`condKernel_bytes_of_emit`, `keystone_arr`, `keystone_arrStore`, `keystone_fq` and
`keystone_setScalar_fq` are stated for an abstract map `Emit` and take
`hEmit : jdenote = Emit val` as an argument, which they return as their first
conjunct. The second conjunct of `keystone_for` is
`wEnc (BitVec.ofNat 64 v) = (v : ZMod (2 ^ 64))`, which holds for every `v`, and the
second conjunct of `keystone_if` is an identity about `ifClosedVal`. For the branch
kernel, `condBackend_declines` proves `cryptoDialectToJasminCom condFrontCom = none`, so
the pipeline produces no program that supplies `hEmit` for `condKernel_bytes_of_emit`.

`keystone_emit`, `keystone_emit_NT`, `keystone_emit_arr` and `keystone_emit_fq`
discharge `hEmit` from `rustToJasminCom_endToEnd_topLevel_unconditional`.
`keystone_emit_NT` has the instances `feSub_endToEnd` and `feAdd_endToEnd`.
`keystone_emit` is used only by the generic `welding` and `welding_program`, and
`keystone_emit_arr`, `keystone_emit_fq`, `corres_while_exit` and `corresU_while_exit`
have no instance in the package. The emit fragment `IsCoveredSCtl` has no `RWhileNz`
arm, so `corres_while`, `corresU_while` and the exit rules have no weld to a
`Com jasminDialect` program.

### The total abstraction assigns an unsatisfiable guard to most constructors

`ascendG` (`Guards.lean`) maps 17 of the 27 `LowCT` constructors to `unsupportedAbs`,
whose guard `Guard.unsupported` means `False`: `RLetZero`, `RCall`, `RCallSwap`,
`RCloneCall`, `RCallN`, `RSelect`, `RLimbStore`, `RLimbStoreExpr`, `RFnDef`, `RFnCall`,
`RTupleLoad`, `RArrStore`, `RArrLoad`, `RArrStoreLit`, `RArrLoadLit`,
`RCallDstThreaded` and `RForRuntime`. Twelve of these are in the emit leg's fragment
`IsCoveredS`. `ascendG` does the same for `RLetU64Zero` over a body containing a loop,
for `RIfNz` and `RWhileNz` on a temporary name, for `RIfNz` shapes other than a guarded
then-branch or a φ-merge of two literal writes to one name, and for `RScalarSetExpr`
outside `srcClean`. `ascendG_sound` holds for every command, but at those nodes its
precondition `guardsHold` is unsatisfiable; `tsLowCT` returns `none` for them
(`tsLowCT_isSome_iff`). The leaves `corres_arrStore`, `corres_arrLoad` and
`corres_ctSelect` are not used by `ascendG`.

### Worked examples with symbolic inputs

The results that are parametric in the machine state and conclude an arithmetic
specification are stated over instruction lists built by Lean definitions
(`adcxBlock`, `kernelBlock`, `emitMontRedc4Block`), not over the output of a compiler
front: `mpnAdd_runBlock`, `mpnSub_runBlock`, `mpnAddKernel_runBlock` and
`mpnSubKernel_runBlock` over any number of limbs, `feAddN_capstone`,
`feAdd4_capstone_field` and `corresJ_montRedc4Block`. `corresJ_sbbChain`,
`corresJ_adxBlock` and `corresR_subBorrow3` refine their blocks to abstract folds
(`sbbAbs`, `adxAbs`, `subBorrow3Step`); `feSub4_capstone` and `feMul4_capstone` are
identities about the limb functions `sbbLimbs` and `mulxLimbs` under `SRcarryLimbs`.

On compiler output, `add_descent_x86`, `add_descent_runBlock` and `add_descent_riscv`
establish `a + b` for symbolic `a` and `b` through the descent. Their ascent
counterparts `add_descent_solver` and `compiled_refines` refine the same blocks to the
two-address fold, such as `addStepX ∘ movStepX`, and not to `a + b`. `Demos/Decide`
and `Demos/Scalar` ascend a `LowCT` kernel to its syntactic specification `asemWExpr`,
`asemWBV` or a `wordStep` fold. `keccakRoundBody_bitwise` targets
`asemWBV keccakRoundBody`, which is not related to FIPS 202; the FIPS 202 statement for
the emitted Keccak permutation is `keccakF1600Com_denote_spec` in
`CatCrypt/Crypto/SecureCompilation/VIR/KeccakFipsAscent.lean`, which does not use
`Corres`. `Demos/EarlyExit` and
`searchU_ts_refines` are stated at hax-lean's `denote'` and `pipeline`, with no `LowCT`
term and no emit leg.

### Hand-written assembly

`X86Backend/NasmParse.lean` reads the NASM Intel subset CryptOpt emits into `JInstr`
blocks. `JInstr` covers Jasmin's scalar `x86_op` set except the instructions declined
for constant time (`DIV`, `IDIV`, `CQO`, `BSR`, `BSF`, `BSWAP`, `LZCNT`, `TZCNT`,
`POPCNT`, `PDEP`, `PEXT`); the `JInstr` docstring in `X86Backend/JasminModel.lean` lists
them with the reason. The CryptOpt Curve25519 `solinas_square` kernel from fiat-crypto
(`bench/cryptopt/fiat_curve25519_solinas_square.asm`) parses in full;
`solinasSquareBlock` is its 99 instructions, and `lake exe nasm-parse-kat` fails unless
parsing the file yields exactly that list. The route to its specification has three
results:

- `solinasSquareBlock_corres` (`Ascent/CorresX86Mem.lean`): the block refines its
  abstract run `absRunMem` over `SRmem solinasCells`, which relates JState's name-keyed
  memory to an address-keyed abstract memory on the fourteen cells the kernel reads and
  writes.
- `absRunMem_solinas_spec` (`Ascent/SolinasSquareCorrect.lean`): the abstract run
  satisfies `SolinasSquareSpec`, fiat-crypto's `sqr_correct` for `2^255 - 19` on four
  saturated limbs, when the spill slots and the input limbs have distinct addresses.
- `solinasSquare_correct`: for every `JState` whose fourteen tracked cells have
  separated addresses, the output limbs of `runBlock st solinasSquareBlock` are
  congruent to the square of the input limbs modulo `2^255 - 19`.

The abstract state carries the registers, `CF` and `OF`. The leaves for `setcc` and
`cmovcc` are stated at the conditions that read those two flags; a kernel branching on
`ZF`, `SF` or `PF` needs further leaves. CryptOpt's `carry_mul` kernel does not parse in
full: it uses memory-source `adcx`, `adox` and `add`, `bzhi`, and the three-operand
`imul` with a memory source, which have no `JInstr` constructor.

### The descent contracts and the ascent meet at the x86 register file

`frefines_ret` (`CorresDescent.lean`) is stated over `Com fieldDialect`, and
`corresScalar_frontDenote_two` over `Com catCryptDialect`. No program in the package is
reached by both. At the x86 machine, `corres_of_refines_x86_runBlock` carries a descent
`Refines` to a `CorresMPost` at `runBlockStep` whose entry and exit relations read only
the register file. It covers every instruction that `x86Target.compile` emits for shift
immediates below 64 (`compile_XJFaithful` at the track `XJTrack.regs`). A relation that
tracks a flag, such as `SRcarry`, is outside this bridge: `XJFaithful` excludes `imul`,
the bitwise instructions and the shifts whenever `CF`, `OF` or `ZF` is tracked, admits
`adc` and `sbb` only when `CF` is tracked and `OF` and `ZF` are not, and admits `neg`
only when neither `OF` nor `ZF` is tracked.

### Word width

The `LowCT` value leaves are at width 64. `Width32Leaf.lean` provides the width-32 word
isomorphism `wEnc32` and its value transfer `wEnc32_evalBV32_evalZMod32`, but no
`Corres` leaf at width 32: `semScalar_setExpr_width64` proves that `semScalar` writes a
64-bit slot for every `RScalarSetExpr`.

## Research probes outside the calculus

The following modules explore extensions of the `Std.Do` weakest-precondition
metatheory and of leakage reasoning. No module of the calculus, capstone or
demonstration imports them, and the capstones do not depend on them.

| Module | Content |
|---|---|
| `GradedMvcgenProbe` | whether stock `mvcgen` carries a grade: as operational state it does (`demo_cost`); as a specification-only index it does not (`forget_gradedBind`, `postShape_exhaustive`) |
| `GradedWP` | a standalone graded predicate transformer with grade-additive sequencing (`seq`) |
| `WriterTMvcgen` | an accumulating log as write-only state for `mvcgen` (`writerM_triple_iff`) |
| `LeakageExceptT` | a leakage channel as the exception branch, `leakEquiv` |
| `RelationalProductMvcgen` | relational Hoare triples as unary `Std.Do` triples over a product program (`relTriple_iff_stddo`) |
| `RelationalExceptTMvcgen` | the same over `ExceptT`, with leakage as the exception barrel (`relExPostCond_except_leak`) |
| `UCLeakageDecomp` | universal composability as a simulator existential over the leakage-transported relational judgment (`UCviaRel_iff_ExactUCEmulates`); imports `CatCrypt.Crypto.UCMonad` |
| `XPostShape`, `XMvcgen`, `XMvcgenControl`, `XMvcgenReg`, `XRelatorPMF`, `XHeapSoundness`, `XMorphismInstance`, `XDijkstraAll` | an extended `PostShape` framework fusing grades, separation logic, relational reasoning and monad-morphism transfer, with the VC generators `xmvcgen`, `xmvcgen_ctl` and `xmvcgen!` |
| `XAdvantageHybrid` | the advantage-triangle tactic `advmvcgen` over hybrid arguments; imports `CatCrypt.Crypto.MultiQueryPRF` |
