# Ascent: contributor guide

This directory holds the ascent, the abstraction leg of the compiler: correspondence
proofs from `LowCT` commands, x86 instruction lists and RV64 instruction lists up to
Lean specifications. [ASCENT.md](../../../../ASCENT.md) explains the calculus, traces
a capstone and states the scope of the results. This file is the working guide: names,
module map, choice of tactic, how to add a kernel, and the rules for editing here.

All modules are in the namespace `CatCrypt.Crypto.SecureCompilation.Ascent`, the
demonstrations in `CatCrypt.Crypto.SecureCompilation.Ascent.Demos`.

## Names

The vocabulary follows [sgraf812/ascent](https://github.com/sgraf812/ascent) and
AutoCorres.

- `Ascent` is the calculus, the directory and the namespace. `ascend` is the verb: the
  tactics `ascend`, `ascend!`, `ascend_meta` and the theorems `ascend_sound`,
  `ascend_expr_sound`.
- `Corres` is the AutoCorres correspondence relation. Its variants carry a suffix for
  the machine or the shape: `CorresU` (the unified waist `semU`), `CorresWhile`,
  `CorresJ` (`runBlock` over `JState 64`), `CorresR` (`runRBlock64`), `CorresM` (any
  step function), `CorresMPost` (separate entry and exit relations), `CorresH`
  (separate pre- and post-state relations), `CorresE` and `CorresUE` (bodies that
  throw). Lemmas take the matching prefix: `corres_`, `corresU_`, `corresJ_`,
  `corresR_`, `corresM_`, `corresH_`.
- State relations start with `SR`: `SRword`, `SRwordNT` (non-temporary names),
  `SRwordBV` (identity word algebra), `SRarr`, `SRarrLoad`, `SRcarry`, `SRcarry2`,
  `SRcarryLimbs`, `SRx` (x86 registers only), `SRr` (RV64 registers), `SRfqCanon`,
  `SRfqVal`, and the generic `SRof`, `SRpi`, `SRcarryOf`. Abstract states start with
  `A`: `AField`, `AArr`, `ACarry`, `AStateX`, `AStateR`.
- A leaf is named after what it refines: `corres_setScalar`, `corres_setExpr`,
  `corres_arrStore` for `LowCT` arms; `corresJ_sbb`, `corresJ_mulx` for instructions
  under `SRcarry`; `corresJ_addX` for instructions under `SRx`; `corresR_add` for RV64.
  The abstract single steps are `sbbStep`, `addStepX`, `addStepR`; folds over blocks are
  `sbbAbs`, `adcxAbs`; blocks are `sbbBlock`, `adcxBlock`.
- The decidable fragments are `IsAscendable`, `IsAscendableExpr`,
  `IsAscendableBitwise`, with specifications `asemW`, `asemWExpr`, `asemWBV`. A `Bool`
  checker ends in `B` and has a `*B_sound` lemma (`isAscendableExprB_sound`).
- Ties between two machines: `*_middle_tie_*` relate `semScalar` and `runBlock`,
  `simTie_*` instantiate `SimTie`, and `*_runBlock_tie` relate a `Com jasminDialect`
  denotation to `runBlock`.
- Welds to the emit leg: the declarations `corres_emit_weld`, `keystone_emit` and their
  variants (`keystone_NT`, `keystone_if`, `keystone_arr`, `keystone_fq`). Capstones end
  in `_endToEnd`, `_source_to_bytes`, `_source_to_bytes_tower` or `_capstone`; the
  "bytes" of these names is a `Com jasminDialect` denotation (see the scope section of
  [ASCENT.md](../../../../ASCENT.md)).
- Recurring hypothesis names: `hCorres` (the ascent correspondence), `hSR` and `hP`
  (entry relation and precondition), `hAgree` (the output word at the readout name does
  not depend on the entry environment), `hEmit` (an emit equation taken as a
  hypothesis), `hBridge` (a source output word identified with the kernel's word).

## Module map

Links are relative to this directory. Every module has a docstring with its results;
the table gives the role and the declarations to read first.

### Correspondence relations and value abstraction

| Module | Role |
|---|---|
| [`Corres`](Corres.lean) | `Corres` over `semScalar`; `corres_skip`, `corres_block`, `corres_seq`, `corres_weaken`; `wEnc`, the squares `wEncAdd`/`wEncSub`/`wEncMul`; `SRword`, `corres_setScalar` |
| [`CorresGeneric`](CorresGeneric.lean) | `CorresM` over a step function; `corres_eq_corresM`, `corresJ_eq_corresM`, `corresM_seq` |
| [`RunBlockCorres`](RunBlockCorres.lean) | `CorresJ` over `runBlock`; `corresJ_append`, `corresJ_loop`; `SRcarry`, `corresJ_sbb`, `corresJ_adc`; `SRcarryLimbs`, `srcarryLimbs_recompose` |
| [`CorresRiscv`](CorresRiscv.lean) | `CorresR` over `runRBlock64`; `corresR_append`, `corresR_eq_corresM` |
| [`While`](While.lean) | `CorresWhile` over the `k`-fold body iteration; `corres_while_iter`, `corres_while` |
| [`WhileTop`](WhileTop.lean) | `CorresU` at `semU`, which denotes `RWhileNz`; `corresU_of_corres`, `corresU_while` |
| [`ExprLeaf`](ExprLeaf.lean) | `SRwordNT`, `SRwordBV`; `wEnc_evalBV_evalZMod`; `corres_setScalar_NT`, `corres_setExpr`, `corres_setExprBitwise` |
| [`HeapAbs`](HeapAbs.lean) | `ValueAbs` and its combinators; `SRof`, `SRpi`, `SRcarryOf`; the bespoke relations as instances (`srwordNT_iff_srof`, `srcarry_iff_srcarryOf`); generic leaves `corres_setExpr_of`, `corresJ_sbb_of` |
| [`StoreRefinement`](StoreRefinement.lean) | re-export of the single-limb field abstraction of ParamTransfer `Transfer.Examples.MachineLimbField` |
| [`MultiLimb`](MultiLimb.lean) | re-export of the multi-limb field abstraction of the same ParamTransfer module |
| [`MlkemFieldLeaf`](MlkemFieldLeaf.lean) | `fqEnc` into `ZMod 3329`; `CorresH`; `SRfqCanon`, `SRfqVal`; `corres_setExpr_fqAdd` |
| [`Width32Leaf`](Width32Leaf.lean) | `wEnc32` and `wEnc32_evalBV32_evalZMod32`; `semScalar_setExpr_width64` (no width-32 `Corres` leaf) |
| [`Phases`](Phases.lean) | the WA/TS phase factoring (`corres_WA`, `ringWA`, `wordWA`); `MonadLevel`, `AbsProg`, `AbsProg.refines_iff_toExcept` |

### Leaves over `LowCT` and control

| Module | Role |
|---|---|
| [`CorresScalar`](CorresScalar.lean) | `corres_setExprWord` over the `srcClean` word algebra; `corres_seqAll`; tactic `corres_solve_scalar`; welds `corresScalar_frontDenote_two`, `corresScalar_frontDenote` to `Com catCryptDialect` |
| [`BitwiseOrNot`](BitwiseOrNot.lean) | `corres_setExprNot`, `corres_setExprOr`, derived over `SXor`/`SAnd` |
| [`RotateLeaf`](RotateLeaf.lean) | `rotl_spec`, `rotl_or_eq_xor`, `corres_rotl` |
| [`SelectLeaf`](SelectLeaf.lean) | `ctSelect_bitmask`, `ctSelect_spec`, `corres_ctSelect` |
| [`ArrStoreLeaf`](ArrStoreLeaf.lean) | `SRarr`, `wEnc_memSetDyn`, `corres_arrStore` |
| [`ArrLoadLeaf`](ArrLoadLeaf.lean) | `SRarrLoad`, `wEnc_memGetDyn`, `corres_arrLoad` |
| [`Control`](Control.lean) | `corres_for` (bounded `RFor`), `corres_if` (φ-merge `RIfNz`) |
| [`MlkemPolyFoldCorres`](MlkemPolyFoldCorres.lean) | `corres_for_indexed` (index-dependent loop step), `corres_rseqUpto`, `SRfqMixed`, `polyAdd_fold_corres` |
| [`Exit`](Exit.lean) | `pipeline_exceptProg` (hax control-flow encoding read as `ExceptT`); `whileE`, `whileExit_sim`, `corres_while_exit`, `corresU_while_exit`, `corresU_condSet` |

### Automation

| Module | Role |
|---|---|
| [`Ascend`](Ascend.lean) | the fragments and their soundness `ascend_sound`, `ascend_expr_sound`, `ascend_bitwise_sound`; tactics `ascend`, `ascend_expr`, `ascend_bitwise` |
| [`AscendDecide`](AscendDecide.lean) | `Bool` fragment checkers with soundness; tactics `ascend!`, `ascend_expr!`, `ascend_bitwise!`, `ascend_unified!` |
| [`AscendMeta`](AscendMeta.lean) | tactic `ascend_meta` (membership by syntax walk); `keccakRoundBody_bitwise` |
| [`Guards`](Guards.lean) | `Guard`, `guardsHold`; array layouts `ArrLayout`, `elemKey`, `SRwordL`; the total abstraction `ascendGL` over a layout and `ascendG = ascendGL []`; `ascendGL_sound`, `ascendG_sound`, `ascendG_sound_scalar`; array leaves `corresL_arrLoad`, `corresL_arrStore`, `corresL_limbStore`; `corresU_for_trips`, `corresU_whileNz` |
| [`GuardsLeaf`](GuardsLeaf.lean) | `CorresL`, `CorresUL` over the waist at a leaf oracle (`semScalarL`, `semUL`); abstract leaves `AVal`, `absArg`, `LeafAbs`, `AbsLeaves`; `ascendGLL`, `ascendGLL_sound`, `ascendGLL_noLeaves`; leaves `corresL_call`, `corresL_selectLeaf`, `corresL_arrLoadLitLeaf`; `leafK_corres` |
| [`Strengthen`](Strengthen.lean) | `tsLowCTL`, `tsLowCTL_sound`, `tsLowCTL_isSome_iff` and the empty-layout `tsLowCT`, `tsLowCT_sound`, `tsLowCT_isSome_iff`; `tsHax`, `tsHax_sound`; `Kernel.tsLevel` |
| [`CorresAttr`](CorresAttr.lean) | the `@[corres]` label attribute |
| [`CorresSolver`](CorresSolver.lean) | `corresJ_cons`, `corresJ_castFa`; tactics `corres_leaf`, `corres_chain`, `corres_solve` |
| [`CorresX86Solver`](CorresX86Solver.lean) | `SRx`, `corresJ_of_regs`, the leaves `corresJ_movX` … `corresJ_mulxX`; tactic `corres_solve_x86` |
| [`CorresRiscvLeaves`](CorresRiscvLeaves.lean) | `SRr`, `corresR_of_set`, the twelve `RInst64` leaves; the `@[corresR]` attribute |
| [`CorresRiscvSolver`](CorresRiscvSolver.lean) | the `@[corresR]` registrations; tactic `corres_solve_rv`; `corresR_subBorrow3` |
| [`MontBounds`](MontBounds.lean) | tactic `mont_bound` for carry-out and Montgomery range side goals |
| [`InvariantSchemas`](InvariantSchemas.lean) | window-invariant templates `MontReduceInvariant`, `SchoolbookMulInvariant`, `DivstepInvariant`, `FieldAddSubInvariant` with layouts |

### Machine-level leaves and value results

| Module | Role |
|---|---|
| [`EcMultiLimbCapstone`](EcMultiLimbCapstone.lean) | `sbbLimbs_spec`, `corresJ_sbbChain`, `feSub4_capstone` |
| [`EcMultiLimbMul`](EcMultiLimbMul.lean) | `mulLimbs_spec`, `corresJ_mulx`, `corresJ_adcxChain`, `SRcarry2`, `corresJ_adxBlock`, `feMul4_capstone` |
| [`EcMultiLimbEmit`](EcMultiLimbEmit.lean) | the `sbb` chain at `lsemStraightMem`: `runBlock_lsem_agreeCF`, `sbbChain_emit_realizes_abstract_CF` |
| [`MpnAdxCorres`](MpnAdxCorres.lean) | `carryAbs_window`, `adcLimbs_spec`, `mpnAdd_runBlock`, `mpnSub_runBlock`, `mpnAddKernel_runBlock`, `mpnSubKernel_runBlock` |
| [`FieldReduce`](FieldReduce.lean) | `montRedc_spec`, `montRedcNormalized_mem_Ico`; `corresJ_montRedcStep`, `corresJ_montRedc4Block` |
| [`Capstone`](Capstone.lean) | `capstone_word_to_field` |
| [`CapstoneField`](CapstoneField.lean) | `feSub_ascends`, `feSub_word_to_field` |

### Ties between machines and program logics

| Module | Role |
|---|---|
| [`CorresBridge`](CorresBridge.lean) | `regEnv`, `corresJ_forget_to_corres`, `coRefine` |
| [`CorresBridgeArith`](CorresBridgeArith.lean) | `arith_middle_tie_at_dst` |
| [`CorresBridgeArithComplete`](CorresBridgeArithComplete.lean) | `arith_middle_tie_nonTmp`, `arith_middle_tie_seq_nonTmp` |
| [`CorresBridgeMem`](CorresBridgeMem.lean) | `regMemEnv`, `mem_load_middle_tie_at_dst`, `mem_store_middle_tie_at_cell` |
| [`CorresBridgeMemStore`](CorresBridgeMemStore.lean) | `mem_store_middle_tie_full` |
| [`CorresBridgeCtrl`](CorresBridgeCtrl.lean) | `for_middle_tie_gen`, `for_middle_tie_arith` |
| [`CorresMachineTie`](CorresMachineTie.lean) | `SimTie`, `simTie_seq`, `simTie_arith_seq` |
| [`CorresMachineTieFragments`](CorresMachineTieFragments.lean) | `simTie_for_of_body`, `simTie_memLoad` |
| [`JasminComRunBlockTie`](JasminComRunBlockTie.lean) | `JStateInterp`, `jasminBop_eq_machine`, `jasminOp_runBlock_tie` |
| [`JasminComRunBlockSeq`](JasminComRunBlockSeq.lean) | `ArithBlock`, `FreshFor`, `lowerBlock_tie` |
| [`JasminComRunBlockRealloc`](JasminComRunBlockRealloc.lean) | `lowerBlock_tie_realloc`, `mulhiOp_runBlock_tie`, `RegBlock`, `lowerBlockR_tie` |
| [`XrunRunBlockTie`](XrunRunBlockTie.lean) | `xinstrToJ`, `XJFaithful`, `xrun_runBlock_tie`, `corres_of_refines_x86_runBlock`, `add_descent_runBlock` |
| [`CorresHoare`](CorresHoare.lean) | `RunBlockTriple`, `corresJ_iff_triple` |
| [`RunBlockMvcgen`](RunBlockMvcgen.lean) | `runBlockM`, `runBlockM_triple_iff`, `sbb_leaf_triple_mvcgen` |
| [`RunBlockMvcgenMorphism`](RunBlockMvcgenMorphism.lean) | `θ : StateM S → StateT S Option`, `Spec.wp_theta`, `theta_sbb_leaf_triple` |
| [`JStateSepLogic`](JStateSepLogic.lean) | `DependsOn`, `ptsTo`, `writesOnly`, `RunBlockTriple.frame`, `sbb_framed_triple` |

### Descent contracts

| Module | Role |
|---|---|
| [`CorresDescent`](CorresDescent.lean) | `frefines_ret`, `dotFrag_ret` over `Com fieldDialect` |
| [`CorresDescentX86`](CorresDescentX86.lean) | `CorresMPost`, `SRview`, `SRret`, `corres_of_refines_x86`, `binFrag_refines` |
| [`CorresDescentRiscv`](CorresDescentRiscv.lean) | `corres_of_refines_riscv`, `corresR_of_refines` |

### Welds to the emit leg and to sources

| Module | Role |
|---|---|
| [`EmitBridge`](EmitBridge.lean) | `corres_emit_weld`, `keystone_emit`, `keystone_setScalar`, `welding` |
| [`FeSubEndToEnd`](FeSubEndToEnd.lean) | `keystone_NT`, `keystone_emit_NT`; the kernel `feSubC` and its front artifacts; `feSub_corres`, `feSub_endToEnd` |
| [`FeAddEndToEnd`](FeAddEndToEnd.lean) | `feAdd_ascends`, `feAdd_endToEnd`, `feAdd_source_to_bytes_tower` |
| [`KeystoneControl`](KeystoneControl.lean) | `ifClosed_hAgree`, `keystone_if`, `forClosed_hAgree`, `keystone_for` |
| [`CondKernelCapstone`](CondKernelCapstone.lean) | `condKernel_ascends`, `condKernel_bytes_of_emit`, `condFront_translates`, `condBackend_declines` |
| [`ArrStoreEmit`](ArrStoreEmit.lean) | `keystone_arr`, `keystone_emit_arr`, `keystone_arrStore` |
| [`MlkemPolyAddCapstone`](MlkemPolyAddCapstone.lean) | `keystone_fq`, `keystone_emit_fq`, `polyAddCoeff_corres` |
| [`LegWeld`](LegWeld.lean) | `AdeqRun`, `agreeRun`, `LitNorm`, `FrontOut`, `legWeld`, `legWeld_lower` |
| [`LegWeldDemo`](LegWeldDemo.lean) | `demo_source_to_bytes` for `r0 := a0 + b0 - c0` |
| [`FeSubSourceTower`](FeSubSourceTower.lean) | `feSubSrc`, `feSubSrc_refines`, `feSub_source_to_bytes_tower` |
| [`LoopSourceLeaf`](LoopSourceLeaf.lean) | `loopSrc_refines`, `loopSrc_corres`, `loopSrc_source_preimage` |
| [`LoopSourceTower`](LoopSourceTower.lean) | `arrKernel_source_to_rustexec_program`, `loop_keystone_emit`, `loop_forFold_source_vacuous`, `arrStore_executes` |
| [`PipelineWeld`](PipelineWeld.lean) | `haxOutcomeWord`, `haxOutcomeWordCF`, `feSub_raw_source_to_bytes`, `feSub_raw_source_to_bytes'` |
| [`SourceBridge`](SourceBridge.lean) | `program_source_word`, `raw_source_to_bytes_of_program`, `welding_program`, `feSubImp_raw_source_to_bytes` |
| [`FeSubSymbolic`](FeSubSymbolic.lean) | `valEnv`, `corresScalar_jasminDenote`; `feSub_symbolic_frontDenote`, `feSub_symbolic_source_to_jasmin` for `r := a - b` at all inputs |

### Demonstrations

| Module | Role |
|---|---|
| [`Demos/Decide`](Demos/Decide.lean) | the deciding tactics on arithmetic and bitwise kernels |
| [`Demos/Scalar`](Demos/Scalar.lean) | `corres_solve_scalar`, `corres_rotl`, and `qrClosed_frontDenote` |
| [`Demos/X86StraightLine`](Demos/X86StraightLine.lean) | `corres_solve_x86` on carry chains and on `x86Target.compile` output |
| [`Demos/Riscv`](Demos/Riscv.lean) | `corres_solve_rv` on an add with materialised carry |
| [`Demos/LeanSourceX86`](Demos/LeanSourceX86.lean) | descent results at x86 (`add_descent_x86`) and the solver on the same blocks (`add_descent_solver`) |
| [`Demos/LeanSourceRiscv`](Demos/LeanSourceRiscv.lean) | descent results at RV64 (`add_descent_riscv`) |
| [`Demos/HeapAbs`](Demos/HeapAbs.lean) | `feAddN_capstone`, `feAdd4_capstone_field` over `ValueAbs` |
| [`Demos/SourceToBytes`](Demos/SourceToBytes.lean) | `feSub_value`, `feAdd_value` |
| [`Demos/EarlyExit`](Demos/EarlyExit.lean) | a hax search loop with `return` read by `pipeline_exceptProg` |
| [`Demos/Strengthen`](Demos/Strengthen.lean) | the level `Kernel.tsLevel` picks for each demo kernel |

### Loops as functions

| Module | Role |
|---|---|
| [`WhileFun`](WhileFun.lean) | the fuel-free abstract loop `LoopRecIn` / `LoopTerminates` / `loopFun`; `whileFun_sim`, `whileFun_total`; node rules `corresU_whileFun_terminates`, `corresU_whileFun`, `corresU_whileFun_total`; `corresU_while_of_loopRec` |
| [`Demos/WhileFunSum`](Demos/WhileFunSum.lean) | a summation do-while with its exit state `sumExit` proved by induction on the loop variable (`sum_loopRecIn`, `sumLoop_corres`, `sumLoop_total`) |
| [`WhileFunEmit`](WhileFunEmit.lean) | the node rule at `Com jasminDialect`: `corresU_whileFun_jasminDenote`, `corresU_whileFun_jasminDenote_of_fuel`, `corresU_whileFun_jasminDenote_word`, through `transU_to_jasminCom_endToEnd` |
| [`Demos/WhileFunSumJasmin`](Demos/WhileFunSumJasmin.lean) | `sumLoop` through `transU` and the jasmin lowering: `sumLoop_jasminDenote` at every entry `k ≠ 0`, `sumLoop3_jasminDenote` closed at `k = 3` |

For an `RWhileNz` whose result the caller needs as a value, state the abstract guard
`guardA` and step `fb`, prove `LoopRecIn guardA fb n a (exit a)` by induction on the
loop variable, and apply `corresU_whileFun` or `corresU_whileFun_total`; the value of
`loopFun` then follows from `loopFun_eq_of_loopRecIn`. `corresU_while` remains the
rule when only an invariant of the exit state is needed.

### Research probes

These modules are not imported by any module above and are not part of the calculus.
[ASCENT.md](../../../../ASCENT.md) lists what each explores.

| Module | Topic |
|---|---|
| [`GradedMvcgenProbe`](GradedMvcgenProbe.lean) | grades in stock `mvcgen` |
| [`GradedWP`](GradedWP.lean) | a standalone graded predicate transformer |
| [`WriterTMvcgen`](WriterTMvcgen.lean) | an accumulating log as write-only state |
| [`LeakageExceptT`](LeakageExceptT.lean) | leakage as the exception branch |
| [`RelationalProductMvcgen`](RelationalProductMvcgen.lean) | relational triples over a product program |
| [`RelationalExceptTMvcgen`](RelationalExceptTMvcgen.lean) | relational triples over `ExceptT` |
| [`UCLeakageDecomp`](UCLeakageDecomp.lean) | universal composability as a simulator existential; imports `CatCrypt.Crypto.UCMonad` |
| [`XPostShape`](XPostShape.lean) | the extended `PostShape` core |
| [`XMvcgen`](XMvcgen.lean) | tactic `xmvcgen` |
| [`XMvcgenControl`](XMvcgenControl.lean) | control flow for `xmvcgen`; tactic `xmvcgen_ctl` |
| [`XMvcgenReg`](XMvcgenReg.lean) | tactic `xmvcgen!` over the `@[xspec]` set |
| [`XRelatorPMF`](XRelatorPMF.lean) | couplings at `PMF` |
| [`XHeapSoundness`](XHeapSoundness.lean) | a disjoint-heap separation logic and a `StateM` soundness instance |
| [`XMorphismInstance`](XMorphismInstance.lean) | a base-change weakest-precondition morphism |
| [`XDijkstraAll`](XDijkstraAll.lean) | aggregator of the `X*` framework |
| [`XAdvantageHybrid`](XAdvantageHybrid.lean) | tactics `advmvcgen`, `advmvcgen_dep`; imports `CatCrypt.Crypto.MultiQueryPRF` |

## Choosing a tactic

| Goal | Tactic | Notes |
|---|---|---|
| `Corres` at `asemW c`, `asemWExpr c` or `asemWBV c` for a small concrete kernel | `ascend!`, `ascend_expr!`, `ascend_bitwise!`, `ascend_unified!` | membership by one `decide` over the whole kernel |
| the same goal for a large or generated kernel (`def`-bound, built by `List.foldr` or `List.map`) | `ascend_meta` | walks the term; `decide` only on single names and literals |
| the same goal when every terminal is a literal `RScalarSet` | `ascend`, `ascend_expr`, `ascend_bitwise` | constructor search; leaves the `IsArithClean` / `IsWordClean` side conditions of expression terminals open |
| `Corres SRwordBV (fun _ => True) fold c` for a straight-line `RSeq` / `RScalarSetExpr` kernel mixing arithmetic and bitwise nodes | `corres_solve_scalar` | synthesises the `wordStep` fold; the only leaf is `corres_setExprWord` |
| a kernel with loops, conditionals, range side conditions or unsupported nodes | `ascendG_sound`, `ascendG_sound_scalar`, `tsLowCT_sound` (terms) | inspect `(ascendG fuel c).1` first; an `unsupported` guard makes the precondition unsatisfiable |
| a kernel with `RArrLoad`, `RArrStore` or `RLimbStore` | `ascendGL_sound_scalar`, `tsLowCTL_sound_scalar` over the array layout (terms) | pass the layout listing each array with its length; `arrSelK` is the template |
| `CorresJ SRcarry` or `CorresJ SRcarry2` over a carry-family `JInstr` block | `corres_solve` | composes the `@[corres]` leaves by `corresJ_cons` |
| `CorresJ SRx` over value instructions, given as `JInstr`s, as `xs.map xinstrToJ`, or as `x86Target.compile p` | `corres_solve_x86` | normalises the block, then `corres_solve` |
| `CorresR SRr` over an `RInst64` block | `corres_solve_rv` | composes the `@[corresR]` leaves |
| carry-out equalities and Montgomery top-carry or range goals | `mont_bound` | linear goals over powers of `2^64` |

A solver closes the goal only when the stated abstract transition is definitionally
equal to the synthesised fold; state the transition as that fold, or leave it to be
synthesised and rewrite afterwards.

## Adding a kernel

### A closed straight-line word kernel with a source

Copy [`LegWeldDemo`](LegWeldDemo.lean). The data are:

1. the source `src : RustSrc` and `src.ifFree = true` by `decide`;
2. the front's term `c` with `LitNorm (lower src) c`, or `c := lower src` with
   `LitNorm.refl`;
3. `∃ rs', AdeqRun c rs rs'`, built from `AdeqRun.rScalarSet`, `AdeqRun.lit` and
   `AdeqRun.rScalarSetExpr` with `srcClean` and the range condition at the state read;
4. `readsOK (fun _ => False) c` and `afterB (fun _ => False) c name`, usually by `simp`;
5. `FrontOut.ofSome c name h₁ h₂ h₃ h₄ h₅` from the five success facts of the front,
   by `rfl`, with `decide` for the slot type;
6. `Corres SRwordNT P fa c`, by `corres_seq` over `corres_setScalar_NT` and
   `corres_setExpr`, or by `ascend_meta` at `asemWExpr c`.

`legWeld_lower` then gives the equation for the kernel's `Com jasminDialect` program.
The kernel has no inputs; state the theorem as a result about that kernel.

### An x86 or RV64 block

State `CorresJ SR (fun _ => True) fold block` and close it with `corres_solve_x86` or
`corres_solve`. A new instruction needs one lemma with conclusion
`CorresJ SR (fun _ => True) step [i]` tagged `@[corres]`, in a module that imports
`CorresAttr`; `corresJ_of_regs` states such a leaf once for any instruction whose
register effect is one write. For RV64, tag the leaf `@[corresR]` (declared in
`CorresRiscvLeaves`, populated in `CorresRiscvSolver`) and use `corresR_of_set`. A label
attribute is visible only in modules that import the module carrying the tagged lemma.

To relate a block produced by the descent to an ascent result, use
`corres_of_refines_x86_runBlock` (register-only relations, shift immediates below 64)
or `corresR_of_refines`.

### Source coverage

- An `if`-free `RustSrc` program: `RustSubsetToLowCT.lowerRefines`, as in `legWeld_lower`.
- A hax program accepted by the scope checker `simScope`:
  `haxToLowCT_simulates_program`. Its image contains no `RScalarSetExpr` from
  arithmetic, and its `FullSimPreconds.leafScalar` excludes scalar-valued builtins.
- A hax program whose builtins return scalars: `haxToLowCT_simulates_programT`
  (`CatCrypt/Crypto/Hax/HaxToLowCTSim_ProgramTower.lean`) under `LeafCallAgreesArgs`
  and `condsScalar`, and, with literal call arguments stored in tower slots by
  `litTower`, `haxToLowCT_simulates_programL`
  (`CatCrypt/Crypto/Hax/HaxToLowCTSim_ProgramLit.lean`) under `simScopeL` and
  `LitStoreAgrees`. Both require a builtin table implementing neither `index` nor
  `array_update`, and both end at `RustExec`.
- A hax function with early returns, through the exit-flag lowering:
  `haxToLowCTFn_simulates` (`CatCrypt/Crypto/Hax/HaxToLowCTSim_Exit.lean`), stated over
  `Hax.denote'`.
- hax-lean's `pipeline`: `pipeline_correct`, `pipeline_correct'` and
  `pipeline_full_correct`, used in `PipelineWeld` and `Exit`.

State call-side side conditions per program, as `haxToLowCT_simulates_program`
and its corollary `haxToLowCT_simulates_full` (`CatCrypt/Crypto/Hax/HaxToLowCTSim_Full.lean`)
do with `simScope`, `ScopeBound` and `NamesFresh`. The same conditions quantified
over every name and state are refuted in `CatCrypt/Crypto/Hax/HaxToLowCTSim_Program.lean`.

## Editing in this directory

- A module docstring says what the module proves and lists its results under
  `## Main results`. Docstrings and comments state what a declaration is, without
  status, history or evaluation. Run `bash scripts/lint-lean-prose.sh <files>` on the
  files you change; the pre-commit hook in `.githooks` runs it on staged files. In prose, call the
  `keystone_*` declarations emit welds.
- After adding or removing a module, run `bash scripts/gen-module-globs.sh` to rewrite
  the module list in `lakefile.lean`, and
  `ROT_GUARD_WRITE_MANIFEST=1 bash scripts/rot-guard-build.sh --check` to regenerate the
  build roots in `scripts/rot-guard/build-roots.txt`. The pre-commit hook runs the
  manifest check and `scripts/module-doc-ratchet.sh` on added modules.
- Pin the axioms of a headline theorem with `#guard_msgs in #print axioms`, as the
  demonstrations, `AscendMeta` and `XrunRunBlockTie` do; a bare `#print axioms` prints
  on every build and checks nothing.
- `decide` and `rfl` over a concrete kernel belong in a proof only when they are fast;
  for a large kernel use `ascend_meta`, which does not reduce a checker over the
  compound term.
- Modules outside this directory import `ExprLeaf`
  (`X86Backend/MpnMul1FrontDenote`), `EcMultiLimbMul`
  (`Secp256k1FeMulBrickProduct`, `X86Backend/EncodedBlockCorres`), `EcMultiLimbEmit`
  (`X86Backend/RunBlockLsemAgreeCondSub`) and `FieldReduce`
  (`X86Backend/MontRedc4RunBlockFused`). A statement change in those modules affects
  them.
- Keep exploratory modules out of the import graph of the calculus, and add them to the
  probe tables here and in [ASCENT.md](../../../../ASCENT.md).
- When a docstring describes a result, name the semantics it is stated over
  (`semScalar`, `semU`, `runBlock`, `runRBlock64`, `Com catCryptDialect`,
  `Com jasminDialect`), and say which hypotheses remain (for example `hEmit` or
  `hBridge`).
