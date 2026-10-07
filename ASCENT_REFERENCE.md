# The ascent: reference

This file collects the detailed material behind [ASCENT.md](ASCENT.md): the results at
the source and leaf boundaries, the layers of the calculus with their declarations,
the loop rules, two worked paths traced step by step, the instruction-set judgement on
compiled programs with their callee specifications, the join of the source readings
with the compiled bytes, the closed capstones, the simulations from hax source, the
total abstraction, and the results on machine states and on hand-written assembly.
Paths are relative to the repository root.

## Results at the source and leaf boundaries

The following statements concern the source and leaf boundaries of the ascent; the
section named in each item gives their hypotheses.

- Data-dependent loops: `corresU_whileFun` relates a terminating `RWhileNz` run to the
  exit state `loopFun` of the abstract loop, and `corresU_whileFun_total` gives the run
  when the trip count is below the fuel; `corresU_whileFun_jasminDenote` carries the
  exit value through the front's unified descent `transU` and the jasmin lowering to
  the `Com jasminDialect` of the node, unrolled at the entry environment's trip count
  ([Data-dependent loops as functions](#data-dependent-loops-as-functions)).
- Leaf calls: `ascendGLL_sound` abstracts `RCall`, `RCallDstThreaded`, `RTupleLoad`,
  `RCallSwap`, `RCloneCall` and `RCallN`, `RSelect` with a layout array among its
  operands or as its destination, `RArrLoadLit` from a source that is not a
  `TArr _ .TU64` layout array, and `RArrStoreLit` that is not a word write to a
  `TArr _ .TU64` array, to abstract word leaves on `u64` destinations and abstract array
  leaves on layout-array destinations at `semUL ls fuel`;
  `semScalarLToJasminCom_denote_eq` carries `semScalarL ls` through the front and the
  jasmin lowering for every oracle pair related by `LeafTransport`
  ([Leaf calls at a leaf oracle](#leaf-calls-at-a-leaf-oracle)).
- hax source: `haxToLowCT_simulates_programT` and `haxToLowCT_simulates_programL`
  simulate programs whose builtins return scalars, the latter with literal call
  arguments stored in tower slots; `haxToLowCT_simulates_programA` adds the array
  builtins `index` and `array_update`, `haxToLowCT_simulates_programF` counted loops
  (`forFold` over literal bounds, read as the `forLoop` of `forToLoop`), and
  `haxToLowCT_simulates_programW` reverse loops (`forFoldRev` over literal bounds),
  runtime-bound loops (`forFold` from a literal to a variable bound, lowered to
  `RForRuntime`) and data-dependent loops (`whileFold` on a scalar guard, lowered to
  `RWhileNz`) under the checker `simScopeW` and the environment invariant `ScalarInv`;
  each concludes a `RustExec` run of the lowered program
  ([Simulations from hax source](#simulations-from-hax-source)).
- Jasmin mirror: `mulhiLoop_mirror_runBlock` relates a `psem.v` mirror derivation of a
  loop calling a `MULX` function to the `runBlock` run of the unrolled `MULX` loop.

## Layers

Each row names the modules of a layer and the declarations that carry it. Paths are
relative to `CatCrypt/Crypto/SecureCompilation/Ascent/`.

| Layer | Modules | Main declarations |
|---|---|---|
| Correspondence relations | `Corres`, `WhileTop`, `While`, `RunBlockCorres`, `CorresRiscv`, `CorresGeneric`, `Exit` | `Corres` over `semScalar` with `corres_seq`, `corres_weaken`; `CorresU` over `semU`; `CorresWhile`; `CorresJ` over `runBlock` with `corresJ_append`, `corresJ_loop`; `CorresR` over `runRBlock64`; `CorresM`, the machine-generic form, with `corres_eq_corresM`, `corresJ_eq_corresM`, `corresR_eq_corresM`; `CorresE`, `CorresUE` for bodies that throw |
| Value abstraction | `Corres`, `ExprLeaf`, `HeapAbs`, `StoreRefinement`, `MultiLimb`, `MlkemFieldLeaf`, `Width32Leaf`, `Phases` | `wEnc : BitVec 64 → ZMod 2^64` and the ParamTransfer squares `wEncAdd`, `wEncSub`, `wEncMul`; `SRword`, `SRwordNT`, `SRwordBV`; `ValueAbs` with `SRof`, `SRcarryOf` and the instance theorems `srwordNT_iff_srof`, `srcarry_iff_srcarryOf`; `fqEnc` and `CorresH`; `corres_WA`, `AbsProg` |
| Leaves over `LowCT` | `Corres`, `ExprLeaf`, `CorresScalar`, `BitwiseOrNot`, `RotateLeaf`, `SelectLeaf`, `ArrStoreLeaf`, `ArrLoadLeaf`, `MlkemFieldLeaf` | `corres_setScalar`, `corres_setScalar_NT`, `corres_setExpr` (arithmetic into `ZMod 2^64`), `corres_setExprBitwise`, `corres_setExprWord` (the `srcClean` word algebra over `BitVec 64`), `corres_setExprOr`, `corres_rotl`, `corres_ctSelect`, `corres_arrStore`, `corres_arrLoad`, `corres_setExpr_fqAdd` |
| Control and early exit | `Control`, `While`, `WhileTop`, `WhileFun`, `WhileFunEmit`, `MlkemPolyFoldCorres`, `Exit` | `corres_for`, `corres_if`, `corres_for_indexed`, `polyAdd_fold_corres`, `corres_while`, `corresU_while`, `corresU_whileFun`, `corresU_whileFun_total`, `corresU_whileFun_jasminDenote`, `pipeline_exceptProg`, `whileExit_sim`, `corresU_while_exit` |
| Automation and total abstraction | `Ascend`, `AscendDecide`, `AscendMeta`, `Guards`, `GuardsLeaf`, `Strengthen`, `CorresSolver`, `CorresAttr`, `CorresX86Solver`, `CorresRiscvLeaves`, `CorresRiscvSolver`, `CorresScalar`, `MontBounds`, `InvariantSchemas` | `ascend_sound`, `ascend_expr_sound`, `ascend_bitwise_sound` and the tactics `ascend!`, `ascend_meta`; `ascendG`, `ascendG_sound`; `ascendGLL`, `ascendGLL_sound`; `tsLowCT_sound`, `tsHax_sound`, `Kernel.tsLevel`; the symbolic-execution tactics `corres_sym`, `corres_sym_rv`, `corres_sym_scalar` and the macro solvers `corres_solve`, `corres_solve_x86`, `corres_solve_rv`, `corres_solve_scalar`; `mont_bound` |
| Machine-level leaves and value results | `RunBlockCorres`, `EcMultiLimbCapstone`, `EcMultiLimbMul`, `MpnAdxCorres`, `FieldReduce`, `CorresX86Solver`, `CorresRiscvLeaves`, `Capstone`, `CapstoneField`, `EcMultiLimbEmit` | `corresJ_sbb`, `corresJ_adc`, `srcarryLimbs_recompose`; `sbbLimbs_spec`, `corresJ_sbbChain`; `mulLimbs_spec`, `corresJ_adxBlock`; `mpnAdd_runBlock`, `mpnSub_runBlock`; `montRedc_spec`, `corresJ_montRedc4Block`; `corresJ_movX` … `corresJ_mulxX`; `corresR_add` … `corresR_slli`; `sbbChain_emit_realizes_abstract_CF` |
| Ties between machines, and program logics | `CorresBridge`, `CorresBridgeArith`, `CorresBridgeArithComplete`, `CorresBridgeMem`, `CorresBridgeMemStore`, `CorresBridgeCtrl`, `CorresMachineTie`, `CorresMachineTieFragments`, `JasminComRunBlockTie`, `JasminComRunBlockSeq`, `JasminComRunBlockRealloc`, `JasminMirrorTie`, `XrunRunBlockTie`, `CorresHoare`, `RunBlockMvcgen`, `RunBlockMvcgenMorphism`, `JStateSepLogic` | `corresJ_forget_to_corres`, `coRefine`; `arith_middle_tie_seq_nonTmp`, `mem_store_middle_tie_full`, `for_middle_tie_gen`; `SimTie`, `simTie_seq`; `lowerBlock_tie`, `lowerBlockR_tie`; `forFold_eq_loopStep`, `mulhiLoop_mirror_runBlock`; `xrun_runBlock_tie`; `corresJ_iff_triple`, `runBlockM_triple_iff`, `Spec.wp_theta`, `RunBlockTriple.frame` |
| Descent contracts in the ascent's shape | `CorresDescent`, `CorresDescentX86`, `CorresDescentRiscv`, `XrunRunBlockTie` | `frefines_ret`; `CorresMPost`, `corres_of_refines_x86`; `corresR_of_refines`; `corres_of_refines_x86_runBlock` |
| Instruction-set judgement, relocation and callees | `CorresIsa`, `CorresIsaX86`, `CorresIsaCfg`, `CorresIsaCall`, `CorresIsaNode`, `CorresIsaRet`, `CorresIsaReloc`, `CorresIsaRelocX86`, `CorresIsaStackFrame`, `ImageSpFree`, `ImageSpFreeCell` | `CorresIsa`, `CorresIsaRun`; `corresIsa_of_labels_floyd`; `IsaCall.ProcSpec`; `corresIsa_of_node_halts_fuel`; `ExitFrame`, `procSpec_snoc_ret_of_corresIsa`; `steps_relocate`, `procSpec_labelled_of_corresIsa`; `x86_stepRelocates`; `x86_step_spFrame`, `x86_procSpec_of_body_judgement`, `x86_procSpec_of_image_judgement`; `virtImg_spFreeBodyB`, `virtImg_noCall`, `cellImage_spFreeBodyB`, `cellImage_noCall` |
| Welds to the emit leg and to sources | `EmitBridge`, `FeSubEndToEnd`, `FeAddEndToEnd`, `KeystoneControl`, `CondKernelCapstone`, `ArrStoreEmit`, `MlkemPolyAddCapstone`, `LegWeld`, `LegWeldDemo`, `FeSubSourceTower`, `LoopSourceLeaf`, `LoopSourceTower`, `PipelineWeld`, `SourceBridge`, `CorresScalar` | `keystone_emit`, `keystone_emit_NT`; `legWeld`, `legWeld_lower`; `feSub_source_to_bytes_tower`, `feAdd_source_to_bytes_tower`; `feSub_raw_source_to_bytes`, `feSubImp_raw_source_to_bytes`; `corresScalar_frontDenote_two`; `corresScalar_jasminDenote`, `feSub_symbolic_source_to_jasmin` (`FeSubSymbolic`) |
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
| [Demos/X86StraightLine](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/X86StraightLine.lean) | `corres_sym` over carry chains and over `x86Target.compile` output | `sbb3_refines`, `mulx_adcx_refines`, `compiled_refines` |
| [Demos/Riscv](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Riscv.lean) | `corres_solve_rv` over an add with materialised carry | `addCarry_ascends` |
| [Demos/LeanSourceX86](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/LeanSourceX86.lean) | a Lean function through the descent to x86, and the same block through the solver | `add_descent_x86`, `add_descent_solver` |
| [Demos/LeanSourceRiscv](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/LeanSourceRiscv.lean) | the RV64 twin | `add_descent_riscv` |
| [Demos/HeapAbs](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/HeapAbs.lean) | an `n`-limb add over the generic value abstraction | `feAddN_capstone`, `feAdd4_capstone_field` |
| [Demos/SourceToBytes](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/SourceToBytes.lean) | the closed capstones at their values | `feSub_value`, `feAdd_value` |
| [Demos/EarlyExit](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/EarlyExit.lean) | a search loop with `return`, an `ImpExpr` term written in Lean in the shape of an extraction, read as an exception program | `searchU_except_found`, `searchU_word_found` |
| [Demos/Strengthen](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Strengthen.lean) | the result monad chosen per kernel | `feSubC_ts_refines`, `qrFrag_ts_refines`, `searchU_ts_refines` |
| [Demos/WhileFunSumJasmin](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/WhileFunSumJasmin.lean) | the summation do-while through `transU` and the jasmin lowering, at every entry and closed at `k = 3` | `sumLoop_jasminDenote`, `sumLoop3_jasminDenote` |

## Data-dependent loops as functions

`corresU_while` (`WhileTop.lean`) relates a terminating run of `.RWhileNz name body`
to some abstract state that satisfies the invariant. The rule in
[WhileFun.lean](CatCrypt/Crypto/SecureCompilation/Ascent/WhileFun.lean) relates it to
the value of one abstract function, in the manner of Myreen's decompilation of loops
into tail-recursive functions (TR-765 §2.7) as adapted to Lean 4 by
[dhsorens/riscv-decomp](https://github.com/dhsorens/riscv-decomp).

The abstract loop is a guard `guardA : A → Bool` and a step `fb : A → A`.
`LoopRecIn guardA fb n a b` is the inductive predicate "the top-tested loop from `a`
exits in `b` after `n` trips". Its least fixpoint is termination
(`LoopTerminates guardA fb a`), and the trip count is an index of the derivation, so
the abstract side has no fuel. `loopFun guardA fb a h` is the exit state of a
terminating loop and `loopTrips` its trip count; `LoopRecIn.det`,
`loopFun_of_guard_false`, `loopFun_of_guard_true`, `LoopTerminates.induction` and
`loopTerminates_of_measure` are the determinism, unfolding, induction and measure
lemmas.

`RWhileNz` is a do-while, so the abstract function at entry `a` is
`loopFun guardA fb (fb a)`. The node rules take the body correspondence
`CorresU fuel SR P fb body`, the invariant `∀ a, P a → P (fb a)` and the guard
agreement `SR env a → P a → guardNz name env = guardA a`:

* `corresU_whileFun_terminates`: a terminating run proves
  `LoopTerminates guardA fb (fb a)`;
* `corresU_whileFun`: a terminating run lands in a state related to
  `loopFun guardA fb (fb a) h`, for every termination proof `h`;
* `corresU_whileFun_total`: when `loopTrips guardA fb (fb a) h < fuel`, the run
  terminates and lands in such a state.

A caller proves termination by the same induction that computes the loop's value.
`corresU_while_of_loopRec` derives the conclusion of `corresU_while` from the
underlying simulation `whileFun_sim`, taking as abstract state the pair of the
concrete environment and the abstract state.

[Demos/WhileFunSum](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/WhileFunSum.lean)
applies the rule to `do { acc := acc + k; k := k - 1 } while (k != 0)` over
`SRwordBV`. `sum_loopRecIn` proves by induction on the value of `k` that the abstract
loop exits in `sumExit`, where `k` is `0` and `acc` has grown by `k (k + 1) / 2`;
`sumLoop_corres` and `sumLoop_total` are the partial and total node statements, and
`sumLoop_corres_of_ne_zero` states the result for entry states with `k ≠ 0`.

[WhileFunEmit.lean](CatCrypt/Crypto/SecureCompilation/Ascent/WhileFunEmit.lean) carries
the exit value to the front's jasmin program. The front compiles the node through the
unified descent `transU fuel vm env` (`Dialects/TranslateDialectUnifiedDenote.lean`),
which unrolls the loop to the trip count of the run from the entry environment `env`,
and `transU_to_jasminCom_endToEnd` (`VIR/RustToJasminComWhile.lean`) carries a tracked
output slot of the resulting `Com catCryptDialect` through `cryptoDialectToJasminCom`.
`corresU_whileFun_jasminDenote` composes it with `corresU_whileFun`: under the node
rule's hypotheses, an entry environment consistent with the entry valuation `V`, the
front's output at that environment with the output name resolved to a word slot, and
the jasmin lowering `jcom` of the continuation closed at that slot,
`jcom.denote (ctMapValD V)` is the projection of `loopFun guardA fb (fb a)` to the
output name. `corresU_whileFun_jasminDenote_of_fuel` replaces the run by a trip count
below the fuel, and `corresU_whileFun_jasminDenote_word` is the form over `SRwordBV`
with the entry environment `valEnv vm V`.
[Demos/WhileFunSumJasmin](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/WhileFunSumJasmin.lean)
applies it to `sumLoop`: `sumLoop_jasminDenote` states that for every entry `k ≠ 0`,
`acc`, the jasmin program returning `acc` denotes `acc + k (k + 1) / 2`, and
`sumLoop3_jasminDenote` closes the front's output at `k = 3`, `acc = 0`, where the
program denotes `6`.

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

## A worked path with symbolic inputs: `feSub_symbolic_source_to_jasmin`

The kernel is `feSubSymC`, `r := a - b`, with `a` and `b` read from the entry
valuation. The theorem, in
[FeSubSymbolic.lean](CatCrypt/Crypto/SecureCompilation/Ascent/FeSubSymbolic.lean), is

```lean
theorem feSub_symbolic_source_to_jasmin (a b : BitVec 64) :
    feSubSymJcom.denote (ctMapValD (valAB a b)) = ctTransTy (a - b)
```

where `valAB a b` is the two-word `catCryptDialect` valuation holding `a` and `b`,
`ctMapValD_valAB` states that its transport holds `ctTransTy a` and `ctTransTy b` at
the same slots, and `feSubSymJcom` is `cryptoDialectToJasminCom` applied to the front's
translation of `feSubSymC` at the entry map `vmAB` (`a` at the first slot, `b` at the
second), closed at `r`.

1. Ascent. `feSubSym_corres : Corres SRwordBV (fun _ => True) _ feSubSymC` is closed by
   `corres_solve_scalar`. The abstract step sets `r` to the wrapping difference, so no
   range condition appears.
2. Weld at a nonempty valuation. `corresScalar_jasminDenote` is `corresScalar_frontDenote`
   at the entry environment `valEnv vm V`, the one the valuation induces through the map,
   composed with `cryptoDialectToJasminCom_denote_eq'`. `ConsistentS vm V (valEnv vm V)`
   holds by definition. `SRwordBV` constrains every non-temp name, so the weld asks that
   `vm` resolve every non-temp name to a word slot carrying the abstract value.
3. Entry map. `vmSubAll` sends `b` to the second slot and every other name to the first,
   which satisfies that condition (`vmSubAll_resolves`). The front produces the same
   `Com catCryptDialect` program at `vmSubAll` as at `vmAB` (`comSubAll_eq`, by `rfl`),
   so the conclusion is stated at `vmAB`.
4. Lowering. `cryptoDialectToJasminCom_denote_eq'` and
   `semScalarToJasminCom_denote_eq` are stated at an arbitrary entry map and valuation;
   their `_topLevel` specialisations are the instances at the empty valuation.

`feSub_symbolic_frontDenote` is the same result one lowering up,
`feSubSymCom.denote (valAB a b) = a - b`. The source of this path is the `LowCT` term
`feSubSymC`.

## Compiled programs at the instruction set

`CorresIsa isa P SR Pre fa fuel`
([CorresIsa.lean](CatCrypt/Crypto/SecureCompilation/Ascent/CorresIsa.lean)) is the
correspondence at the fuelled interpreter `Isa.lsemFuelMemF` of an instruction set, and
`CorresIsaRun` is the form with the fuel chosen per initial state.
[ASCENT_OVERVIEW_LEAN.md](ASCENT_OVERVIEW_LEAN.md) lists the generic rules of the
judgement. This section records its instances at the programs the hax compiler emits and
the callee specifications derived from them. A module cited as `Haxc/…` is in the CatCrypt
development repository, under `CatCrypt/Crypto/SecureCompilation/Haxc/`; every other path
is in this package. Every statement of this section is over `x86Isa`.

### Arms of the compile gate

Each theorem below holds for every program its gate accepts; the gate is its hypothesis
on the program.

| Arm | Gate | Program in the square | Theorems | Module |
|---|---|---|---|---|
| runtime-count loop over an array | `v1LoopB` | the certified loop node | `v1Loop_corresIsa` | `Haxc/LoopCorresIsa.lean` |
| the same | `v1LoopB` | the image of the printed body | `v1Loop_image_corresIsa` | `Haxc/ExportedBodyCorresIsa.lean` |
| runtime-count loop with carry chains and cells | `v1LoopWB` | the certified loop node | `carriedLoop_corresIsa`, `carriedLoop_corresIsaRun` | `Haxc/LoopWideCorresIsa.lean` |
| the same | `v1LoopWB` | the image of the cell body of the printed body | `carriedLoop_image_corresIsa`, `carriedLoop_image_corresIsaRun` | `Haxc/LoopWideCorresIsa.lean` |
| straight-line programs | the four straight arms of `jGateB` | the typed chain of the source | `jGate_straight_corresIsa`, `compileJ_straight_corresIsa` | `Haxc/StraightCorresIsa.lean` |
| straight-line programs returning a register, an array, or an array through cells | `v1StraightRB`, `straightArrB`, `straightCellB` | the image of the printed body | `v1StraightR_image_corresIsa`, `straightArr_image_corresIsa`, `straightCell_image_corresIsa` | `Haxc/ExportedBodyCorresIsa.lean` |

The gate `v1LoopWB` has the conditions of `v1LoopB` with the route check
`CellFoldLReg.routeBW` in place of `ImageAddrRoute.routeB`: the constant-index array
accesses of the printed body are cell accesses and its arithmetic uses carry chains. The
certified node, its entry relation, precondition, specification and fuel are those of a
loop accepted by `v1LoopB`. `carriedRoute_image_run_fuel` is the run statement behind the
image form: under `routeBW`, a halting run of the node at fuel `f` is matched by a run of
the image of the cell body that halts in one state at every fuel from `carriedRouteFuel`
of `f` on, with the output array of the node held in the cell names of its renamed name.
The fixed-fuel forms are at `nodeFuel` and `carriedLoopImageFuel`, each at a bound `N` on
the count.

In every row the image is the printed body up to its closing return, where a run of
`x86Isa` halts; the next subsection treats the return.
[ASCENT_OVERVIEW_LEAN.md](ASCENT_OVERVIEW_LEAN.md) describes the squares of the rows for
`v1LoopB` and the straight arms.

### Compiled bodies as callees

An image judgement of the previous subsection starts from the entry state of the image
route, whose memory is zero, at the counter `0` of a program that consists of the body
alone. A callee is entered by a call step, which writes
the stack pointer and the memory cell it addresses, at a label inside a larger program,
and ends in a return. The following modules of this package derive the procedure
specification `IsaCall.ProcSpec` at the instruction set with calls `isa.withCalls` from a
judgement on the body.

| Module | Declarations | Content |
|---|---|---|
| [CorresIsaRet](CatCrypt/Crypto/SecureCompilation/Ascent/CorresIsaRet.lean) | `RetAddrAt`, `ExitFrame`, `procSpec_snoc_ret_of_corresIsa` | the state of a callee entered by a call; the exit contract of the run of a body (the end state is at the counter `B.length`, with a frame relation and the return address contract `IsaCall.RetFrame`); the specification of `B ++ [Lret]` from the correspondence of `B` and its exit contract |
| [CorresIsaReloc](CatCrypt/Crypto/SecureCompilation/Ascent/CorresIsaReloc.lean) | `shiftPc`, `LabelsFresh`, `StepRelocates`, `steps_relocate`, `procSpec_labelled_of_corresIsa` | a segment of `B` from `s` to `t` is a segment of `pre ++ B ++ post` with the same number of steps between the states with the counter advanced by `pre.length`, when no label declared in `B` is declared in `pre` and the non-control steps commute with the shift; the specification of a body placed after a label and followed by its return |
| [CorresIsaRelocX86](CatCrypt/Crypto/SecureCompilation/Ascent/CorresIsaRelocX86.lean) | `evalInstrPMemF_goto`, `x86_stepRelocates`, `x86_steps_relocate` | `StepRelocates x86Isa fn pre B post` for every function name, `pre`, `B` and `post`: the x86 step of a non-control instruction reads neither the counter nor the program |
| [CorresIsaStackFrame](CatCrypt/Crypto/SecureCompilation/Ascent/CorresIsaStackFrame.lean) | `spFrame`, `SpFree`, `x86_step_spFrame`, `x86_lsemFuelMemF_atPc_length`, `x86_exitFrame_of_spFree`, `x86_procSpec_of_body_judgement`, `x86_procSpec_of_image_judgement`, `spRel_callEntry` | the step of a body no instruction of which names the stack pointer commutes with a write of the stack pointer and its cell; a run from a counter within the body halts at the counter after its last instruction; the exit contract and the specification of a labelled body followed by a return, with "no call" and "does not name `RSP`" as Boolean checks on the body; the entry relation of the specification holds after a call step |
| [ImageSpFree](CatCrypt/Crypto/SecureCompilation/Ascent/ImageSpFree.lean), [ImageSpFreeCell](CatCrypt/Crypto/SecureCompilation/Ascent/ImageSpFreeCell.lean) | `virtImg_spFreeBodyB`, `virtImg_noCall`, `synthRen_target_mem`; `cellImage_spFreeBodyB`, `cellImage_noCall` | the two Boolean checks hold of the image of every covered printed body in the image class, at a slot map whose array names are no stack names, and of the image of the cell body of every covered printed body with carry chains |

The instances at the compile gate are in the development repository.

* `Haxc/ExportedProcSpec.lean` applies `x86_procSpec_of_image_judgement` to the five
  image judgements: `loopImage_procSpec`, `carriedLoopImage_procSpec`,
  `straightRegImage_procSpec`, `straightArrImage_procSpec` and `cellImage_procSpec`, each
  with the two Boolean checks on the image as hypotheses.
* `Haxc/ExportedProcSpecGated.lean` derives the two checks from the route check that each
  gate contains: `gatedLoop_callee_procSpec` (`v1LoopB`),
  `gatedStraightReg_callee_procSpec` (`v1StraightRB`), `gatedStraightArr_callee_procSpec`
  (`straightArrB`), `gatedCarriedLoop_callee_procSpec` (`v1LoopWB`) and
  `gatedCell_callee_procSpec` (`straightCellB`). For every program one of these five
  gates accepts, its exported image placed after a label and followed by a return
  satisfies a procedure specification
  over `x86Isa.withCalls`, and the hypotheses are the gate and `LabelsFresh` for the
  prefix with the label. The entry relation is the two-phase relation of the image
  judgement up to the stack pointer and its cell (`spRel`), at the offset of the image in
  the program (`relocRel`).
* `Haxc/ExportedProcSpecInstances.lean` states the specification for the results of the
  compiler under its route gates, with the instances `mpn_and_n_image_procSpec` (a
  runtime-count loop) and `ltu_image_procSpec` (a straight-line comparison). Each takes
  the compile equation and the gate equation as hypotheses; the gate equations are
  Boolean evaluations of the compiler on a closed program, checked by evaluation.

## Source readings joined to compiled bytes

The hax compiler's theorem `haxc_correct_auto` (development repository) relates the bytes
`compileA` returns to a run of the source reading of the typed extraction under the
compiler's builtin table `hax64WExit`. An ascent result `FnCorres bi e entry G f`, or a
total `Std.Do` triple of the reading `toRustMS appRt` of the body in `RustM`, is stated
under another reading of the calls. The results of this section carry such a result to
the compiled bytes.

In this package:

* [HaxAscent/Ascent/TableCongr.lean](HaxAscent/Ascent/TableCongr.lean). Let `bi'` return
  the value `bi` returns wherever `bi` returns one on a name accepted by `ok`, and let
  every call of `e` be to such a name (`callsOK ok e`). `denote'_eq_of_tableLE`: a run of
  `e` under `bi` that does not end in an error is the run under `bi'`, outcome and
  environment, at the same fuel. `denote'_mono`: a value run under `bi` is the same value
  run under `bi'`. `fnCorres_val_of_sub`: a function correspondence under `bi'` fixes
  every value a run under `bi` returns, at any fuel.
* [HaxAscent/RustSemantics/ToRustMSCongr.lean](HaxAscent/RustSemantics/ToRustMSCongr.lean).
  `toRustMS_congr`: two readings of the calls that are the same function at every
  accepted name give the same reading of an expression whose calls are to accepted
  names, from every environment.

In the development repository:

* `CatCrypt/Crypto/Hax/Hax64WReading.lean`. `app64` is the restriction of `appRt` to the
  names of `hax64Reads`, and `app64_ok` states `AppOk hax64WExit app64`: at those names
  every value the reading returns is the value of the table.
  `fnCorres_hax64WExit_of_triple`: for a program whose calls are to names of
  `hax64Reads`, a total triple of the reading under `appRt` gives the function
  correspondence at `hax64WExit`.
* `Haxc/BytesOfFnCorres.lean`. `bytes_of_fnCorres`: for a typed extraction, a layout and
  a Lean function `f`, when the table of the ascent result is `hax64WExit` on the called
  names and the statement spine of the body binds no closure, the bytes decode to a
  program that halts from an entry state laid out by the layout, and the layout reads
  back `enc (f a)` from the exit state. `bytes_of_fnCorres_of_tableLE` has the same
  conclusion for a table that includes `hax64WExit` on the called names, and takes a
  value run of the source reading under `hax64WExit` as a hypothesis.
  `bytes_of_toRustMS_triple` takes the specification as a triple of the reading, for a
  body whose calls are to names of `hax64Reads`, and has no hypothesis on a source run.
  `bytes_ct_of_fnCorres` and `bytes_ct_of_toRustMS_triple` add constant time: one
  decoding of the bytes halts with the encoding of `f a` and has equal leakage traces on
  any two entry states that satisfy the regions of the layout and agree on the public
  data, under a secrecy record that the source constant-time check accepts.
* `Haxc/CndCopyDemo.lean`, with `CatCrypt/Crypto/Mpn/CndCopySpec.lean` and
  `CatCrypt/Crypto/Mpn/CndCopyReading.lean`, applies the route to the conditional copy
  `mpn_cnd_copy_n`. `cndCopy_bytes_spec_ct`: from every entry state of the layout the
  decoded bytes compute the closed form `cndCopySpec`, with equal leakage traces on entry
  states that agree on the public registers. Its hypotheses are the compile equation and
  gates that are Booleans checked by evaluation; the source run at the compiler's table
  is obtained from the triple `cndCopy_triple` by `cndCopy_run_of_triple`.

The reading and the compiler's table agree at these calls:

| Calls | Statement |
|---|---|
| `index` and `array_update` at a `usize` index below the length; `BitAnd`, `BitOr`, `BitXor`, `wrapping_add`, `wrapping_sub`, `wrapping_mul`, `Shr`, `Shl`, `rotate_right` at 8, 16, 32 and 64 bits; `BitAnd`, `BitOr`, `BitXor`, `Shr` at `usize`; `Not` at 8, 16, 32 and 64 bits | `app64_ok`, by the name of the call (`hax64Reads`) |
| checked `Add`, `Sub`, `Mul`, `Div`, `Rem` on words of at most 64 bits, `usize` included | `hax64WExit_appArith`; bodies that use them reach the bytes through `fnCorres_hax64WExit_of_triple_arith` and `bytes_of_toRustMS_triple_arith`, from an entry environment whose words and arrays have at most 64 bits |
| the nine word operations and `Not` at `usize` | `appHost_ok`, against the table at the host platform's width (`hax64WExitAt Platform.host`) |

## Closed capstones at the `Com jasminDialect` denotation

`bash scripts/ascent-corpus.sh` lists, from the declaration text of the tracked files, the kernels of the package (closed `LowCT` values, `reifyLowCT%` kernels, and `ImpExpr` terms with an exit-lowering theorem), which of them an ascent correspondence names (single-store correspondences in a separate column), and which a closed capstone reaches, one that takes no emit, denotation or correspondence equation as a hypothesis; its header states the method.

The source-to-bytes capstones conclude an equation
`jcom.denote (ctMapValD .nil) = ctTransTy val` for the program
`jcom : Com jasminDialect …` that `cryptoDialectToJasminCom` produces from the front's
translation of the kernel, together with the reading of `val` in the abstract domain. The
word "bytes" in their names and docstrings refers to that denotation. The statements at
decoded bytes are those of
[Source readings joined to compiled bytes](#source-readings-joined-to-compiled-bytes)
and of [ASCENT.md](ASCENT.md).

| What is proved | Programs | Lean name |
|---|---|---|
| The emitted program `F.jcom` denotes the transport of the output word `BitVec.ofNat 64 (spec rs.rsScalar name)` of the source step, and `wEnc` of that word is `fa (derivedAbs rs) name` | a `LowCT` term `c` with a refinement `RRefines spec c`, a run `AdeqRun c rs rs'` from an in-range entry state, every read after a write (`readsOK (fun _ => False) c`), the front's artifacts `FrontOut c name` and a correspondence `Corres SRwordNT P fa c` | [`legWeld`](CatCrypt/Crypto/SecureCompilation/Ascent/LegWeld.lean) |
| The same, with the refinement obtained from `lowerRefines` and moved along a `LitNorm` normalisation | a `RustSrc` term in the fragment of `RustSubsetToLowCT.lower` | [`legWeld_lower`](CatCrypt/Crypto/SecureCompilation/Ascent/LegWeld.lean) |
| `feJcom` denotes the transport of the output word (`feSubSourceWord` in the tower, `feVal` in the end-to-end form), and `wEnc` of that word is `av - bv` in `ZMod (2 ^ 64)` | `r0 := a0 - b0` at the literals `av`, `bv` | [`feSub_source_to_bytes_tower`](CatCrypt/Crypto/SecureCompilation/Ascent/FeSubSourceTower.lean), [`feSub_endToEnd`](CatCrypt/Crypto/SecureCompilation/Ascent/FeSubEndToEnd.lean) |
| `feAddJcom` denotes the transport of the output word, and `wEnc` of that word is `av + bv` | `r0 := a0 + b0` at the literals `av`, `bv` | [`feAdd_source_to_bytes_tower`](CatCrypt/Crypto/SecureCompilation/Ascent/FeAddEndToEnd.lean), [`feAdd_endToEnd`](CatCrypt/Crypto/SecureCompilation/Ascent/FeAddEndToEnd.lean) |
| The emitted program denotes the transport of the output word of `RustSrc.exec demoSrc`, whose `wEnc` is `dav + dbv - dcv` | `r0 := a0 + b0 - c0` at the literals `dav`, `dbv`, `dcv` | [`demo_source_to_bytes`](CatCrypt/Crypto/SecureCompilation/Ascent/LegWeldDemo.lean) |
| The second conjuncts of the two towers evaluated to numerals | the same two kernels | [`feSub_value`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/SourceToBytes.lean), [`feAdd_value`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/SourceToBytes.lean) |
| `jcom` denotes the transport of `val`, and `wEnc val = fa a₀ name` | a kernel in `IsCoveredSCtl` with a `RustExec` run, the front's and the lowering's success equations, a correspondence over `SRword` (`keystone_emit`) or `SRwordNT` (`keystone_emit_NT`) and the readout hypothesis `hAgree` | [`keystone_emit`](CatCrypt/Crypto/SecureCompilation/Ascent/EmitBridge.lean), [`keystone_emit_NT`](CatCrypt/Crypto/SecureCompilation/Ascent/FeSubEndToEnd.lean) |
| `jcom` denotes the transport of the array `val`, whose pointwise `wEnc` is the abstract array `(fa a₀).arr` | the same hypotheses with a correspondence over `SRarr`, at output type `.memref n` | [`keystone_emit_arr`](CatCrypt/Crypto/SecureCompilation/Ascent/ArrStoreEmit.lean) |
| `jcom` denotes the transport of `val`, whose coefficient in `ZMod 3329` is `fa a₀ name` | the same hypotheses with the field encoding `fqEnc` | [`keystone_emit_fq`](CatCrypt/Crypto/SecureCompilation/Ascent/MlkemPolyAddCapstone.lean) |
| `keystone_emit` with the `RustExec` run listed first among its hypotheses, the premise a source simulation delivers | as `keystone_emit` | [`welding`](CatCrypt/Crypto/SecureCompilation/Ascent/EmitBridge.lean) |
| `welding` with the `RustExec` run obtained from `haxToLowCT_simulates_program` | a hax `ImpExpr` accepted by `simScope`, with an `evalImp` run and an entry state in agreement with the entry environment | [`welding_program`](CatCrypt/Crypto/SecureCompilation/Ascent/SourceBridge.lean) |

`keystone_emit`, `keystone_emit_NT`, `keystone_emit_arr` and `keystone_emit_fq` obtain
the emit equation from `rustToJasminCom_endToEnd_topLevel_unconditional`
([CompilerCorrectnessExtracted.lean](CatCrypt/Crypto/SecureCompilation/VIR/CompilerCorrectnessExtracted.lean));
`feSub_endToEnd` and `feAdd_endToEnd` are the instances of `keystone_emit_NT`.

The machine-level ascent results are stated over instruction-list semantics: `runBlock`
over `JInstr 64` (`CorresJ`), `xrun` / `x86Target.runOps` over the `Instr 64` lists of
the `ScalarLinX86Demo` target (`corres_of_refines_x86`), `runRBlock64` over `RInst64`
(`CorresR`), and `lsemStraightMem` over `LinstrRM` for the `sbb`-chain lowering
`sbbChainL` defined in `EcMultiLimbEmit` (`sbbChain_emit_realizes_abstract_CF`).

### Closed kernels and kernels with inputs

`legWeld` takes `hReads : readsOK (fun _ => False) c`, so every read in `c` follows a
write in `c`, and it closes the front at `VarMap.empty` and the jasmin program at the
empty valuation. Its conclusion determines the constant
`F.jcom.denote (ctMapValD .nil)` of a closed kernel. `corres_emit_weld` and the
`keystone_*` welds state the same condition through `hAgree`: the word at the readout
name is the same for every entry environment. The instances fix their inputs as
literals: `feSub_source_to_bytes_tower` and `feAdd_source_to_bytes_tower` at `av` and
`bv`, `demo_source_to_bytes` at `dav`, `dbv` and `dcv`, and `qrClosed_frontDenote_val`
([Demos/Scalar](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Scalar.lean)), which concludes
`qrCom.denote .nil = 393216#64`.

The weld at a nonempty entry valuation is `corresScalar_frontDenote`
([CorresScalar.lean](CatCrypt/Crypto/SecureCompilation/Ascent/CorresScalar.lean)), over `Com catCryptDialect Γ`, and its
lowering `corresScalar_jasminDenote` ([FeSubSymbolic.lean](CatCrypt/Crypto/SecureCompilation/Ascent/FeSubSymbolic.lean)), over
`Com jasminDialect`. Its instance is `feSub_symbolic_source_to_jasmin`, for the `LowCT`
term `r := a - b` at all `a`, `b`
([A worked path with symbolic inputs](#a-worked-path-with-symbolic-inputs-fesub_symbolic_source_to_jasmin)).

### Welds parametric in the emit map

The following welds are stated for an arbitrary map `Emit` from the output value to a
type `β`. Each takes the emit equation `hEmit : jdenote = Emit val` as a hypothesis,
returns it as its first conjunct, and adds the reading of `val` in the abstract domain;
the `keystone_emit*` theorems of the previous table instantiate `Emit` to `ctTransTy`.

| What is proved, given `hEmit` | Programs | Lean name |
|---|---|---|
| `wEnc val = fa a₀ name` | a `LowCT` term with `Corres SRword P fa c` at a related entry `(env₀, a₀)` and the readout hypothesis `hAgree` | [`corres_emit_weld`](CatCrypt/Crypto/SecureCompilation/Ascent/EmitBridge.lean) |
| the same with the correspondence supplied by `corres_setScalar` | a literal assignment | [`keystone_setScalar`](CatCrypt/Crypto/SecureCompilation/Ascent/EmitBridge.lean) |
| `wEnc (ifClosedVal gv tv ev)` is `if gv = 0 then ev else tv` in `ZMod (2 ^ 64)` | the closed φ-merge kernel `ifClosedKernel g r gv tv ev`, through `corres_if` | [`keystone_if`](CatCrypt/Crypto/SecureCompilation/Ascent/KeystoneControl.lean) |
| `wEnc (ifClosedVal 0 7 9) = 9`, at `Emit = ctTransTy` | the branch kernel at guard `0` and literals `7`, `9` | [`condKernel_bytes_of_emit`](CatCrypt/Crypto/SecureCompilation/Ascent/CondKernelCapstone.lean) |
| `wEnc (BitVec.ofNat 64 v) = v` | the closed bounded loop `forClosedKernel` with distinct counter and output names, through `corres_for` | [`keystone_for`](CatCrypt/Crypto/SecureCompilation/Ascent/KeystoneControl.lean), [`loop_keystone_emit`](CatCrypt/Crypto/SecureCompilation/Ascent/LoopSourceTower.lean) |
| the pointwise `wEnc` of the array `val` is `(fa a₀).arr` | a correspondence over `SRarr`; `keystone_arrStore` supplies it from `corres_arrStore` at `RArrStore arr idxVar src` | [`keystone_arr`](CatCrypt/Crypto/SecureCompilation/Ascent/ArrStoreEmit.lean), [`keystone_arrStore`](CatCrypt/Crypto/SecureCompilation/Ascent/ArrStoreEmit.lean) |
| the coefficient of `val` in `ZMod 3329` is `fa a₀ name` | a correspondence at the field encoding `fqEnc`; `keystone_setScalar_fq` is the literal assignment | [`keystone_fq`](CatCrypt/Crypto/SecureCompilation/Ascent/MlkemPolyAddCapstone.lean), [`keystone_setScalar_fq`](CatCrypt/Crypto/SecureCompilation/Ascent/MlkemPolyAddCapstone.lean) |

### The raw hax source of `feSub`

[PipelineWeld.lean](CatCrypt/Crypto/SecureCompilation/Ascent/PipelineWeld.lean) and
[SourceBridge.lean](CatCrypt/Crypto/SecureCompilation/Ascent/SourceBridge.lean) add hax-lean's optimisation pipeline above the
`feSub` tower. The three theorems conclude the same conjunction: the optimised program
`Hax.pipeline e` evaluates to the word `feSubSourceWord`, `feJcom` denotes the transport
of that word, and `wEnc feSubSourceWord = av - bv`. The first conjunct is hax-lean's
`pipeline_correct` applied to the output word of the reference run; the second and third
are `feSub_source_to_bytes_tower`.

| What is proved | Programs | Lean name |
|---|---|---|
| the conjunction, at any builtin table, fuel and environment | every `Hax.ImpExpr` `e` whose form after local mutation and reference dropping satisfies `Hax.NoLoops` and `Hax.NoEarlyExit`, and whose reference run `Hax.denote bi fuel e env` returns a `uint` value with the word `feSubSourceWord` (`hBridge`, read by `haxOutcomeWord`) | [`feSub_raw_source_to_bytes`](CatCrypt/Crypto/SecureCompilation/Ascent/PipelineWeld.lean) |
| the conjunction with the optimised program read by `denote'` through `pipeline_correct'`, at `Hax.defaultBuiltins` | every `e` with `Hax.NoCFConstructors` whose form after local mutation and reference dropping satisfies `Hax.NoEarlyExit`, from an environment with `Hax.Env.NoControlFlow`, with `hBridge` at `Hax.defaultBuiltins` | [`feSub_raw_source_to_bytes'`](CatCrypt/Crypto/SecureCompilation/Ascent/PipelineWeld.lean) |
| the conjunction at `Hax.widthAwareBuiltins`, for every fuel and environment; `hBridge` is the evaluation `feSubImp_word` | the hax term `feSubImp` | [`feSubImp_raw_source_to_bytes`](CatCrypt/Crypto/SecureCompilation/Ascent/SourceBridge.lean) |
| the conjunction, with `hBridge` derived from `haxToLowCT_simulates_program` | a program `body; r` accepted by `simScope` that returns a `uint` variable `r`, under the hypotheses of the simulation and the output condition that every `RustExec` run of its lowering leaves `feSubSourceWord` in the scalar slot `r` | [`raw_source_to_bytes_of_program`](CatCrypt/Crypto/SecureCompilation/Ascent/SourceBridge.lean) |

## Simulations from hax source

`haxToLowCT` lowers a builtin call to a leaf call (`RCall`, or `RCallSwap` for a
two-component result), the builtins `array_update` and `index` to `RArrStore` and
`RArrLoad`, and the index shift of a `forFold` with a nonzero start to
`RScalarSetExpr`. The arithmetic of a hax program is carried by the leaf specification
of its `RCall` nodes.

The program-level simulations conclude, for a program accepted by a scope checker and
an entry state related to the entry environment, that every successful source run
`evalImp` is matched by a `RustExec` run of the lowered program to a state related to
the exit environment. The modules are under `CatCrypt/Crypto/Hax/`.

| What is proved | Programs | Lean name |
|---|---|---|
| the simulation under `envAgreesRustFull`, given `FullSimPreconds` (whose field `leafScalar` states that no builtin result decodes as a scalar), `ProjPreconds` and the array arms `ProgramSimArms` | programs accepted by `simScope` | [`haxToLowCT_simulates_program`](CatCrypt/Crypto/Hax/HaxToLowCTSim_Program.lean) |
| the same with the exit-scope invariants in the conclusion | programs with `SimWellFormed Γ e`, from an entry state bound on `Γ` and fresh on the scalar names of the program | [`haxToLowCT_simulates_full`](CatCrypt/Crypto/Hax/HaxToLowCTSim_Full.lean) |
| every hypothesis of `haxToLowCT_simulates_full` holds, and the lowered program runs | `let y = leaf(a); y` at a table whose builtin `leaf` returns `.array []` | [`simFull_runs`](CatCrypt/Crypto/Hax/HaxToLowCTSim_Full.lean) |
| `ProgramSimArms` holds | builtin tables that implement neither `array_update` nor `index` | [`ProgramSimArms_of_vacuity`](CatCrypt/Crypto/Hax/HaxToLowCTSim_Program.lean) |
| the simulation under `envAgreesRustT`, which asks scalar agreement at the names without a tower binding, given `LeafCallAgreesArgs`: when the argument values are related to the tower slots the call reads, the result of the builtin is related to the leaf output | programs accepted by `simScope` whose `if` and `while` conditions are scalar-binding names (`condsScalar`), at a table implementing neither `array_update` nor `index` | [`haxToLowCT_simulates_programT`](CatCrypt/Crypto/Hax/HaxToLowCTSim_ProgramTower.lean) |
| the same for `litTower T` of the lowering, which stores each literal bound to a name of `T` into a `.TFp` slot with `RLimbStore` so that a call reads a literal argument, given the leaf condition `LitStoreAgrees`; `litTower_nil` and `simScopeL_nil` recover the lowering and `simScope` at `T = []` | programs accepted by `simScopeL` | [`haxToLowCT_simulates_programL`](CatCrypt/Crypto/Hax/HaxToLowCTSim_ProgramLit.lean) |
| the same for `arrTower A (litTower T c)`, given that the array load and store agree with the builtins `index` and `array_update` (`IndexAgrees`, `ArrUpdateAgrees`) and that tuple loads agree with `Value.projIdx` | programs with array reads and writes | [`haxToLowCT_simulates_programA`](CatCrypt/Crypto/Hax/HaxToLowCTSim_ProgramArr.lean) |
| the same with counted loops, read as the `forLoop` of `forToLoop` | programs with `forFold` over literal bounds | [`haxToLowCT_simulates_programF`](CatCrypt/Crypto/Hax/HaxToLowCTSim_ProgramFor.lean) |
| the same with reverse loops, runtime-bound loops (lowered to `RForRuntime`) and data-dependent loops (lowered to `RWhileNz`), given `ScalarCallsAgree` and `LimbReadAgrees`, under the environment invariant `ScalarInv` | programs accepted by `simScopeW`: `forFoldRev` over literal bounds, `forFold` from a literal to a variable bound, `whileFold` on a scalar guard | [`haxToLowCT_simulates_programW`](CatCrypt/Crypto/Hax/HaxToLowCTSim_ProgramLoops.lean) |
| the lowered function simulates `Hax.denote'`, given `ScalarOpsSound`, which `scalarOpsSound_noOverflow64_width` proves for hax-lean's width tables with overflowing `add` and `sub` refused | the fragment `exitSimOk` of the exit-flag lowering `haxToLowCTK` ([HaxToLowCTExit.lean](CatCrypt/Crypto/Hax/HaxToLowCTExit.lean)), which lowers `let x = op(a, b)` for `add`, `sub` and the unsigned comparisons to `RScalarSetExpr` and loops to `RWhileNz` | [`haxToLowCTFn_simulates`](CatCrypt/Crypto/Hax/HaxToLowCTSim_Exit.lean) |

The instances of `haxToLowCT_simulates_programT` and `haxToLowCT_simulates_programL`
at a builtin table with arithmetic, bitwise, shift and rotation builtins on `int`
values below `2 ^ 64` (`arith_haxToLowCT_simulates_programT`,
`arith_haxToLowCT_simulates_programL`), their composition with A-normalisation, and
their application to the extracted SHA-256 functions `maj` and `big_sigma0` (`maj_runs`,
`bigSigma0_runs`, each at one input) are in the CatCrypt development repository. They
conclude a `RustExec` run of the lowered normal form.

### Array and loop source kernels

| What is proved | Programs | Lean name |
|---|---|---|
| every `evalImp` run is matched by a `RustExec` run of the `RArrStore`-headed lowering, with `envAgreesRustFull` at exit, given the array-store step `hArrUpd` of the program-level simulation and a table without `index` | the array-write kernel `arrKernel` | [`arrKernel_source_to_rustexec_program`](CatCrypt/Crypto/SecureCompilation/Ascent/LoopSourceTower.lean) |
| the lowered loop refines `RustSrc.exec (loopSrc v n)`, corresponds to `nfold (loopSrcStep v) n` over `SRwordNT`, and is the node `RFor "i" n (lower (loopBodySrc v))` | the counted source loop `loopSrc v n` (a `RustSrc.forN`), for `v < 2 ^ 64` and every `n` | [`loopSrc_source_preimage`](CatCrypt/Crypto/SecureCompilation/Ascent/LoopSourceLeaf.lean) |

## The total abstraction over an array layout

The total abstraction `ascendGL L` ([Guards.lean](CatCrypt/Crypto/SecureCompilation/Ascent/Guards.lean)) is indexed by an
array layout `L : ArrLayout`, the `.memref` slots of the concrete store with their
lengths, and is sound over `SRwordL L` (`ascendGL_sound`): unreserved non-temp names
hold `u64` words, and element `j` of a layout array `arr` is encoded at the abstract
name `elemKey arr j`. `ascendG` is `ascendGL []`, and `SRwordL []` is `SRwordNT`
(`srwordL_nil_iff`), so `ascendG_sound` is the empty-layout instance. `tsLowCTL L`
([Strengthen.lean](CatCrypt/Crypto/SecureCompilation/Ascent/Strengthen.lean)) is the type-strengthening pass over a layout,
with `tsLowCTL_sound` and `tsLowCTL_isSome_iff`; `tsLowCT` is `tsLowCTL []`.

Over a layout that contains the array, five array constructors carry no guard; their
side conditions are static and decided by the abstraction:

| Constructor | Static condition | Abstract step | Leaf |
|---|---|---|---|
| `RArrLoad dst src i` | `src` has length `m + 1` in `L`; `dst` typed `TU64` and unreserved; `i` non-temp and unreserved | `dst := A[i mod (m + 1)]` | [`corresL_arrLoad`](CatCrypt/Crypto/SecureCompilation/Ascent/Guards.lean) |
| `RArrStore arr i src` | `arr` has length `m + 1` in `L` and `encodeTy` gives `.memref (m + 1)`; `i` and `src` non-temp and unreserved | `A[i mod (m + 1)] := src` | [`corresL_arrStore`](CatCrypt/Crypto/SecureCompilation/Ascent/Guards.lean) |
| `RArrLoadLit dst src idx` | `src` typed `TArr _ .TU64` and of length `m + 1` in `L`; `idx < m + 1` and `idx < 2 ^ 64`; `dst` typed `TU64` and unreserved | `dst := A[idx]` | [`corresL_arrLoadLit`](CatCrypt/Crypto/SecureCompilation/Ascent/Guards.lean) |
| `RArrStoreLit arr idx src` | `arr` typed `TArr _ .TU64` and of length `m + 1` in `L`; `idx < m + 1` and `idx < 2 ^ 64`; `src` non-temp and unreserved | `A[idx] := src` | [`corresL_arrStoreLit`](CatCrypt/Crypto/SecureCompilation/Ascent/Guards.lean) |
| `RLimbStore loc idx v` | `loc` has length `n` in `L` and `idx < n` | `A[idx] := v` | [`corresL_limbStore`](CatCrypt/Crypto/SecureCompilation/Ascent/Guards.lean) |

The index is reduced modulo the length because `semScalar` reads and writes through
`memGetDyn` and `memSetDyn`, which reduce it. A literal index is taken as a 64-bit word
before the reduction, as the front's `bvConst` temporary holds it, so the literal leaves
require it below `2 ^ 64` and the length. The literal leaves apply to arrays typed
`TArr _ .TU64`, whose elements are 64-bit words; byte and `u32` arrays, which `encodeTy`
also binds as `.memref` and whose element `idx` the direct route
(`LowCTToJasmin.arrLitElemWS`) reads at the array's own width, go through the leaf
oracle of the next subsection.

The constant-time select `RSelect dst sel src0 src1` goes through `corresL_select`
over any layout, with the abstract step `dst := if sel = 0 then src0 else src1`, when
`dst` is typed `TU64` and `dst`, `sel`, `src0` and `src1` are non-temp names the layout
does not reserve. `semScalar` gives it `selectWord`, the value of the front's eight-op
mask chain (`selectMaskCont_denote`), which lowers to jasmin. The value leaves over a
layout (`corresL_setScalar`, `corresL_setExprVal`, `corresL_if`) apply to written and
read word names that the layout does not reserve. Among the control and value
constructors, `ascendGL` abstracts `RScalarSetExpr` within `srcClean`, `RLetU64Zero`
over a loop-free body, `RWhileNz` on a non-temporary name, and `RIfNz` on a
non-temporary name in two shapes, a guarded then-branch and a φ-merge of two literal
writes to one name.

The worked instance is `arrSelK`: two array reads, the mask select
`r := y ^^^ ((x ^^^ y) &&& m)` and an array write over `[("A", 4)]`.
`arrSelK_ascendGL_prog` states its abstract program, `arrSelK_guardsHold` that its one
guard holds on every store, `arrSelK_corres` the correspondence, `arrSelK_srwordL` a
store and abstract store related by `SRwordL [("A", 4)]`, and `arrSelK_tsLowCTL` that
the pass returns the pure program.

`ascendGL` is a total function. To a node outside the cases above it assigns
`unsupportedAbs`, whose guard means `False`, so `ascendGL_sound` holds for every
command, with the precondition `guardsHold` carrying the guards of the program.
`tsLowCTL` returns a program exactly when the guards of `ascendGL` contain no such
node (`tsLowCTL_isSome_iff`). The leaf-call constructors `RCall`, `RCallSwap`,
`RCloneCall`, `RCallN`, `RCallDstThreaded` and `RTupleLoad`, `RSelect` over slots other
than 64-bit words, and `RArrLoadLit` / `RArrStoreLit` over slots other than a
`TArr _ .TU64` array and a 64-bit word bind their destinations in `semScalar` to
`CryptoTy.default`, the value of the front's `extCall`; the abstraction `ascendGLL` of
the next subsection gives them abstract leaves at a leaf oracle. The three-name leaves
`corres_arrStore` and `corres_arrLoad` are stated over the relations `SRarr` and
`SRarrLoad` on one array, its index and its source or destination.

### Leaf calls at a leaf oracle

`LowCT.LeafSpec` gives the leaf calls their meaning in `RustExec` (`call`,
`tupleLoad`, and `arrLoad` / `arrStore`, of which `semScalar` fixes the word-cell
instance `memGetDyn` / `memSetDyn`), and `CompileFromHaxLink.LeafSpec` relates
`jasminExtSem` to a specification. `semScalar` binds the destination of a leaf call to
`CryptoTy.default`, and the emit-leg preservation theorems
`translateDialectControl_denote_ctl`, `semScalarToJasminCom_denote_eq` and
`rustToJasminCom_endToEnd_unconditional` are stated at that default, which the dialect
`extCall` and the jasmin `extCall` both denote.

A leaf oracle `SemLeafSpec` (`VIR/CatCryptLeafOracle.lean`) maps a leaf name, the
destination's `CryptoTy` and the typed argument values to a value of that type;
`defaultLeaf` returns `CryptoTy.default`. Four layers are stated at a leaf oracle, each
alongside the default statement, which is unchanged:

1. `semScalarL ls` and `semUL ls fuel` (`Dialects/LeafOracleScalar.lean`) are
   `semScalar` and `semU` with each leaf arm binding its destination to `ls` at the name
   and arguments of the `extCall` the front emits for that node, the arguments read with
   `argVals`. `semScalar_eq_semScalarL` and `semU_eq_semUL` identify the default
   instances. The front's `"select"` leaf receives the selector and the two sources.
2. `catCryptDenoteWith ls` is the dialect denotation consulting `ls` at `extCall`, and
   `jasminDenoteWith jls` the jasmin one. `cryptoDialectToJasminCom_denote_eq_of_transport`
   (`VIR/DialectToJasminComLeaf.lean`) holds for every oracle pair related by
   `LeafTransport ls jls`, the jasmin oracle on transported arguments being the
   transport of `ls`; the lowering passes the argument variables through
   (`lookupArgs_toJArgsD`). With `leafTransport_default`, `catCryptDenoteWith_default` and
   `jasminDenoteWith_jasminExtSem` it gives `cryptoDialectToJasminCom_denote_eq'`
   (`cryptoDialectToJasminCom_denote_eq'_of_default`).
3. `CallAgrees leafSpec ls`, `ArrLoadAgrees leafSpec ls`, `TupleLoadLeafAgrees leafSpec ls`
   and `ArrStoreAgrees leafSpec ls` (`Dialects/RustExecLeafOracleBridge.lean`) say a
   `RustExec` oracle, encoded by `cryptoTyOfRustVal`, is `ls` on the encoded arguments.
   Under them `rustExec_semScalarL_call`, `rustExec_semScalarL_callDstThreaded`,
   `rustExec_semScalarL_tupleLoad`, `rustExec_semScalarL_arrLoadLit` and
   `rustExec_semScalarL_arrStoreLit` relate a `RustExec` step of `RCall`,
   `RCallDstThreaded`, `RTupleLoad`, and of a literal-index read or write in the leaf
   case, to the `semScalarL` step from an environment encoding the arguments;
   `rustExec_semScalarL_callSwap` and `rustExec_semScalarL_callN` do the same for the
   two-destination and multi-destination calls when no destination written before an
   argument is read is itself an argument, `RustExec` reading the arguments once and
   `semScalarL` before each write. `RustExec` copies the old destination of `RCloneCall`
   into the clone variable, where `semScalarL` binds the `"clone"` leaf;
   `rustExec_semScalarL_cloneCall` relates the two under `CloneAgrees ls`, the statement
   that the `"clone"` leaf returns its argument. `zeroLeafSpec` agrees with `defaultLeaf`
   (`callAgrees_zero`, `tupleLoadLeafAgrees_zero`, `arrStoreAgrees_zero`,
   `rustExec_semScalar_call_zero`).
4. `ascendGLL lf lfa L fuel` (`Ascent/GuardsLeaf.lean`) is `ascendGL L fuel` with abstract
   word leaves `lf : AbsLeaves`, an optional function `List AVal → ZMod 2^64` per name,
   and abstract array leaves `lfa : AbsArrLeaves`, an optional function
   `List AVal → Nat → ZMod 2^64` per name, where an argument abstracts to a word or to
   the element values of a layout array (`absArg`). `LeafAbs ls name f` is the hypothesis
   that `wEnc` of the oracle's `u64` result is `f` of the abstracted arguments, and
   `LeafAbsArr ls name g` that cell `j` of its `.memref n` result, encoded, is
   `g (abstracted arguments) j`; the abstract write of an array leaf is
   `setCells s n (g args)`, and `cellLeaf k f` is the array leaf writing cell `k` to `f`
   and keeping the others. Every leaf node is a binding, or a sequence of bindings, of a
   destination to the oracle (`leafDstStep`); `leafDstAbs` abstracts one binding to the
   word leaf on an unreserved `u64` word or to the array leaf on a layout array whose
   type encodes to its layout length, `AbsStep` and `seqAbs` compose bindings, and
   `absStep_leafDst` is the soundness of one binding. The rules per form are
   `corresL_call` and `corresL_callArr` (`RCall`), `corresL_callDstThreaded` and
   `corresL_callDstThreadedArr`, `corresL_tupleLoadLeaf` and `corresL_tupleLoadArrLeaf`,
   `corresL_callSwap` (two `u64` destinations, the second read after the first write),
   `corresL_cloneCall` (a `u64` clone of a `u64` old destination, then the inner call),
   `corresL_callN` (the fold `callNAbsL` over the destinations, output `i` at the leaf
   `callNLeafName f i`), `corresL_selectLeaf` and `corresL_selectArrLeaf` (`RSelect` with
   a layout array among the selector and sources, or as its destination),
   `corresL_arrLoadLitLeaf` (`RArrLoadLit` from a source that is not a `TArr _ .TU64`
   array in the layout) and `corresL_arrStoreLitLeaf` with its one-cell form
   `corresL_arrStoreLitCell` (`RArrStoreLit` that is not a word write to a `TArr _ .TU64`
   array). `ascendGLL_sound` holds at `semUL ls fuel` under `LeavesSound ls lf` and
   `ArrLeavesSound ls lfa`. `ascendGLL_noLeaves` and `ascendGL_sound_of_ascendGLL` recover
   `ascendGL_sound`; `leafAbs_leafOfAbs`, `leafAbs_leafOfAbsArr` and
   `leafAbsArr_leafOfAbsArr` give, for every family of abstract leaves, an oracle for
   which it is sound. The worked instance `leafK` reads a `TBytes 8` array through
   `"arrLoad:0"` and selects over it through `"select"`; `leafK_corres` refines it to
   `leafKProg` with no guard. `leafK2` writes byte `3` of a `TBytes 8` array through
   `"arrStore:3"`, reads a tuple component through `"tupleLoad:1"`, and runs an `RCallN`,
   an `RCallDstThreaded`, an `RCallSwap` and an `RCloneCall`; `leafK2_corres` refines it
   to `leafK2Prog` with no guard, and `leafK2_value` evaluates the abstract program on a
   store related to a concrete environment (`leafK2_srwordL`).

The front preservation theorems hold at every leaf oracle.
`translateDialectFull_denoteWith` and `translateDialectControl_denote_ctlWith`
(`Dialects/TranslateDialectScalarDenote.lean`) state, for an `IsCoveredS` and an
`IsCoveredSCtl` body respectively, that the dialect prefix the front emits, denoted
under `catCryptDenoteWith ls`, agrees with `semScalarL ls` from a consistent entry
state; `translateDialectFull_denote` and `translateDialectControl_denote_ctl` are their
instances at `defaultLeaf`. `semScalarLToJasminCom_denote_eq`
(`VIR/SemScalarLToJasminCom.lean`) composes the control form with
`cryptoDialectToJasminCom_denote_eq_of_transport`: for oracles `ls` and `jls` related by
`LeafTransport`, the lowered program denoted under `jasminDenoteWith jls` computes the
transport of the value `semScalarL ls` leaves in the tracked output. `jleafOfAbs fs`
is the jasmin oracle of a family of abstract leaves on `u64` destinations,
`leafTransport_leafOfAbs` relates it to `leafOfAbs fs`, and
`leafK_semScalarLToJasminCom` is the composed statement at `leafK`.

## Results parametric in the machine state

The following results hold for every machine state and conclude an arithmetic
specification. They are stated over instruction lists built by Lean definitions
(`adcxBlock`, `kernelBlock`, `emitMontRedc4Block`): `mpnAdd_runBlock`,
`mpnSub_runBlock`, `mpnAddKernel_runBlock` and `mpnSubKernel_runBlock` over any number
of limbs ([MpnAdxCorres.lean](CatCrypt/Crypto/SecureCompilation/Ascent/MpnAdxCorres.lean)), `feAddN_capstone` and
`feAdd4_capstone_field` ([Demos/HeapAbs](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/HeapAbs.lean)), and
`corresJ_montRedc4Block` ([FieldReduce.lean](CatCrypt/Crypto/SecureCompilation/Ascent/FieldReduce.lean)). `corresJ_sbbChain`,
`corresJ_adxBlock` and `corresR_subBorrow3` refine their blocks to abstract folds
(`sbbAbs`, `adxAbs`, `subBorrow3Step`); `feSub4_capstone` and `feMul4_capstone` are
identities about the limb functions `sbbLimbs` and `mulxLimbs` under `SRcarryLimbs`.

On compiler output, `add_descent_x86`, `add_descent_runBlock` and `add_descent_riscv`
establish `a + b` for symbolic `a` and `b` through the descent. `add_descent_solver`
and `compiled_refines` refine the same compiled blocks, translated to `JInstr`, to the
fold of their two-address value steps, such as `addStepX ∘ movStepX`, over the
register relation `SRx`. `Demos/Decide` and `Demos/Scalar` ascend a `LowCT` kernel to
its syntactic specification `asemWExpr`, `asemWBV` or a `wordStep` fold;
`keccakRoundBody_bitwise` is the correspondence of the Keccak round body with
`asemWBV keccakRoundBody` over `SRwordBV`. The FIPS 202 statement for the emitted
Keccak permutation is `keccakF1600Com_denote_spec`
([KeccakFipsAscent.lean](CatCrypt/Crypto/SecureCompilation/VIR/KeccakFipsAscent.lean)). `Demos/EarlyExit` and
`searchU_ts_refines` are stated at hax-lean's `denote'` and `pipeline`.

## Hand-written assembly

[NasmParse.lean](CatCrypt/Crypto/SecureCompilation/X86Backend/NasmParse.lean) reads the NASM Intel subset CryptOpt
emits into `JInstr` blocks. `JInstr` covers Jasmin's scalar `x86_op` set except the
instructions declined for constant time (`DIV`, `IDIV`, `CQO`, `BSR`, `BSF`, `BSWAP`,
`LZCNT`, `TZCNT`, `POPCNT`, `PDEP`, `PEXT`); the `JInstr` docstring in
[JasminModel.lean](CatCrypt/Crypto/SecureCompilation/X86Backend/JasminModel.lean) lists them with the reason. The
CryptOpt Curve25519 `solinas_square` kernel from fiat-crypto
(`bench/cryptopt/fiat_curve25519_solinas_square.asm`) parses in full;
`solinasSquareBlock` is its 99 instructions, and `lake exe nasm-parse-kat` fails unless
parsing the file yields exactly that list.

| What is proved | Programs | Lean name |
|---|---|---|
| the block refines its abstract run `absRunMem` over `SRmem solinasCells`, which relates the name-keyed memory of `JState` to an address-keyed abstract memory on the fourteen cells the kernel reads and writes | `solinasSquareBlock` | [`solinasSquareBlock_corres`](CatCrypt/Crypto/SecureCompilation/Ascent/CorresX86Mem.lean) |
| the abstract run satisfies `SolinasSquareSpec`, fiat-crypto's `sqr_correct` for `2^255 - 19` on four saturated limbs | abstract states whose spill slots and input limbs have distinct addresses | [`absRunMem_solinas_spec`](CatCrypt/Crypto/SecureCompilation/Ascent/SolinasSquareCorrect.lean) |
| the output limbs of `runBlock st solinasSquareBlock` are congruent to the square of the input limbs modulo `2^255 - 19` | every `JState` whose fourteen tracked cells have separated addresses | [`solinasSquare_correct`](CatCrypt/Crypto/SecureCompilation/Ascent/SolinasSquareCorrect.lean) |

The abstract state carries the registers, `CF` and `OF`, and the leaves for `setcc` and
`cmovcc` are stated at the conditions that read those two flags. `JInstr` has
memory-source forms of `add` (both memory kinds), `adcx`, `adox`, `imul` and
three-operand `imul` (`addMem`, `addToMem`, `adcxMem`, `adoxMem`, `imulMem`,
`imulriMem`), each equal to a load into a scratch register followed by the register
form (`runBlock_loadMem_*_eq_*Mem`), with `CorresJ` leaves in
[CorresX86Mem.lean](CatCrypt/Crypto/SecureCompilation/Ascent/CorresX86Mem.lean).

`JInstr` also has BMI2 `bzhi` (`x86_BZHI`, following the Intel SDM), in the
constant-time set. With it the CryptOpt Curve25519 `carry_mul` kernel
(`bench/cryptopt/fiat_curve25519_carry_mul.asm`) parses in full: `carryMulBlock`
([CarryMulBlock.lean](CatCrypt/Crypto/SecureCompilation/X86Backend/CarryMulBlock.lean)) is its 167 instructions,
checked by the same `lake exe nasm-parse-kat`. The kernel writes registers it uses as
memory bases (`sub rsp`, `xchg rdx, rax`, `mov r10, [rsp - 0x50]`), and the proof splits
the block at those instructions, with `SRmem` on one cell list per part; instructions
1–4, 147 and 167 are stepped on the machine state directly.

| What is proved | Programs | Lean name |
|---|---|---|
| each part refines its abstract run over `SRmem` on its own cell list (inputs and frame slots; outputs and saved-register slots) | instructions 5–146 and 148–166 of `carryMulBlock` | [`carryMulMid_corres`](CatCrypt/Crypto/SecureCompilation/Ascent/CarryMulCorres.lean), [`carryMulTail_corres`](CatCrypt/Crypto/SecureCompilation/Ascent/CarryMulCorres.lean) |
| the two abstract runs compute limbs whose value is congruent to the product of the inputs modulo `2^255 - 19` | inputs below `2^54`, at addresses apart from the frame slots | [`absRunMem_carryMulMid_spec`](CatCrypt/Crypto/SecureCompilation/Ascent/CarryMulCorrect.lean), [`absRunMem_carryMulTail_spec`](CatCrypt/Crypto/SecureCompilation/Ascent/CarryMulCorrect.lean) |
| the five words `runBlock st carryMulBlock` writes through `%r10` meet `CarryMulSpec`, fiat-crypto's `mul_correct` congruence | every `JState` whose input limbs are below `2^54`, whose cells are separated at the addresses the kernel uses, and whose memory bank `%rax` agrees with `%rdx` on the second input | [`carryMul_correct`](CatCrypt/Crypto/SecureCompilation/Ascent/CarryMulCorrect.lean) |

## Descent contracts at the x86 register file

`frefines_ret` ([CorresDescent.lean](CatCrypt/Crypto/SecureCompilation/Ascent/CorresDescent.lean)) is stated over
`Com fieldDialect`, and `corresScalar_frontDenote_two` over `Com catCryptDialect`. At
the x86 machine, `corres_of_refines_x86_runBlock`
([XrunRunBlockTie.lean](CatCrypt/Crypto/SecureCompilation/Ascent/XrunRunBlockTie.lean)) carries a descent `Refines` to a
`CorresMPost` at `runBlockStep` whose entry and exit relations read the register file.
It applies to every instruction that `x86Target.compile` emits for shift immediates
below 64 (`compile_XJFaithful` at the track `XJTrack.regs`).

`XJFaithful t` is the set of instructions on which the relation `XJRel t` between the
two x86 models is preserved, for a track `t` of the flags `CF`, `OF` and `ZF`. It
contains `mov`, `mulx`, `not`, `add` and `sub` at every track; `neg` when `OF` and `ZF`
are untracked; `adc` and `sbb` when `CF` is tracked and `OF` and `ZF` are untracked;
`adcx` when `CF` is tracked and `adox` when `OF` is tracked; `mul`, the bitwise
instructions and the shifts by an immediate below 64 when the three flags are
untracked; and the conditional moves on `CF` or `ZF` when that flag is tracked.

## Word width of the value leaves

The `LowCT` value leaves are at width 64: `semScalar_setExpr_width64` proves that
`semScalar` writes a 64-bit slot for every `RScalarSetExpr`.
[Width32Leaf.lean](CatCrypt/Crypto/SecureCompilation/Ascent/Width32Leaf.lean) provides the width-32 word isomorphism `wEnc32`
and its value transfer `wEnc32_evalBV32_evalZMod32`.

## Research probes outside the calculus

The following modules explore extensions of the `Std.Do` weakest-precondition
metatheory and of leakage reasoning. They are separate from the import closure of the
calculus, the capstones and the demonstrations.

Four modules are defined in this package, under
`CatCrypt/Crypto/SecureCompilation/Ascent/`:

| Module | Content |
|---|---|
| `GradedMvcgenProbe` | whether stock `mvcgen` carries a grade: as operational state it does (`demo_cost`); as a specification-only index it does not (`forget_gradedBind`, `postShape_exhaustive`) |
| `WriterTMvcgen` | an accumulating log as write-only state for `mvcgen` (`writerM_triple_iff`) |
| `RelationalProductMvcgen` | relational Hoare triples as unary `Std.Do` triples over a product program (`relTriple_iff_stddo`) |
| `RelationalExceptTMvcgen` | the same over `ExceptT`, with leakage as the exception barrel (`relExPostCond_except_leak`) |

The graded Dijkstra kernel and the relational modules it uses are defined in the core
library. The modules of the same names under
`CatCrypt/Crypto/SecureCompilation/Ascent/`, and `CatCrypt/Relational/Approx.lean` and
`CatCrypt/Relational/SpanLifting.lean`, are one-line re-exports, kept so that existing
imports resolve; new code imports the core module.

| Module of the core library | Re-exported as | Content |
|---|---|---|
| `CatCryptCore/XDijkstra/GradedWP.lean` | `Ascent/GradedWP` | a standalone graded predicate transformer with grade-additive sequencing (`seq`) |
| `CatCryptCore/XDijkstra/` : `XPredCore`, `XPostShape`, `XMvcgen`, `XMvcgenControl`, `XMvcgenReg`, `XRelatorPMF`, `XHeapSoundness`, `XMorphismInstance`, `XDijkstraAll` | `Ascent/` under the same names | an extended `PostShape` framework fusing grades, separation logic, relational reasoning and monad-morphism transfer, with the VC generators `xmvcgen`, `xmvcgen_ctl` and `xmvcgen!` |
| `CatCryptCore/XDijkstra/XAdvantageHybrid.lean` | `Ascent/XAdvantageHybrid` | the advantage-triangle tactic `advmvcgen` over hybrid arguments |
| `CatCryptCore/XDijkstra/XCostMonad.lean`, `Demo.lean`, `README.md` | none | a cost-counting program monad observed at a graded shape; a tutorial module; the description of the kernel |
| `CatCryptCore/Crypto/UCMonad/LeakageExceptT.lean` | `Ascent/LeakageExceptT` | a leakage channel as the exception branch, `leakEquiv` |
| `CatCryptCore/Crypto/UCMonad/UCLeakageDecomp.lean` | `Ascent/UCLeakageDecomp` | universal composability as a simulator existential over the leakage-transported relational judgment (`UCviaRel_iff_ExactUCEmulates`) |
| `CatCryptCore/Relational/Approx.lean`, `CatCryptCore/Relational/SpanLifting.lean` | `CatCrypt/Relational/Approx`, `CatCrypt/Relational/SpanLifting` | approximate couplings and span liftings for the relational layer of the kernel |
