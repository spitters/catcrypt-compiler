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

## Status, 2026-09-15

The following statements concern the source and leaf boundaries of the ascent; the
section [Scope](#scope) gives their hypotheses.

- Data-dependent loops: `corresU_whileFun` relates a terminating `RWhileNz` run to the
  exit state `loopFun` of the abstract loop, and `corresU_whileFun_total` gives the run
  when the trip count is below the fuel; `corresU_whileFun_jasminDenote` carries the
  exit value through the front's unified descent `transU` and the jasmin lowering to
  the `Com jasminDialect` of the node, unrolled at the entry environment's trip count
  ([Data-dependent loops as functions](#data-dependent-loops-as-functions)).
- Leaf calls: `ascendGLL_sound` abstracts `RCall`, `RSelect` with a layout array among
  its operands, and `RArrLoadLit` from a source that is not a `TArr _ .TU64` layout
  array, to abstract leaves at `semUL ls fuel`;
  `semScalarLToJasminCom_denote_eq` carries `semScalarL ls` through the front and the
  jasmin lowering for every oracle pair related by `LeafTransport`
  ([Leaf calls](#leaf-calls-the-boundary-of-semscalar)).
- hax source: `haxToLowCT_simulates_programT` and `haxToLowCT_simulates_programL`
  simulate programs whose builtins return scalars, the latter with literal call
  arguments stored in tower slots; both end at `RustExec`
  ([Simulations from hax source](#simulations-from-hax-source-end-at-rustexec)).
- Jasmin mirror: `mulhiLoop_mirror_runBlock` relates a `psem.v` mirror derivation of a
  loop calling a `MULX` function to the `runBlock` run of the unrolled `MULX` loop.

Not covered by any theorem in the package:

- the selector of `RSelect` at the front's `"select"` leaf, and the ascent of
  array-writing leaves, `RCallSwap`, `RCloneCall`, `RCallN`, `RCallDstThreaded` and
  `RTupleLoad`;
- hax programs with renaming aliases, tower-bound conditions, `forFold` or `whileFold`,
  or a builtin table implementing `index` or `array_update`, and a composition of the
  hax simulations with the front and the jasmin lowering;
- a weld of `corresU_whileFun` to the rolled loop: the `Com jasminDialect` of
  `corresU_whileFun_jasminDenote` is the front's unrolling of the `RWhileNz` node at
  the entry environment's trip count (`transU`), and no theorem relates it to the
  back-edge emitted at `Lcmd` (`TranslateDialectDataWhile.rolledWhileNz`).

## Layers

Each row names the modules of a layer and the declarations that carry it. Paths are
relative to `CatCrypt/Crypto/SecureCompilation/Ascent/`.

| Layer | Modules | Main declarations |
|---|---|---|
| Correspondence relations | `Corres`, `WhileTop`, `While`, `RunBlockCorres`, `CorresRiscv`, `CorresGeneric`, `Exit` | `Corres` over `semScalar` with `corres_seq`, `corres_weaken`; `CorresU` over `semU`; `CorresWhile`; `CorresJ` over `runBlock` with `corresJ_append`, `corresJ_loop`; `CorresR` over `runRBlock64`; `CorresM`, the machine-generic form, with `corres_eq_corresM`, `corresJ_eq_corresM`, `corresR_eq_corresM`; `CorresE`, `CorresUE` for bodies that throw |
| Value abstraction | `Corres`, `ExprLeaf`, `HeapAbs`, `StoreRefinement`, `MultiLimb`, `MlkemFieldLeaf`, `Width32Leaf`, `Phases` | `wEnc : BitVec 64 → ZMod 2^64` and the ParamTransfer squares `wEncAdd`, `wEncSub`, `wEncMul`; `SRword`, `SRwordNT`, `SRwordBV`; `ValueAbs` with `SRof`, `SRcarryOf` and the instance theorems `srwordNT_iff_srof`, `srcarry_iff_srcarryOf`; `fqEnc` and `CorresH`; `corres_WA`, `AbsProg` |
| Leaves over `LowCT` | `Corres`, `ExprLeaf`, `CorresScalar`, `BitwiseOrNot`, `RotateLeaf`, `SelectLeaf`, `ArrStoreLeaf`, `ArrLoadLeaf`, `MlkemFieldLeaf` | `corres_setScalar`, `corres_setScalar_NT`, `corres_setExpr` (arithmetic into `ZMod 2^64`), `corres_setExprBitwise`, `corres_setExprWord` (the `srcClean` word algebra over `BitVec 64`), `corres_setExprOr`, `corres_rotl`, `corres_ctSelect`, `corres_arrStore`, `corres_arrLoad`, `corres_setExpr_fqAdd` |
| Control and early exit | `Control`, `While`, `WhileTop`, `WhileFun`, `WhileFunEmit`, `MlkemPolyFoldCorres`, `Exit` | `corres_for`, `corres_if`, `corres_for_indexed`, `polyAdd_fold_corres`, `corres_while`, `corresU_while`, `corresU_whileFun`, `corresU_whileFun_total`, `corresU_whileFun_jasminDenote`, `pipeline_exceptProg`, `whileExit_sim`, `corresU_while_exit` |
| Automation and total abstraction | `Ascend`, `AscendDecide`, `AscendMeta`, `Guards`, `GuardsLeaf`, `Strengthen`, `CorresSolver`, `CorresAttr`, `CorresX86Solver`, `CorresRiscvLeaves`, `CorresRiscvSolver`, `CorresScalar`, `MontBounds`, `InvariantSchemas` | `ascend_sound`, `ascend_expr_sound`, `ascend_bitwise_sound` and the tactics `ascend!`, `ascend_meta`; `ascendG`, `ascendG_sound`; `ascendGLL`, `ascendGLL_sound`; `tsLowCT_sound`, `tsHax_sound`, `Kernel.tsLevel`; the solvers `corres_solve`, `corres_solve_x86`, `corres_solve_rv`, `corres_solve_scalar`; `mont_bound` |
| Machine-level leaves and value results | `RunBlockCorres`, `EcMultiLimbCapstone`, `EcMultiLimbMul`, `MpnAdxCorres`, `FieldReduce`, `CorresX86Solver`, `CorresRiscvLeaves`, `Capstone`, `CapstoneField`, `EcMultiLimbEmit` | `corresJ_sbb`, `corresJ_adc`, `srcarryLimbs_recompose`; `sbbLimbs_spec`, `corresJ_sbbChain`; `mulLimbs_spec`, `corresJ_adxBlock`; `mpnAdd_runBlock`, `mpnSub_runBlock`; `montRedc_spec`, `corresJ_montRedc4Block`; `corresJ_movX` … `corresJ_mulxX`; `corresR_add` … `corresR_slli`; `sbbChain_emit_realizes_abstract_CF` |
| Ties between machines, and program logics | `CorresBridge`, `CorresBridgeArith`, `CorresBridgeArithComplete`, `CorresBridgeMem`, `CorresBridgeMemStore`, `CorresBridgeCtrl`, `CorresMachineTie`, `CorresMachineTieFragments`, `JasminComRunBlockTie`, `JasminComRunBlockSeq`, `JasminComRunBlockRealloc`, `JasminMirrorTie`, `XrunRunBlockTie`, `CorresHoare`, `RunBlockMvcgen`, `RunBlockMvcgenMorphism`, `JStateSepLogic` | `corresJ_forget_to_corres`, `coRefine`; `arith_middle_tie_seq_nonTmp`, `mem_store_middle_tie_full`, `for_middle_tie_gen`; `SimTie`, `simTie_seq`; `lowerBlock_tie`, `lowerBlockR_tie`; `forFold_eq_loopStep`, `mulhiLoop_mirror_runBlock`; `xrun_runBlock_tie`; `corresJ_iff_triple`, `runBlockM_triple_iff`, `Spec.wp_theta`, `RunBlockTriple.frame` |
| Descent contracts in the ascent's shape | `CorresDescent`, `CorresDescentX86`, `CorresDescentRiscv`, `XrunRunBlockTie` | `frefines_ret`; `CorresMPost`, `corres_of_refines_x86`; `corresR_of_refines`; `corres_of_refines_x86_runBlock` |
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
| [Demos/X86StraightLine](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/X86StraightLine.lean) | `corres_solve_x86` over carry chains and over `x86Target.compile` output | `sbb3_refines`, `mulx_adcx_refines`, `compiled_refines` |
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
4. Lowering. No descent lemma is generalised: `cryptoDialectToJasminCom_denote_eq'` and
   `semScalarToJasminCom_denote_eq` are stated at an arbitrary entry map and valuation,
   and the empty valuation enters only in their `_topLevel` specialisations.

`feSub_symbolic_frontDenote` is the same result one lowering up,
`feSubSymCom.denote (valAB a b) = a - b`. The source of this path is the `LowCT` term.
A `RustSrc` source through `lowerRefines` would add the `Nat` model of `RustExec`,
whose subtraction saturates, so a statement through `legWeld` would hold only for
`b ≤ a`.

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
`CorresScalar.lean`, over `Com catCryptDialect Γ`, and its lowering
`corresScalar_jasminDenote` in `FeSubSymbolic.lean`, over `Com jasminDialect`. Their one
instance is `feSub_symbolic_source_to_jasmin`, for `r := a - b` at all `a`, `b`; its
source is the `LowCT` term, not a `RustSrc` or hax term.

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

### Simulations from hax source end at `RustExec`

`haxToLowCT` lowers a builtin call to a leaf call (`RCall`, or `RCallSwap` for a
two-component result) or, for `array_update` and `index`, to `RArrStore` and
`RArrLoad`. It produces `RScalarSetExpr` only for the index shift of a `forFold` with
a nonzero start, so no lowered hax program contains the `RScalarSetExpr` kernels that
`legWeld` and the value leaves abstract; the arithmetic of a hax program is carried by
the leaf specification of its `RCall` nodes. `raw_source_to_bytes_of_program` and
`welding_program` are stated for arbitrary programs and have no instance in the
package.

Three program-level simulations conclude, for a program accepted by a scope checker
and an entry state related to the entry environment, that every successful source run
`evalImp` is matched by a `RustExec` run of the lowered program to a state related to
the exit environment:

* `haxToLowCT_simulates_program` (`CatCrypt/Crypto/Hax/HaxToLowCTSim_Program.lean`)
  takes `FullSimPreconds`, whose field `leafScalar` states that no builtin result
  decodes as a scalar; a builtin table implementing arithmetic does not satisfy it.
  `haxToLowCT_simulates_full` (`CatCrypt/Crypto/Hax/HaxToLowCTSim_Full.lean`) is its
  corollary for a program with `SimWellFormed Γ e`, an entry state bound on `Γ` and
  fresh on the program's scalar names, and the preconditions `FullSimPreconds`,
  `ProjPreconds` and `ProgramSimArms`; its conclusion adds the exit-scope invariants.
  `simFull_runs` instantiates every hypothesis at `let y = leaf(a); y` with a builtin
  table whose builtin `leaf` returns the constant `.array []`.
* `haxToLowCT_simulates_programT` (`CatCrypt/Crypto/Hax/HaxToLowCTSim_ProgramTower.lean`)
  relates environment and state by `envAgreesRustT`, which asks scalar agreement only at
  names without a tower binding, and replaces `FullSimPreconds` by `LeafCallAgreesArgs`:
  when the argument values are related to the tower slots the call reads, the builtin's
  result is related to the leaf output. It requires `condsScalar` (every `if` and
  `while` condition is a scalar-binding name) and a builtin table implementing neither
  `array_update` nor `index`.
* `haxToLowCT_simulates_programL` (`CatCrypt/Crypto/Hax/HaxToLowCTSim_ProgramLit.lean`)
  is the same statement for `litTower T` of the lowering, which stores each literal
  bound to a name of `T` into a `.TFp` slot with `RLimbStore`, so that a call can read a
  literal argument. Its scope checker is `simScopeL`, and it adds the leaf condition
  `LitStoreAgrees`. `litTower_nil` and `simScopeL_nil` recover the lowering and
  `simScope` at `T = []`.

The side conditions of the call arms quantified over every name, state and argument
list are unsatisfiable: `HaxToLowCTSim_Program.lean` refutes them by
`hScalarFresh_all_unsat`, `hDestBoundAll_unsat`, `hArgsEnvAll_unsat`,
`hArgsBoundAll_unsat` and `hArgsFreshAll_unsat`, and `pipelineAppInvariants_unsat`
refutes the bundle `PipelineAppInvariants`. `EmitBridge.welding` takes its `RustExec`
premise as a hypothesis, and `welding_program` supplies that premise from
`haxToLowCT_simulates_program`.

The instances of `haxToLowCT_simulates_programT` and `haxToLowCT_simulates_programL`
at a builtin table with arithmetic, bitwise, shift and rotation builtins on `int`
values below `2 ^ 64` (`arith_haxToLowCT_simulates_programT`,
`arith_haxToLowCT_simulates_programL`), their composition with A-normalisation, and
their application to the extracted SHA-256 functions `maj` and `big_sigma0` (`maj_runs`,
`bigSigma0_runs`, each at one input) are in the CatCrypt development repository, not in
this package. Those statements end at the `RustExec` run of the lowered normal form; no
theorem composes them with the front and the jasmin lowering.

`simScope` and `simScopeL` reject a renaming alias `let a = b` with `a ≠ b` and the
fold forms `forFold` and `whileFold`; `condsScalar` rejects an `if` or `while` condition
bound in the tower, such as the result of a comparison builtin; and
`haxToLowCT_simulates_programT` and `haxToLowCT_simulates_programL` require a builtin
table without `index` and `array_update`. No simulation in the package covers programs
with these constructs.

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

### The total abstraction assigns an unsatisfiable guard to 11 constructors

The total abstraction `ascendGL L` (`Guards.lean`) is indexed by an array layout
`L : ArrLayout`, the `.memref` slots of the concrete store with their lengths, and is
sound over `SRwordL L` (`ascendGL_sound`): unreserved non-temp names hold `u64` words,
and element `j` of a layout array `arr` is encoded at the abstract name
`elemKey arr j`. `ascendG` is `ascendGL []`, and `SRwordL []` is `SRwordNT`
(`srwordL_nil_iff`), so `ascendG_sound` is the empty-layout instance. `tsLowCTL L`
(`Strengthen.lean`) is the type-strengthening pass over a layout, with `tsLowCTL_sound`
and `tsLowCTL_isSome_iff`; `tsLowCT` is `tsLowCTL []`.

Over a layout that contains the array, five array constructors carry no guard; their
side conditions are static and decided by the abstraction:

| constructor | leaf | static condition | abstract step |
|---|---|---|---|
| `RArrLoad dst src i` | `corresL_arrLoad` | `src` has length `m + 1` in `L`; `dst` typed `TU64` and unreserved; `i` non-temp and unreserved | `dst := A[i mod (m + 1)]` |
| `RArrStore arr i src` | `corresL_arrStore` | `arr` has length `m + 1` in `L` and `encodeTy` gives `.memref (m + 1)`; `i` and `src` non-temp and unreserved | `A[i mod (m + 1)] := src` |
| `RArrLoadLit dst src idx` | `corresL_arrLoadLit` | `src` typed `TArr _ .TU64` and of length `m + 1` in `L`; `idx < m + 1` and `idx < 2 ^ 64`; `dst` typed `TU64` and unreserved | `dst := A[idx]` |
| `RArrStoreLit arr idx src` | `corresL_arrStoreLit` | `arr` typed `TArr _ .TU64` and of length `m + 1` in `L`; `idx < m + 1` and `idx < 2 ^ 64`; `src` non-temp and unreserved | `A[idx] := src` |
| `RLimbStore loc idx v` | `corresL_limbStore` | `loc` has length `n` in `L` and `idx < n` | `A[idx] := v` |

The index is reduced modulo the length because `semScalar` reads and writes through
`memGetDyn` and `memSetDyn`, which do; an out-of-bounds dynamic index is not a guard.
A literal index is taken as a 64-bit word before the reduction, as the front's
`bvConst` temporary holds it, so the literal leaves require it below `2 ^ 64` and the
length. The literal leaves also require the array to be typed `TArr _ .TU64`:
`encodeTy` binds byte and `u32` arrays as `.memref` as well, but the direct route
(`LowCTToJasmin.arrLitElemWS`) reads their element `idx` at the array's own width, so
`semScalar` and the front give those arrays the opaque leaf. Over the empty layout
these constructors stay unsupported, since `SRwordNT` requires every non-temp name to
hold a word.

The constant-time select `RSelect dst sel src0 src1` goes through `corresL_select`
over any layout, with the abstract step `dst := if sel = 0 then src0 else src1`, when
`dst` is typed `TU64` and `dst`, `sel`, `src0` and `src1` are non-temp names the layout
does not reserve. `semScalar` gives it `selectWord`, the value of the front's eight-op
mask chain (`selectMaskCont_denote`), which lowers to jasmin. The value leaves over a layout (`corresL_setScalar`,
`corresL_setExprVal`, `corresL_if`) additionally require the written and read word
names to be unreserved by the layout; `ascendGL` returns the unsupported guard when one
is reserved. The worked instance is `arrSelK`: two array reads, the mask select
`r := y ^^^ ((x ^^^ y) &&& m)` and an array write over `[("A", 4)]`.
`arrSelK_ascendGL_prog` states its abstract program, `arrSelK_guardsHold` that its one
guard holds on every store, `arrSelK_corres` the correspondence, `arrSelK_srwordL` a
store and abstract store related by `SRwordL [("A", 4)]`, and `arrSelK_tsLowCTL` that
the pass returns the pure program.

The remaining 11 constructors map to `unsupportedAbs`, whose guard means `False`, and
the obstruction is in the waist semantics `semScalar`, not in a missing leaf:

* `RLetZero`, `RLimbStoreExpr`, `RFnDef`, `RFnCall` and `RForRuntime` have no arm in
  `semScalar`, which returns `none`; `CorresU` requires a successor state, so no
  satisfiable precondition exists at this waist.
* `RCall`, `RCallSwap`, `RCloneCall`, `RCallN`, `RCallDstThreaded` and `RTupleLoad`
  bind their destinations to `CryptoTy.default`, the opaque `extCall` waist,
  independent of the arguments. So do `RSelect` over slots other than 64-bit words
  and `RArrLoadLit` / `RArrStoreLit` over slots other than a `TArr _ .TU64` array
  bound as `.memref` and a 64-bit word, which the front lowers to the opaque `extCall "select"`,
  `"arrLoad:i"` and `"arrStore:i"`. An arm would abstract such a node to a zero write.

Six of these 11 are in the emit leg's fragment `IsCoveredS`.

#### Leaf calls: the boundary of `semScalar`

`LowCT.LeafSpec` gives the leaf calls their meaning in `RustExec` (`call`,
`tupleLoad`, and `arrLoad` / `arrStore`, of which `semScalar` fixes the word-cell
instance `memGetDyn` / `memSetDyn`), and `CompileFromHaxLink.LeafSpec` relates
`jasminExtSem` to a specification. Neither enters `semScalar`, so no statement over
`semScalar` constrains the value a leaf call returns: the emit-leg preservation
theorems `translateDialectControl_denote_ctl`, `semScalarToJasminCom_denote_eq` and
`rustToJasminCom_endToEnd_unconditional` equate two opaque defaults at those nodes, the
dialect `extCall` and the jasmin `extCall` both denoting `CryptoTy.default`.

A leaf oracle `SemLeafSpec` (`VIR/CatCryptLeafOracle.lean`) maps a leaf name, the
destination's `CryptoTy` and the typed argument values to a value of that type;
`defaultLeaf` returns `CryptoTy.default`. Four layers are stated at a leaf oracle, each
alongside the default statement, which is unchanged:

1. `semScalarL ls` and `semUL ls fuel` (`Dialects/LeafOracleScalar.lean`) are
   `semScalar` and `semU` with each leaf arm binding its destination to `ls` at the name
   and arguments of the `extCall` the front emits for that node, the arguments read with
   `argVals`. `semScalar_eq_semScalarL` and `semU_eq_semUL` identify the default
   instances. The front's `"select"` leaf receives the two sources and not the selector.
2. `catCryptDenoteWith ls` is the dialect denotation consulting `ls` at `extCall`, and
   `jasminDenoteWith jls` the jasmin one. `cryptoDialectToJasminCom_denote_eq_of_transport`
   (`VIR/DialectToJasminComLeaf.lean`) holds for every oracle pair related by
   `LeafTransport ls jls`, the jasmin oracle on transported arguments being the
   transport of `ls`; the lowering passes the argument variables through
   (`lookupArgs_toJArgsD`). With `leafTransport_default`, `catCryptDenoteWith_default` and
   `jasminDenoteWith_jasminExtSem` it gives `cryptoDialectToJasminCom_denote_eq'`
   (`cryptoDialectToJasminCom_denote_eq'_of_default`).
3. `CallAgrees leafSpec ls` and `ArrLoadAgrees leafSpec ls`
   (`Dialects/RustExecLeafOracleBridge.lean`) say a `RustExec` oracle, encoded by
   `cryptoTyOfRustVal`, is `ls` on the encoded arguments. Under them
   `rustExec_semScalarL_call` and `rustExec_semScalarL_arrLoadLit` relate a `RustExec`
   step of `RCall`, and of a literal-index read in the leaf case, to the `semScalarL` step
   from an environment encoding the arguments. `zeroLeafSpec` agrees with `defaultLeaf`
   (`callAgrees_zero`, `rustExec_semScalar_call_zero`). `RSelect` has no such statement:
   `RustExec` reads the selector, and the `"select"` leaf does not receive it.
4. `ascendGLL lf L fuel` (`Ascent/GuardsLeaf.lean`) is `ascendGL L fuel` with abstract
   leaves `lf : AbsLeaves`, an optional function `List AVal → ZMod 2^64` per name, where
   an argument abstracts to a word or to the element values of a layout array
   (`absArg`). `LeafAbs ls name f` is the hypothesis that `wEnc` of the oracle's `u64`
   result is `f` of the abstracted arguments. `corresL_call` (`RCall`),
   `corresL_selectLeaf` (`RSelect` with a layout array among the selector and sources)
   and `corresL_arrLoadLitLeaf` (`RArrLoadLit` from a source that is not a `TArr _ .TU64`
   array in the layout) abstract such a node to a write of `f` to a `u64` destination,
   and `ascendGLL_sound` holds at `semUL ls fuel` under `LeavesSound ls lf`.
   `ascendGLL_noLeaves` and `ascendGL_sound_of_ascendGLL` recover `ascendGL_sound`;
   `leafAbs_leafOfAbs` gives, for every family of abstract leaves, an oracle for which it
   is sound. The worked instance `leafK` reads a `TBytes 8` array through `"arrLoad:0"`
   and selects over it through `"select"`; `leafK_corres` refines it to `leafKProg` with
   no guard.

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
`leafK_semScalarLToJasminCom` is the composed statement at `leafK`. Since the
`"select"` leaf does not receive the selector (item 1), no oracle computes the value
`RustExec` gives `RSelect` at that node.

The leaf rules of the ascent write a `u64` destination: a leaf writing an array (`"arrStore:i"`, or
`RSelect` into an array) stays unsupported, as do `RCallSwap`, `RCloneCall`, `RCallN`,
`RCallDstThreaded` and `RTupleLoad`. The `RustExec` bridge covers `RCall` and
`RArrLoadLit`.

`ascendGL` also returns
the unsupported guard for `RLetU64Zero` over a body containing a loop, for `RIfNz` and
`RWhileNz` on a temporary name, for `RIfNz` shapes other than a guarded then-branch or a
φ-merge of two literal writes to one name, for `RScalarSetExpr` outside `srcClean`, and
for word names the layout reserves. `ascendGL_sound` holds for every command, but at
those nodes its precondition `guardsHold` is unsatisfiable; `tsLowCTL` returns `none`
for them (`tsLowCTL_isSome_iff`). The three-name leaves `corres_arrStore` and
`corres_arrLoad` over `SRarr` and `SRarrLoad` are not used by `ascendGL`, whose relation
ties the whole store.

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
`ZF`, `SF` or `PF` needs further leaves. `JInstr` has memory-source forms of `add` (both
memory kinds), `adcx`, `adox`, `imul` and three-operand `imul` (`addMem`, `addToMem`,
`adcxMem`, `adoxMem`, `imulMem`, `imulriMem`), each equal to a load into a scratch
register followed by the register form (`runBlock_loadMem_*_eq_*Mem`), with `CorresJ`
leaves in `Ascent/CorresX86Mem.lean`.

`JInstr` also has BMI2 `bzhi` (`x86_BZHI`, following the Intel SDM, since Jasmin's
`x86_op` has no `BZHI`), in the constant-time set. With it the CryptOpt Curve25519
`carry_mul` kernel (`bench/cryptopt/fiat_curve25519_carry_mul.asm`) parses in full:
`carryMulBlock` (`X86Backend/CarryMulBlock.lean`) is its 167 instructions, checked by
the same `lake exe nasm-parse-kat`. The kernel writes registers it uses as memory bases
(`sub rsp`, `xchg rdx, rax`, `mov r10, [rsp - 0x50]`), so `SRmem` over one cell list
does not hold across the whole block; the block splits at those instructions:

- `carryMulMid_corres` and `carryMulTail_corres` (`Ascent/CarryMulCorres.lean`):
  instructions 5–146 and 148–166 refine their abstract runs over `SRmem` on their own
  cell lists (inputs and frame slots; outputs and saved-register slots).
- `absRunMem_carryMulMid_spec` and `absRunMem_carryMulTail_spec`
  (`Ascent/CarryMulCorrect.lean`): for inputs below `2^54` apart from the frame slots,
  the two abstract runs compute limbs whose value is congruent to the product of the
  inputs modulo `2^255 - 19`.
- `carryMul_correct`: for every `JState` whose input limbs are below `2^54`, whose
  cells are separated at the addresses the kernel uses, and whose memory bank `%rax`
  agrees with `%rdx` on the second input, the five words `runBlock st carryMulBlock`
  writes through `%r10` meet `CarryMulSpec`, fiat-crypto's `mul_correct` congruence.
  Instructions 1–4, 147 and 167 are stepped on the machine state directly.

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
