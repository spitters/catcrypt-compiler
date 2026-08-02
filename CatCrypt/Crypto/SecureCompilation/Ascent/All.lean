/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
import CatCrypt.Crypto.SecureCompilation.Ascent.ExprLeaf
import CatCrypt.Crypto.SecureCompilation.Ascent.StoreRefinement
import CatCrypt.Crypto.SecureCompilation.Ascent.MultiLimb
import CatCrypt.Crypto.SecureCompilation.Ascent.Control
import CatCrypt.Crypto.SecureCompilation.Ascent.While
import CatCrypt.Crypto.SecureCompilation.Ascent.Ascend
import CatCrypt.Crypto.SecureCompilation.Ascent.Capstone
import CatCrypt.Crypto.SecureCompilation.Ascent.CapstoneField
import CatCrypt.Crypto.SecureCompilation.Ascent.EmitBridge
import CatCrypt.Crypto.SecureCompilation.Ascent.KeystoneControl
import CatCrypt.Crypto.SecureCompilation.Ascent.Phases
import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
import CatCrypt.Crypto.SecureCompilation.Ascent.FeSubEndToEnd
import CatCrypt.Crypto.SecureCompilation.Ascent.FeSubSourceTower
import CatCrypt.Crypto.SecureCompilation.Ascent.FeAddEndToEnd
import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbCapstone
import CatCrypt.Crypto.SecureCompilation.Ascent.PipelineWeld
import CatCrypt.Crypto.SecureCompilation.Ascent.LoopSourceTower
import CatCrypt.Crypto.SecureCompilation.Ascent.ArrStoreLeaf
import CatCrypt.Crypto.SecureCompilation.Ascent.ArrStoreEmit
import CatCrypt.Crypto.SecureCompilation.Ascent.LoopSourceLeaf
import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbEmit
import CatCrypt.Crypto.SecureCompilation.Ascent.CondKernelCapstone
import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbMul
import CatCrypt.Crypto.SecureCompilation.Ascent.FieldReduce
import CatCrypt.Crypto.SecureCompilation.Ascent.SelectLeaf
import CatCrypt.Crypto.SecureCompilation.Ascent.ArrLoadLeaf
import CatCrypt.Crypto.SecureCompilation.Ascent.RotateLeaf
import CatCrypt.Crypto.SecureCompilation.Ascent.Width32Leaf
import CatCrypt.Crypto.SecureCompilation.Ascent.BitwiseOrNot
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridge
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridgeArith
import CatCrypt.Crypto.SecureCompilation.Ascent.MlkemFieldLeaf
import CatCrypt.Crypto.SecureCompilation.Ascent.MlkemPolyAddCapstone
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridgeArithComplete
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridgeCtrl
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridgeMem
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresGeneric
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresMachineTie
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridgeMemStore
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresMachineTieFragments
import CatCrypt.Crypto.SecureCompilation.Ascent.JasminComRunBlockTie
import CatCrypt.Crypto.SecureCompilation.Ascent.JasminComRunBlockSeq
import CatCrypt.Crypto.SecureCompilation.Ascent.JasminComRunBlockRealloc
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresHoare
import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockMvcgen
import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockMvcgenMorphism
import CatCrypt.Crypto.SecureCompilation.Ascent.JStateSepLogic
import CatCrypt.Crypto.SecureCompilation.Ascent.RelationalProductMvcgen
import CatCrypt.Crypto.SecureCompilation.Ascent.RelationalExceptTMvcgen
-- MlkemPolyFoldCorres: the index-dependent bounded-loop combinator (corres_for_indexed)
-- + polyAdd_fold_corres, lifting the per-coefficient ZMod 3329 add over the poly loop
-- to a whole-polynomial corres tie (the ascent granularity-lift for ML-KEM poly-add).
import CatCrypt.Crypto.SecureCompilation.Ascent.MlkemPolyFoldCorres
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresAttr
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresSolver
import CatCrypt.Crypto.SecureCompilation.Ascent.InvariantSchemas
import CatCrypt.Crypto.SecureCompilation.Ascent.MontBounds
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar
import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalarDemo

/-!
# The LowCT ascent refinement calculus — import aggregator (rot guard)

The proof-producing *abstraction* (ascent) leg of the CatCrypt pipeline — LowCT → clean
Lean spec with a machine-checked `Corres` correspondence, the AutoCorres/Ascent dual of
the descent relational compiler — over the real `semScalar`. Forces the whole calculus so
a change to `semScalar`/`LowCT`/ParamTransfer cannot silently rot it.

* `Corres`      — the correspondence relation over the real `semScalar`; structural core
                  (`corres_seq`/`_skip`/`_block`/`_weaken`); Phase-1 word layer via
                  ParamTransfer (`wEnc`, `RelatedBinOp`); value leaf `corres_setScalar`.
* `ExprLeaf`    — Phase 1 arithmetic: `corres_setExpr` (`RScalarSetExpr`), the word-tree
                  transfer through `wEnc`, over `SRwordNT` (non-temp restriction).
* `StoreRefinement` — Phase 2: the single-limb `BitVec 64 ↠ ZMod p` split surjection
                  (`limbFieldParam : Param .map0 .map2a`) + operation squares.
* `MultiLimb`   — Phase 2: the multi-limb `(Fin n → BitVec 64) ↠ ZMod p` split surjection
                  (`multiLimbFieldParam`, general `n`, base-2^64 recompose retraction).
* `Control`     — Phase 4: `corres_for` (bounded loop), `corres_if` (φ-merge).
* `While`       — Phase 4: `corres_while` via `CorresWhile` over `semScalarWhile`.
* `Ascend`      — the `ascend` tactic + total `ascend_sound` over `IsAscendable`.
* `Capstone`    — word ascent ∘ field split-surjection, end-to-end.
* `CapstoneField` — a real `feSub` subtraction kernel ascending to its `ZMod p` field spec.
* `EmitBridge`   — the core result: an ascent `Corres SRword` result discharges the emit leg
                  (`rustToJasminCom_endToEnd_topLevel_unconditional`), so the emitted jasmin
                  bytes denote to `ctTransTy val` with `wEnc val` the clean `ZMod 2^64` spec;
                  plus the upward welding onto `haxToLowCT_simulates_full` (`evalImp` → bytes).
* `KeystoneControl` — the result extended to `if`/`for` control flow
                  (`ifClosed_hAgree`/`forClosed_hAgree`, `keystone_if`/`keystone_for`).
* `Phases`      — the AutoCorres phase split: `WAPhase` word-abstraction leg
                  (`ringWA`/`wordWA`, `corres_WA`) with `ringWA_not_valid_xor` marking
                  the arithmetic-only boundary the word phase does not cross.
* `RunBlockCorres` — `CorresJ`, a flag-carrying `Corres` over `runBlock`; the
                  subtract-with-borrow leaf `corresJ_sbb` and its add-with-carry dual
                  `corresJ_adc` refine `sbbStep`/`adcStep` through the carry relation
                  `SRcarry`; plus the multi-limb value relation `SRcarryLimbs`
                  (base-2^64 recompose) and the counted-loop combinator `corresJ_loop`.
* `FeSubEndToEnd` — the closed capstone: `feSub_endToEnd` runs the abstraction leg
                  (`feSub_corres : Corres SRwordNT`) into the emit leg via `keystone_emit_NT`,
                  so for the `r := a - b` kernel the emitted jasmin bytes denote to
                  `ctTransTy feVal` with `wEnc feVal` the `ZMod 2^64` subtraction spec;
                  `feSub_source_to_bytes` chains one level up to the source `ImpExpr`.
* `FeSubSourceTower` — `feSub_source_to_bytes_tower` discharges that source-word
                  interface: `feSubSrc_refines` (`RustSubsetToLowCT.lowerRefines`) is the
                  source→LowCT simulation for the `RScalarSetExpr` kernel, and
                  `feSubSourceWord_eq_feVal` identifies the source word with the emitted
                  spec by `decide`.
* `FeAddEndToEnd` — the `r := a + b` capstone: `feAdd_endToEnd` and
                  `feAdd_source_to_bytes_tower` mirror feSub through the shared arithmetic
                  value leaf (`corres_setExpr` over `SAdd`), reusing `keystone_emit_NT`.
* `EcMultiLimbCapstone` — the multi-limb byte-backend vertical: `sbbLimbs_spec` proves the
                  base-2^64 borrow-chain identity, `corresJ_sbbChain` lifts an arbitrary-length
                  `sbb` chain to a `CorresJ SRcarry`, and `feSub4_capstone` is a concrete
                  4-limb (2^256) field-subtract value capstone through `SRcarryLimbs`.
* `PipelineWeld` — `feSub_raw_source_to_bytes` chains hax-lean's `pipeline_correct` on top
                  of the source tower, reaching the raw pre-optimization hax `ImpExpr` (leaving
                  the loop-free/early-exit-free side conditions and the hax↔RustSubset word
                  identification as explicit hypotheses).
* `LoopSourceTower` — the loop/array frontier: `arrKernel_source_to_rustexec` instantiates
                  `haxToLowCT_simulates_full` at an array-store kernel, and records the two
                  gaps that block a full loop/array capstone — no ascent `Corres` leaf for
                  `RArrStore`/`RArrLoad`, and no source `ImpExpr` reaching the bounded-loop leaf.
* `ArrStoreLeaf` — closes the first of those gaps: `corres_arrStore` is the `Corres` value
                  leaf for the dynamic-index array write over `semScalar`, relating the
                  concrete `.memref` slot to an abstract `AArr` update through the `wEnc`
                  intertwining lemma `wEnc_memSetDyn`.
* `ArrStoreEmit` — the array emit result: `keystone_emit_arr` welds `corres_arrStore` to
                  emitted bytes (`translateDialectControl` lowers `RArrStore → memrefSetDyn →
                  jasmin stackStore`; the end-to-end emit theorem is `CryptoTy`-polymorphic, so
                  the `.memref n` output needs no new backend theorem).
* `LoopSourceLeaf` — closes the loop source-preimage gap: `RustSrc.forN` (in the
                  `RustSubsetToLowCT` front) has a defined evaluation and lowers to `RFor`, so
                  `loopSrc_corres` welds `corres_for` to a real source-front bounded loop.
* `EcMultiLimbEmit` — welds the multi-limb `sbb` chain toward bytes: `sbbChain_emit_realizes_fieldSub`
                  proves the abstraction + value legs; the machine-wire leg is the named interface
                  `SbbChainWire`, since `RunBlockLsemAgree` covers ADX `adcx`/`adox` but not `sbb`
                  (`sbb_not_in_subsetM`) — the one leaf to add.
* `CondKernelCapstone` — the control-flow frontier: `condKernel_ascends` is the branch-select
                  `Corres` via `corres_if`, welded to the emit interface by `keystone_if`; the
                  `Com`→jasmin backend declines the branch (`condBackend_declines`: `.ite`/`.bvEq`/`.not`
                  are outside the straight-line fragment), so branches reach bytes only via the
                  separate labelled-branch emitter.

Frontier (= the descent's): the uncovered LowCT arms (`SLt`/`SAsr`/`SMulS`/`SMulHiS`, …)
are excluded because the target dialect lacks the ops — the descent cannot lower them
either; extending them is shared IR/dialect work, after which the ascent follows.
-/
