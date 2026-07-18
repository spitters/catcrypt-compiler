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
* `EmitBridge`   — the keystone: an ascent `Corres SRword` result discharges the emit leg
                  (`rustToJasminCom_endToEnd_topLevel_unconditional`), so the emitted jasmin
                  bytes denote to `ctTransTy val` with `wEnc val` the clean `ZMod 2^64` spec;
                  plus the upward welding onto `haxToLowCT_simulates_full` (`evalImp` → bytes).

Frontier (= the descent's): the uncovered LowCT arms (`SLt`/`SAsr`/`SMulS`/`SMulHiS`, …)
are excluded because the target dialect lacks the ops — the descent cannot lower them
either; extending them is shared IR/dialect work, after which the ascent follows.
-/
