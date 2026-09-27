/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTSyntax


@[expose] public section
set_option autoImplicit false

/-!
# Phase J.1 — Information-Flow Propagation Rules for LowCT

This file lands the propagation rules consumed by a constant-time (CT)
analyser on top of the `LevelTable : String → SecretLevel` lookup
introduced in Phase J (`CatCrypt/Crypto/Jasmin/LowCT.lean`).

The core predicate `infoFlowOk : LevelTable → LowCT → Bool` rejects
**secret-dependent control flow** — i.e. branches and loops whose
condition variable is classified `.Secret`.  All other constructors
recurse into their body sub-terms; leaf constructors (`RSkip`,
`RScalarSet`, `RCall`, …) trivially return `true` since they do not
introduce secret-dependent control flow.

This is the pre-condition consumed by the larger CT analyser stack:
* If `infoFlowOk lt c = true`, the program is free of secret-dependent
  control flow under classification `lt`.  (The remaining CT
  obligations — secret-indexed memory access, etc. — are layered on
  top via separate predicates.)
* If `infoFlowOk lt c = false`, at least one `RIfNz` / `RWhileNz` site
  branches on a `.Secret` classified scalar, and the analyser must
  report it.

## Helper definitions

In addition to `LevelTable.allPublic` (already defined in
`LowCT.lean`), this file provides:
* `LevelTable.set` — pointwise update at a single variable.
* `LevelTable.markSecret` — mark a list of variables as `.Secret`.

These are convenience builders for assembling CT classifications
without writing full lambdas at every call site.

## References

* Phase J (2026-05-03) — `LevelTable` lookup added to LowCT.
* CT analyser scaffolding — `CatCrypt/Crypto/SecureCompilation/LowCTCT.lean`.
-/

namespace CatCrypt.Crypto.Jasmin.LowCT.InfoFlow

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  Helper builders for `LevelTable` -/

/-- Pointwise update: `LevelTable.set lt x l` returns a level table
    that agrees with `lt` everywhere except at `x`, where it returns
    `l`.  Used to incrementally build a classification: start from
    `LevelTable.allPublic` and `set` the secret slots. -/
def _root_.CatCrypt.Crypto.Jasmin.LowCT.LevelTable.set
    (lt : LevelTable) (x : String) (l : SecretLevel) : LevelTable :=
  fun y => if y = x then l else lt y

/-- Mark a list of variables `.Secret` on top of an existing level
    table.  Variables outside `xs` are left untouched. -/
def _root_.CatCrypt.Crypto.Jasmin.LowCT.LevelTable.markSecret
    (lt : LevelTable) (xs : List String) : LevelTable :=
  fun y => if y ∈ xs then SecretLevel.Secret else lt y

/-! ## §2  The `infoFlowOk` predicate -/

/-- **Phase J.1 — secret-dependent control-flow rejector.**

    Returns `true` iff the program contains no `RIfNz`/`RWhileNz`
    whose condition variable is classified `.Secret` under `lt`.

    Recurses into all body subterms (`RSeq`, `RLetZero`, `RLetU64Zero`,
    both arms of `RIfNz`, the body of `RFor`, `RBlock`, `RFnDef`).
    Leaf constructors (`RSkip`, `RScalarSet`, `RCall`, `RCallSwap`,
    `RCloneCall`, `RLimbStore`, `RCallN`, `RSelect`, `RAssert`,
    `RFnCall`, `RTupleLoad`, `RArrStore`, `RArrLoad`,
    `RScalarSetExpr`) return `true`. -/
def infoFlowOk (lt : LevelTable) : LowCT → Bool
  | .RSkip                       => true
  | .RSeq c1 c2                  => infoFlowOk lt c1 && infoFlowOk lt c2
  | .RLetZero _ _ body           => infoFlowOk lt body
  | .RLetU64Zero _ body          => infoFlowOk lt body
  | .RScalarSet _ _              => true
  | .RCall _ _ _                 => true
  | .RCallSwap _ _ _ _           => true
  | .RCloneCall _ _ _ _ _ _      => true
  | .RIfNz cond thn els          =>
      match lt cond with
      | .Secret => false
      | .Public => infoFlowOk lt thn && infoFlowOk lt els
  | .RWhileNz cond body          =>
      match lt cond with
      | .Secret => false
      | .Public => infoFlowOk lt body
  | .RFor _ _ body               => infoFlowOk lt body
  | .RLimbStore _ _ _            => true
  | .RLimbStoreExpr _ _ _        => true
  | .RCallN _ _ _                => true
  | .RSelect _ _ _ _             => true
  | .RAssert _                   => true
  | .RBlock body                 => infoFlowOk lt body
  | .RFnDef _ _ _ body cont      => infoFlowOk lt body && infoFlowOk lt cont
  | .RFnCall _ _ _               => true
  | .RTupleLoad _ _ _            => true
  -- Phase Ext (2026-05-12) / Ext2 (2026-05-13): no control-flow.
  | .RArrStore _ _ _             => true
  | .RArrLoad _ _ _              => true
  -- Phase DD (2026-05-28): literal-index array load/store — constant-time
  -- by construction (idx is compile-time, no scalar dependency).
  | .RArrStoreLit _ _ _          => true
  | .RArrLoadLit _ _ _           => true
  | .RScalarSetExpr _ _          => true
  | .RCallDstThreaded _ _ _      => true
  | .RForRuntime _ _ body        => infoFlowOk lt body

/-! ## §3  Characterisation lemma -/

/-- Characterisation: `infoFlowOk` returns `false` on `RIfNz e t f` iff
    either the condition is `.Secret`, or one of the arms itself fails
    the check.  This is the core propagation rule consumed by the CT
    analyser. -/
theorem infoFlowOk_RIfNz_secret_iff
    (lt : LevelTable) (e : String) (t f : LowCT) :
    infoFlowOk lt (.RIfNz e t f) = false ↔
      lt e = .Secret ∨ ¬ infoFlowOk lt t ∨ ¬ infoFlowOk lt f := by
  show (match lt e with
        | .Secret => false
        | .Public => infoFlowOk lt t && infoFlowOk lt f) = false ↔ _
  cases hLevel : lt e with
  | Public =>
    simp only []
    cases infoFlowOk lt t <;> cases infoFlowOk lt f <;> simp
  | Secret =>
    simp

/-! ## §4  Smoke tests -/

/-- A program with no branches passes `infoFlowOk` under any
    classification.  Smoke test 1: pure straight-line code. -/
example (lt : LevelTable) :
    infoFlowOk lt
      (.RSeq (.RScalarSet "x" 7)
        (.RSeq (.RScalarSet "y" 3) .RSkip)) = true := by
  rfl

/-- An `RIfNz` branching on a variable classified `.Secret` is
    rejected (returns `false`).  Smoke test 2: secret-dependent
    branch. -/
example :
    let lt : LevelTable := LevelTable.allPublic.set "secret_cond" .Secret
    infoFlowOk lt (.RIfNz "secret_cond" .RSkip .RSkip) = false := by
  rfl

/-- The same `RIfNz` with the condition variable left at `.Public`
    passes.  Smoke test 3: the classification decides the result. -/
example :
    let lt : LevelTable := LevelTable.allPublic
    infoFlowOk lt (.RIfNz "public_cond" .RSkip .RSkip) = true := by
  rfl

/-- A nested program: an outer `RBlock` containing an inner secret
    branch is rejected — the recursive walk catches the inner site. -/
example :
    let lt : LevelTable := LevelTable.allPublic.set "leak" .Secret
    infoFlowOk lt
      (.RBlock (.RSeq (.RScalarSet "x" 1)
        (.RIfNz "leak" .RSkip .RSkip))) = false := by
  rfl

/-- `markSecret` correctly classifies a list of variables: a branch
    on any of them is rejected. -/
example :
    let lt : LevelTable :=
      LevelTable.allPublic.markSecret ["k1", "k2", "k3"]
    infoFlowOk lt (.RIfNz "k2" .RSkip .RSkip) = false := by
  rfl

end CatCrypt.Crypto.Jasmin.LowCT.InfoFlow
