/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.LowCTLeakTraceDef
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis

/-!
# The public-guard clauses of `cmdCT`

The analyser `cmdCT` (`LowCTCTAnalysis.lean`) accepts the variable-time
constructors `RIfNz cond _ _` and `RWhileNz cond _` only when the guard `cond`
is `Public`, and `RArrLoad _ _ idx` only when the index `idx` is `Public`.
This module names those two conditions (`guardPublic`, `indexPublic`) and
states each clause of `cmdCT` as an equivalence, with the fail-closed
corollary for a secret branch guard.

It also defines the guard reading `guardBit` and the branch event
`branchEvent` used by the flow-sensitive trace of `LowCTCTFlowSensitive.lean`.

Constant time of a `LowCT` program in the traced semantics `RustExecLeak` is
`CT.LowCTConstantTime` (`CT/LowCTLeakage.lean`), established by the level
checker through `CT.levelCheck_sound` (`CT/LowCTLevelCheck.lean`).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.LowCTVartimeLeak

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTLeakTrace

set_option autoImplicit false

/-! ## §1. The public-guard clauses

`guardPublic`/`indexPublic` state that the guard or index variable is
classified `Public`. The analyser accepts a variable-time construct exactly
when the predicate holds and the sub-programs are accepted; on a `Secret`
guard or index it rejects. -/

/-- The guard `cond` of a branch or loop is classified `Public`. -/
def guardPublic (lt : LevelTable) (cond : String) : Prop := lt cond = .Public

/-- The index variable of an array access is classified `Public`. -/
def indexPublic (lt : LevelTable) (idxVar : String) : Prop := lt idxVar = .Public

/-- **Branch clause.** `cmdCT` accepts `RIfNz cond ct cf` iff the guard is
public and both branches are accepted. -/
theorem cmdCT_RIfNz_iff (cond : String) (ct cf : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RIfNz cond ct cf) lt leafCT = true ↔
      (guardPublic lt cond ∧ cmdCT ct lt leafCT = true ∧ cmdCT cf lt leafCT = true) := by
  simp only [cmdCT_RIfNz, Bool.and_eq_true, guardPublic]
  rw [level_beq_public_iff]
  tauto

/-- **Loop clause.** `cmdCT` accepts `RWhileNz cond body` iff the guard is
public and the body is accepted. -/
theorem cmdCT_RWhileNz_iff (cond : String) (body : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RWhileNz cond body) lt leafCT = true ↔
      (guardPublic lt cond ∧ cmdCT body lt leafCT = true) := by
  simp only [cmdCT_RWhileNz, Bool.and_eq_true, guardPublic]
  rw [level_beq_public_iff]

/-- **Indexed-load clause.** `cmdCT` accepts `RArrLoad dst src idxVar` iff
the index, the destination and the source are public. -/
theorem cmdCT_RArrLoad_iff (dst src : Located) (idxVar : String)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RArrLoad dst src idxVar) lt leafCT = true ↔
      (indexPublic lt idxVar ∧ lt dst.locVar = .Public ∧ lt src.locVar = .Public) := by
  simp only [cmdCT_RArrLoad, Bool.and_eq_true, indexPublic]
  rw [level_beq_public_iff, level_beq_public_iff, level_beq_public_iff, and_assoc]

/-- A secret branch guard is rejected. -/
theorem cmdCT_RIfNz_secret_rejected (cond : String) (ct cf : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (hSecret : lt cond = .Secret) :
    cmdCT (.RIfNz cond ct cf) lt leafCT = false := by
  by_contra h
  simp only [Bool.not_eq_false] at h
  rw [cmdCT_RIfNz_iff] at h
  have := h.1
  unfold guardPublic at this
  rw [hSecret] at this
  exact absurd this (by decide)

/-! ## §2. Guard reading and the branch event -/

/-- The event recording which arm of a branch ran: `"branch:1"` for the true
arm (guard nonzero), `"branch:0"` for the false arm, on the `LeakEvent.pureOp`
carrier. -/
@[simp] def branchEvent (b : Bool) : LeakEvent := .pureOp (if b then "branch:1" else "branch:0")

/-- The scalar guard of a `RIfNz`/`RWhileNz`: nonzero selects the true arm. -/
@[simp] def guardBit (rs : RustState) (cond : String) : Bool := rs.rsScalar cond ≠ 0

end CatCrypt.Crypto.SecureCompilation.LowCTVartimeLeak
