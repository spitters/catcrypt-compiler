/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.TranslationValidation
public import CatCrypt.Crypto.Optimizer.SchedulerPass

/-!
# Schedule-aware translation validation (#591 continuation)

This file **broadens** the verified translation-validation (TV) checker so that,
in addition to the relations the base `tvCheck`
(`CatCrypt.Crypto.Optimizer.TranslationValidation`) already certifies, an
*untrusted* optimizer oracle's output is also accepted when that output is a
**dependence-respecting instruction schedule** of the input — the `#525`/`#593`
`scheduleBlock` pass (`CatCrypt.Crypto.Optimizer.SchedulerPass`), whose
`scheduleBlock_denote_eq` already proves semantics preservation against the
big-step `RustExec` semantics.

## The representation split

The base checker `tvCheck` is decidable structural/peephole equivalence over the
typed VIR `Com jasminDialect Γ t`, and its soundness `tvCheck_sound` is phrased
over `Com.denote`.  The scheduler `scheduleBlock`, by contrast, operates over a
basic block `List BBStmt` lowered to `LowCT` by `blockToCmd`, and its soundness
`scheduleBlock_denote_eq` is phrased over the big-step relation `RustExec` of
`blockToCmd`.  `Com jasminDialect` and `LowCT` are *distinct* inductive
families with *distinct* denotation notions, so a single Boolean disjunction
cannot literally range over both — there is no shared candidate type.

Following the project guidance ("if they operate on different representations,
state `tvCheckSched` at the representation that makes the soundness composition
clean"), we state `tvCheckSched` at the **`List BBStmt`** representation, where
the scheduler lives.  Each accepted arm carries its own soundness lemma and the
two compose:

* **identity arm** — `b' = b` (the optimizer returned its input unchanged); this
  is the block-level analogue of `tvCheck`'s first disjunct (`comEqB c c'`,
  "candidate is structurally the input").  Soundness is reflexivity of `RustExec`
  equivalence.
* **schedule arm** — `b' = scheduleBlock b` (the optimizer returned a
  latency-aware list schedule).  Soundness is exactly `scheduleBlock_denote_eq`.

The base `tvCheck`/`tvCheck_sound` over `Com` is re-exported unchanged
(`tvCheckSched_subsumes_tvCheck`): the broadening adds the scheduling arm
*alongside* the existing checker without touching its TCB.

## What is proved

* `tvCheckSched_sound` — the headline: `tvCheckSched b b' = true →`
  `(RustExec N leafSpec (blockToCmd b') rs rs' ↔ RustExec N leafSpec`
  `(blockToCmd b) rs rs')`.  Composes the identity-arm reflexivity with
  `scheduleBlock_denote_eq`.  **Incomplete** (only this conservative relation is
  certified) but **never unsound**: it never certifies a candidate that changes
  the denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.TranslationValidationSched

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Optimizer.SchedulerPass
open CatCrypt.Crypto.Optimizer.TranslationValidation

/-! ## §1  Decidable equality for blocks

`Located` already has `DecidableEq`; `SExpr` and `BBStmt` do not (they only
`deriving Repr, Inhabited`).  We derive `DecidableEq` for both so that the two
checker arms (`b' = b`, `b' = scheduleBlock b`) are `decide`-able Booleans — the
whole point of a *checker* is that its verdict is computable. -/

deriving instance DecidableEq for CatCrypt.Crypto.Jasmin.LowCT.SExpr
deriving instance DecidableEq for BBStmt

/-! ## §2  The schedule-aware TV checker -/

/-- **The schedule-aware TV checker.**  Accepts the candidate block `b'`
(output of an untrusted optimizer oracle) against the input block `b` when `b'`
is *either* structurally `b` itself (the optimizer returned its input unchanged
— the block-level analogue of `tvCheck`'s identity disjunct) *or* the verified
latency-aware schedule `scheduleBlock b`.  Returns `true` only on a relation that
`tvCheckSched_sound` proves implies `RustExec`-equivalence of the lowered
programs.  Decidable, hence executable as a checker. -/
def tvCheckSched (b b' : List BBStmt) : Bool :=
  decide (b' = b) || decide (b' = scheduleBlock b)

/-! ## §3  Soundness -/

/-- **Soundness of the schedule-aware TV checker (#591 continuation).**  If
`tvCheckSched b b' = true`, the candidate block `b'` lowers to a program that
reaches exactly the same final states as the input `b` under the big-step
`RustExec` semantics, for every leaf spec and start state.  The optimizer that
produced `b'` is *not* trusted: this theorem certifies the candidate purely from
the checker's `true` verdict, by composing the identity-arm reflexivity with the
verified `SchedulerPass.scheduleBlock_denote_eq`.  Incomplete (only the
conservative relation is accepted) but never unsound. -/
theorem tvCheckSched_sound (N : Nat) (leafSpec : LeafSpec)
    (b b' : List BBStmt) (h : tvCheckSched b b' = true)
    (rs rs' : RustState) :
    RustExec N leafSpec (blockToCmd b') rs rs'
  ↔ RustExec N leafSpec (blockToCmd b) rs rs' := by
  simp only [tvCheckSched, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · -- identity arm: candidate is the input unchanged
    subst h; exact Iff.rfl
  · -- schedule arm: candidate is the verified latency schedule of the input
    subst h; exact scheduleBlock_denote_eq N leafSpec b rs rs'

/-! ## §4  The base `Com`-level checker is subsumed unchanged

The broadening adds the scheduling arm *alongside* the existing `tvCheck` over
`Com jasminDialect`; it does not weaken or replace it.  We re-export the base
soundness so both checkers are available from this module. -/

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- The base TV checker's soundness still holds verbatim: `tvCheckSched` extends
the accepted relation but leaves `tvCheck`'s `Com`-level guarantee intact.  This
is a thin re-export of `TranslationValidation.tvCheck_sound`, kept here so a
caller wiring the broadened checker sees both arms from one module. -/
theorem tvCheckSched_subsumes_tvCheck {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c c' : Com jasminDialect Γ t) (h : tvCheck c c' = true) :
    ∀ V : Ctxt.Valuation Γ, c'.denote V = c.denote V :=
  tvCheck_sound c c' h

/-! ## §5  Self-contained validation

Two demos exercising both arms of the schedule-aware checker on a concrete
two-statement independent block. -/

/-- A concrete independent block: `a := 1` then `b := 2`.  The two scalar writes
target distinct vars and read no shared var, so they are independent and the
scheduler may reorder them. -/
def demoBlock : List BBStmt :=
  [BBStmt.sset "a" (.SLit 1), BBStmt.sset "b" (.SLit 2)]

/-- **Accept (identity arm).**  The optimizer that returns its input unchanged is
certified. -/
example : tvCheckSched demoBlock demoBlock = true := by
  simp only [tvCheckSched, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl trivial

/-- **Accept (schedule arm).**  A candidate equal to the verified schedule of the
input is certified. -/
example : tvCheckSched demoBlock (scheduleBlock demoBlock) = true := by
  simp only [tvCheckSched, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr trivial

/-- The accepted schedule candidate genuinely denotes the same function as the
input under `RustExec` — the soundness theorem applied to the demo. -/
example (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState) :
    RustExec N leafSpec (blockToCmd (scheduleBlock demoBlock)) rs rs'
  ↔ RustExec N leafSpec (blockToCmd demoBlock) rs rs' :=
  tvCheckSched_sound N leafSpec demoBlock _
    (by simp only [tvCheckSched, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr trivial) rs rs'

/-- Smoke check: the module builds and its obligations close. -/
theorem tvSched_compiles : True := trivial

end CatCrypt.Crypto.Optimizer.TranslationValidationSched
