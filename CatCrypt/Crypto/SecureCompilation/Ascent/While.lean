/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileDenote


@[expose] public section
set_option autoImplicit false

/-!
# The ascent `while` rule for `RWhileNz`

The base `Corres` (`Ascent/Corres.lean`) is stated over the compositional
denotation `semScalar`.  But `semScalar` has **no** `RWhileNz` arm — it hits the
catch-all `| _, _ => none` — so a `Corres`-over-`semScalar` loop rule would be
vacuous: the guard-driven back-edge is not modeled at the `semScalar` waist.

The while loop denotes through the SEPARATE transformer layer of
`TranslateDialectWhileDenote`:

* `semWhileIter (semScalar body) k` — the clean unconditional `k`-fold body
  iteration (the `semRForD` twin; peels the LAST trip);
* `semScalarWhile (semScalar body) guard fuel` — the guard-driven fuel-indexed
  do-while;
* `semScalarWhile_eq_iter` — the fuel/termination bridge: a run halting within
  `fuel` equals `semWhileIter` at the trip count read off the run.

So this module defines a `Corres` VARIANT stated against `semWhileIter` (the
clean `k`-fold layer) and proves the loop rule there:

* `CorresWhile SR P fb body` — forward simulation of the `k`-fold body iteration
  by the `k`-fold abstract iterate `kfold fb k`;
* `corres_while_iter` — from the body's one-step `Corres SR P fb body` plus a
  precondition invariant `∀ a, P a → P (fb a)`, derive `CorresWhile` by
  induction on the trip index `k` (the per-step obligation is exactly the body's
  `Corres`, mirroring the trip induction of `corres_for`);
* `corres_while` — the loop rule on the ACTUAL fuel-run: given termination
  within `fuel`, `semScalarWhile_eq_iter` reduces it to `corres_while_iter` at
  the run's read-off trip count.

`kfold` mirrors `semWhileIter`'s last-trip peeling exactly, so the trip-index
induction closes in lock-step.

**0 sorries; no axioms beyond the front's existing set.**
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-! ## The abstract iterate `kfold` (the `semWhileIter` twin) -/

/-- `k`-fold application of the abstract step `fb`, peeling the LAST application
    to match `semWhileIter`'s recursion (`n+1 ↦ semBody (semWhileIter n)`).  So
    `kfold fb (n+1) a = fb (kfold fb n a)`, in lock-step with the concrete
    `k`-fold body iteration. -/
def kfold {A : Type} (fb : A → A) : Nat → A → A
  | 0, a => a
  | n + 1, a => fb (kfold fb n a)

/-- The abstract iterate preserves any `fb`-invariant precondition. -/
theorem kfold_pres {A : Type} {P : A → Prop} {fb : A → A}
    (hinv : ∀ a, P a → P (fb a)) : ∀ (k : Nat) (a : A), P a → P (kfold fb k a)
  | 0, _, ha => ha
  | n + 1, a, ha => hinv _ (kfold_pres hinv n a ha)

/-! ## The `Corres` variant over the clean `k`-fold layer -/

variable {AState : Type} (SR : SEnvScalar → AState → Prop)

/-- `CorresWhile SR P fb body`: forward simulation of the loop region against the
    clean `k`-fold body iteration `semWhileIter (semScalar body)`.  From a
    concrete `SEnvScalar` related by `SR` to an abstract state satisfying `P`,
    every `k`-fold run of the body (that makes progress) lands related to the
    `k`-fold abstract iterate `kfold fb k`.  This is the correct waist for the
    loop rule: `semScalar` itself has no `RWhileNz` arm, so the loop is modeled
    through `semWhileIter`, not `semScalar (.RWhileNz …)`. -/
def CorresWhile (P : AState → Prop) (fb : AState → AState) (body : LowCT) : Prop :=
  ∀ env a k env', SR env a → P a →
    semWhileIter (fun e => semScalar body e) k env = some env' → SR env' (kfold fb k a)

/-- **The `while` rule on the clean `k`-fold layer.**  From the body's one-step
    `Corres SR P fb body` and the precondition invariant `∀ a, P a → P (fb a)`,
    the loop simulates: `CorresWhile SR P fb body`.  Proved by induction on the
    trip index `k`; the per-step obligation is exactly the body's `Corres`
    applied at the abstract state `kfold fb k a` (whose `P` follows from
    `kfold_pres`).  This mirrors the trip induction of the counted-loop rule. -/
theorem corres_while_iter {P : AState → Prop} {fb : AState → AState} {body : LowCT}
    (hbody : Corres SR P fb body) (hinv : ∀ a, P a → P (fb a)) :
    CorresWhile SR P fb body := by
  intro env a k env' hSR hP
  induction k generalizing env' with
  | zero =>
      intro hrun
      simp only [semWhileIter] at hrun
      obtain rfl := Option.some.inj hrun
      simpa only [kfold] using hSR
  | succ n ih =>
      intro hrun
      simp only [semWhileIter] at hrun
      rcases hpre : semWhileIter (fun e => semScalar body e) n env with _ | envPre
      · rw [hpre] at hrun; simp at hrun
      · rw [hpre] at hrun
        simp only at hrun
        -- IH: envPre is related to the n-fold abstract iterate.
        have hSRpre : SR envPre (kfold fb n a) := ih envPre hpre
        -- P holds at the n-fold abstract iterate.
        have hPpre : P (kfold fb n a) := kfold_pres hinv n a hP
        -- The body's one-step Corres closes the last trip.
        obtain ⟨env'', hstep, hSR''⟩ := hbody envPre (kfold fb n a) hSRpre hPpre
        rw [hstep] at hrun
        obtain rfl := Option.some.inj hrun
        simpa only [kfold] using hSR''

/-! ## The loop rule on the actual fuel-run -/

/-- **The ascent `while` rule for `RWhileNz`** on the real guard-driven do-while
    run.  For a body with a one-step `Corres SR P fb body` and a `P`-invariant
    step, any guard-driven run that terminates within `fuel` lands related to the
    abstract iterate at the trip count `scalarWhileTrips … fuel env` read off the
    run.  The fuel/termination hypothesis is discharged through
    `semScalarWhile_eq_iter`, reducing to `corres_while_iter` on the clean
    `k`-fold layer. -/
theorem corres_while {P : AState → Prop} {fb : AState → AState} {body : LowCT}
    (hbody : Corres SR P fb body) (hinv : ∀ a, P a → P (fb a))
    (guard : SEnvScalar → Bool) (fuel : Nat)
    (env : SEnvScalar) (a : AState) (env' : SEnvScalar)
    (hSR : SR env a) (hP : P a)
    (hrun : semScalarWhile (fun e => semScalar body e) guard fuel env = some env') :
    SR env' (kfold fb (scalarWhileTrips (fun e => semScalar body e) guard fuel env) a) :=
  corres_while_iter SR hbody hinv env a
    (scalarWhileTrips (fun e => semScalar body e) guard fuel env) env' hSR hP
    (semScalarWhile_eq_iter (fun e => semScalar body e) guard fuel env env' hrun)

end CatCrypt.Crypto.SecureCompilation.Ascent
