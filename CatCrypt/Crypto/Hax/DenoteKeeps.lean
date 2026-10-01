/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Phase.InlineLocalClosures

/-!
# A run keeps the names it does not bind

A run of `denote'` on an expression that binds no `x` (`frameOk` with the binding
check `· != x`) and does not end in an error leaves the value of `x` in the
environment unchanged. It is the instance of the frame theorem `denote'_frame` at the
identity renaming.

## Main results

* `denote'_keeps` — a run of an expression that binds no `x` leaves `x` unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr Env Outcome Builtins denote')
open _root_.Hax.InlineLocalClosures (frameOk denote'_frame IsErr)

variable (bi : Builtins)

/-- A run of an expression that binds no `x` and does not err leaves `x` unchanged. -/
theorem denote'_keeps {x : String} (e : ImpExpr)
    (h : frameOk (fun _ => true) (fun n => n != x) (fun _ => true) e = true) (fuel : Nat)
    (env : Env) {o : Outcome} {s : Env} (hr : (denote' bi fuel e).run env = (o, s))
    (ho : ¬ IsErr o) : s x = env x := by
  have := denote'_frame (R := fun e₁ e₂ => e₁ = e₂ ∧ e₂ x = env x) (bi₁ := bi) (bi₂ := bi) id
    (fun _ => true) (fun n => n != x) (fun _ => true)
    (fun e₁ e₂ y hR _ => by rw [hR.1]; rfl)
    (fun e₁ e₂ n w hR hn => ⟨by rw [hR.1], by
      have hne : x ≠ n := fun h' => by simp [h'] at hn
      rw [Env.extend_other _ _ _ _ hne]; exact hR.2⟩)
    (fun _ _ => rfl) e h fuel
  obtain ⟨s₁, _, hs⟩ := this env env ⟨rfl, rfl⟩ o s hr ho
  exact hs.2

end CatCrypt.Crypto.Hax
