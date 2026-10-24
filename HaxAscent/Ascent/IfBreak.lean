/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.EarlyExit

/-!
# Guarded early returns

The pipeline encodes a Rust `if c { return w; }` followed by the rest `k` of a function as
`seq (ifThenElse c (seq (cfBreak (lit w)) unitVal) unitVal) k`. `ifBreak c w` is the
conditional, and `corresX_seq_ifBreak` states the exception-level correspondence of the
sequence: the thrown `w` when the condition holds, the result of `k` otherwise. The
condition is read without changing the bindings.

## Main results

* `corresX_ifBreak` — the conditional throws `w` or returns `.unit`
* `corresX_seq_ifBreak` — the conditional followed by `k`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-- The guarded early return `if c then (return w; ()) else ()`. -/
def ifBreak (c : ImpExpr) (w : ImpLit) : ImpExpr :=
  .ifThenElse c (.seq (.cfBreak (.lit w)) .unitVal) .unitVal

theorem ofLit_isControlFlow (w : ImpLit) : (Value.ofLit w).isControlFlow = false := by
  cases w <;> rfl

variable {S : Type} {bi : Builtins}

/-- **The guarded early return.** With a condition that returns `.bool (C σ)` and keeps
    the relation `P`, the conditional throws `w` when `C σ` holds and returns `.unit`
    otherwise. -/
theorem corresX_ifBreak {P : Env → S → Prop} {G : S → Prop} {c : ImpExpr} {C : S → Bool}
    (hc : Corres bi P G c (fun σ => .bool (C σ)) P) (w : ImpLit) :
    CorresX bi P G (ifBreak c w)
      (fun σ => if C σ = true then .error (Value.ofLit w) else .ok .unit) P := by
  refine corresX_ifThenElse hc ?_ ?_
  · have h := corresX_seq (bi := bi)
      (corresX_throw (corres_lit P (fun σ => G σ ∧ C σ = true) w)
        fun _ _ => ofLit_isControlFlow w)
      (fun _ _ _ h => nomatch h) (corresX_of_corres (corres_unitVal P _))
    refine corresX_conseq h (fun _ _ h _ => h) (fun _ h => h) (fun σ hG => ?_)
      (fun _ _ _ h => h)
    rw [ite_eq_left hG.2]
    rfl
  · refine corresX_conseq (corresX_of_corres (corres_unitVal P _)) (fun _ _ h _ => h)
      (fun _ h => h) (fun σ hG => ?_) (fun _ _ _ h => h)
    rw [ite_eq_right (by rw [hG.2]; decide)]

/-- **A guarded early return followed by `k`.** -/
theorem corresX_seq_ifBreak {P Q : Env → S → Prop} {G : S → Prop} {c k : ImpExpr}
    {C : S → Bool} {w : ImpLit} {R : S → Except Value Value}
    (hc : Corres bi P G c (fun σ => .bool (C σ)) P)
    (hk : CorresX bi P (fun σ => G σ ∧ C σ = false) k R Q) :
    CorresX bi P G (.seq (ifBreak c w) k)
      (fun σ => if C σ = true then .error (Value.ofLit w) else R σ)
      (fun env σ => if C σ = true then P env σ else Q env σ) := by
  have hfalse : ∀ σ, G σ ∧ (∃ v, (if C σ = true then Except.error (Value.ofLit w)
      else Except.ok Value.unit) = Except.ok v) → G σ ∧ C σ = false := by
    intro σ ⟨hG, v, hv⟩
    refine ⟨hG, ?_⟩
    cases hC : C σ
    · rfl
    · rw [hC, ite_eq_left rfl] at hv
      cases hv
  have h := corresX_seq (corresX_ifBreak hc w)
    (fun σ v _ h => by
      split at h
      · cases h
      · cases h; rfl)
    (corresX_conseq hk (fun _ _ h _ => h) hfalse (fun _ _ => rfl) (fun _ _ _ h => h))
  refine corresX_conseq h (fun _ _ h _ => h) (fun _ h => h) (fun σ _ => ?_) (fun env σ _ h => ?_)
  · cases C σ <;> rfl
  · unfold excExit at h
    cases hC : C σ <;> simp only [hC] at h ⊢ <;> exact h

end Hax.Ascent
