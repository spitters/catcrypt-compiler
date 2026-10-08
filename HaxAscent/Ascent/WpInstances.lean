/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Wp
public import HaxAscent.Ascent.EarlyExit
public import HaxAscent.Ascent.GenRules

/-!
# The derived correspondence judgments as weakest preconditions

Each correspondence judgment built on `Corres` is the weakest precondition of its
expression at a pair of postconditions over the outcome value.

## Main results

* `corresB_iff_wp` — `CorresB` over binding lists
* `corresX_iff_wp` — `CorresX`, whose result is an `Except` of an early exit
* `corresG_iff_wp` — `CorresG`, whose guard selects an early exit
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

variable {bi : Builtins} {S : Type}

/-- **`CorresB` as a weakest precondition.** The postcondition is the value `V σ` with the
    exit bindings `Γ' σ`, at plain and control-flow outcomes alike. -/
theorem corresB_iff_wp {Γ Γ' : S → List (String × Value)} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} :
    CorresB bi Γ G e V Γ' ↔ ∀ σ, G σ → ∀ env, Binds env (Γ σ) →
      wp bi e (fun v s => v = V σ ∧ Binds s (Γ' σ)) (fun v s => v = V σ ∧ Binds s (Γ' σ)) env :=
  corres_iff_wp

/-- The outcome postcondition of an `Except` result: a plain value is the normal result,
    and a control-flow value is either an early exit or a normal result. -/
theorem wpPost_except_iff (r : Except Value Value) (q : Env → Prop) (v : Value) (s : Env) :
    wpPost (fun v s => r = .ok v ∧ q s)
      (fun v s => ((∃ w, r = .error w ∧ v = .controlFlow true w) ∨ r = .ok v) ∧ q s) v s ↔
      v = excVal r ∧ q s := by
  cases hc : v.isControlFlow
  · rw [wpPost_of_plain hc]
    cases r with
    | ok u =>
      constructor
      · rintro ⟨h, hq⟩
        exact ⟨(Except.ok.inj h).symm, hq⟩
      · rintro ⟨rfl, hq⟩
        exact ⟨rfl, hq⟩
    | error w =>
      refine ⟨fun ⟨h, _⟩ => (nomatch h), fun ⟨h, _⟩ => ?_⟩
      subst h
      simp [excVal, Value.isControlFlow] at hc
  · rw [wpPost_of_cf hc]
    cases r with
    | ok u =>
      refine ⟨fun ⟨h, hq⟩ => ?_, fun ⟨h, hq⟩ => ⟨Or.inr (h ▸ rfl), hq⟩⟩
      rcases h with ⟨w, h, _⟩ | h
      · exact nomatch h
      · exact ⟨(Except.ok.inj h).symm, hq⟩
    | error w =>
      refine ⟨fun ⟨h, hq⟩ => ?_, fun ⟨h, hq⟩ => ⟨Or.inl ⟨w, rfl, h⟩, hq⟩⟩
      rcases h with ⟨w', h, hv⟩ | h
      · cases h
        exact ⟨hv, hq⟩
      · exact nomatch h

/-- **`CorresX` as a weakest precondition.** A plain outcome is the normal result `R σ`;
    a control-flow outcome is the early exit `controlFlow true w` of `R σ = .error w`, or a
    normal result that is itself a control-flow value. -/
theorem corresX_iff_wp {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {R : S → Except Value Value} :
    CorresX bi P G e R Q ↔ ∀ σ, G σ → ∀ env, P env σ →
      wp bi e (fun v s => R σ = .ok v ∧ Q s σ)
        (fun v s => ((∃ w, R σ = .error w ∧ v = .controlFlow true w) ∨ R σ = .ok v) ∧ Q s σ)
        env := by
  unfold CorresX
  rw [corres_iff_wp]
  refine forall_congr' fun σ => forall_congr' fun _ => forall_congr' fun env =>
    forall_congr' fun _ => wp_congr fun v s => ?_
  rw [wpPost_self]
  exact (wpPost_except_iff (R σ) (fun s => Q s σ) v s).symm

/-- **`CorresG` as a weakest precondition.** A plain outcome is the value `V σ` with the
    bindings `N σ` when the guard `C σ` is off; a control-flow outcome is the early exit
    `controlFlow true (W σ)` with the bindings `T σ` when the guard is on, or the value
    `V σ` with the bindings `N σ` when it is off. -/
theorem corresG_iff_wp {Γ N T : S → BList} {G : S → Prop} {e : ImpExpr} {C : S → Bool}
    {W V : S → Value} :
    CorresG bi Γ G e C W V T N ↔ ∀ σ, G σ → ∀ env, Binds env (Γ σ) →
      wp bi e (fun v s => C σ = false ∧ v = V σ ∧ Binds s (N σ))
        (fun v s => (C σ = true ∧ v = .controlFlow true (W σ) ∧ Binds s (T σ)) ∨
          (C σ = false ∧ v = V σ ∧ Binds s (N σ))) env := by
  unfold CorresG
  rw [corresB_iff_wp]
  refine forall_congr' fun σ => forall_congr' fun _ => forall_congr' fun env =>
    forall_congr' fun _ => wp_congr fun v s => ?_
  rw [wpPost_self]
  cases hc : v.isControlFlow
  · rw [wpPost_of_plain hc]
    cases hC : C σ
    · simp only [Bool.false_eq_true, if_false, true_and]
    · simp only [if_true, Bool.true_eq_false, false_and, iff_false, not_and]
      rintro rfl
      simp [Value.isControlFlow] at hc
  · rw [wpPost_of_cf hc]
    cases hC : C σ
    · simp only [Bool.false_eq_true, if_false, false_and, true_and, false_or]
    · simp only [if_true, Bool.true_eq_false, false_and, true_and, or_false]

end Hax.Ascent
