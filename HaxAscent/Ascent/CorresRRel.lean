/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Wp
public import CatCryptCore.Refinement.Programs

/-!
# The source correspondence `Corres` as a relational refinement `RRelPT`

`Corres bi P G e V Q` (`Ascent/Corres.lean`) states that the run of `e` from an
environment related by `P` to an abstract state `σ` with `G σ` eventually returns
`V σ` in an environment related by `Q` to `σ`. This module states it as the
relational refinement `RRelPT` of `CatCryptCore/Refinement/RRel.lean` between the
weakest precondition of the abstract program `guardProg`
(`CatCryptCore/Refinement/Programs.lean`) and the weakest precondition of `e`.

* `wpA bi e Φ Ψ` is `wp bi e` (`Ascent/Wp.lean`) at `Assertion (.arg Env .pure)`; the
  second argument `Ψ` is the postcondition of control-flow values.
* `wpAT bi e` is `wpA bi e` over tagged environments `Env ⊕ Env`: `.inl env` is an
  environment before the run and `.inr env` one after it. A relation between tagged
  environments carries one relation for entry environments and another for exit
  environments, so a simulation with distinct entry and exit relations is one
  `AssnRel.ofRel`.
* The abstract state space is `S ⊕ S`: `.inl σ` is the state `σ` before the run and
  `.inr σ` the state `σ` after it. The abstract program of `Corres` is
  `guardProg G (fun σ => valExc (V σ))`: it returns a plain `V σ` and raises a
  control-flow `V σ`.

## Main definitions

* `wpA`, `wpAT`: the weakest precondition of `ImpExpr` as an `Assertion` transformer,
  over environments and over tagged environments.
* `valExc`: a value read as an `Except`, raising control-flow values.

## Main results

* `guardProg_rrelPT_wpA_iff`: `RRelPT` between `guardProg G f` and `wpA bi e` is the
  triple whose postconditions name the result of `f`.
* `corres_iff_rrelPT`, `corres_iff_rrelPT_wpAT`: `Corres bi P G e V Q` is `RRelPT`
  between `guardProg G (valExc ∘ V)` and `wpA bi e` (resp. `wpAT bi e`).
* `rrelPT_wpAT_of_sim`: a fuel-uniform simulation of `e` by `e'` from an entry relation
  to an exit relation is a refinement of `wpAT bi e` by `wpAT bi e'`.
* `corres_trans_of_rrelPT`: a correspondence for `e` and a refinement of `wpAT bi e` by
  `wpAT bi e'` give the correspondence for `e'` at the composite relations, by
  `RRelPT.trans`.
* `corres_of_fuelSim_via_rrel`: transport of `Corres` along a fuel-uniform simulation,
  derived from `rrelPT_wpAT_of_sim` and `corres_trans_of_rrelPT`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

open Std.Do
open CatCrypt.Refinement

variable {bi : Builtins} {S : Type}

/-! ## The weakest precondition as an assertion transformer -/

variable (bi) in
/-- The weakest precondition `wp bi e` as a transformer of assertions over `Env`: `Φ`
    is the postcondition of plain values and `Ψ` that of control-flow values. -/
def wpA (e : ImpExpr) (Φ Ψ : Value → Assertion (.arg Env .pure)) :
    Assertion (.arg Env .pure) :=
  fun env => ⌜wp bi e (fun v s => (Φ v s).down) (fun v s => (Ψ v s).down) env⌝

theorem wpA_apply {e : ImpExpr} {Φ Ψ : Value → Assertion (.arg Env .pure)} {env : Env} :
    (wpA bi e Φ Ψ env).down ↔ wp bi e (fun v s => (Φ v s).down) (fun v s => (Ψ v s).down) env :=
  Iff.rfl

/-- At pure postconditions `wpA` is the pure assertion of `wp`. -/
theorem wpA_pure {e : ImpExpr} {Φ Ψ : Value → Env → Prop} :
    wpA bi e (fun v s => ⌜Φ v s⌝) (fun v s => ⌜Ψ v s⌝) = fun env => ⌜wp bi e Φ Ψ env⌝ :=
  rfl

/-- **Monotonicity** of `wpA` in both postconditions. -/
theorem wpA_mono {e : ImpExpr} {Φ Ψ Φ' Ψ' : Value → Assertion (.arg Env .pure)}
    (hΦ : ∀ v, Φ v ⊢ₛ Φ' v) (hΨ : ∀ v, Ψ v ⊢ₛ Ψ' v) : wpA bi e Φ Ψ ⊢ₛ wpA bi e Φ' Ψ' :=
  fun _ h => wp_mono h (fun v s _ => hΦ v s) (fun v s _ => hΨ v s)

variable (bi) in
/-- The weakest precondition `wpA bi e` over tagged environments: an entry environment
    `.inl env` satisfies it when `wpA bi e` holds at `env` with both postconditions
    read at the exit environment `.inr env'`; an exit environment satisfies nothing. -/
def wpAT (e : ImpExpr) (Φ Ψ : Value → Assertion (.arg (Env ⊕ Env) .pure)) :
    Assertion (.arg (Env ⊕ Env) .pure) :=
  Sum.elim (wpA bi e (fun v s => Φ v (.inr s)) (fun v s => Ψ v (.inr s))) fun _ => ⌜False⌝

/-- **Monotonicity** of `wpAT` in both postconditions. -/
theorem wpAT_mono {e : ImpExpr} {Φ Ψ Φ' Ψ' : Value → Assertion (.arg (Env ⊕ Env) .pure)}
    (hΦ : ∀ v, Φ v ⊢ₛ Φ' v) (hΨ : ∀ v, Ψ v ⊢ₛ Ψ' v) : wpAT bi e Φ Ψ ⊢ₛ wpAT bi e Φ' Ψ' :=
  fun x => match x with
  | .inl env => wpA_mono (fun v s => hΦ v (.inr s)) (fun v s => hΨ v (.inr s)) env
  | .inr _ => fun h => False.elim h

/-! ## The abstract program of a correspondence -/

/-- A value read as an `Except`: a control-flow value is raised and a plain value
    returned. -/
def valExc (v : Value) : Except Value Value :=
  if v.isControlFlow = true then .error v else .ok v

theorem valExc_eq_ok {v b : Value} (h : valExc v = .ok b) : b = v := by
  unfold valExc at h
  split at h <;> cases h
  rfl

theorem valExc_eq_error {v r : Value} (h : valExc v = .error r) : r = v := by
  unfold valExc at h
  split at h <;> cases h
  rfl

/-- **`RRelPT` from a guarded function.** The refinement of `guardProg G f` by `wpA bi e`
    at the assertion map of `entryExitRel P Q`, the value relation `Rv` and `GuardRE` is
    the triple: under the guard, from an environment related by `P`, the run of `e`
    returns a plain value `Rv`-related to `b` when `f σ = .ok b` and the control-flow
    value `encE r` when `f σ = .error r`, in an environment related by `Q`. -/
theorem guardProg_rrelPT_wpA_iff {ε α : Type} {P Q : Env → S → Prop} {G : S → Prop}
    {e : ImpExpr} {f : S → Except ε α} {Rv : α → Value → Prop} {encE : ε → Value} :
    RRelPT (AssnRel.ofStateRel (entryExitRel P Q)) (GuardRE (entryExitRel P Q) encE) Rv
        (fun Φ E => wp⟦guardProg G f⟧ (Φ, E)) (wpA bi e) ↔
      ∀ σ, G σ → ∀ env, P env σ →
        wp bi e (fun v env' => Q env' σ ∧ ∃ b, f σ = .ok b ∧ Rv b v)
          (fun v env' => Q env' σ ∧ ∃ r, f σ = .error r ∧ v = encE r) env :=
  guardProg_rrelPT_iff fun _ _ _ _ => wpA_mono

/-! ## `Corres` as `RRelPT` -/

/-- **`Corres` is `RRelPT`.** The correspondence `Corres bi P G e V Q` is the relational
    refinement of the abstract program `guardProg G (valExc ∘ V)` by the weakest
    precondition `wpA bi e`, at the assertion map of `entryExitRel P Q`, the relation
    `GuardRE` of the second postconditions and equality of values. -/
theorem corres_iff_rrelPT {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} :
    Corres bi P G e V Q ↔
      RRelPT (AssnRel.ofStateRel (entryExitRel P Q)) (GuardRE (entryExitRel P Q) id) Eq
        (fun Φ E => wp⟦guardProg G (fun σ => valExc (V σ))⟧ (Φ, E)) (wpA bi e) := by
  rw [corres_iff_wp, guardProg_rrelPT_wpA_iff]
  refine forall_congr' fun σ => forall_congr' fun _ => forall_congr' fun env =>
    forall_congr' fun _ => wp_congr fun v s => ?_
  cases hc : v.isControlFlow
  · rw [wpPost_of_plain hc, wpPost_of_plain hc]
    refine ⟨fun ⟨hv, hQ⟩ => ⟨hQ, v, ?_, rfl⟩, fun ⟨hQ, b, hb, hv⟩ => ⟨?_, hQ⟩⟩
    · subst hv
      simp only [valExc, hc, Bool.false_eq_true, if_false]
    · rw [← hv]
      exact valExc_eq_ok hb
  · rw [wpPost_of_cf hc, wpPost_of_cf hc]
    refine ⟨fun ⟨hv, hQ⟩ => ⟨hQ, v, ?_, rfl⟩, fun ⟨hQ, r, hr, hv⟩ => ⟨?_, hQ⟩⟩
    · subst hv
      simp only [valExc, hc, if_true]
    · rw [hv]
      exact valExc_eq_error hr

/-- **`Corres` is `RRelPT` over tagged environments.** The correspondence
    `Corres bi P G e V Q` is the refinement of `guardProg G (valExc ∘ V)` by `wpAT bi e`,
    at the assertion map of the relation `Sum.LiftRel P Q` between tagged environments
    and tagged abstract states. -/
theorem corres_iff_rrelPT_wpAT {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} :
    Corres bi P G e V Q ↔
      RRelPT (AssnRel.ofStateRel (Sum.LiftRel P Q)) (GuardRE (Sum.LiftRel P Q) id) Eq
        (fun Φ E => wp⟦guardProg G (fun σ => valExc (V σ))⟧ (Φ, E)) (wpAT bi e) := by
  rw [corres_iff_rrelPT, guardProg_rrelPT_wpA_iff,
    guardProg_rrelPT_iff fun _ _ _ _ => wpAT_mono]
  refine forall_congr' fun σ => forall_congr' fun _ => ⟨fun h x hx => ?_, fun h env hP => ?_⟩
  · cases hx with
    | inl hP =>
      exact wp_mono (h _ hP) (fun _ _ _ ⟨hQ, hb⟩ => ⟨.inr hQ, hb⟩)
        (fun _ _ _ ⟨hQ, hr⟩ => ⟨.inr hQ, hr⟩)
  · exact wp_mono (h (.inl env) (.inl hP)) (fun _ _ _ ⟨hQ, hb⟩ => ⟨Sum.liftRel_inr_inr.mp hQ, hb⟩)
      (fun _ _ _ ⟨hQ, hr⟩ => ⟨Sum.liftRel_inr_inr.mp hQ, hr⟩)

/-! ## Simulation and composition -/

/-- **A simulation is a refinement.** When from `R`-related environments the runs of
    `e` and `e'` have the same outcome and end in `Rx`-related environments at every
    fuel, `wpAT bi e` is refined by `wpAT bi e'` at the assertion map of the relation
    `Sum.LiftRel (flip R) (flip Rx)` between tagged environments, with the second
    postconditions related as the first ones. -/
theorem rrelPT_wpAT_of_sim {R Rx : Env → Env → Prop} {e e' : ImpExpr}
    (hsim : ∀ fuel env envF, R env envF →
      ((denote' bi fuel e).run env).1 = ((denote' bi fuel e').run envF).1 ∧
        Rx ((denote' bi fuel e).run env).2 ((denote' bi fuel e').run envF).2) :
    RRelPT (AssnRel.ofRel (Sum.LiftRel (flip R) (flip Rx)))
      (fun Ψ Ψ' => ∀ v, (AssnRel.ofRel (Sum.LiftRel (flip R) (flip Rx))).γ (Ψ v) ⊢ₛ Ψ' v)
      Eq (wpAT bi e) (wpAT bi e') := by
  rintro Φ Φ' hΦ Ψ Ψ' hΨ xF ⟨x, hR, hwp⟩
  cases hR with
  | inr _ => exact False.elim hwp
  | inl hR =>
    rename_i envF env
    obtain ⟨v, env₁, ⟨f₀, hrun⟩, hp⟩ := hwp
    obtain ⟨h1, h2⟩ := hsim f₀ env envF hR
    have r₀ : denote' bi f₀ e env = (.val v, env₁) := hrun f₀ (Nat.le_refl _)
    have hv : (denote' bi f₀ e' envF).1 = .val v := by
      have : ((denote' bi f₀ e).run env).1 = .val v := by
        show (denote' bi f₀ e env).1 = _; rw [r₀]
      rw [← this]; exact h1.symm
    have hx : Rx env₁ (denote' bi f₀ e' envF).2 := by
      have : ((denote' bi f₀ e).run env).2 = env₁ := by
        show (denote' bi f₀ e env).2 = _; rw [r₀]
      rw [← this]; exact h2
    refine ⟨v, (denote' bi f₀ e' envF).2, ⟨f₀, fun fuel hf => ?_⟩, ?_⟩
    · rw [denote'_val_mono bi hv hf]
      exact Prod.ext hv rfl
    · rcases hp with ⟨hc, hp⟩ | ⟨hc, hp⟩
      · exact Or.inl ⟨hc, @hΦ v v rfl _ ⟨.inr env₁, .inr hx, hp⟩⟩
      · exact Or.inr ⟨hc, hΨ v _ ⟨.inr env₁, .inr hx, hp⟩⟩

/-- **Composition by `RRelPT.trans`.** A correspondence `Corres bi P G e V Q` and a
    refinement of `wpAT bi e` by `wpAT bi e'` at the assertion map of
    `Sum.LiftRel R Rx`, whose second postconditions are related as the first ones,
    give the correspondence for `e'` from the environments `R`-related to the entry
    environments of `e` to those `Rx`-related to its exit environments. -/
theorem corres_trans_of_rrelPT {R Rx : Env → Env → Prop} {P Q : Env → S → Prop}
    {G : S → Prop} {e e' : ImpExpr} {V : S → Value} (h₁ : Corres bi P G e V Q)
    (h₂ : RRelPT (AssnRel.ofRel (Sum.LiftRel R Rx))
      (fun Ψ Ψ' => ∀ v, (AssnRel.ofRel (Sum.LiftRel R Rx)).γ (Ψ v) ⊢ₛ Ψ' v)
      Eq (wpAT bi e) (wpAT bi e')) :
    Corres bi (fun env' σ => ∃ env, R env' env ∧ P env σ) G e' V
      (fun env' σ => ∃ env, Rx env' env ∧ Q env σ) := by
  have hrel : (fun x' y => ∃ x, Sum.LiftRel R Rx x' x ∧ Sum.LiftRel P Q x y) =
      Sum.LiftRel (fun env' σ => ∃ env, R env' env ∧ P env σ)
        (fun env' σ => ∃ env, Rx env' env ∧ Q env σ) := by
    funext x' y
    refine propext ⟨fun ⟨x, hR, hP⟩ => ?_, fun h => ?_⟩
    · cases hR with
      | inl hR => cases hP with | inl hP => exact .inl ⟨_, hR, hP⟩
      | inr hR => cases hP with | inr hP => exact .inr ⟨_, hR, hP⟩
    · cases h with
      | inl h => obtain ⟨_, hR, hP⟩ := h; exact ⟨_, .inl hR, .inl hP⟩
      | inr h => obtain ⟨_, hR, hQ⟩ := h; exact ⟨_, .inr hR, .inr hQ⟩
  have h := RRelPT.trans (corres_iff_rrelPT_wpAT.mp h₁) h₂
  refine corres_iff_rrelPT_wpAT.mpr fun Φ Φ' hΦ E E' ⟨hnone, hE⟩ => ?_
  have hc := @h Φ Φ'
    (fun a a'' ⟨_, h₁, h₂⟩ => by
      subst h₁ h₂
      rw [AssnRel.Rel, AssnRel.ofRel_comp_ofStateRel_γ, hrel]
      exact @hΦ a a rfl)
    E E'
    ⟨fun v => (AssnRel.ofStateRel (ε := Option Value) (Sum.LiftRel P Q)).γ (E.1 (some v)),
      ⟨hnone, fun _ => .rfl⟩, fun v => by
        have := hE v
        rw [← hrel, ← AssnRel.ofRel_comp_ofStateRel_γ] at this
        exact this⟩
  rw [AssnRel.Rel] at hc ⊢
  rwa [AssnRel.ofRel_comp_ofStateRel_γ, hrel] at hc

/-- **Transport along a simulation**, by `rrelPT_wpAT_of_sim` and
    `corres_trans_of_rrelPT`: when from `R`-related environments the runs of `e` and
    `e'` have the same outcome at every fuel and end in `Rx`-related environments, a
    `Corres` statement for `e` gives one for `e'` with the same value, from the
    environments `R`-related to the entry environments of `e` to those `Rx`-related to
    its exit environments. -/
theorem corres_of_fuelSim_via_rrel {R Rx : Env → Env → Prop} {e e' : ImpExpr}
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (hsim : ∀ fuel env envF, R env envF →
      ((denote' bi fuel e).run env).1 = ((denote' bi fuel e').run envF).1 ∧
        Rx ((denote' bi fuel e).run env).2 ((denote' bi fuel e').run envF).2)
    (h : Corres bi P G e V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ R env envF) G e' V
      (fun envF σ => ∃ env, Q env σ ∧ Rx env envF) :=
  corres_conseq (corres_trans_of_rrelPT h (rrelPT_wpAT_of_sim hsim))
    (fun _ _ ⟨env, hP, hR⟩ _ => ⟨env, hR, hP⟩) (fun _ h => h) (fun _ _ => rfl)
    (fun _ _ _ ⟨env, hR, hQ⟩ => ⟨env, hQ, hR⟩)

end Hax.Ascent

end
