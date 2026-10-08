/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Wp
public import Transfer.Integrations.ParamPredTransAbs

/-!
# The source correspondence `Corres` as a relational refinement `RRelPT`

`Corres bi P G e V Q` (`Ascent/Corres.lean`) states that the run of `e` from an
environment related by `P` to an abstract state `σ` with `G σ` eventually returns
`V σ` in an environment related by `Q` to `σ`. This module states it as the
relational refinement `RRelPT` of `Transfer.Integrations.ParamPredTransAbs` between
the weakest precondition of an abstract program and the weakest precondition
`wpA bi e` of `e`.

* `wpA bi e Φ Ψ` is `wp bi e` (`Ascent/Wp.lean`) at `Assertion (.arg Env .pure)`; the
  second argument `Ψ` is the postcondition of control-flow values.
* The abstract state space is `S ⊕ S`: `.inl σ` is the state `σ` before the run and
  `.inr σ` the state `σ` after it. The relation `entryExitRel P Q` relates an
  environment to `.inl σ` by `P` and to `.inr σ` by `Q`, so one assertion map
  `AssnRel.ofStateRelExc (entryExitRel P Q)` carries both relations of `Corres`.
* The abstract program `corresProg G V : EStateM (Option Value) (S ⊕ S) Value` moves
  `.inl σ` to `.inr σ` with result `V σ` when `G σ` holds; a control-flow value `V σ`
  is raised as the exception `some (V σ)`. A failed guard, and a start from `.inr σ`,
  raise `none`, whose postcondition `CorresRE` fixes to false.

## Main definitions

* `AssnRel.ofStateRelExc`: the assertion map of a relation between states and abstract
  states, at an abstract shape with one exception type.
* `AssnRel.ofArgRel`: the assertion map of a relation between two state spaces.
* `entryExitRel`: one relation to `S ⊕ S` from an entry and an exit relation to `S`.
* `wpA`: the weakest precondition of `ImpExpr` as an `Assertion` transformer.
* `corresProg`, `CorresRE`: the abstract program and the relation of the second
  postconditions.

## Main results

* `corres_iff_rrelPT`: `Corres bi P G e V Q` is `RRelPT` between `corresProg G V` and
  `wpA bi e`, at `AssnRel.ofStateRelExc (entryExitRel P Q)` and equality of values.
* `corres_trans_of_rrelPT`: a correspondence for `e` and a refinement of `wpA bi e` by
  `wpA bi e'` at `AssnRel.ofArgRel R` give the correspondence for `e'` at the composite
  relations, by `RRelPT.trans`.
* `rrelPT_wpA_of_sim`: a fuel-uniform simulation of `e` by `e'` along one relation is a
  refinement of `wpA bi e` by `wpA bi e'`.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.Param

open Std.Do

/-- The relation of a state `s` to `S ⊕ S`: `.inl σ` by the entry relation `P` and
    `.inr σ` by the exit relation `Q`. -/
def entryExitRel {σ S : Type} (P Q : σ → S → Prop) (s : σ) : S ⊕ S → Prop :=
  Sum.elim (P s) (Q s)

namespace AssnRel

/-- The assertion map of a relation `SR` between states `σ` and abstract states `A`:
    an abstract assertion `Q` goes to `fun s => ⌜∃ a, SR s a ∧ Q a⌝`. The abstract
    shape carries one exception of type `ε`. -/
def ofStateRelExc {ε σ A : Type} (SR : σ → A → Prop) :
    AssnRel (.except ε (.arg A .pure)) (.arg σ .pure) where
  γ Q := fun s => ⌜∃ a, SR s a ∧ (Q a).down⌝
  mono h := fun _ ⟨a, hs, hq⟩ => ⟨a, hs, h a hq⟩
  exists_le _ := fun _ ⟨a, hs, ⟨i, hi⟩⟩ => ⟨i, a, hs, hi⟩

/-- The assertion map of a relation `R` between states `σ'` and states `σ`: an
    assertion `Q` on `σ` goes to `fun s' => ⌜∃ s, R s' s ∧ Q s⌝`. -/
def ofArgRel {σ σ' : Type} (R : σ' → σ → Prop) :
    AssnRel (.arg σ .pure) (.arg σ' .pure) where
  γ Q := fun s' => ⌜∃ s, R s' s ∧ (Q s).down⌝
  mono h := fun _ ⟨s, hs, hq⟩ => ⟨s, hs, h s hq⟩
  exists_le _ := fun _ ⟨s, hs, ⟨i, hi⟩⟩ => ⟨i, s, hs, hi⟩

/-- The composite of `ofArgRel R` after `ofStateRelExc SR` is `ofStateRelExc` of the
    relational composite of `R` and `SR`. -/
theorem ofArgRel_comp_ofStateRelExc_γ {ε σ σ' A : Type} (R : σ' → σ → Prop)
    (SR : σ → A → Prop) (Q : Assertion (.except ε (.arg A .pure))) :
    ((ofArgRel R).comp (ofStateRelExc (ε := ε) SR)).γ Q =
      (ofStateRelExc (ε := ε) (fun s' a => ∃ s, R s' s ∧ SR s a)).γ Q := by
  funext s'
  exact congrArg ULift.up (propext
    ⟨fun ⟨s, hR, a, hs, hq⟩ => ⟨a, ⟨s, hR, hs⟩, hq⟩,
     fun ⟨a, ⟨s, hR, hs⟩, hq⟩ => ⟨s, hR, a, hs, hq⟩⟩)

end AssnRel

end Transfer.Param

namespace Hax.Ascent

open Std.Do
open Transfer.Param

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

/-! ## The abstract program of a correspondence -/

/-- The abstract program of `Corres`: from `.inl σ` with `G σ` it returns `V σ` in
    `.inr σ`, raising `some (V σ)` when `V σ` is a control-flow value; otherwise it
    raises `none`. -/
noncomputable def corresProg (G : S → Prop) (V : S → Value) :
    EStateM (Option Value) (S ⊕ S) Value := fun x =>
  open Classical in
  match x with
  | .inl σ =>
    if G σ then
      (if (V σ).isControlFlow = true then .error (some (V σ)) (.inr σ) else .ok (V σ) (.inr σ))
    else .error none x
  | .inr _ => .error none x

/-- The weakest precondition of an `EStateM` program is the postcondition of its
    result. -/
theorem wp_eStateM_apply {ε σ α : Type} (x : EStateM ε σ α)
    (Q : PostCond α (.except ε (.arg σ .pure))) (s : σ) :
    wp⟦x⟧ Q s = match x.run s with
      | .ok a s' => Q.1 a s'
      | .error e s' => Q.2.1 e s' := by
  cases h : x.run s <;> simp only [WP.wp, PredTrans.apply, h]

/-- The weakest precondition of `corresProg G V`, when the exception `none` has the
    false postcondition: the start is `.inl σ` with `G σ`, and the result `V σ` meets
    the normal postcondition when plain and the postcondition of `some (V σ)` when it
    is a control-flow value. -/
theorem wp_corresProg_iff {G : S → Prop} {V : S → Value}
    {Q : PostCond Value (.except (Option Value) (.arg (S ⊕ S) .pure))} {x : S ⊕ S}
    (hnone : ∀ y, ¬ (Q.2.1 none y).down) :
    (wp⟦corresProg G V⟧ Q x).down ↔ ∃ σ, x = .inl σ ∧ G σ ∧
      (((V σ).isControlFlow = false ∧ (Q.1 (V σ) (.inr σ)).down) ∨
        ((V σ).isControlFlow = true ∧ (Q.2.1 (some (V σ)) (.inr σ)).down)) := by
  rw [wp_eStateM_apply]
  rcases x with σ | σ
  · by_cases hG : G σ
    · cases hc : (V σ).isControlFlow
      · simp only [EStateM.run, corresProg, if_pos hG, hc, Bool.false_eq_true, if_false]
        refine ⟨fun h => ⟨σ, rfl, hG, Or.inl ⟨hc, h⟩⟩, fun ⟨_, h, _, hp⟩ => ?_⟩
        cases h
        rcases hp with ⟨_, hp⟩ | ⟨h, _⟩
        · exact hp
        · rw [hc] at h
          cases h
      · simp only [EStateM.run, corresProg, if_pos hG, hc, if_true]
        refine ⟨fun h => ⟨σ, rfl, hG, Or.inr ⟨hc, h⟩⟩, fun ⟨_, h, _, hp⟩ => ?_⟩
        cases h
        rcases hp with ⟨h, _⟩ | ⟨_, hp⟩
        · rw [hc] at h
          cases h
        · exact hp
    · simp only [EStateM.run, corresProg, if_neg hG]
      exact ⟨fun h => (hnone _ h).elim, fun ⟨_, h, hG', _⟩ => by cases h; exact (hG hG').elim⟩
  · simp only [EStateM.run, corresProg]
    exact ⟨fun h => (hnone _ h).elim, fun ⟨_, h, _⟩ => nomatch h⟩

/-- The relation of the second postconditions in `corres_iff_rrelPT`: the abstract
    exception `none` has the false postcondition, and the abstract postcondition of
    `some v`, mapped by `ofStateRelExc SR`, entails the control-flow postcondition at
    `v`. -/
def CorresRE {σ A : Type} (SR : σ → A → Prop)
    (E : ExceptConds (.except (Option Value) (.arg A .pure)))
    (E' : Value → Assertion (.arg σ .pure)) : Prop :=
  (∀ a, ¬ (E.1 none a).down) ∧
    ∀ v, (AssnRel.ofStateRelExc (ε := Option Value) SR).γ (E.1 (some v)) ⊢ₛ E' v

/-! ## `Corres` as `RRelPT` -/

/-- **`Corres` is `RRelPT`.** The correspondence `Corres bi P G e V Q` is the relational
    refinement of the abstract program `corresProg G V` by the weakest precondition
    `wpA bi e`, at the assertion map of `entryExitRel P Q`, the relation `CorresRE` of
    the second postconditions and equality of values. -/
theorem corres_iff_rrelPT {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} :
    Corres bi P G e V Q ↔
      RRelPT (AssnRel.ofStateRelExc (entryExitRel P Q)) (CorresRE (entryExitRel P Q)) Eq
        (fun Φ E => wp⟦corresProg G V⟧ (Φ, E)) (wpA bi e) := by
  rw [corres_iff_wp]
  constructor
  · rintro h Φ Φ' E E' hΦ ⟨hnone, hE⟩ env ⟨x, hx, hwp⟩
    obtain ⟨σ, rfl, hG, hp⟩ := (wp_corresProg_iff hnone).mp hwp
    refine wp_mono (h σ hG env hx) ?_ ?_
    · rintro v s hc ⟨rfl, hQ⟩
      rcases hp with ⟨_, hp⟩ | ⟨hc', _⟩
      · exact hΦ _ _ rfl s ⟨.inr σ, hQ, hp⟩
      · rw [hc] at hc'
        cases hc'
    · rintro v s hc ⟨rfl, hQ⟩
      rcases hp with ⟨hc', _⟩ | ⟨_, hp⟩
      · rw [hc] at hc'
        cases hc'
      · exact hE _ s ⟨.inr σ, hQ, hp⟩
  · intro h σ hG env hP
    let E : ExceptConds (.except (Option Value) (.arg (S ⊕ S) .pure)) :=
      (fun o y => ⌜o = some (V σ) ∧ y = .inr σ⌝, ())
    have hnone : ∀ y, ¬ (E.1 none y).down := fun _ ⟨h, _⟩ => nomatch h
    have hw := h (fun v y => ⌜v = V σ ∧ y = .inr σ⌝) (fun v s => ⌜v = V σ ∧ Q s σ⌝)
      E (fun v s => ⌜v = V σ ∧ Q s σ⌝)
      (fun _ _ hv s ⟨_, hx, h₁, h₂⟩ => by subst hv h₂; exact ⟨h₁, hx⟩)
      ⟨hnone, fun v s ⟨_, hx, h₁, h₂⟩ => by cases h₁; subst h₂; exact ⟨rfl, hx⟩⟩ env
      ⟨.inl σ, hP, (wp_corresProg_iff hnone).mpr ⟨σ, rfl, hG, by
        cases hc : (V σ).isControlFlow
        · exact Or.inl ⟨rfl, rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl, rfl⟩⟩⟩
    exact hw

/-! ## Composition with a refinement of the source -/

/-- **Composition by `RRelPT.trans`.** A correspondence `Corres bi P G e V Q` and a
    refinement of `wpA bi e` by `wpA bi e'` at `AssnRel.ofArgRel R`, whose second
    postconditions are related as the first ones, give the correspondence for `e'`
    from and to the environments `R`-related to the entry and exit environments of
    `e`. -/
theorem corres_trans_of_rrelPT {R : Env → Env → Prop} {P Q : Env → S → Prop}
    {G : S → Prop} {e e' : ImpExpr} {V : S → Value} (h₁ : Corres bi P G e V Q)
    (h₂ : RRelPT (AssnRel.ofArgRel R) (fun Ψ Ψ' => ∀ v, (AssnRel.ofArgRel R).γ (Ψ v) ⊢ₛ Ψ' v)
      Eq (wpA bi e) (wpA bi e')) :
    Corres bi (fun env' σ => ∃ env, R env' env ∧ P env σ) G e' V
      (fun env' σ => ∃ env, R env' env ∧ Q env σ) := by
  have hrel : (fun env' x => ∃ env, R env' env ∧ entryExitRel P Q env x) =
      entryExitRel (fun env' σ => ∃ env, R env' env ∧ P env σ)
        (fun env' σ => ∃ env, R env' env ∧ Q env σ) := by
    funext env' x
    cases x <;> rfl
  have h := RRelPT.trans (corres_iff_rrelPT.mp h₁) h₂
  refine corres_iff_rrelPT.mpr fun Φ Φ' E E' hΦ ⟨hnone, hE⟩ => ?_
  have hc := h Φ Φ' E E'
    (fun a a'' ⟨_, h₁, h₂⟩ => by
      subst h₁ h₂
      rw [AssnRel.ofArgRel_comp_ofStateRelExc_γ, hrel]
      exact hΦ a a rfl)
    ⟨fun v => (AssnRel.ofStateRelExc (ε := Option Value) (entryExitRel P Q)).γ (E.1 (some v)),
      ⟨hnone, fun _ => .rfl⟩, fun v => by
        have := hE v
        rw [← hrel, ← AssnRel.ofArgRel_comp_ofStateRelExc_γ] at this
        exact this⟩
  rwa [AssnRel.ofArgRel_comp_ofStateRelExc_γ, hrel] at hc

/-- **A simulation is a refinement.** When from `R`-related environments the runs of
    `e` and `e'` have the same outcome and end in `R`-related environments at every
    fuel, `wpA bi e` is refined by `wpA bi e'` at `AssnRel.ofArgRel (flip R)`, with the
    second postconditions related as the first ones. -/
theorem rrelPT_wpA_of_sim {R : Env → Env → Prop} {e e' : ImpExpr}
    (hsim : ∀ fuel env envF, R env envF →
      ((denote' bi fuel e).run env).1 = ((denote' bi fuel e').run envF).1 ∧
        R ((denote' bi fuel e).run env).2 ((denote' bi fuel e').run envF).2) :
    RRelPT (AssnRel.ofArgRel (flip R))
      (fun Ψ Ψ' => ∀ v, (AssnRel.ofArgRel (flip R)).γ (Ψ v) ⊢ₛ Ψ' v)
      Eq (wpA bi e) (wpA bi e') := by
  rintro Φ Φ' Ψ Ψ' hΦ hΨ envF ⟨env, hR, v, env₁, ⟨f₀, hrun⟩, hp⟩
  obtain ⟨h1, h2⟩ := hsim f₀ env envF hR
  have r₀ : denote' bi f₀ e env = (.val v, env₁) := hrun f₀ (Nat.le_refl _)
  have hv : (denote' bi f₀ e' envF).1 = .val v := by
    have : ((denote' bi f₀ e).run env).1 = .val v := by
      show (denote' bi f₀ e env).1 = _; rw [r₀]
    rw [← this]; exact h1.symm
  have hx : R env₁ (denote' bi f₀ e' envF).2 := by
    have : ((denote' bi f₀ e).run env).2 = env₁ := by
      show (denote' bi f₀ e env).2 = _; rw [r₀]
    rw [← this]; exact h2
  refine ⟨v, (denote' bi f₀ e' envF).2, ⟨f₀, fun fuel hf => ?_⟩, ?_⟩
  · rw [denote'_val_mono bi hv hf]
    exact Prod.ext hv rfl
  · rcases hp with ⟨hc, hp⟩ | ⟨hc, hp⟩
    · exact Or.inl ⟨hc, hΦ v v rfl _ ⟨env₁, hx, hp⟩⟩
    · exact Or.inr ⟨hc, hΨ v _ ⟨env₁, hx, hp⟩⟩

end Hax.Ascent

end
