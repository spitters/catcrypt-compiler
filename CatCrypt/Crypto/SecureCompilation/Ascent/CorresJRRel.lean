/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockMvcgen
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import Transfer.Integrations.ParamPredTrans

@[expose] public section
set_option autoImplicit false

/-!
# The machine correspondence `CorresJ` as a relational refinement `RRel`

`CorresJ SR P fa c` (`Ascent/RunBlockCorres.lean`) states that the straight-line
block `c`, run by `runBlock` from a state related by `SR` to an abstract state `a`
with `P a`, ends in a state related by `SR` to `fa a`. This module states it as the
relational refinement `RRel` of `Transfer.Integrations.ParamPredTrans` between an
abstract program and the monadic block run `runBlockM c`
(`Ascent/RunBlockMvcgen.lean`).

* The abstract program `guardedUpdate P fa : EStateM PUnit A Unit` updates the
  abstract state by `fa` when `P` holds and raises the exception `()` otherwise.
* The assertion map `AssnRel.ofStateRel SR` sends an abstract assertion `Q` to the
  machine assertion `fun s => ⌜∃ a, SR s a ∧ Q a⌝`.
* The exception postcondition of the abstract program is fixed to
  `ExceptConds.false`, so the weakest precondition of `guardedUpdate P fa` at `Q` is
  `P a ∧ Q (fa a)`: `P` acts as an assumption of the abstract side.

## Main definitions

* `AssnRel.ofStateRel`: the assertion map of a relation between machine states and
  abstract states.
* `AssnRel.ofRel`: the assertion map of a relation between two state spaces of
  shape `.arg σ .pure`.
* `guardedUpdate P fa`: the abstract program of a correspondence.

## Main results

* `corresJ_iff_rrel`: `CorresJ SR P fa c` is `RRel (AssnRel.ofStateRel SR)` between
  `guardedUpdate P fa` and `runBlockM c`.
* `corresJ_trans_of_rrel`: a correspondence for `c₁` and a refinement of
  `runBlockM c₁` by `runBlockM c₂` at `AssnRel.ofRel R` give the correspondence for
  `c₂` at the composite relation, by `RRel.trans`.
-/

namespace Transfer.Param.AssnRel

open Std.Do

/-- The assertion map of a relation `SR` between states `σ` and abstract states `A`:
    an abstract assertion `Q` goes to `fun s => ⌜∃ a, SR s a ∧ Q a⌝`. The abstract
    shape carries one exception of type `PUnit`. -/
def ofStateRel {σ A : Type} (SR : σ → A → Prop) :
    AssnRel (.except PUnit (.arg A .pure)) (.arg σ .pure) where
  γ Q := fun s => ⌜∃ a, SR s a ∧ (Q a).down⌝
  mono h := fun _ ⟨a, hs, hq⟩ => ⟨a, hs, h a hq⟩
  exists_le _ := fun _ ⟨a, hs, ⟨i, hi⟩⟩ => ⟨i, a, hs, hi⟩

/-- The assertion map of a relation `R` between states `σ'` and states `σ`: an
    assertion `Q` on `σ` goes to `fun s' => ⌜∃ s, R s' s ∧ Q s⌝`. -/
def ofRel {σ σ' : Type} (R : σ' → σ → Prop) :
    AssnRel (.arg σ .pure) (.arg σ' .pure) where
  γ Q := fun s' => ⌜∃ s, R s' s ∧ (Q s).down⌝
  mono h := fun _ ⟨s, hs, hq⟩ => ⟨s, hs, h s hq⟩
  exists_le _ := fun _ ⟨s, hs, ⟨i, hi⟩⟩ => ⟨i, s, hs, hi⟩

/-- The composite of `ofRel R` after `ofStateRel SR` is `ofStateRel` of the
    relational composite of `R` and `SR`. -/
theorem ofRel_comp_ofStateRel_γ {σ σ' A : Type} (R : σ' → σ → Prop) (SR : σ → A → Prop)
    (Q : Assertion (.except PUnit (.arg A .pure))) :
    ((ofRel R).comp (ofStateRel SR)).γ Q =
      (ofStateRel (fun s' a => ∃ s, R s' s ∧ SR s a)).γ Q := by
  funext s'
  exact congrArg ULift.up (propext
    ⟨fun ⟨s, hR, a, hs, hq⟩ => ⟨a, ⟨s, hR, hs⟩, hq⟩,
     fun ⟨a, ⟨s, hR, hs⟩, hq⟩ => ⟨s, hR, a, hs, hq⟩⟩)

end Transfer.Param.AssnRel

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.Do
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open Transfer.Param

variable {A : Type}

/-- The abstract program of a correspondence: update the abstract state by `fa`
    when `P` holds, and raise the exception `()` otherwise. -/
noncomputable def guardedUpdate (P : A → Prop) (fa : A → A) : EStateM PUnit A Unit :=
  fun a => open Classical in if P a then .ok () (fa a) else .error () a

/-- The weakest precondition of `guardedUpdate P fa` at a state where `P` holds is
    the postcondition at the updated state. -/
theorem wp_guardedUpdate_of_pos {P : A → Prop} {fa : A → A}
    (Q : PostCond Unit (.except PUnit (.arg A .pure))) {a : A} (hP : P a) :
    wp⟦guardedUpdate P fa⟧ Q a = Q.1 () (fa a) := by
  have h : (guardedUpdate P fa).run a = EStateM.Result.ok () (fa a) := by
    simp only [EStateM.run, guardedUpdate, if_pos hP]
  simp only [wp, PredTrans.apply, h]

/-- The weakest precondition of `guardedUpdate P fa` at a state where `P` fails is
    the exception postcondition at that state. -/
theorem wp_guardedUpdate_of_neg {P : A → Prop} {fa : A → A}
    (Q : PostCond Unit (.except PUnit (.arg A .pure))) {a : A} (hP : ¬ P a) :
    wp⟦guardedUpdate P fa⟧ Q a = Q.2.1 () a := by
  have h : (guardedUpdate P fa).run a = EStateM.Result.error () a := by
    simp only [EStateM.run, guardedUpdate, if_neg hP]
  simp only [wp, PredTrans.apply, h]

/-- The weakest precondition of the block run `runBlockM c` at a state `s` is the
    postcondition at `runBlock s c`. -/
theorem wp_runBlockM_apply (c : List (JInstr 64)) (Q : PostCond Unit psJM)
    (s : JState 64) : wp⟦runBlockM c⟧ Q s = Q.1 () (runBlock s c) := by
  show wp⟦(runBlockM c).run s⟧ (fun p => Q.1 p.1 p.2, Q.2) = _
  rw [runBlockM_run]
  rfl

/-- **`CorresJ` is `RRel`.** The correspondence `CorresJ SR P fa c` is the relational
    refinement of the abstract program `guardedUpdate P fa` by the block run
    `runBlockM c`, at the assertion map `AssnRel.ofStateRel SR`, with the abstract
    exception postcondition fixed to `ExceptConds.false` and the trivial relation on
    the `Unit` return values. -/
theorem corresJ_iff_rrel (SR : JState 64 → A → Prop) (P : A → Prop) (fa : A → A)
    (c : List (JInstr 64)) :
    CorresJ SR P fa c ↔
      RRel (AssnRel.ofStateRel SR) (fun E _ => E = ExceptConds.false)
        (fun _ _ => True) (guardedUpdate P fa) (runBlockM c) := by
  constructor
  · rintro h Q Q' E E' hQ rfl s ⟨a, hs, hwp⟩
    rw [wp_runBlockM_apply]
    by_cases hP : P a
    · rw [wp_guardedUpdate_of_pos _ hP] at hwp
      exact hQ () () trivial (runBlock s c) ⟨fa a, h s a hs hP, hwp⟩
    · rw [wp_guardedUpdate_of_neg _ hP] at hwp
      exact hwp.elim
  · intro h st a hs hP
    have hwp := h (fun _ a' => ⌜a' = fa a⌝) (fun _ s' => ⌜SR s' (fa a)⌝)
      ExceptConds.false ExceptConds.false
      (fun _ _ _ s' ⟨a', hs', he⟩ => he ▸ hs') rfl st
      ⟨a, hs, by rw [wp_guardedUpdate_of_pos _ hP]; exact rfl⟩
    rw [wp_runBlockM_apply] at hwp
    exact hwp

/-- **Composition by `RRel.trans`.** A correspondence `CorresJ SR P fa c₁` and a
    refinement of `runBlockM c₁` by `runBlockM c₂` at the assertion map
    `AssnRel.ofRel R` give the correspondence for `c₂` at the composite relation
    `fun s₂ a => ∃ s₁, R s₂ s₁ ∧ SR s₁ a`. -/
theorem corresJ_trans_of_rrel {SR : JState 64 → A → Prop}
    {R : JState 64 → JState 64 → Prop} {P : A → Prop} {fa : A → A}
    {c₁ c₂ : List (JInstr 64)} (h₁ : CorresJ SR P fa c₁)
    (h₂ : RRel (AssnRel.ofRel R) (fun _ _ => True) (fun _ _ => True)
      (runBlockM c₁) (runBlockM c₂)) :
    CorresJ (fun s₂ a => ∃ s₁, R s₂ s₁ ∧ SR s₁ a) P fa c₂ := by
  have h := RRel.trans ((corresJ_iff_rrel SR P fa c₁).mp h₁) h₂
  refine (corresJ_iff_rrel _ P fa c₂).mpr fun Q Q' E E' hQ hE => ?_
  have hc := h Q Q' E E'
    (fun _ _ _ => by rw [AssnRel.ofRel_comp_ofStateRel_γ]; exact hQ () () trivial)
    ⟨ExceptConds.false, hE, trivial⟩
  rwa [AssnRel.ofRel_comp_ofStateRel_γ] at hc

end CatCrypt.Crypto.SecureCompilation.Ascent

end
