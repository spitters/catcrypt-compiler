/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockMvcgen
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import CatCryptCore.Refinement.Programs
public import HaxAscent.Ascent.Refines

@[expose] public section
set_option autoImplicit false

/-!
# The machine correspondence `CorresJ` as a relational refinement `RRel`

`CorresJ SR P fa c` (`Ascent/RunBlockCorres.lean`) states that the straight-line
block `c`, run by `runBlock` from a state related by `SR` to an abstract state `a`
with `P a`, ends in a state related by `SR` to `fa a`. This module states it as the
relational refinement `RRel` of `CatCryptCore/Refinement/RRel.lean` between an
abstract program and the monadic block run `runBlockM c`
(`Ascent/RunBlockMvcgen.lean`).

* The abstract program is `optProg (optGuard P fun a => ((), fa a))`
  (`CatCryptCore/Refinement/Programs.lean`, `Ascent/Refines.lean`), at the classical
  decision of `P`: it updates the abstract state by `fa` when `P` holds and raises the
  exception `()` otherwise.
* The assertion map `AssnRel.ofStateRel SR` sends an abstract assertion `Q` to the
  machine assertion `fun s => ⌜∃ a, SR s a ∧ Q a⌝`.
* The exception postcondition of the abstract program is fixed to
  `ExceptConds.false`, so the weakest precondition of the abstract program at `Q` is
  `P a ∧ Q (fa a)`: `P` acts as an assumption of the abstract side.

## Main results

* `corresJ_iff_rrel`: `CorresJ SR P fa c` is `RRel (AssnRel.ofStateRel SR)` between
  the guarded update and `runBlockM c`.
* `corresJ_trans_of_rrel`: a correspondence for `c₁` and a refinement of
  `runBlockM c₁` by `runBlockM c₂` at `AssnRel.ofRel R` give the correspondence for
  `c₂` at the composite relation, by `RRel.trans`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.Do
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Refinement

open _root_.Hax.Ascent (optGuard)

variable {A : Type}

/-- The weakest precondition of the block run `runBlockM c` at a state `s` is the
    postcondition at `runBlock s c`. -/
theorem wp_runBlockM_apply (c : List (JInstr 64)) (Q : PostCond Unit psJM)
    (s : JState 64) : wp⟦runBlockM c⟧ Q s = Q.1 () (runBlock s c) := by
  show wp⟦(runBlockM c).run s⟧ (fun p => Q.1 p.1 p.2, Q.2) = _
  rw [runBlockM_run]
  rfl

/-- **`CorresJ` is `RRel`.** The correspondence `CorresJ SR P fa c` is the relational
    refinement of the abstract program `optProg (optGuard P fun a => ((), fa a))` by the
    block run `runBlockM c`, at the assertion map `AssnRel.ofStateRel SR`, with the
    abstract exception postcondition fixed to `ExceptConds.false` and the trivial
    relation on the `Unit` return values. -/
theorem corresJ_iff_rrel (SR : JState 64 → A → Prop) (P : A → Prop) (fa : A → A)
    (c : List (JInstr 64)) :
    CorresJ SR P fa c ↔
      RRel (AssnRel.ofStateRel SR) (fun E _ => E = ExceptConds.false) (fun _ _ => True)
        (open Classical in optProg (optGuard P fun a => ((), fa a))) (runBlockM c) := by
  constructor
  · rintro h Q Q' hQ E E' rfl s ⟨a, hs, hwp⟩
    beta_reduce at hwp ⊢
    rw [wp_runBlockM_apply]
    rw [wp_optProg_apply] at hwp
    by_cases hP : P a
    · simp only [optGuard, if_pos hP] at hwp
      exact @hQ () () trivial (runBlock s c) ⟨fa a, h s a hs hP, hwp⟩
    · simp only [optGuard, if_neg hP] at hwp
      exact hwp.elim
  · intro h st a hs hP
    have hwp := @h (fun _ a' => ⌜a' = fa a⌝) (fun _ s' => ⌜SR s' (fa a)⌝)
      (fun _ _ _ s' ⟨a', hs', he⟩ => he ▸ hs') ExceptConds.false ExceptConds.false rfl st
      ⟨a, hs, by beta_reduce; rw [wp_optProg_apply]; simp only [optGuard, if_pos hP]; exact trivial⟩
    beta_reduce at hwp
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
  refine (corresJ_iff_rrel _ P fa c₂).mpr fun Q Q' hQ E E' hE => ?_
  have hc := @h Q Q'
    (fun _ _ _ => by rw [AssnRel.Rel, AssnRel.ofRel_comp_ofStateRel_γ]; exact @hQ () () trivial)
    E E' ⟨ExceptConds.false, hE, trivial⟩
  rw [AssnRel.Rel] at hc ⊢
  rwa [AssnRel.ofRel_comp_ofStateRel_γ] at hc

end CatCrypt.Crypto.SecureCompilation.Ascent

end
