/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Calculus.CorresMCutPoint
public import HaxAscent.Calculus.RustMSquareLoop

/-!
# The `RustM` loop rule as an instance of the cut-point rule

`corresM_loop_of_cutPoint` has the statement of `corresM_loop`
(`HaxAscent.Calculus.RustMSquareLoop`) and is proved from the generic cut-point rule
`CutPoint.sim` at the reachability relation `loop body x = loop body x'`. It is kept in
its own module so that `CorresMCutPoint` imports the calculus core only.

## Main results

* `Hax.Ascent.RustM.corresM_loop_of_cutPoint`
-/

@[expose] public section

set_option autoImplicit false

/-! ## The `RustM` loop rule as an instance -/

namespace Hax.Ascent.RustM

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.Ascent

/-- **The invariant rule for a `RustM` loop from the cut-point rule.** The statement of
    `corresM_loop`. The machine state is the loop state, the reachability relation is
    `fun x x' => loop body x = loop body x'`, there is one cut point with the invariant
    `G σ ∧ inv σ x` over the entry abstract state `σ`, and the exit relation states that
    the loop from `x` returns `(V σ, c')` with `Q c' σ`. A `.cont` trip is a segment to
    the cut point at a smaller measure; a `.done` trip is an exit at the same state. -/
theorem corresM_loop_of_cutPoint {α C S A : Type} {P Q : C → S → Prop} {G : S → Prop}
    {V : S → A} {body : α → Aeneas.Std.RustM (ControlFlow α (A × C))} {init : C → α}
    (inv : S → α → Prop) (measure : S → α → Nat)
    (hinit : ∀ c σ, P c σ → G σ → inv σ (init c))
    (hbody : ∀ σ, G σ → ∀ x, inv σ x → WP.spec (body x) (fun r => match r with
      | .done y => ∃ c', y = (V σ, c') ∧ Q c' σ
      | .cont x' => inv σ x' ∧ measure σ x' < measure σ x)) :
    CorresM P G (fun c => loop body (init c)) V Q := by
  intro c σ hP hG
  obtain ⟨x', σ', _, hR, hσ, c', hx', hQ⟩ :=
    CutPoint.sim (L := Unit) (E := Unit) (fun x x' => loop body x = loop body x')
      (fun _ _ _ h h' => h.trans h') (fun σ σ' : S => σ' = σ) (fun _ _ _ h h' => h'.trans h)
      (fun _ x σ => G σ ∧ inv σ x)
      (fun _ x σ => ∃ c', loop body x = .ok (V σ, c') ∧ Q c' σ)
      (fun _ x σ => measure σ x)
      (fun _ x σ hI => by
        obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (hbody σ hI.1 x hI.2)
        cases r with
        | done y =>
          obtain ⟨c', rfl, hQ⟩ := hp
          exact ⟨x, σ, rfl, rfl, Or.inl ⟨(), c', by rw [loop, hr], hQ⟩⟩
        | cont x' =>
          exact ⟨x', σ, by rw [loop, hr], rfl, Or.inr ⟨(), ⟨hI.1, hp.1⟩, hp.2⟩⟩)
      () (init c) σ ⟨hG, hinit c σ hP hG⟩
  subst hσ
  exact ⟨c', hR.trans hx', hQ⟩

end Hax.Ascent.RustM
