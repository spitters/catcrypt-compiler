/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Calculus.RustMSquare

/-!
# The `RustM` square as `Std.Do` specifications

The square `Hax.Ascent.RustM.CorresM` over a state-passing `RustM` program, stated as
`Std.Do` triples. `corresM_spec_at` is the triple at a fixed concrete state `c` and
abstract state `σ`, with the fixed postcondition `r.1 = V σ ∧ Q r.2 σ`; the family of
these triples is equivalent to the square (`corresM_iff_spec_at`). Because the
postcondition is fixed by `σ`, `mvcgen` composes the triple with a continuation.
`corresM_spec_post` is the form with the postcondition as a parameter.

## Main definitions

* `corresM_spec_at`, `corresM_iff_spec_at`, `corresM_spec_post`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent.RustM

open Aeneas.Std
open Std.Do

variable {C S A : Type} {P Q : C → S → Prop} {G : S → Prop}
  {p : C → Aeneas.Std.RustM (A × C)} {V : S → A}

/-- The `Std.Do` triple of a square at a fixed concrete state `c` and abstract state
    `σ`: under the entry relation and the guard, `p c` returns the value `V σ` and a
    state related to `σ` by `Q`. The postcondition is fixed by `σ`, so an instance
    with `c` and `σ` universally quantified is a specification `mvcgen` composes with
    a continuation. -/
theorem corresM_spec_at (h : CorresM P G p V Q) (c : C) (σ : S) (hP : P c σ)
    (hG : G σ) :
    ⦃⌜True⌝⦄ p c ⦃⇓ r => ⌜r.1 = V σ ∧ Q r.2 σ⌝⦄ := by
  obtain ⟨c', hQ, ht⟩ := corresM_iff_triple.mp h c σ hP hG
  exact (Aeneas.Std.WP.triple_iff_post_of_eq_ok
    (Aeneas.Std.WP.triple_post_eq_iff_eq.mp ht)).mpr ⟨rfl, hQ⟩

/-- The square is equivalent to the family of triples of `corresM_spec_at`. -/
theorem corresM_iff_spec_at :
    CorresM P G p V Q ↔
      ∀ c σ, P c σ → G σ → ⦃⌜True⌝⦄ p c ⦃⇓ r => ⌜r.1 = V σ ∧ Q r.2 σ⌝⦄ := by
  refine ⟨corresM_spec_at, fun h => corresM_iff_triple.mpr fun c σ hP hG => ?_⟩
  obtain ⟨r, hr, hV, hQ⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (h c σ hP hG)
  refine ⟨r.2, hQ, Aeneas.Std.WP.triple_post_eq_iff_eq.mpr ?_⟩
  rw [hr, ← hV]

/-- The triple of a square for an arbitrary postcondition `R` on the returned pair:
    it suffices that some abstract state `σ` satisfies the entry relation and the
    guard, and that `R` holds at `(V σ, c')` for every exit state `c'` related to
    `σ` by `Q`. -/
theorem corresM_spec_post (h : CorresM P G p V Q) (c : C) (R : A × C → Prop)
    (hpre : ∃ σ, P c σ ∧ G σ ∧ ∀ c', Q c' σ → R (V σ, c')) :
    ⦃⌜True⌝⦄ p c ⦃⇓ r => ⌜R r⌝⦄ := by
  obtain ⟨σ, hP, hG, hR⟩ := hpre
  obtain ⟨c', hQ, ht⟩ := corresM_iff_triple.mp h c σ hP hG
  exact (Aeneas.Std.WP.triple_iff_post_of_eq_ok
    (Aeneas.Std.WP.triple_post_eq_iff_eq.mp ht)).mpr (hR c' hQ)

end Hax.Ascent.RustM
