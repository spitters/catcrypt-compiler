/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockMvcgen

@[expose] public section
set_option autoImplicit false

/-!
# `CorresJ` as a specification for an arbitrary postcondition

`corresJ_iff_triple` reads `CorresJ SR P fa c` as the family of triples
`{SR · a} c {SR · (fa a)}` indexed by the abstract state `a`. The postcondition of
each member is fixed, so a caller whose goal is another predicate `Q` has to apply
the consequence rule by hand.

This module states the same correspondence with the postcondition as a parameter:

    {fun st => ∃ a, SR st a ∧ P a ∧ ∀ st', SR st' (fa a) → Q st'} c {Q}

The precondition asks for an abstract state related to the initial machine state,
the abstract precondition at it, and the implication from the relation at the
abstract result to `Q`.

## Main results

* `corresJ_triple_post` — the `RunBlockTriple` form.
* `corresJ_iff_triple_post` — `CorresJ` is equivalent to this family over all `Q`.
* `corresJ_spec` — the `Std.Do` form over `runBlockM c`, with the postcondition a
  `PostCond` variable.
* `corresJ_spec_at` — the `Std.Do` triple at a fixed abstract state, the image of
  `corresJ_toTriple` under `runBlockM_triple_iff`.

## Use under `mvcgen`

`mvcgen` resolves a specification given as a constant or a local hypothesis, so a
call site names an instance of one of the two `Std.Do` forms (a theorem, or a
`have`) and passes that name.

`corresJ_spec_at` is the form `mvcgen` composes at any position. Its postcondition
is fixed, so `mvcgen` emits the entailment from `SR · (fa a)` to the weakest
precondition of the continuation as a goal of its own and generates the
verification conditions of the continuation from it.

`corresJ_spec` applies at any position as well, but its precondition mentions the
postcondition at a state `st'` bound inside a pure proposition. When the call is
followed by further code, the weakest precondition of the continuation is placed
under that binder, where `mvcgen` does not generate verification conditions. It
is the suitable form when `runBlockM c` is the last call of the program, or with
a postcondition that is not `SR · (fa a)` for the abstract state at hand.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.Do
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

variable {AState : Type} {SR : JState 64 → AState → Prop} {P : AState → Prop}
  {fa : AState → AState} {c : List (JInstr 64)}

/-- A `CorresJ` correspondence gives a `runBlock` triple for every postcondition `Q`:
    the precondition holds at `st` when some abstract state `a` is related to `st`,
    satisfies `P`, and every machine state related to `fa a` satisfies `Q`. -/
theorem corresJ_triple_post (h : CorresJ SR P fa c) (Q : JState 64 → Prop) :
    RunBlockTriple (fun st => ∃ a, SR st a ∧ P a ∧ ∀ st', SR st' (fa a) → Q st') c Q :=
  fun st ⟨a, hSR, hP, hQ⟩ => hQ _ (h st a hSR hP)

/-- The family of triples of `corresJ_triple_post` over all postconditions gives
    back the correspondence, by instantiating `Q` with `SR · (fa a)`. -/
theorem corresJ_of_triple_post
    (h : ∀ Q : JState 64 → Prop,
      RunBlockTriple (fun st => ∃ a, SR st a ∧ P a ∧ ∀ st', SR st' (fa a) → Q st') c Q) :
    CorresJ SR P fa c :=
  fun st a hSR hP => h (fun st' => SR st' (fa a)) st ⟨a, hSR, hP, fun _ h' => h'⟩

/-- `CorresJ SR P fa c` is equivalent to the family of `runBlock` triples of
    `corresJ_triple_post` over all postconditions. -/
theorem corresJ_iff_triple_post :
    CorresJ SR P fa c ↔ ∀ Q : JState 64 → Prop,
      RunBlockTriple (fun st => ∃ a, SR st a ∧ P a ∧ ∀ st', SR st' (fa a) → Q st') c Q :=
  ⟨corresJ_triple_post, corresJ_of_triple_post⟩

/-- The `Std.Do` form of `corresJ_triple_post` over `runBlockM c`. The postcondition
    is an arbitrary `PostCond`; the precondition evaluates it at every machine
    state related to `fa a`. -/
theorem corresJ_spec (h : CorresJ SR P fa c) (Q : PostCond Unit psJM) :
    ⦃fun st => ⌜∃ a, SR st a ∧ P a ∧ ∀ st', SR st' (fa a) → (Q.1 () st').down⌝⦄
      runBlockM c ⦃Q⦄ :=
  (runBlockM_triple_iff _ (fun st => (Q.1 () st).down) c).mpr (corresJ_triple_post h _)

/-- The `Std.Do` triple at a fixed abstract state `a` satisfying `P`: from `SR · a`,
    `runBlockM c` reaches `SR · (fa a)`. An instance with `a` left universally
    quantified is a specification `mvcgen` composes with a continuation. -/
theorem corresJ_spec_at (h : CorresJ SR P fa c) (a : AState) (ha : P a) :
    ⦃fun st => ⌜SR st a⌝⦄ runBlockM c ⦃⇓ _ st => ⌜SR st (fa a)⌝⦄ :=
  (runBlockM_triple_iff _ _ c).mpr (corresJ_toTriple SR P fa c h a ha)

end CatCrypt.Crypto.SecureCompilation.Ascent
