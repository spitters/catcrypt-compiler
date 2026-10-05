/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Calculus.CorresMCore

/-!
# The generic correspondence as a specification for an arbitrary postcondition

`CorresM step SR P fa c` fixes the postcondition of the step at `SR · (fa a)`. This
module states the same correspondence with the postcondition `Q : M → Prop` as a
parameter. `StepTriple step pre c post` is the total triple over an `Option`-valued
step: from every state satisfying `pre`, the step succeeds in a state satisfying
`post`. The correspondence is equivalent to the family of triples

    StepTriple step (fun m => ∃ a, SR m a ∧ P a ∧ ∀ m', SR m' (fa a) → Q m') c Q

over all `Q` (`corresM_iff_post`). The precondition asks for an abstract state
related to the initial machine state, the abstract precondition at it, and the
implication from the relation at the abstract result to `Q`.

The statements use only the definition `CorresM`; the machine instances are in
`CorresInstanceSpec`, the `RustM` square in `RustMSquareSpec`.

## Main definitions

* `StepTriple`, `StepTriple.consequence` — the total triple over an `Option`-valued step
* `corresM_post`, `corresM_of_post`, `corresM_iff_post` — the generic correspondence
  and the family of triples over all postconditions
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## The total triple over a step -/

/-- The total triple over an `Option`-valued step: from every machine state
    satisfying `pre`, the step `step c` succeeds in a state satisfying `post`. -/
def StepTriple {M C : Type} (step : C → M → Option M) (pre : M → Prop) (c : C)
    (post : M → Prop) : Prop :=
  ∀ m, pre m → ∃ m', step c m = some m' ∧ post m'

/-- Consequence: strengthen the precondition, weaken the postcondition. -/
theorem StepTriple.consequence {M C : Type} {step : C → M → Option M}
    {pre pre' post post' : M → Prop} {c : C} (hpre : ∀ m, pre' m → pre m)
    (hpost : ∀ m, post m → post' m) (h : StepTriple step pre c post) :
    StepTriple step pre' c post' := by
  intro m hm
  obtain ⟨m', hstep, hm'⟩ := h m (hpre m hm)
  exact ⟨m', hstep, hpost m' hm'⟩

/-! ## The generic correspondence -/

section Generic

variable {M C AState : Type} {step : C → M → Option M} {SR : M → AState → Prop}
  {P : AState → Prop} {fa : AState → AState} {c : C}

/-- A `CorresM` correspondence gives a step triple for every postcondition `Q`: the
    precondition holds at `m` when some abstract state `a` is related to `m`,
    satisfies `P`, and every machine state related to `fa a` satisfies `Q`. -/
theorem corresM_post (h : CorresM step SR P fa c) (Q : M → Prop) :
    StepTriple step (fun m => ∃ a, SR m a ∧ P a ∧ ∀ m', SR m' (fa a) → Q m') c Q := by
  rintro m ⟨a, hSR, hP, hQ⟩
  obtain ⟨m', hstep, hSR'⟩ := h m a hSR hP
  exact ⟨m', hstep, hQ m' hSR'⟩

/-- The family of triples of `corresM_post` over all postconditions gives the
    correspondence, by instantiating `Q` with `SR · (fa a)`. -/
theorem corresM_of_post
    (h : ∀ Q : M → Prop,
      StepTriple step (fun m => ∃ a, SR m a ∧ P a ∧ ∀ m', SR m' (fa a) → Q m') c Q) :
    CorresM step SR P fa c :=
  fun m a hSR hP => h (fun m' => SR m' (fa a)) m ⟨a, hSR, hP, fun _ h' => h'⟩

/-- `CorresM step SR P fa c` is equivalent to the family of step triples of
    `corresM_post` over all postconditions. -/
theorem corresM_iff_post :
    CorresM step SR P fa c ↔ ∀ Q : M → Prop,
      StepTriple step (fun m => ∃ a, SR m a ∧ P a ∧ ∀ m', SR m' (fa a) → Q m') c Q :=
  ⟨corresM_post, corresM_of_post⟩

end Generic

end CatCrypt.Crypto.SecureCompilation.Ascent
