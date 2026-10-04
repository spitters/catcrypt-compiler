/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# The dialect-generic correspondence `CorresM`

`CorresM step SR P fa c` is the forward simulation of a machine with step function
`step : C → M → Option M` against an abstract state transformer `fa`, under the state
relation `SR` and the abstract precondition `P`. The definition uses only Lean core,
so modules that reason about the generic relation import no machine model.

## Main definitions

* `CorresM` — the forward simulation, generic in the machine state, the program and
  the step function
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-- The dialect-generic forward simulation: from a machine state `m` related by `SR`
    to an abstract state satisfying `P`, the step `step c` makes progress
    (`= some m'`) to a state related to the abstract result `fa a`. Generic in the
    machine state `M`, the program `C`, the step function, the state relation `SR`,
    and the abstract state `AState`. -/
def CorresM {M : Type} {C : Type} {AState : Type} (step : C → M → Option M)
    (SR : M → AState → Prop) (P : AState → Prop) (fa : AState → AState) (c : C) : Prop :=
  ∀ m a, SR m a → P a → ∃ m', step c m = some m' ∧ SR m' (fa a)

end CatCrypt.Crypto.SecureCompilation.Ascent
