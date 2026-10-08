/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Refines

/-!
# The dialect-generic correspondence `CorresM`

`CorresM step SR P fa c` is the forward simulation of a machine with step function
`step : C → M → Option M` against an abstract state transformer `fa`, under the state
relation `SR` and the abstract precondition `P`: the forward simulation `RefinesP`
(`Ascent/Refines.lean`) of `fa` by `step c` with `SR` as the input and the output
relation. The module imports no machine model.

## Main definitions

* `CorresM` — the forward simulation, generic in the machine state, the program and
  the step function
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-- The dialect-generic forward simulation: from a machine state `m` related by `SR`
    to an abstract state satisfying `P`, the step `step c` makes progress
    (`= some m'`) to a state related to the abstract result `fa a`. It is `RefinesP`
    of `fa` by `step c` with `SR` on inputs and outputs. -/
abbrev CorresM {M : Type} {C : Type} {AState : Type} (step : C → M → Option M)
    (SR : M → AState → Prop) (P : AState → Prop) (fa : AState → AState) (c : C) : Prop :=
  _root_.Hax.Ascent.RefinesP (step c) SR SR P fa

end CatCrypt.Crypto.SecureCompilation.Ascent
