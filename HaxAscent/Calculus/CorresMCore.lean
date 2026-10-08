/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Refines
public import CatCryptCore.Refinement.Programs

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

## Main results

* `corresM_iff_rrelPT`: `CorresM` is the refinement `GuardedRRelPT`
  (`CatCryptCore/Refinement/Programs.lean`) of the guarded update by `wpRel` of the
  step relation.
* `corresM_trans_of_rrelPT`: the composition of a `CorresM` with a forward simulation,
  derived from `guardedRRelPT_trans`.
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

section RRel

open Std.Do
open CatCrypt.Refinement

variable {AState : Type}

/-- `CorresM step SR P fa c` is `GuardedRRelPT` at the step relation of `step c`. -/
theorem corresM_iff_rrelPT {M C : Type} (step : C → M → Option M) (SR : M → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : C) :
    CorresM step SR P fa c ↔
      GuardedRRelPT SR P fa (wpRel fun m (_ : Unit) m' => step c m = some m') :=
  corresRel_iff_rrelPT SR P fa _

/-- **Composition of `CorresM` with a forward simulation.** A correspondence for `c₁`
    under `step₁` and a refinement of its step relation by that of `c₂` under `step₂`
    at the assertion map `AssnRel.ofRel R` give the correspondence for `c₂` at the
    composite relation. -/
theorem corresM_trans_of_rrelPT {M₁ M₂ C₁ C₂ : Type} {step₁ : C₁ → M₁ → Option M₁}
    {step₂ : C₂ → M₂ → Option M₂} {SR : M₁ → AState → Prop} {R : M₂ → M₁ → Prop}
    {P : AState → Prop} {fa : AState → AState} {c₁ : C₁} {c₂ : C₂}
    (h₁ : CorresM step₁ SR P fa c₁)
    (h₂ : RRelPT (AssnRel.ofRel R) (fun (_ : Unit) (_ : Unit) => True)
      (fun (_ : Unit) (_ : Unit) => True) (wpRel fun m (_ : Unit) m' => step₁ c₁ m = some m')
      (wpRel fun m (_ : Unit) m' => step₂ c₂ m = some m')) :
    CorresM step₂ (fun m₂ a => ∃ m₁, R m₂ m₁ ∧ SR m₁ a) P fa c₂ :=
  (corresM_iff_rrelPT _ _ _ _ _).mpr
    (guardedRRelPT_trans () ((corresM_iff_rrelPT _ _ _ _ _).mp h₁) h₂)

end RRel

end CatCrypt.Crypto.SecureCompilation.Ascent
