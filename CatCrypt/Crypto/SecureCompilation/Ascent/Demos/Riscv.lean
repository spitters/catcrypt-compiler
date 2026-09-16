/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRiscvSolver

/-!
# A worked RV64 ascent: one limb of an add with carry-out

RV64 has no carry flag: the carry out of `t := a + b` is the word `t <ᵘ a`,
computed by `sltu`. `addCarryBlock` is that two-instruction idiom, and
`addCarry_ascends` refines it against the composed abstract fold through
`corres_sym_rv`. `addCarry_readout` reads the two written words back off the
abstract state.

## Main results

* `addCarry_ascends`: the add-with-carry-out block refines `addCarryStep` under
  `SRr`, by `corres_sym_rv`.
* `addCarry_readout`: the abstract state after the block holds the sum in `t0`
  and the carry word in `t1`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-- `t0 := a0 + a1; t1 := t0 <ᵘ a0` — the sum and its carry-out word. -/
def addCarryBlock : List RInst64 :=
  [ .add "t0" "a0" "a1", .sltu "t1" "t0" "a0" ]

/-- The abstract transition: the `add` step, then the `sltu` step on its result. -/
def addCarryStep (st : AStateR) : AStateR :=
  sltuStepR "t1" "t0" "a0" (addStepR "t0" "a0" "a1" st)

/-- The block refines its abstract fold: from any machine state related by `SRr`,
    running `addCarryBlock` lands in a state related to `addCarryStep`. -/
theorem addCarry_ascends :
    CorresR SRr (fun _ => True) addCarryStep addCarryBlock := by
  corres_sym_rv

/-- Reading the abstract result: `t0` holds the wrapped sum and `t1` holds the
    carry-out word, `1` exactly when the sum wrapped below `a0`. -/
theorem addCarry_readout (st : AStateR) :
    addCarryStep st "t0" = st "a0" + st "a1" ∧
    addCarryStep st "t1" = (if st "a0" + st "a1" < st "a0" then 1 else 0) := by
  simp +decide [addCarryStep, sltuStepR, addStepR, writeR]

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.addCarry_ascends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addCarry_ascends

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
