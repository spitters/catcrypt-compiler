/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresSolver

/-!
# Demo: `corres_solve` over straight-line x86 blocks

Route: a `JInstr` block run by `runBlock` refines a composed abstract transition
through the carry-tracking relation `SRcarry` (`CorresJ`). Each instruction has a
`@[corres]` leaf (`corresJ_sbb`, `corresJ_adc`, `corresJ_mulx`, `corresJ_adcx`);
`corres_solve` folds the leaves through `corresJ_cons` and reconciles the
synthesized fold with the stated transition by `rfl`.

Tactic: `corres_solve` (`Ascent/CorresSolver.lean`).

## Main results

* `sbb3_refines`: a three-limb subtract-with-borrow chain refines the composed
  `sbbStep` fold under `SRcarry`.
* `mulx_adcx_refines`: a widening multiply followed by an add-with-carry refines
  `adcStep ∘ mulxStep` under `SRcarry`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- A three-limb subtract-with-borrow chain `r0 -= s0; r1 -= s1 - CF; r2 -= s2 - CF`.
    The abstract transition subtracts limb by limb: after limb `i` the register
    holds the wrapped difference and the carry bit is
    `decide (rᵢ − sᵢ − cf < 0)` over `ℤ`, the borrow-out `sbbStep` writes; the
    borrow of limb `i` is the `cf` limb `i + 1` reads. -/
theorem sbb3_refines :
    CorresJ SRcarry (fun _ => True)
      (fun a => sbbStep "r2" "s2" (sbbStep "r1" "s1" (sbbStep "r0" "s0" a)))
      [.sbb "r0" (.reg "s0"), .sbb "r1" (.reg "s1"), .sbb "r2" (.reg "s2")] := by
  corres_solve

/-- A widening multiply followed by an add-with-carry: `(hi, lo) := x * y;
    acc += lo + CF`. `mulxStep` writes the low and high words of the 128-bit
    product `x * y` and leaves the carry bit unchanged; `adcStep` writes the
    wrapped sum `acc + lo + cf` and sets the carry bit to
    `decide (2 ^ 64 ≤ acc + lo + cf)` over `ℕ`. -/
theorem mulx_adcx_refines :
    CorresJ SRcarry (fun _ => True)
      (fun a => adcStep "acc" "lo" (mulxStep "hi" "lo" "x" "y" a))
      [.mulx "hi" "lo" (.reg "x") (.reg "y"), .adcx "acc" (.reg "lo")] := by
  corres_solve

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.sbb3_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sbb3_refines

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.mulx_adcx_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mulx_adcx_refines

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
