/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresX86Solver

/-!
# Demo: `corres_sym` over straight-line x86 blocks

Route: a `JInstr` block run by `runBlock` refines a composed abstract transition
(`CorresJ`), through the carry-tracking relation `SRcarry` for the carry-family
instructions and through the register-only relation `SRx` for the value
instructions. Each instruction has a `@[corres]` leaf (`corresJ_sbb`,
`corresJ_adc`, `corresJ_mulx`, `corresJ_adcx` under `SRcarry`; `corresJ_movX`,
`corresJ_addX`, `corresJ_shlX`, … under `SRx`); `corres_sym` puts a block given
as the compiled output of the x86 `ScalarTarget` in weak head normal form
instruction by instruction, folds the leaves through `corresJ_cons_true` and
compares the synthesized fold with the stated transition by definitional
equality.

Tactic: `corres_sym` (`Ascent/CorresSolver.lean`), over the leaves of
`Ascent/CorresX86Solver.lean`.

## Main results

* `sbb3_refines`: a three-limb subtract-with-borrow chain refines the composed
  `sbbStep` fold under `SRcarry`.
* `mulx_adcx_refines`: a widening multiply followed by an add-with-carry refines
  `adcStep ∘ mulxStep` under `SRcarry`.
* `alu_refines`: a move, an add, a subtract and a shift by an immediate refine
  the composed value fold under `SRx`.
* `compiled_refines`: the x86 `ScalarTarget`'s output on a two-statement
  `RegProg`, translated by `xinstrToJ`, refines the two-address fold under `SRx`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo
open CatCrypt.Crypto.SecureCompilation.X86Backend
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
  corres_sym

/-- A widening multiply followed by an add-with-carry: `(hi, lo) := x * y;
    acc += lo + CF`. `mulxStep` writes the low and high words of the 128-bit
    product `x * y` and leaves the carry bit unchanged; `adcStep` writes the
    wrapped sum `acc + lo + cf` and sets the carry bit to
    `decide (2 ^ 64 ≤ acc + lo + cf)` over `ℕ`. -/
theorem mulx_adcx_refines :
    CorresJ SRcarry (fun _ => True)
      (fun a => adcStep "acc" "lo" (mulxStep "hi" "lo" "x" "y" a))
      [.mulx "hi" "lo" (.reg "x") (.reg "y"), .adcx "acc" (.reg "lo")] := by
  corres_sym

/-- A value block: `r := a; r += b; r -= c; r <<= 3`. Under `SRx` no flag is
    tracked; each step is the abstract register write of the word the
    instruction computes, the shift count masked as Jasmin masks it. -/
theorem alu_refines :
    CorresJ SRx (fun _ => True)
      (fun st => shlStepX "r" (.imm 3) (subStepX "r" (.reg "c") (addStepX "r" (.reg "b")
        (movStepX "r" (.reg "a") st))))
      [.mov "r" (.reg "a"), .add "r" (.reg "b"), .sub "r" (.reg "c"), .shl "r" (.imm 3)] := by
  corres_sym

/-- The x86 `ScalarTarget` compiles `r := a + b; s := r >> 3` to the two-address
    pairs `mov r a; add r b; mov s r; shr s 3`; translated by `xinstrToJ`, the
    block refines the fold of the four value steps. -/
theorem compiled_refines :
    CorresJ SRx (fun _ => True)
      (fun st => shrStepX "s" (.imm 3) (movStepX "s" (.reg "r")
        (addStepX "r" (.reg "b") (movStepX "r" (.reg "a") st))))
      ((x86Target.compile [.add "r" "a" "b", .shrI "s" "r" 3]).map xinstrToJ) := by
  corres_sym

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.sbb3_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sbb3_refines

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.mulx_adcx_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mulx_adcx_refines

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.alu_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alu_refines

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.compiled_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiled_refines

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
