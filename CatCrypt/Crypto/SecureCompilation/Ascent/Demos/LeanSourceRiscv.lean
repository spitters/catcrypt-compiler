/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresDescentRiscv
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

/-!
# Lean source functions through the descent to the RV64 machine

The RV64 twin of `Demos.LeanSourceX86`: the Lean functions
`fun a b : BitVec 64 => a + b` and `a - b`, as the descent fragments `binFrag .add`
and `binFrag .sub` closed at slot `0` over `twoArgEnv`, compiled through
`comToRegProg`, `regToROp` and `lowerRBlock64`. `corresR_of_refines` turns each
descent result into the `CorresR`-shaped simulation over `runRBlock64`, and reading
its exit relation at the valuation `[b, a]` gives the closed statement: the compiled
RV64 block, run from a state with `a` in `v0` and `b` in `v1`, leaves `a + b` (resp.
`a - b`) in the result register.

## Main results

* `add_descent_riscv`, `sub_descent_riscv`: the compiled RV64 block of the Lean
  function leaves `a + b` (resp. `a - b`) in the result register.
* `binOp_descent_riscv`: the same for any `binFrag` binary operation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
open CatCrypt.Crypto.SecureCompilation.Ascent

/-- The two-argument word kernel of a supported ALU op, compiled through the
    descent and run on RV64 from a state with `a` in `v0` and `b` in `v1`, leaves
    `op.apply a b` in the result register. -/
theorem binOp_descent_riscv (op : JasminBinOp) (hop : SupportedOp (.regArith op 64))
    (a b : BitVec 64) (s : RState64) (hs : s.regs = envOf 2 (twoArgVal a b)) :
    (runRBlock64 s (lowerRBlock64 (regToROp
        (comToRegProg (descentCom (binFrag op) twoArgEnv 0) 2)))).regs
      (comRetName (descentCom (binFrag op) twoArgEnv 0) 2) = op.apply a b := by
  rw [← binStep_readout op a b]
  exact corresR_of_refines FieldEmitGoldenPath.allReg64_two twoArgEnv (binFrag_refines op) 0
    (binCom_ok op hop) s _ ⟨_, hs, rfl⟩

/-- The compiled RV64 block of `fun a b : BitVec 64 => a + b`, run from a state with
    `a` in `v0` and `b` in `v1`, leaves `a + b` in the result register. -/
theorem add_descent_riscv (a b : BitVec 64) (s : RState64)
    (hs : s.regs = envOf 2 (twoArgVal a b)) :
    (runRBlock64 s (lowerRBlock64 (regToROp
        (comToRegProg FieldEmitGoldenPath.fieldAddCom 2)))).regs
      (comRetName FieldEmitGoldenPath.fieldAddCom 2) = a + b :=
  binOp_descent_riscv .add (by supported_op) a b s hs

/-- The compiled RV64 block of `fun a b : BitVec 64 => a - b`, run from a state with
    `a` in `v0` and `b` in `v1`, leaves `a - b` in the result register. -/
theorem sub_descent_riscv (a b : BitVec 64) (s : RState64)
    (hs : s.regs = envOf 2 (twoArgVal a b)) :
    (runRBlock64 s (lowerRBlock64 (regToROp (comToRegProg descentSubCom 2)))).regs
      (comRetName descentSubCom 2) = a - b :=
  binOp_descent_riscv .sub (by supported_op) a b s hs

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.add_descent_riscv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_descent_riscv

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.sub_descent_riscv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sub_descent_riscv

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
