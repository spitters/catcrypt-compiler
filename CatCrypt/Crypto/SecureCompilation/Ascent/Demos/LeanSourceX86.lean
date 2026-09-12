/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresDescentX86
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

/-!
# Lean source functions through the descent to the x86 machine

The Lean functions `fun a b : BitVec 64 => a + b` and `a - b` reach the descent as
`binFrag .add` and `binFrag .sub`; closed at slot `0` over `twoArgEnv` the first is
`fieldAddCom` by unfolding. `corres_of_refines_x86` turns each descent result into
a forward simulation at the x86 machine, and reading the exit relation at the
valuation `[b, a]` gives the closed statement: the compiled x86 block, run from a
state with `a` in `v0` and `b` in `v1`, leaves `a + b` (resp. `a - b`) in the result
register.

## Main results

* `add_descent_x86`, `sub_descent_x86`: the compiled x86 block of the Lean
  function leaves `a + b` (resp. `a - b`) in the result register.
* `binOp_descent_x86`: the same for any `binFrag` binary operation.
* `fieldAddCom_eq_descent`: `fieldAddCom` is the descent's closed `Com` for `add`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo
open CatCrypt.Crypto.SecureCompilation.Ascent

/-- The two-argument word kernel of a supported ALU op, compiled through the
    descent and run on x86 from a state with `a` in `v0` and `b` in `v1`, leaves
    `op.apply a b` in the result register. -/
theorem binOp_descent_x86 (op : JasminBinOp) (hop : SupportedOp (.regArith op 64))
    (a b : BitVec 64) (s : XState) (hs : s.regs = envOf 2 (twoArgVal a b)) :
    (x86Target.runOps s
        (x86Target.compile (comToRegProg (descentCom (binFrag op) twoArgEnv 0) 2))).regs
      (comRetName (descentCom (binFrag op) twoArgEnv 0) 2) = op.apply a b := by
  obtain ⟨m', hstep, hout⟩ := corres_of_refines_x86 FieldEmitGoldenPath.allReg64_two twoArgEnv
    (binFrag_refines op) 0 (binCom_ok op hop) (binCom_shiftOK op) s _ ⟨_, hs, rfl⟩ trivial
  replace hstep := Option.some.inj hstep
  subst hstep
  rw [← binStep_readout op a b]
  exact hout

/-- `fieldAddCom` is the two-argument add kernel closed through the descent. -/
theorem fieldAddCom_eq_descent :
    FieldEmitGoldenPath.fieldAddCom = descentCom (binFrag .add) twoArgEnv 0 := rfl

/-- The compiled x86 block of `fun a b : BitVec 64 => a + b`, run from a state with
    `a` in `v0` and `b` in `v1`, leaves `a + b` in the result register. -/
theorem add_descent_x86 (a b : BitVec 64) (s : XState)
    (hs : s.regs = envOf 2 (twoArgVal a b)) :
    (x86Target.runOps s
        (x86Target.compile (comToRegProg FieldEmitGoldenPath.fieldAddCom 2))).regs
      (comRetName FieldEmitGoldenPath.fieldAddCom 2) = a + b :=
  binOp_descent_x86 .add (by supported_op) a b s hs

/-- The compiled x86 block of `fun a b : BitVec 64 => a - b`, run from a state with
    `a` in `v0` and `b` in `v1`, leaves `a - b` in the result register. -/
theorem sub_descent_x86 (a b : BitVec 64) (s : XState)
    (hs : s.regs = envOf 2 (twoArgVal a b)) :
    (x86Target.runOps s (x86Target.compile (comToRegProg descentSubCom 2))).regs
      (comRetName descentSubCom 2) = a - b :=
  binOp_descent_x86 .sub (by supported_op) a b s hs

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.add_descent_x86' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_descent_x86

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.sub_descent_x86' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sub_descent_x86

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
