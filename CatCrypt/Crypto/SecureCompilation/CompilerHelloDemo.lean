/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public meta import CatCrypt.Crypto.SecureCompilation.ScalarLinFront
public import CatCrypt.Crypto.SecureCompilation.ScalarLinFront
public meta import CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
public import CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo

/-!
# Hello, compiler: a program compiled to assembly, printed, and proved correct

The compiler takes input through a front. Here the hax front lowers a straight-line
64-bit arithmetic routine, the compiled AArch64 block is printed by `#eval` over the
64-bit `xN` registers, and `srcArm_correct` states that running the block computes
the denotation of the front's output.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompilerHelloDemo

open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo

/-- The source, as hax extracts it: Rust `fn f(a, b) { let t = a * b; t + a }`
    as a `Thir` the front lowers into the compiler's IR. -/
def srcThir : Thir :=
  .let_ "t" (.mul (.inp 0) (.inp 1))
    (.let_ "r" (.add (.lvar "t") (.inp 0))
      (.ret (.lvar "r")))

/-- The front lowers it at width 64 with two inputs. `thirToJasmin` is defined by
    well-founded recursion, so the check runs in the kernel. -/
theorem srcThir_lowers :
    (thirToJasmin (w := 64) (nIn := 2) [] (initFState 64 2) srcThir).isSome := by
  decide +kernel

/-- The front's output `Com`, produced by the front. -/
def srcCom : Com jasminDialect (frontCtxt 64 2 []) (rW 64) :=
  (thirToJasmin (w := 64) (nIn := 2) [] (initFState 64 2) srcThir).get srcThir_lowers

/-- Compiled to an AArch64 machine block: `Com → RegProg → AArch64`. -/
def srcArm : List BInst := lowerBBlock (regToBOp (comToRegProg srcCom 2))

/-- A register assignment for printing: `vN ↦ xN`, the 64-bit general-purpose
    registers, matching the 64-bit `BInst` block. -/
def demoAlloc : GpAlloc := (List.range 8).map (fun i => ("v" ++ toString i, "x" ++ toString i))

-- The emitted AArch64 assembly. `#eval` prints it:
--   mul x2, x1, x0
--   add x3, x2, x1
--   orr x4, x3, x3
#eval String.intercalate "\n" (renderBBlockBody demoAlloc srcArm)

/-! ## Correctness

`srcCom` is in the fragment `ComOK` (three bindings, each a supported 64-bit op) over
a context of 64-bit registers, so `ScalarLinNeutralDemo.com_arm_e2e` applies to it.
The front's value-preservation (`ThirToComFront.thirToJasmin_denote`) relates
`Com.denote srcCom` to the source. The printer carries no theorem.

The relational front is the other on-ramp: `RelationalFrontCurve25519` realizes the
Curve25519 base-field add and multiply from their `ZMod` specifications, over a
4×64-bit carrier, with the field laws proved (`c25519_add_commutes`,
`c25519_mul_commutes`). -/

/-- The front's output is a straight-line program over the supported 64-bit ops. -/
theorem srcCom_ok : ComOK srcCom := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp srcThir_lowers
  have hs : srcCom = c := Option.get_of_eq_some _ hc
  rw [hs]
  simp [thirToJasmin, srcThir, rhsExpr, Atom.toVar, FState.push, initFState,
    inputVarRep] at hc
  cases hc
  exact ComOK.var (by supported_op) (ComOK.var (by supported_op)
    (ComOK.var (by supported_op) (ComOK.ret _)))

/-- The input context of the front is two 64-bit registers. -/
theorem srcCtxt_allReg64 : AllReg64 (frontCtxt 64 2 []) :=
  fun _ ht => (List.mem_replicate.mp ht).2

/-- Running the compiled AArch64 block from a machine state whose registers hold the
    inputs `V` leaves `Com.denote srcCom V` in the result register. An instance of
    `com_arm_e2e`. -/
theorem srcArm_correct (V : Ctxt.Valuation (frontCtxt 64 2 [])) (s : BState)
    (hs : s.regs = envOf 2 V) :
    (runBBlock s srcArm).regs (comRetName srcCom 2) = Com.denote srcCom V := by
  rw [srcArm, bignumBlock_lowering_denote]
  exact com_arm_e2e srcCom_ok srcCtxt_allReg64 V s hs

end CatCrypt.Crypto.SecureCompilation.CompilerHelloDemo
