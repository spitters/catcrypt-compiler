/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirToComFront
import CatCrypt.Crypto.SecureCompilation.ScalarLinFront
import CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmAsmPrinter

/-!
# Hello, compiler: a program compiled to assembly, and printed

The compiler takes input through a front — never a hand-authored `Com`. Here the
hax front lowers a straight-line arithmetic routine; the compiled AArch64 block is
printed by `#eval`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompilerHelloDemo

open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm

/-- The source, as hax extracts it: Rust `fn f(a, b) { let t = a * b; t + a }`
    as a `Thir` the front lowers. Not a hand-authored `Com`. -/
def srcThir : Thir :=
  .let_ "t" (.mul (.inp 0) (.inp 1))
    (.let_ "r" (.add (.lvar "t") (.inp 0))
      (.ret (.lvar "r")))

/-- The front lowers it at width 64 with two inputs. -/
theorem srcThir_lowers :
    (thirToJasmin (w := 64) (nIn := 2) [] (initFState 64 2) srcThir).isSome := by
  native_decide

/-- The front's output `Com` — produced by the front, not authored. -/
def srcCom : Com jasminDialect (frontCtxt 64 2 []) (rW 64) :=
  (thirToJasmin (w := 64) (nIn := 2) [] (initFState 64 2) srcThir).get srcThir_lowers

/-- Compiled to an AArch64 machine block: `Com → RegProg → AArch64`. -/
def srcArm : List BInst := lowerBBlock (regToBOp (comToRegProg srcCom 2))

/-- A register assignment for printing (`v0 → w0`, … — the AAPCS64 convention). -/
def demoAlloc : GpAlloc := (List.range 8).map (fun i => ("v" ++ toString i, "w" ++ toString i))

-- The emitted AArch64 assembly. `#eval` prints it:
--   mul w2, w1, w0
--   add w3, w2, w1
--   orr w4, w3, w3
#eval String.intercalate "\n" (renderBBlockBody demoAlloc srcArm)

/-! ## Correctness

The front's value-preservation (`ThirToComFront.thirToJasmin_denote`) proves `srcCom`
denotes the source; `MultiBackendDemo.com_riscv_e2e` proves the compiled machine
block computes that denotation for every supported program (shown there for RISC-V;
the AArch64 lowering carries the same denotation keystone).

The relational front is the other on-ramp: `RelationalFrontCurve25519` realizes the
Curve25519 base-field add and multiply from their `ZMod` specifications, over a
4×64-bit carrier, with the field laws proved (`c25519_add_commutes`,
`c25519_mul_commutes`). -/

end CatCrypt.Crypto.SecureCompilation.CompilerHelloDemo
