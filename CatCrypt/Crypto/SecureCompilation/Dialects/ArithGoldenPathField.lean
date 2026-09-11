/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminComOK
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminDenote
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

@[expose] public section

set_option autoImplicit false

/-!
# Golden path, lifted to the neutral `arith` dialect — the template

The `*GoldenPath` crypto kernels were authored as `Com jasminDialect` (below the
waist). This file is the **template** for re-expressing them one level up, as
`Com arithDialect` (the upstream-aligned neutral dialect), connected to emit through
the *proven* arith→jasmin lowering:

* the kernel is `Com arithDialect` (the upstream-aligned source);
* `denote = <spec>` is the **same** `BitVec` proof as the jasmin twin (the arith
  denote was *defined* equal to the jasmin image), so it ports verbatim;
* `ArithOK64` (mechanical) ⇒ `lowerArithToJasmin_ComOK` ⇒ the lowered jasmin kernel
  is `ComOK`, so it rides the existing `com_arm_e2e` / `com_riscv_e2e` emit;
* `lowerArithToJasmin_denote` carries the spec down: the emitted code computes the
  arith kernel's value.

Worked on the field-add core `a + b`. The pattern is mechanical for every kernel.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithGoldenPathField

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.Arith
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
open CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-- **The neutral-`arith` field-add source.** `a + b` over `[i64, i64]`. -/
def arithAddCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.addi 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)

/-- Value proof at the neutral level — the same `rfl` as the jasmin twin. -/
theorem arithAddCom_denote (x0 x1 : BitVec 64) :
    arithAddCom.denote (.cons x0 (.cons x1 .nil)) = x1 + x0 := rfl

/-- Emit-legality (mechanical, one constructor per op). -/
theorem arithAddCom_ok : ArithOK64 arithAddCom :=
  ArithOK64.var rfl (ArithOK64.ret _)

/-- The lowered jasmin kernel is in the supported fragment (rides `com_*_e2e`). -/
theorem arithAddCom_lowered_ok : ComOK (lowerArithToJasmin arithAddCom) :=
  lowerArithToJasmin_ComOK arithAddCom_ok

/-- **The spec carried to the emit layer.** The lowered jasmin kernel — the thing
    the backends emit — computes the field-add value. -/
theorem arithAddCom_lowered_denote (x0 x1 : BitVec 64) :
    (lowerArithToJasmin arithAddCom).denote (mapVal (.cons x0 (.cons x1 .nil)))
      = x1 + x0 := by
  rw [lowerArithToJasmin_denote arithAddCom, arithAddCom_denote, transTy_int]

/-- **Emitted AArch64**, from the neutral-`arith` source via the proven lowering +
    the existing `com_arm_e2e` (no per-kernel backend proof). -/
theorem arithAddCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin arithAddCom) 2))).regs)
        (comRetName (lowerArithToJasmin arithAddCom) 2)
      = Com.denote (lowerArithToJasmin arithAddCom) V :=
  com_arm_e2e arithAddCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **Emitted RISC-V** — same neutral source, same lowering. -/
theorem arithAddCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin arithAddCom) 2))).regs)
        (comRetName (lowerArithToJasmin arithAddCom) 2)
      = Com.denote (lowerArithToJasmin arithAddCom) V :=
  com_riscv_e2e arithAddCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithGoldenPathField
