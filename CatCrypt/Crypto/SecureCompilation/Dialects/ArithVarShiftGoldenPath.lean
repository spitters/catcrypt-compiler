/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminComOK
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminDenote
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import Std.Tactic.BVDecide

set_option autoImplicit false

/-!
# Bounded public variable-shift, lifted to the neutral `arith` dialect

The `VarShiftEmitGoldenPath` bounded-public variable shift (mask-select tree of
immediate shifts) re-expressed as `Com arithDialect` — the same pattern as the other
lifted kernels (denote=spec + `ArithOK64` + lowered `ComOK` + arm/riscv emit through
the proven lowering). Shows the constant-time mask-select idiom lifts to arith with no
new ops, exactly as at the jasmin level.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithVarShiftGoldenPath

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

/-- Bounded (`n < 2`) public variable right-shift via a branchless mask-select of the
    immediate-shift candidates `a>>>0` / `a>>>1`, over `[a, n]`. Op-for-op the arith
    twin of `VarShiftEmit.boundedShrCom`. -/
def boundedShrArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.constant 64 0) rfl .nil)
  (.var (.mk (.subi 64) rfl (.cons .here (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.constant 64 18446744073709551615) rfl .nil)
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shrui_imm 64 1) rfl (.cons (.there (.there (.there (.there .here)))) .nil))
  (.var (.mk (.andi 64) rfl (.cons .here (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.andi 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there .here))))))
        (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here))))))))

theorem boundedShrArithCom_denote (a n : BitVec 64) :
    boundedShrArithCom.denote (.cons a (.cons n .nil))
      = ((a >>> 1) &&& ((0 : BitVec 64) - n))
          ||| (a &&& (((0 : BitVec 64) - n) ^^^ BitVec.ofNat 64 18446744073709551615)) := by
  unfold boundedShrArithCom; rfl

/-- **The non-vacuous bounded-public correctness** (ports verbatim from the jasmin
    twin): for `n.toNat < 2` the mask-select denotes exactly `a >>> n.toNat`. -/
theorem boundedShrArithCom_spec (a n : BitVec 64) (hn : n.toNat < 2) :
    boundedShrArithCom.denote (.cons a (.cons n .nil)) = a >>> n.toNat := by
  rw [boundedShrArithCom_denote]
  have h : n = 0 ∨ n = 1 := by bv_omega
  rcases h with rfl | rfl
  · show _ = a >>> (0 : Nat); bv_decide
  · show _ = a >>> (1 : Nat); bv_decide

theorem boundedShrArithCom_ok : ArithOK64 boundedShrArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.ret _))))))))

theorem boundedShrArithCom_lowered_ok : ComOK (lowerArithToJasmin boundedShrArithCom) :=
  lowerArithToJasmin_ComOK boundedShrArithCom_ok

theorem boundedShrArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin boundedShrArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin boundedShrArithCom) 2)
      = Com.denote (lowerArithToJasmin boundedShrArithCom) V :=
  com_arm_e2e boundedShrArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

theorem boundedShrArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin boundedShrArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin boundedShrArithCom) 2)
      = Com.denote (lowerArithToJasmin boundedShrArithCom) V :=
  com_riscv_e2e boundedShrArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithVarShiftGoldenPath
