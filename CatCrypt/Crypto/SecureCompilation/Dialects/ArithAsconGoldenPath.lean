/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminComOK
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminDenote
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithEmulations
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import Std.Tactic.BVDecide

set_option autoImplicit false

/-!
# The Ascon primitive family, lifted to the neutral `arith` dialect

Item 1 of the MLIR dialect-alignment restructure: re-express the Ascon permutation's
linear diffusion layer (`Σ₀..Σ₄`) and nonlinear S-box (`y0..y4`) one level up, from
`Com jasminDialect` (below the waist) to `Com arithDialect` (the upstream-aligned
neutral dialect), connected to emit through the *proven* arith→jasmin lowering.

The two source files this mirrors are `AsconLinearGoldenPath.lean` (the `Σ` functions)
and `AsconSboxGoldenPath.lean` (the S-box lanes), both authored as `Com jasminDialect`.
The de-Bruijn structure of each kernel is **identical** to its jasmin twin; only the op
names change (`.regArith .xor 64 → .xori 64`, `.shrImm 64 k → .shrui_imm 64 k`,
`.regConst 64 n → .constant 64 n`, …) and the type `.reg 64 → .int 64`.

Per the D0 template (`Dialects/ArithGoldenPathField.lean`), each kernel gets:

* the `Com arithDialect` source (op-swapped from the jasmin twin);
* `denote = <in-Com expr>`: the **same** `BitVec` proof as the jasmin twin (the arith
  denote was *defined* equal to the jasmin image), so it ports verbatim;
* the recognizable `_spec` (`Σ`: `BitVec.rotateRight`; S-box: textbook `~~~`/`&&&`/`^^^`);
* `ArithOK64` (mechanical, one constructor per op) ⇒ `lowerArithToJasmin_ComOK` ⇒ the
  lowered jasmin kernel is `ComOK`, so it rides the existing `com_arm_e2e` /
  `com_riscv_e2e` emit;
* the spec carried to the emit layer via `lowerArithToJasmin_denote`.

The `Σ` rotation constants (NIST SP 800-232): `Σ₀ = (19,28)`, `Σ₁ = (61,39)`,
`Σ₂ = (1,6)`, `Σ₃ = (10,17)`, `Σ₄ = (7,41)`. The S-box `~~~` is expressed as
`e ^^^ 0xFFFF…FFFF` via an `arith.constant 64 18446744073709551615` binding.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithAsconGoldenPath

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.Arith
open CatCrypt.Crypto.SecureCompilation.Dialects.ArithEmulations
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
open CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-! ## The five-input neutral-arith context `[i64,i64,i64,i64,i64]` is all-`reg 64` after lowering

The S-box lanes take five inputs. Their lowered jasmin context is
`[.int 64,…].map ArithTy.toJasmin = [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64]`, for
which `com_arm_e2e` / `com_riscv_e2e` need `AllReg64`. Proved inline, mirroring
`AsconSbox.allReg64_five`. -/

/-- The five-input lowered context `[x0,x1,x2,x3,x4]` is all-`reg 64`. -/
theorem allReg64_five :
    AllReg64 ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect) := by
  intro u hu
  rcases List.mem_cons.mp hu with h | h
  · exact h
  · rcases List.mem_cons.mp h with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact h
      · rcases List.mem_cons.mp h with h | h
        · exact h
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · exact absurd h List.not_mem_nil

/-! # Part 1 — the Ascon linear diffusion layer `Σ₀..Σ₄`

Each `Σᵢ x = x ^ ROTR^p x ^ ROTR^q x`; the rotate `ROTR^n x = (x >>> n) ||| (x <<< (64-n))`
is `shrui_imm`/`shli_imm`/`ori`, all neutral. Body (`Σ₀`):
`r19 := rot x 19 ; r28 := rot x 28 ; t := x ^ r19 ; r := t ^ r28`. -/

/-! ## `Σ₀ x = x ^ ROTR^19 x ^ ROTR^28 x` -/

/-- `Σ₀ x = x ^ ROTR^19 x ^ ROTR^28 x` over `[x]`, neutral-arith. -/
def asconSigma0ArithCom : Com arithDialect [.int 64] (.int 64) :=
  .var (.mk (.shrui_imm 64 19) rfl (.cons .here .nil))
  (.var (.mk (.shli_imm 64 45) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shrui_imm 64 28) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.shli_imm 64 36) rfl (.cons (.there (.there (.there (.there .here)))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here))))))))

/-- In-Com value proof, cheap `rfl`. -/
theorem asconSigma0ArithCom_denote (x : BitVec 64) :
    asconSigma0ArithCom.denote (.cons x .nil)
      = (x ^^^ ((x >>> 19) ||| (x <<< 45))) ^^^ ((x >>> 28) ||| (x <<< 36)) := rfl

/-- Recognizable-spec proof: ties the `shr | shl` source to textbook `ROTR`. -/
theorem asconSigma0ArithCom_spec (x : BitVec 64) :
    asconSigma0ArithCom.denote (.cons x .nil)
      = x ^^^ x.rotateRight 19 ^^^ x.rotateRight 28 := by
  rw [asconSigma0ArithCom_denote]; simp only [BitVec.rotateRight_def]

/-- Emit-legality (mechanical, one constructor per op). -/
theorem asconSigma0ArithCom_ok : ArithOK64 asconSigma0ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.ret _))))))))

/-- The lowered jasmin kernel is in the supported fragment (rides `com_*_e2e`). -/
theorem asconSigma0ArithCom_lowered_ok : ComOK (lowerArithToJasmin asconSigma0ArithCom) :=
  lowerArithToJasmin_ComOK asconSigma0ArithCom_ok

/-- The spec carried to the emit layer: the lowered jasmin kernel computes `Σ₀`. -/
theorem asconSigma0ArithCom_lowered_denote (x : BitVec 64) :
    (lowerArithToJasmin asconSigma0ArithCom).denote (mapVal (.cons x .nil))
      = x ^^^ x.rotateRight 19 ^^^ x.rotateRight 28 := by
  rw [lowerArithToJasmin_denote asconSigma0ArithCom, asconSigma0ArithCom_spec, transTy_int]

/-- **Emitted AArch64**, from the neutral source via the proven lowering + `com_arm_e2e`. -/
theorem asconSigma0ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin asconSigma0ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin asconSigma0ArithCom) 1)
      = Com.denote (lowerArithToJasmin asconSigma0ArithCom) V :=
  com_arm_e2e asconSigma0ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-- **Emitted RISC-V** — same neutral source, same lowering. -/
theorem asconSigma0ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin asconSigma0ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin asconSigma0ArithCom) 1)
      = Com.denote (lowerArithToJasmin asconSigma0ArithCom) V :=
  com_riscv_e2e asconSigma0ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-! ## `Σ₁ x = x ^ ROTR^61 x ^ ROTR^39 x` -/

/-- `Σ₁ x = x ^ ROTR^61 x ^ ROTR^39 x` over `[x]`, neutral-arith. -/
def asconSigma1ArithCom : Com arithDialect [.int 64] (.int 64) :=
  .var (.mk (.shrui_imm 64 61) rfl (.cons .here .nil))
  (.var (.mk (.shli_imm 64 3) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shrui_imm 64 39) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.shli_imm 64 25) rfl (.cons (.there (.there (.there (.there .here)))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here))))))))

/-- In-Com value proof, cheap `rfl`. -/
theorem asconSigma1ArithCom_denote (x : BitVec 64) :
    asconSigma1ArithCom.denote (.cons x .nil)
      = (x ^^^ ((x >>> 61) ||| (x <<< 3))) ^^^ ((x >>> 39) ||| (x <<< 25)) := rfl

/-- Recognizable-spec proof. -/
theorem asconSigma1ArithCom_spec (x : BitVec 64) :
    asconSigma1ArithCom.denote (.cons x .nil)
      = x ^^^ x.rotateRight 61 ^^^ x.rotateRight 39 := by
  rw [asconSigma1ArithCom_denote]; simp only [BitVec.rotateRight_def]

/-- Emit-legality (mechanical). -/
theorem asconSigma1ArithCom_ok : ArithOK64 asconSigma1ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.ret _))))))))

/-- The lowered jasmin kernel is `ComOK`. -/
theorem asconSigma1ArithCom_lowered_ok : ComOK (lowerArithToJasmin asconSigma1ArithCom) :=
  lowerArithToJasmin_ComOK asconSigma1ArithCom_ok

/-- The spec carried to the emit layer. -/
theorem asconSigma1ArithCom_lowered_denote (x : BitVec 64) :
    (lowerArithToJasmin asconSigma1ArithCom).denote (mapVal (.cons x .nil))
      = x ^^^ x.rotateRight 61 ^^^ x.rotateRight 39 := by
  rw [lowerArithToJasmin_denote asconSigma1ArithCom, asconSigma1ArithCom_spec, transTy_int]

/-- **Emitted AArch64**. -/
theorem asconSigma1ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin asconSigma1ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin asconSigma1ArithCom) 1)
      = Com.denote (lowerArithToJasmin asconSigma1ArithCom) V :=
  com_arm_e2e asconSigma1ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-- **Emitted RISC-V**. -/
theorem asconSigma1ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin asconSigma1ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin asconSigma1ArithCom) 1)
      = Com.denote (lowerArithToJasmin asconSigma1ArithCom) V :=
  com_riscv_e2e asconSigma1ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-! ## `Σ₂ x = x ^ ROTR^1 x ^ ROTR^6 x` -/

/-- `Σ₂ x = x ^ ROTR^1 x ^ ROTR^6 x` over `[x]`, neutral-arith. -/
def asconSigma2ArithCom : Com arithDialect [.int 64] (.int 64) :=
  .var (.mk (.shrui_imm 64 1) rfl (.cons .here .nil))
  (.var (.mk (.shli_imm 64 63) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shrui_imm 64 6) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.shli_imm 64 58) rfl (.cons (.there (.there (.there (.there .here)))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here))))))))

/-- In-Com value proof, cheap `rfl`. -/
theorem asconSigma2ArithCom_denote (x : BitVec 64) :
    asconSigma2ArithCom.denote (.cons x .nil)
      = (x ^^^ ((x >>> 1) ||| (x <<< 63))) ^^^ ((x >>> 6) ||| (x <<< 58)) := rfl

/-- Recognizable-spec proof. -/
theorem asconSigma2ArithCom_spec (x : BitVec 64) :
    asconSigma2ArithCom.denote (.cons x .nil)
      = x ^^^ x.rotateRight 1 ^^^ x.rotateRight 6 := by
  rw [asconSigma2ArithCom_denote]; simp only [BitVec.rotateRight_def]

/-- Emit-legality (mechanical). -/
theorem asconSigma2ArithCom_ok : ArithOK64 asconSigma2ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.ret _))))))))

/-- The lowered jasmin kernel is `ComOK`. -/
theorem asconSigma2ArithCom_lowered_ok : ComOK (lowerArithToJasmin asconSigma2ArithCom) :=
  lowerArithToJasmin_ComOK asconSigma2ArithCom_ok

/-- The spec carried to the emit layer. -/
theorem asconSigma2ArithCom_lowered_denote (x : BitVec 64) :
    (lowerArithToJasmin asconSigma2ArithCom).denote (mapVal (.cons x .nil))
      = x ^^^ x.rotateRight 1 ^^^ x.rotateRight 6 := by
  rw [lowerArithToJasmin_denote asconSigma2ArithCom, asconSigma2ArithCom_spec, transTy_int]

/-- **Emitted AArch64**. -/
theorem asconSigma2ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin asconSigma2ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin asconSigma2ArithCom) 1)
      = Com.denote (lowerArithToJasmin asconSigma2ArithCom) V :=
  com_arm_e2e asconSigma2ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-- **Emitted RISC-V**. -/
theorem asconSigma2ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin asconSigma2ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin asconSigma2ArithCom) 1)
      = Com.denote (lowerArithToJasmin asconSigma2ArithCom) V :=
  com_riscv_e2e asconSigma2ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-! ## `Σ₃ x = x ^ ROTR^10 x ^ ROTR^17 x` -/

/-- `Σ₃ x = x ^ ROTR^10 x ^ ROTR^17 x` over `[x]`, neutral-arith. -/
def asconSigma3ArithCom : Com arithDialect [.int 64] (.int 64) :=
  .var (.mk (.shrui_imm 64 10) rfl (.cons .here .nil))
  (.var (.mk (.shli_imm 64 54) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shrui_imm 64 17) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.shli_imm 64 47) rfl (.cons (.there (.there (.there (.there .here)))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here))))))))

/-- In-Com value proof, cheap `rfl`. -/
theorem asconSigma3ArithCom_denote (x : BitVec 64) :
    asconSigma3ArithCom.denote (.cons x .nil)
      = (x ^^^ ((x >>> 10) ||| (x <<< 54))) ^^^ ((x >>> 17) ||| (x <<< 47)) := rfl

/-- Recognizable-spec proof. -/
theorem asconSigma3ArithCom_spec (x : BitVec 64) :
    asconSigma3ArithCom.denote (.cons x .nil)
      = x ^^^ x.rotateRight 10 ^^^ x.rotateRight 17 := by
  rw [asconSigma3ArithCom_denote]; simp only [BitVec.rotateRight_def]

/-- Emit-legality (mechanical). -/
theorem asconSigma3ArithCom_ok : ArithOK64 asconSigma3ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.ret _))))))))

/-- The lowered jasmin kernel is `ComOK`. -/
theorem asconSigma3ArithCom_lowered_ok : ComOK (lowerArithToJasmin asconSigma3ArithCom) :=
  lowerArithToJasmin_ComOK asconSigma3ArithCom_ok

/-- The spec carried to the emit layer. -/
theorem asconSigma3ArithCom_lowered_denote (x : BitVec 64) :
    (lowerArithToJasmin asconSigma3ArithCom).denote (mapVal (.cons x .nil))
      = x ^^^ x.rotateRight 10 ^^^ x.rotateRight 17 := by
  rw [lowerArithToJasmin_denote asconSigma3ArithCom, asconSigma3ArithCom_spec, transTy_int]

/-- **Emitted AArch64**. -/
theorem asconSigma3ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin asconSigma3ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin asconSigma3ArithCom) 1)
      = Com.denote (lowerArithToJasmin asconSigma3ArithCom) V :=
  com_arm_e2e asconSigma3ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-- **Emitted RISC-V**. -/
theorem asconSigma3ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin asconSigma3ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin asconSigma3ArithCom) 1)
      = Com.denote (lowerArithToJasmin asconSigma3ArithCom) V :=
  com_riscv_e2e asconSigma3ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-! ## `Σ₄ x = x ^ ROTR^7 x ^ ROTR^41 x` -/

/-- `Σ₄ x = x ^ ROTR^7 x ^ ROTR^41 x` over `[x]`, neutral-arith. -/
def asconSigma4ArithCom : Com arithDialect [.int 64] (.int 64) :=
  .var (.mk (.shrui_imm 64 7) rfl (.cons .here .nil))
  (.var (.mk (.shli_imm 64 57) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shrui_imm 64 41) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.shli_imm 64 23) rfl (.cons (.there (.there (.there (.there .here)))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here))))))))

/-- In-Com value proof, cheap `rfl`. -/
theorem asconSigma4ArithCom_denote (x : BitVec 64) :
    asconSigma4ArithCom.denote (.cons x .nil)
      = (x ^^^ ((x >>> 7) ||| (x <<< 57))) ^^^ ((x >>> 41) ||| (x <<< 23)) := rfl

/-- Recognizable-spec proof. -/
theorem asconSigma4ArithCom_spec (x : BitVec 64) :
    asconSigma4ArithCom.denote (.cons x .nil)
      = x ^^^ x.rotateRight 7 ^^^ x.rotateRight 41 := by
  rw [asconSigma4ArithCom_denote]; simp only [BitVec.rotateRight_def]

/-- Emit-legality (mechanical). -/
theorem asconSigma4ArithCom_ok : ArithOK64 asconSigma4ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.ret _))))))))

/-- The lowered jasmin kernel is `ComOK`. -/
theorem asconSigma4ArithCom_lowered_ok : ComOK (lowerArithToJasmin asconSigma4ArithCom) :=
  lowerArithToJasmin_ComOK asconSigma4ArithCom_ok

/-- The spec carried to the emit layer. -/
theorem asconSigma4ArithCom_lowered_denote (x : BitVec 64) :
    (lowerArithToJasmin asconSigma4ArithCom).denote (mapVal (.cons x .nil))
      = x ^^^ x.rotateRight 7 ^^^ x.rotateRight 41 := by
  rw [lowerArithToJasmin_denote asconSigma4ArithCom, asconSigma4ArithCom_spec, transTy_int]

/-- **Emitted AArch64**. -/
theorem asconSigma4ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin asconSigma4ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin asconSigma4ArithCom) 1)
      = Com.denote (lowerArithToJasmin asconSigma4ArithCom) V :=
  com_arm_e2e asconSigma4ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-- **Emitted RISC-V**. -/
theorem asconSigma4ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin asconSigma4ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin asconSigma4ArithCom) 1)
      = Com.denote (lowerArithToJasmin asconSigma4ArithCom) V :=
  com_riscv_e2e asconSigma4ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-! # Part 2 — the Ascon S-box `y0..y4`

The χ-layer applied bitsliced across five 64-bit lanes `x0..x4`. Each output lane is
neutral-arith over `[i64,i64,i64,i64,i64]` in the `andi`/`ori`/`xori`/`constant`
alphabet (`~~~` is `xori` against `arith.constant 64 18446744073709551615`). The
de-Bruijn structure is identical to the jasmin twin; the deep S-box denote uses
`unfold … ; rfl` to stay within the whnf budget. -/

/-! ## `y4 = x4a ^ ((~x0a) & x1)` where `x0a = x0^x4`, `x4a = x4^x3` -/

/-- `y4 = x4a ^ ((~x0a) & x1)` over `[x0,x1,x2,x3,x4]`, neutral-arith. -/
def asconY4ArithCom : Com arithDialect [.int 64, .int 64, .int 64, .int 64, .int 64] (.int 64) :=
  .var (.mk (.xori 64) rfl
         (.cons (.there (.there (.there (.there .here))))
           (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there .here)
            (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  (.var (.mk (.constant 64 18446744073709551615) rfl .nil)
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.andi 64) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)))
    (.ret .here))))))

/-- In-Com value proof (the `~` is `^ 0xFF…FF`). The deep S-box term needs an explicit
    `unfold` to stay within the whnf budget for `rfl`. -/
theorem asconY4ArithCom_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    asconY4ArithCom.denote (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = (x4 ^^^ x3) ^^^ (((x0 ^^^ x4) ^^^ BitVec.ofNat 64 18446744073709551615) &&& x1) := by
  unfold asconY4ArithCom; rfl

/-- Recognizable-spec proof, `bv_decide`: ties the source to the textbook lane
    `y4 = (x4^x3) ^ ((~(x0^x4)) & x1)`. -/
theorem asconY4ArithCom_spec (x0 x1 x2 x3 x4 : BitVec 64) :
    asconY4ArithCom.denote (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = (x4 ^^^ x3) ^^^ ((~~~(x0 ^^^ x4)) &&& x1) := by
  rw [asconY4ArithCom_denote]; congr 1; bv_decide

/-- Emit-legality (mechanical). -/
theorem asconY4ArithCom_ok : ArithOK64 asconY4ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _))))))

/-- The lowered jasmin kernel is `ComOK`. -/
theorem asconY4ArithCom_lowered_ok : ComOK (lowerArithToJasmin asconY4ArithCom) :=
  lowerArithToJasmin_ComOK asconY4ArithCom_ok

/-- The spec carried to the emit layer. -/
theorem asconY4ArithCom_lowered_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    (lowerArithToJasmin asconY4ArithCom).denote
        (mapVal (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil))))))
      = (x4 ^^^ x3) ^^^ ((~~~(x0 ^^^ x4)) &&& x1) := by
  rw [lowerArithToJasmin_denote asconY4ArithCom, asconY4ArithCom_spec, transTy_int]

/-- **Emitted AArch64**. -/
theorem asconY4ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 5 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin asconY4ArithCom) 5))).regs)
        (comRetName (lowerArithToJasmin asconY4ArithCom) 5)
      = Com.denote (lowerArithToJasmin asconY4ArithCom) V :=
  com_arm_e2e asconY4ArithCom_lowered_ok allReg64_five V s hs

/-- **Emitted RISC-V**. -/
theorem asconY4ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 5 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin asconY4ArithCom) 5))).regs)
        (comRetName (lowerArithToJasmin asconY4ArithCom) 5)
      = Com.denote (lowerArithToJasmin asconY4ArithCom) V :=
  com_riscv_e2e asconY4ArithCom_lowered_ok allReg64_five V s hs

/-! ## `y0 = x0b ^ x4b` where `x0b = x0a ^ ((~x1)&x2a)`, `x4b = x4a ^ ((~x0a)&x1)` -/

/-- `y0 = (x0a ^ ((~x1)&x2a)) ^ (x4a ^ ((~x0a)&x1))` over `[x0,x1,x2,x3,x4]`, neutral-arith. -/
def asconY0ArithCom : Com arithDialect [.int 64, .int 64, .int 64, .int 64, .int 64] (.int 64) :=
  .var (.mk (.xori 64) rfl
         (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  (.var (.mk (.constant 64 18446744073709551615) rfl .nil)
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil)))
  (.var (.mk (.andi 64) rfl
          (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil)))
  (.var (.mk (.andi 64) rfl
          (.cons (.there .here)
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
            (.cons (.there .here) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there .here) .nil)))
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)))))))))))

/-- In-Com value proof. -/
theorem asconY0ArithCom_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    asconY0ArithCom.denote (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = ((x0 ^^^ x4) ^^^ ((x1 ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x2 ^^^ x1)))
          ^^^ ((x4 ^^^ x3)
                ^^^ (((x0 ^^^ x4) ^^^ BitVec.ofNat 64 18446744073709551615) &&& x1)) := by
  unfold asconY0ArithCom; rfl

/-- Recognizable-spec proof, `bv_decide`. -/
theorem asconY0ArithCom_spec (x0 x1 x2 x3 x4 : BitVec 64) :
    asconY0ArithCom.denote (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = ((x0 ^^^ x4) ^^^ ((~~~x1) &&& (x2 ^^^ x1)))
          ^^^ ((x4 ^^^ x3) ^^^ ((~~~(x0 ^^^ x4)) &&& x1)) := by
  rw [asconY0ArithCom_denote]; congr 2 <;> bv_decide

/-- Emit-legality (mechanical). -/
theorem asconY0ArithCom_ok : ArithOK64 asconY0ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))))))))))

/-- The lowered jasmin kernel is `ComOK`. -/
theorem asconY0ArithCom_lowered_ok : ComOK (lowerArithToJasmin asconY0ArithCom) :=
  lowerArithToJasmin_ComOK asconY0ArithCom_ok

/-- The spec carried to the emit layer. -/
theorem asconY0ArithCom_lowered_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    (lowerArithToJasmin asconY0ArithCom).denote
        (mapVal (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil))))))
      = ((x0 ^^^ x4) ^^^ ((~~~x1) &&& (x2 ^^^ x1)))
          ^^^ ((x4 ^^^ x3) ^^^ ((~~~(x0 ^^^ x4)) &&& x1)) := by
  rw [lowerArithToJasmin_denote asconY0ArithCom, asconY0ArithCom_spec, transTy_int]

/-- **Emitted AArch64**. -/
theorem asconY0ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 5 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin asconY0ArithCom) 5))).regs)
        (comRetName (lowerArithToJasmin asconY0ArithCom) 5)
      = Com.denote (lowerArithToJasmin asconY0ArithCom) V :=
  com_arm_e2e asconY0ArithCom_lowered_ok allReg64_five V s hs

/-- **Emitted RISC-V**. -/
theorem asconY0ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 5 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin asconY0ArithCom) 5))).regs)
        (comRetName (lowerArithToJasmin asconY0ArithCom) 5)
      = Com.denote (lowerArithToJasmin asconY0ArithCom) V :=
  com_riscv_e2e asconY0ArithCom_lowered_ok allReg64_five V s hs

/-! ## `y1 = x1b ^ x0b` where `x1b = x1 ^ ((~x2a)&x3)`, `x0b = x0a ^ ((~x1)&x2a)` -/

/-- `y1 = (x1 ^ ((~x2a)&x3)) ^ (x0a ^ ((~x1)&x2a))` over `[x0,x1,x2,x3,x4]`, neutral-arith. -/
def asconY1ArithCom : Com arithDialect [.int 64, .int 64, .int 64, .int 64, .int 64] (.int 64) :=
  .var (.mk (.xori 64) rfl
         (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.constant 64 18446744073709551615) rfl .nil)
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there .here) .nil)))
  (.var (.mk (.andi 64) rfl
          (.cons (.there .here)
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))
  (.var (.mk (.andi 64) rfl
          (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.cons (.there .here) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
            (.cons (.there .here) .nil)))
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here))))))))))

/-- In-Com value proof. -/
theorem asconY1ArithCom_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    asconY1ArithCom.denote (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = (x1 ^^^ (((x2 ^^^ x1) ^^^ BitVec.ofNat 64 18446744073709551615) &&& x3))
          ^^^ ((x0 ^^^ x4)
                ^^^ ((x1 ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x2 ^^^ x1))) := by
  unfold asconY1ArithCom; rfl

/-- Recognizable-spec proof, `bv_decide`. -/
theorem asconY1ArithCom_spec (x0 x1 x2 x3 x4 : BitVec 64) :
    asconY1ArithCom.denote (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = (x1 ^^^ ((~~~(x2 ^^^ x1)) &&& x3))
          ^^^ ((x0 ^^^ x4) ^^^ ((~~~x1) &&& (x2 ^^^ x1))) := by
  rw [asconY1ArithCom_denote]; congr 2 <;> bv_decide

/-- Emit-legality (mechanical). -/
theorem asconY1ArithCom_ok : ArithOK64 asconY1ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _))))))))))

/-- The lowered jasmin kernel is `ComOK`. -/
theorem asconY1ArithCom_lowered_ok : ComOK (lowerArithToJasmin asconY1ArithCom) :=
  lowerArithToJasmin_ComOK asconY1ArithCom_ok

/-- The spec carried to the emit layer. -/
theorem asconY1ArithCom_lowered_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    (lowerArithToJasmin asconY1ArithCom).denote
        (mapVal (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil))))))
      = (x1 ^^^ ((~~~(x2 ^^^ x1)) &&& x3))
          ^^^ ((x0 ^^^ x4) ^^^ ((~~~x1) &&& (x2 ^^^ x1))) := by
  rw [lowerArithToJasmin_denote asconY1ArithCom, asconY1ArithCom_spec, transTy_int]

/-- **Emitted AArch64**. -/
theorem asconY1ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 5 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin asconY1ArithCom) 5))).regs)
        (comRetName (lowerArithToJasmin asconY1ArithCom) 5)
      = Com.denote (lowerArithToJasmin asconY1ArithCom) V :=
  com_arm_e2e asconY1ArithCom_lowered_ok allReg64_five V s hs

/-- **Emitted RISC-V**. -/
theorem asconY1ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 5 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin asconY1ArithCom) 5))).regs)
        (comRetName (lowerArithToJasmin asconY1ArithCom) 5)
      = Com.denote (lowerArithToJasmin asconY1ArithCom) V :=
  com_riscv_e2e asconY1ArithCom_lowered_ok allReg64_five V s hs

/-! ## `y3 = x3b ^ x2b` where `x3b = x3 ^ ((~x4a)&x0a)`, `x2b = x2a ^ ((~x3)&x4a)` -/

/-- `y3 = (x3 ^ ((~x4a)&x0a)) ^ (x2a ^ ((~x3)&x4a))` over `[x0,x1,x2,x3,x4]`, neutral-arith. -/
def asconY3ArithCom : Com arithDialect [.int 64, .int 64, .int 64, .int 64, .int 64] (.int 64) :=
  .var (.mk (.xori 64) rfl
         (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there .here)))))
            (.cons (.there (.there (.there (.there .here)))) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there .here))))
            (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.constant 64 18446744073709551615) rfl .nil)
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there .here)) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
            (.cons (.there .here) .nil)))
  (.var (.mk (.andi 64) rfl
          (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  (.var (.mk (.andi 64) rfl
          (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
            (.cons (.there .here) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there .here) .nil)))
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)))))))))))

/-- In-Com value proof. -/
theorem asconY3ArithCom_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    asconY3ArithCom.denote (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = (x3 ^^^ (((x4 ^^^ x3) ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x0 ^^^ x4)))
          ^^^ ((x2 ^^^ x1)
                ^^^ ((x3 ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x4 ^^^ x3))) := by
  unfold asconY3ArithCom; rfl

/-- Recognizable-spec proof, `bv_decide`. -/
theorem asconY3ArithCom_spec (x0 x1 x2 x3 x4 : BitVec 64) :
    asconY3ArithCom.denote (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = (x3 ^^^ ((~~~(x4 ^^^ x3)) &&& (x0 ^^^ x4)))
          ^^^ ((x2 ^^^ x1) ^^^ ((~~~x3) &&& (x4 ^^^ x3))) := by
  rw [asconY3ArithCom_denote]; congr 2 <;> bv_decide

/-- Emit-legality (mechanical). -/
theorem asconY3ArithCom_ok : ArithOK64 asconY3ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))))))))))

/-- The lowered jasmin kernel is `ComOK`. -/
theorem asconY3ArithCom_lowered_ok : ComOK (lowerArithToJasmin asconY3ArithCom) :=
  lowerArithToJasmin_ComOK asconY3ArithCom_ok

/-- The spec carried to the emit layer. -/
theorem asconY3ArithCom_lowered_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    (lowerArithToJasmin asconY3ArithCom).denote
        (mapVal (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil))))))
      = (x3 ^^^ ((~~~(x4 ^^^ x3)) &&& (x0 ^^^ x4)))
          ^^^ ((x2 ^^^ x1) ^^^ ((~~~x3) &&& (x4 ^^^ x3))) := by
  rw [lowerArithToJasmin_denote asconY3ArithCom, asconY3ArithCom_spec, transTy_int]

/-- **Emitted AArch64**. -/
theorem asconY3ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 5 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin asconY3ArithCom) 5))).regs)
        (comRetName (lowerArithToJasmin asconY3ArithCom) 5)
      = Com.denote (lowerArithToJasmin asconY3ArithCom) V :=
  com_arm_e2e asconY3ArithCom_lowered_ok allReg64_five V s hs

/-- **Emitted RISC-V**. -/
theorem asconY3ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 5 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin asconY3ArithCom) 5))).regs)
        (comRetName (lowerArithToJasmin asconY3ArithCom) 5)
      = Com.denote (lowerArithToJasmin asconY3ArithCom) V :=
  com_riscv_e2e asconY3ArithCom_lowered_ok allReg64_five V s hs

/-! ## `y2 = ~x2b` where `x2b = x2a ^ ((~x3)&x4a)`

The only lane ending in a complement (`x2a=x2^x1`, `x4a=x4^x3`). -/

/-- `y2 = ~(x2a ^ ((~x3)&x4a))` over `[x0,x1,x2,x3,x4]`, neutral-arith. -/
def asconY2ArithCom : Com arithDialect [.int 64, .int 64, .int 64, .int 64, .int 64] (.int 64) :=
  .var (.mk (.xori 64) rfl
         (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there .here)))))
            (.cons (.there (.there (.there (.there .here)))) .nil)))
  (.var (.mk (.constant 64 18446744073709551615) rfl .nil)
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil)))
  (.var (.mk (.andi 64) rfl (.cons .here (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons .here (.cons (.there (.there (.there .here))) .nil)))
    (.ret .here)))))))

/-- In-Com value proof. -/
theorem asconY2ArithCom_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    asconY2ArithCom.denote (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = ((x2 ^^^ x1)
            ^^^ ((x3 ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x4 ^^^ x3)))
          ^^^ BitVec.ofNat 64 18446744073709551615 := by
  unfold asconY2ArithCom; rfl

/-- Recognizable-spec proof: ties the source to `y2 = ~(x2a ^ ((~x3)&x4a))`. -/
theorem asconY2ArithCom_spec (x0 x1 x2 x3 x4 : BitVec 64) :
    asconY2ArithCom.denote (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = ~~~((x2 ^^^ x1) ^^^ ((~~~x3) &&& (x4 ^^^ x3))) := by
  rw [asconY2ArithCom_denote,
    show BitVec.ofNat 64 18446744073709551615 = BitVec.allOnes 64 from rfl]
  simp only [BitVec.xor_allOnes]

/-- Emit-legality (mechanical). -/
theorem asconY2ArithCom_ok : ArithOK64 asconY2ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))))))

/-- The lowered jasmin kernel is `ComOK`. -/
theorem asconY2ArithCom_lowered_ok : ComOK (lowerArithToJasmin asconY2ArithCom) :=
  lowerArithToJasmin_ComOK asconY2ArithCom_ok

/-- The spec carried to the emit layer. -/
theorem asconY2ArithCom_lowered_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    (lowerArithToJasmin asconY2ArithCom).denote
        (mapVal (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil))))))
      = ~~~((x2 ^^^ x1) ^^^ ((~~~x3) &&& (x4 ^^^ x3))) := by
  rw [lowerArithToJasmin_denote asconY2ArithCom, asconY2ArithCom_spec, transTy_int]

/-- **Emitted AArch64**. -/
theorem asconY2ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 5 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin asconY2ArithCom) 5))).regs)
        (comRetName (lowerArithToJasmin asconY2ArithCom) 5)
      = Com.denote (lowerArithToJasmin asconY2ArithCom) V :=
  com_arm_e2e asconY2ArithCom_lowered_ok allReg64_five V s hs

/-- **Emitted RISC-V**. -/
theorem asconY2ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 5 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin asconY2ArithCom) 5))).regs)
        (comRetName (lowerArithToJasmin asconY2ArithCom) 5)
      = Com.denote (lowerArithToJasmin asconY2ArithCom) V :=
  com_riscv_e2e asconY2ArithCom_lowered_ok allReg64_five V s hs

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithAsconGoldenPath
