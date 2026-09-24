/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminComOK
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithEmulations
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
public import Std.Tactic.BVDecide

@[expose] public section

set_option autoImplicit false

/-!
# The field-arithmetic golden-path kernels, lifted to the neutral `arith` dialect

Item 1 of the MLIR dialect-alignment restructure (D0): the field-arithmetic kernels
that were authored below the waist as `Com jasminDialect`
(`FieldEmitGoldenPath` / `FieldSubBorrowGoldenPath` / `FieldModOpsGoldenPath`) are
here re-expressed one level up as `Com arithDialect` — the upstream-aligned neutral
dialect — and connected back to emit through the **proven** arith→jasmin lowering, in
the pattern of the template `ArithGoldenPathField.lean`:

* each kernel is `Com arithDialect` over the neutral op set (`addi`/`subi`/`muli`/
  `andi`/`ori`/`xori`/`mului_extended_hi`/`shrui_imm`/`shli_imm`/`constant`),
  de Bruijn-identical to its jasmin twin (only op names and `.int 64` vs `.reg 64`
  differ);
* `denote = <spec>` is the **same** `BitVec` proof as the jasmin twin (the arith
  denote is *defined* equal to the jasmin image), so the value lemmas
  (`fieldMul_widening`, `fieldAdd_carry_reconstruct`, the borrow/mod specs) port
  verbatim over the arith denotes;
* `ArithOK64` (one constructor per op, each `width = 64` by `rfl`) ⇒
  `lowerArithToJasmin_ComOK` ⇒ the lowered jasmin kernel is `ComOK`, so it rides the
  existing `com_arm_e2e` / `com_riscv_e2e` emit;
* `lowerArithToJasmin_denote` carries the spec down: the emitted code computes the
  arith kernel's value.

`fieldAddCom` is **not** re-lifted here — it is the template's `arithAddCom`. The
remaining members of the three jasmin field files are lifted below.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithFieldGoldenPath

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

/-! ## 1. From `FieldEmitGoldenPath` -/

/-! ### `fieldCondSub251` — the branchless GF(251) conditional-subtract reduce -/

/-- Neutral-`arith` lift of `FieldEmitGoldenPath.fieldCondSub251Com`. de Bruijn
    identical; ops `regConst/sub/shrImm/and/add` ↦ `constant/subi/shrui_imm/andi/addi`. -/
def fieldCondSub251ArithCom : Com arithDialect [.int 64] (.int 64) :=
  .var (.mk (.constant 64 251) rfl .nil)
  (.var (.mk (.subi 64) rfl (.cons (.there .here) (.cons .here .nil)))              -- a - c251
  (.var (.mk (.shrui_imm 64 63) rfl (.cons .here .nil))                            -- t >>> 63
  (.var (.mk (.constant 64 0) rfl .nil)
  (.var (.mk (.subi 64) rfl (.cons .here (.cons (.there .here) .nil)))             -- c0 - bit
  (.var (.mk (.andi 64) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there .here)))) .nil)))               -- m & c251
  (.var (.mk (.addi 64) rfl
          (.cons (.there (.there (.there (.there .here))))
            (.cons .here .nil)))                                                   -- t + masked
    (.ret .here)))))))

theorem fieldCondSub251ArithCom_denote (a : BitVec 64) :
    Com.denote fieldCondSub251ArithCom (.cons a .nil)
      = (a - (251 : BitVec 64))
          + (((0 : BitVec 64) - ((a - (251 : BitVec 64)) >>> 63)) &&& (251 : BitVec 64)) := by
  unfold fieldCondSub251ArithCom; rfl

theorem fieldCondSub251ArithCom_ok : ArithOK64 fieldCondSub251ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))))))

theorem fieldCondSub251ArithCom_lowered_ok : ComOK (lowerArithToJasmin fieldCondSub251ArithCom) :=
  lowerArithToJasmin_ComOK fieldCondSub251ArithCom_ok

theorem fieldCondSub251ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin fieldCondSub251ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin fieldCondSub251ArithCom) 1)
      = Com.denote (lowerArithToJasmin fieldCondSub251ArithCom) V :=
  com_arm_e2e fieldCondSub251ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

theorem fieldCondSub251ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin fieldCondSub251ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin fieldCondSub251ArithCom) 1)
      = Com.denote (lowerArithToJasmin fieldCondSub251ArithCom) V :=
  com_riscv_e2e fieldCondSub251ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-! ### `fieldMulLo` / `fieldMulHi` — the widening 64×64→128 multiply + value step -/

/-- Neutral-`arith` lift of `FieldEmitGoldenPath.fieldMulLoCom` (`mul` ↦ `muli`). -/
def fieldMulLoArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.muli 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)

/-- Neutral-`arith` lift of `FieldEmitGoldenPath.fieldMulHiCom`
    (`mulhi` ↦ `mului_extended_hi`; denote = `mulHiW`). -/
def fieldMulHiArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.mului_extended_hi 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)

theorem fieldMulLoArithCom_denote (x0 x1 : BitVec 64) :
    Com.denote fieldMulLoArithCom (.cons x0 (.cons x1 .nil)) = x1 * x0 := rfl

theorem fieldMulHiArithCom_denote (x0 x1 : BitVec 64) :
    Com.denote fieldMulHiArithCom (.cons x0 (.cons x1 .nil)) = mulHiW x1 x0 := rfl

/-- **The `mul` value step that closes the golden path**: the low and high output
    words reassemble to the exact 128-bit integer product, `lo + hi · 2^64 = a · b`.
    The same `MontMulFragmentDemo.mulx_reconstruct` widening law as the jasmin twin,
    here over the neutral-`arith` denotes. -/
theorem fieldMul_widening (x0 x1 : BitVec 64) :
    (Com.denote fieldMulLoArithCom (.cons x0 (.cons x1 .nil))).toNat
      + (Com.denote fieldMulHiArithCom (.cons x0 (.cons x1 .nil))).toNat * 2 ^ 64
      = x1.toNat * x0.toNat := by
  rw [fieldMulLoArithCom_denote, fieldMulHiArithCom_denote]
  exact MontMulFragmentDemo.mulx_reconstruct x1 x0

theorem fieldMulLoArithCom_ok : ArithOK64 fieldMulLoArithCom :=
  ArithOK64.var rfl (ArithOK64.ret _)

theorem fieldMulHiArithCom_ok : ArithOK64 fieldMulHiArithCom :=
  ArithOK64.var rfl (ArithOK64.ret _)

theorem fieldMulLoArithCom_lowered_ok : ComOK (lowerArithToJasmin fieldMulLoArithCom) :=
  lowerArithToJasmin_ComOK fieldMulLoArithCom_ok

theorem fieldMulHiArithCom_lowered_ok : ComOK (lowerArithToJasmin fieldMulHiArithCom) :=
  lowerArithToJasmin_ComOK fieldMulHiArithCom_ok

theorem fieldMulLoArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin fieldMulLoArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin fieldMulLoArithCom) 2)
      = Com.denote (lowerArithToJasmin fieldMulLoArithCom) V :=
  com_arm_e2e fieldMulLoArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

theorem fieldMulLoArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin fieldMulLoArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin fieldMulLoArithCom) 2)
      = Com.denote (lowerArithToJasmin fieldMulLoArithCom) V :=
  com_riscv_e2e fieldMulLoArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

theorem fieldMulHiArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin fieldMulHiArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin fieldMulHiArithCom) 2)
      = Com.denote (lowerArithToJasmin fieldMulHiArithCom) V :=
  com_arm_e2e fieldMulHiArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

theorem fieldMulHiArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin fieldMulHiArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin fieldMulHiArithCom) 2)
      = Com.denote (lowerArithToJasmin fieldMulHiArithCom) V :=
  com_riscv_e2e fieldMulHiArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-! ### `fieldAddCarry` — branchless add-with-carry-out + value step -/

/-- Neutral-`arith` lift of `FieldEmitGoldenPath.fieldAddCarryCom`. -/
def fieldAddCarryArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  -- s = x1 + x0
  .var (.mk (.addi 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- ones = 2^64-1
  (.var (.mk (.constant 64 18446744073709551615) rfl .nil)
  -- ns = s ^ ones   (= ~s)
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- ab_and = x1 & x0
  (.var (.mk (.andi 64) rfl
          (.cons (.there (.there (.there (.there .here))))
                    (.cons (.there (.there (.there .here))) .nil)))
  -- ab_or = x1 | x0
  (.var (.mk (.ori 64) rfl
          (.cons (.there (.there (.there (.there (.there .here)))))
                    (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- t = ab_or & ns
  (.var (.mk (.andi 64) rfl
          (.cons .here (.cons (.there (.there .here)) .nil)))
  -- u = ab_and | t
  (.var (.mk (.ori 64) rfl
          (.cons (.there (.there .here)) (.cons .here .nil)))
  -- cout = u >>> 63
  (.var (.mk (.shrui_imm 64 63) rfl (.cons .here .nil))
    (.ret .here))))))))

theorem fieldAddCarryArithCom_denote (x0 x1 : BitVec 64) :
    Com.denote fieldAddCarryArithCom (.cons x0 (.cons x1 .nil))
      = ((x1 &&& x0) ||| ((x1 ||| x0) &&& ((x1 + x0) ^^^ BitVec.ofNat 64 18446744073709551615)))
          >>> 63 := by
  unfold fieldAddCarryArithCom; rfl

/-- **The add value step that closes the carry chain**: the low word `arithAddCom`
    (template `a + b`) and the carry-out `fieldAddCarryArithCom` reassemble to the
    exact integer sum, `lo + cout · 2^64 = a + b`. The bit-twiddle equals
    `BitVec.uaddOverflow`, by `bv_decide` — the same proof as the jasmin twin. -/
theorem fieldAdd_carry_reconstruct (x0 x1 : BitVec 64) :
    (x1 + x0).toNat
      + (Com.denote fieldAddCarryArithCom (.cons x0 (.cons x1 .nil))).toNat * 2 ^ 64
      = x1.toNat + x0.toNat := by
  rw [fieldAddCarryArithCom_denote]
  have h : (((x1 &&& x0) ||| ((x1 ||| x0) &&& ((x1 + x0) ^^^ BitVec.ofNat 64 18446744073709551615)))
        >>> 63)
      = (if x1.uaddOverflow x0 then (1 : BitVec 64) else 0) := by bv_decide
  have ho := BitVec.uaddOverflow.eq_1 x1 x0
  rw [BitVec.toNat_add, h]
  split <;> simp_all
  omega

theorem fieldAddCarryArithCom_ok : ArithOK64 fieldAddCarryArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
      (ArithOK64.ret _))))))))

theorem fieldAddCarryArithCom_lowered_ok : ComOK (lowerArithToJasmin fieldAddCarryArithCom) :=
  lowerArithToJasmin_ComOK fieldAddCarryArithCom_ok

theorem fieldAddCarryArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin fieldAddCarryArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin fieldAddCarryArithCom) 2)
      = Com.denote (lowerArithToJasmin fieldAddCarryArithCom) V :=
  com_arm_e2e fieldAddCarryArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

theorem fieldAddCarryArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin fieldAddCarryArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin fieldAddCarryArithCom) 2)
      = Com.denote (lowerArithToJasmin fieldAddCarryArithCom) V :=
  com_riscv_e2e fieldAddCarryArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-! ### `fieldAdc` — add-with-carry-in, low word -/

/-- The 3-input context `[a, b, cin]` is all-`reg 64` (jasmin side, post-lowering). -/
theorem allReg64_three : AllReg64 ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect) :=
  FieldEmitGoldenPath.allReg64_three

/-- Neutral-`arith` lift of `FieldEmitGoldenPath.fieldAdcCom`. -/
def fieldAdcArithCom : Com arithDialect [.int 64, .int 64, .int 64] (.int 64) :=
  -- t = a + b
  .var (.mk (.addi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- r = t + cin
  (.var (.mk (.addi 64) rfl (.cons .here (.cons (.there (.there (.there .here))) .nil)))
    (.ret .here))

theorem fieldAdcArithCom_denote (a b cin : BitVec 64) :
    Com.denote fieldAdcArithCom (.cons a (.cons b (.cons cin .nil))) = (a + b) + cin := by
  unfold fieldAdcArithCom; rfl

theorem fieldAdcArithCom_ok : ArithOK64 fieldAdcArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _))

theorem fieldAdcArithCom_lowered_ok : ComOK (lowerArithToJasmin fieldAdcArithCom) :=
  lowerArithToJasmin_ComOK fieldAdcArithCom_ok

theorem fieldAdcArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin fieldAdcArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin fieldAdcArithCom) 3)
      = Com.denote (lowerArithToJasmin fieldAdcArithCom) V :=
  com_arm_e2e fieldAdcArithCom_lowered_ok allReg64_three V s hs

theorem fieldAdcArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin fieldAdcArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin fieldAdcArithCom) 3)
      = Com.denote (lowerArithToJasmin fieldAdcArithCom) V :=
  com_riscv_e2e fieldAdcArithCom_lowered_ok allReg64_three V s hs

/-! ## 2. From `FieldSubBorrowGoldenPath` -/

/-! ### `fieldSub` — the low word `a - b` -/

/-- Neutral-`arith` lift of `FieldSubBorrow.fieldSubCom` (`sub` ↦ `subi`). -/
def fieldSubArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.subi 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)

theorem fieldSubArithCom_denote (x0 x1 : BitVec 64) :
    Com.denote fieldSubArithCom (.cons x0 (.cons x1 .nil)) = x1 - x0 := rfl

theorem fieldSubArithCom_ok : ArithOK64 fieldSubArithCom :=
  ArithOK64.var rfl (ArithOK64.ret _)

theorem fieldSubArithCom_lowered_ok : ComOK (lowerArithToJasmin fieldSubArithCom) :=
  lowerArithToJasmin_ComOK fieldSubArithCom_ok

theorem fieldSubArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin fieldSubArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin fieldSubArithCom) 2)
      = Com.denote (lowerArithToJasmin fieldSubArithCom) V :=
  com_arm_e2e fieldSubArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

theorem fieldSubArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin fieldSubArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin fieldSubArithCom) 2)
      = Com.denote (lowerArithToJasmin fieldSubArithCom) V :=
  com_riscv_e2e fieldSubArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-! ### `fieldBorrow` — branchless subtract-with-borrow-out + spec + value step -/

/-- Neutral-`arith` lift of `FieldSubBorrow.fieldBorrowCom`. -/
def fieldBorrowArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  -- ones = 2^64-1
  .var (.mk (.constant 64 18446744073709551615) rfl .nil)
  -- na = a ^ ones   (= ~a)
  (.var (.mk (.xori 64) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
  -- axb = a ^ b
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there .here)))
                    (.cons (.there (.there .here)) .nil)))
  -- naxb = axb ^ ones (= ~(a^b))
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there (.there .here)) .nil)))
  -- d = a - b
  (.var (.mk (.subi 64) rfl
          (.cons (.there (.there (.there (.there (.there .here)))))
                    (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- l = na & b
  (.var (.mk (.andi 64) rfl
          (.cons (.there (.there (.there .here)))
                    (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  -- rr = naxb & d
  (.var (.mk (.andi 64) rfl
          (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- u = l | rr
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- borrow = u >>> 63
  (.var (.mk (.shrui_imm 64 63) rfl (.cons .here .nil))
    (.ret .here)))))))))

theorem fieldBorrowArithCom_denote (x0 x1 : BitVec 64) :
    Com.denote fieldBorrowArithCom (.cons x0 (.cons x1 .nil))
      = (((x1 ^^^ BitVec.ofNat 64 18446744073709551615) &&& x0)
          ||| (((x1 ^^^ x0) ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x1 - x0)))
          >>> 63 := by
  unfold fieldBorrowArithCom; rfl

/-- **The borrow-out spec.** The branchless borrow expression equals
    `if x1 < x0 then 1 else 0` (`a = x1`, `b = x0`), by `bv_decide`. -/
theorem fieldBorrowArithCom_spec (x0 x1 : BitVec 64) :
    Com.denote fieldBorrowArithCom (.cons x0 (.cons x1 .nil))
      = (if x1.toNat < x0.toNat then (1 : BitVec 64) else 0) := by
  rw [fieldBorrowArithCom_denote]
  have key : (((x1 ^^^ BitVec.ofNat 64 18446744073709551615) &&& x0)
        ||| (((x1 ^^^ x0) ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x1 - x0)))
        >>> 63 = (if x1 < x0 then (1 : BitVec 64) else 0) := by bv_decide
  rw [key]; simp [BitVec.lt_def]

/-- **The subtract value step that closes the borrow chain**: the low word
    `fieldSubArithCom` and the borrow-out `fieldBorrowArithCom` reconstruct the
    exact integer subtraction, `r.toNat + b.toNat = a.toNat + borrow · 2^64`. -/
theorem field_sub_borrow_reconstruct (x0 x1 : BitVec 64) :
    (Com.denote fieldSubArithCom (.cons x0 (.cons x1 .nil))).toNat
      + x0.toNat
      = x1.toNat
      + (Com.denote fieldBorrowArithCom (.cons x0 (.cons x1 .nil))).toNat * 2 ^ 64 := by
  rw [fieldSubArithCom_denote, fieldBorrowArithCom_spec, BitVec.toNat_sub]
  have hx0 : x0.toNat < 2 ^ 64 := x0.isLt
  have hx1 : x1.toNat < 2 ^ 64 := x1.isLt
  split <;> simp_all <;> omega

theorem fieldBorrowArithCom_ok : ArithOK64 fieldBorrowArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
      (ArithOK64.var rfl (ArithOK64.ret _)))))))))

theorem fieldBorrowArithCom_lowered_ok : ComOK (lowerArithToJasmin fieldBorrowArithCom) :=
  lowerArithToJasmin_ComOK fieldBorrowArithCom_ok

theorem fieldBorrowArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin fieldBorrowArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin fieldBorrowArithCom) 2)
      = Com.denote (lowerArithToJasmin fieldBorrowArithCom) V :=
  com_arm_e2e fieldBorrowArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

theorem fieldBorrowArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin fieldBorrowArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin fieldBorrowArithCom) 2)
      = Com.denote (lowerArithToJasmin fieldBorrowArithCom) V :=
  com_riscv_e2e fieldBorrowArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-! ## 3. From `FieldModOpsGoldenPath` -/

/-! ### `modDouble` — `(a + a) mod 251` -/

/-- Neutral-`arith` lift of `FieldModOps.modDoubleCom`. -/
def modDoubleArithCom : Com arithDialect [.int 64] (.int 64) :=
  -- t = a + a
  .var (.mk (.addi 64) rfl (.cons .here (.cons .here .nil)))
  -- c251 = 251
  (.var (.mk (.constant 64 251) rfl .nil)
  -- d = t - c251
  (.var (.mk (.subi 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- bit = d >>> 63
  (.var (.mk (.shrui_imm 64 63) rfl (.cons .here .nil))
  -- c0 = 0
  (.var (.mk (.constant 64 0) rfl .nil)
  -- m = c0 - bit
  (.var (.mk (.subi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- masked = m & c251
  (.var (.mk (.andi 64) rfl
          (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- r = d + masked
  (.var (.mk (.addi 64) rfl
          (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)))
    (.ret .here))))))))

theorem modDoubleArithCom_denote (a : BitVec 64) :
    Com.denote modDoubleArithCom (.cons a .nil)
      = ((a + a) - (251 : BitVec 64))
          + (((0 : BitVec 64) - (((a + a) - (251 : BitVec 64)) >>> 63)) &&& (251 : BitVec 64)) := by
  unfold modDoubleArithCom; rfl

/-- **The modular spec.** For a reduced input `a.toNat < 251`, the source computes
    `(2 · a) mod 251`. -/
theorem modDoubleArithCom_spec (a : BitVec 64) (ha : a.toNat < 251) :
    (Com.denote modDoubleArithCom (.cons a .nil)).toNat = (2 * a.toNat) % 251 := by
  rw [modDoubleArithCom_denote]
  have hlt : a < 251#64 := by rw [BitVec.lt_def]; simpa using ha
  have key : ((a + a) - (251 : BitVec 64))
        + (((0 : BitVec 64) - (((a + a) - (251 : BitVec 64)) >>> 63)) &&& (251 : BitVec 64))
      = if a < 126#64 then a + a else (a + a) - 251#64 := by bv_decide
  rw [key]
  have hadd : (a + a).toNat = 2 * a.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
  by_cases hc : a < 126#64
  · rw [if_pos hc, hadd]
    rw [BitVec.lt_def] at hc; simp only [BitVec.toNat_ofNat] at hc
    omega
  · rw [if_neg hc, BitVec.toNat_sub, hadd]
    rw [BitVec.lt_def] at hc; simp only [BitVec.toNat_ofNat] at hc ⊢
    rw [show (2 ^ 64 - 251 % 2 ^ 64 + 2 * a.toNat) % 2 ^ 64 = 2 * a.toNat - 251 by omega]
    omega

theorem modDoubleArithCom_ok : ArithOK64 modDoubleArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
      (ArithOK64.ret _))))))))

theorem modDoubleArithCom_lowered_ok : ComOK (lowerArithToJasmin modDoubleArithCom) :=
  lowerArithToJasmin_ComOK modDoubleArithCom_ok

theorem modDoubleArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin modDoubleArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin modDoubleArithCom) 1)
      = Com.denote (lowerArithToJasmin modDoubleArithCom) V :=
  com_arm_e2e modDoubleArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

theorem modDoubleArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin modDoubleArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin modDoubleArithCom) 1)
      = Com.denote (lowerArithToJasmin modDoubleArithCom) V :=
  com_riscv_e2e modDoubleArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-! ### `modNeg` — `(251 - a) mod 251` -/

/-- Neutral-`arith` lift of `FieldModOps.modNegCom`. -/
def modNegArithCom : Com arithDialect [.int 64] (.int 64) :=
  -- c251 = 251
  .var (.mk (.constant 64 251) rfl .nil)
  -- t = c251 - a
  (.var (.mk (.subi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- d = t - c251
  (.var (.mk (.subi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- bit = d >>> 63
  (.var (.mk (.shrui_imm 64 63) rfl (.cons .here .nil))
  -- c0 = 0
  (.var (.mk (.constant 64 0) rfl .nil)
  -- m = c0 - bit
  (.var (.mk (.subi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- masked = m & c251
  (.var (.mk (.andi 64) rfl
          (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  -- r = d + masked
  (.var (.mk (.addi 64) rfl
          (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)))
    (.ret .here))))))))

theorem modNegArithCom_denote (a : BitVec 64) :
    Com.denote modNegArithCom (.cons a .nil)
      = (((251 : BitVec 64) - a) - (251 : BitVec 64))
          + (((0 : BitVec 64) - ((((251 : BitVec 64) - a) - (251 : BitVec 64)) >>> 63))
              &&& (251 : BitVec 64)) := by
  unfold modNegArithCom; rfl

/-- **The modular spec.** For a reduced input `a.toNat < 251`, the source computes
    `(251 - a) mod 251` (`0` at `a = 0`). -/
theorem modNegArithCom_spec (a : BitVec 64) (ha : a.toNat < 251) :
    (Com.denote modNegArithCom (.cons a .nil)).toNat = (251 - a.toNat) % 251 := by
  rw [modNegArithCom_denote]
  have hlt : a < 251#64 := by rw [BitVec.lt_def]; simpa using ha
  have hb : (((251 : BitVec 64) - a) - (251 : BitVec 64))
          + (((0 : BitVec 64) - ((((251 : BitVec 64) - a) - (251 : BitVec 64)) >>> 63))
              &&& (251 : BitVec 64))
      = if a = 0 then 0 else (251 : BitVec 64) - a := by
    bv_decide
  rw [hb]
  by_cases h0 : a = 0
  · subst h0; simp
  · have hane : a.toNat ≠ 0 := by
      intro hc; apply h0; apply BitVec.toNat_injective; rw [hc]; rfl
    rw [if_neg h0, BitVec.toNat_sub]
    have h251 : (251 : BitVec 64).toNat = 251 := by decide
    rw [h251, show (2 ^ 64 - a.toNat + 251) % 2 ^ 64 = 251 - a.toNat by omega,
       Nat.mod_eq_of_lt (by omega)]

theorem modNegArithCom_ok : ArithOK64 modNegArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
      (ArithOK64.ret _))))))))

theorem modNegArithCom_lowered_ok : ComOK (lowerArithToJasmin modNegArithCom) :=
  lowerArithToJasmin_ComOK modNegArithCom_ok

theorem modNegArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin modNegArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin modNegArithCom) 1)
      = Com.denote (lowerArithToJasmin modNegArithCom) V :=
  com_arm_e2e modNegArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

theorem modNegArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin modNegArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin modNegArithCom) 1)
      = Com.denote (lowerArithToJasmin modNegArithCom) V :=
  com_riscv_e2e modNegArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-! ### `condNeg` — constant-time `cond ? (251 - a) mod 251 : a` -/

/-- Neutral-`arith` lift of `FieldModOps.condNegCom`. -/
def condNegArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  -- c251 = 251
  .var (.mk (.constant 64 251) rfl .nil)
  -- t = c251 - a
  (.var (.mk (.subi 64) rfl (.cons .here (.cons (.there (.there .here)) .nil)))
  -- d = t - c251
  (.var (.mk (.subi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- bit = d >>> 63
  (.var (.mk (.shrui_imm 64 63) rfl (.cons .here .nil))
  -- c0 = 0
  (.var (.mk (.constant 64 0) rfl .nil)
  -- mm = c0 - bit
  (.var (.mk (.subi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- masked = mm & c251
  (.var (.mk (.andi 64) rfl
          (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  -- neg = d + masked
  (.var (.mk (.addi 64) rfl
          (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)))
  -- mask = c0 - cond
  (.var (.mk (.subi 64) rfl
          (.cons (.there (.there (.there .here)))
                    (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))
  -- ones = 2^64-1
  (.var (.mk (.constant 64 18446744073709551615) rfl .nil)
  -- nmask = mask ^ ones
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- nm = neg & mask
  (.var (.mk (.andi 64) rfl
          (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))
  -- am = a & nmask
  (.var (.mk (.andi 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))
                    (.cons (.there .here) .nil)))
  -- r = nm | am
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here))))))))))))))

theorem condNegArithCom_denote (cond a : BitVec 64) :
    Com.denote condNegArithCom (.cons cond (.cons a .nil))
      = let neg := (((251 : BitVec 64) - a) - (251 : BitVec 64))
            + (((0 : BitVec 64) - ((((251 : BitVec 64) - a) - (251 : BitVec 64)) >>> 63))
                &&& (251 : BitVec 64))
        let mask := (0 : BitVec 64) - cond
        (neg &&& mask) ||| (a &&& (mask ^^^ (18446744073709551615 : BitVec 64))) := by
  unfold condNegArithCom; rfl

/-- **The conditional-negate spec (both branches).** For a reduced input
    `a.toNat < 251` and a `0/1` flag `cond`, the source selects between the modular
    negate and the identity. -/
theorem condNegArithCom_spec (cond a : BitVec 64) (ha : a.toNat < 251)
    (hc : cond = 0 ∨ cond = 1) :
    (Com.denote condNegArithCom (.cons cond (.cons a .nil))).toNat
      = if cond = 1 then (251 - a.toNat) % 251 else a.toNat := by
  rw [condNegArithCom_denote]
  simp only
  have hlt : a < 251#64 := by rw [BitVec.lt_def]; simpa using ha
  rcases hc with h0 | h1
  · subst h0
    have hsel : (((((251 : BitVec 64) - a) - (251 : BitVec 64))
              + (((0 : BitVec 64) - ((((251 : BitVec 64) - a) - (251 : BitVec 64)) >>> 63))
                  &&& (251 : BitVec 64))) &&& ((0 : BitVec 64) - 0))
              ||| (a &&& (((0 : BitVec 64) - 0) ^^^ (18446744073709551615 : BitVec 64)))
            = a := by bv_decide
    rw [hsel]; simp
  · subst h1
    have hsel : (((((251 : BitVec 64) - a) - (251 : BitVec 64))
              + (((0 : BitVec 64) - ((((251 : BitVec 64) - a) - (251 : BitVec 64)) >>> 63))
                  &&& (251 : BitVec 64))) &&& ((0 : BitVec 64) - 1))
              ||| (a &&& (((0 : BitVec 64) - 1) ^^^ (18446744073709551615 : BitVec 64)))
            = if a = 0 then 0 else (251 : BitVec 64) - a := by bv_decide
    rw [hsel]
    simp only [if_true]
    by_cases h0 : a = 0
    · subst h0; simp
    · have hane : a.toNat ≠ 0 := by
        intro hcc; apply h0; apply BitVec.toNat_injective; rw [hcc]; rfl
      rw [if_neg h0, BitVec.toNat_sub]
      have h251 : (251 : BitVec 64).toNat = 251 := by decide
      rw [h251, show (2 ^ 64 - a.toNat + 251) % 2 ^ 64 = 251 - a.toNat by omega,
         Nat.mod_eq_of_lt (by omega)]

theorem condNegArithCom_ok : ArithOK64 condNegArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
      (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
        (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _))))))))))))))

theorem condNegArithCom_lowered_ok : ComOK (lowerArithToJasmin condNegArithCom) :=
  lowerArithToJasmin_ComOK condNegArithCom_ok

theorem condNegArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin condNegArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin condNegArithCom) 2)
      = Com.denote (lowerArithToJasmin condNegArithCom) V :=
  com_arm_e2e condNegArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

theorem condNegArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin condNegArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin condNegArithCom) 2)
      = Com.denote (lowerArithToJasmin condNegArithCom) V :=
  com_riscv_e2e condNegArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithFieldGoldenPath
