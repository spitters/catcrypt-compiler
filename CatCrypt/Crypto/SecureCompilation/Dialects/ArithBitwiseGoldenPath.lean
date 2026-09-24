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
# The bitwise / constant-time golden-path families, lifted to the neutral `arith` dialect

Item 1 of the MLIR dialect-alignment restructure: the constant-time bit-twiddle
kernels of `BranchlessSelectGoldenPath`, `BranchlessSarGoldenPath`,
`Width32EmitGoldenPath`, and `CtTableEmitGoldenPath` — authored as `Com jasminDialect`
(below the waist) — re-expressed one level up as `Com arithDialect` (the
upstream-aligned neutral dialect), connected to emit through the *proven*
arith→jasmin lowering (`lowerArithToJasmin`).

Each lifted kernel is the de-Bruijn-identical twin of its jasmin original, with only
the op names re-pointed to the neutral `arith` op set (`.addi`/`.xori`/`.andi`/`.ori`/
`.subi`/`.shrui_imm`/`.shli_imm`/`.constant`). The chain per kernel is:

* the source is `Com arithDialect` (the upstream-aligned neutral form);
* `denote = <expr>` reduces structurally (`arith_denote` / `unfold; rfl`), and the
  recognizable `_spec` (select true/false, `BitVec.sshiftRight`, the u32
  `setWidth`/`rotateLeft` ties, the AES S-box `= T[i]`) is the **same** `BitVec`
  proof as the jasmin twin (`arithDenote` is *defined* equal to the jasmin image);
* `ArithOK64` (mechanical) ⇒ `lowerArithToJasmin_ComOK` ⇒ the lowered jasmin kernel
  is `ComOK`, so it rides the existing `com_arm_e2e` / `com_riscv_e2e` emit;
* `lowerArithToJasmin_denote` carries the spec down: the emitted code computes the
  arith kernel's value.

This is the dialect-alignment lift of the whole bitwise / CT family — select,
and-not, arithmetic shift-right, u32-via-masked-u64 ARX, and the constant-time
fixed-table gather — onto the neutral `arith` source, with no new emit machinery.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithBitwiseGoldenPath

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
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

/-! ## 1. Constant-time select `cond ? a : b` and and-not `~a & b`
    (lifted from `BranchlessSelectGoldenPath`) -/

/-- `c0 := 0 ; m := c0 - cond ; allOnes := 0xFF…FF ; nm := m ^ allOnes ;
    am := a & m ; bn := b & nm ; r := am | bn ; ret r` over args `[cond, a, b]`.
    Neutral-`arith` twin of `BranchlessSelect.ctSelectCom`. -/
def ctSelectArithCom : Com arithDialect [.int 64, .int 64, .int 64] (.int 64) :=
  .var (.mk (.constant 64 0) rfl .nil)
  (.var (.mk (.subi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.constant 64 18446744073709551615) rfl .nil)
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.andi 64) rfl
          (.cons (.there (.there (.there (.there (.there .here)))))
                    (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.andi 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                    (.cons (.there .here) .nil)))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)))))))

/-- **Value proof at the source.** With `m := 0 - cond`, the source denotes
    `(a & m) | (b & (m ^ 0xFF…FF))`. -/
theorem ctSelectArithCom_denote (cond a b : BitVec 64) :
    Com.denote ctSelectArithCom (.cons cond (.cons a (.cons b .nil)))
      = (a &&& ((0 : BitVec 64) - cond))
          ||| (b &&& (((0 : BitVec 64) - cond) ^^^ BitVec.ofNat 64 18446744073709551615)) := by
  simp only [ctSelectArithCom]; arith_denote; rfl

/-- **Non-vacuity, `cond = 1`**: the select returns `a`. -/
theorem ctSelectArithCom_true (a b : BitVec 64) :
    Com.denote ctSelectArithCom (.cons (1 : BitVec 64) (.cons a (.cons b .nil))) = a := by
  rw [ctSelectArithCom_denote]
  show (a &&& ((0 : BitVec 64) - 1))
        ||| (b &&& (((0 : BitVec 64) - 1) ^^^ BitVec.ofNat 64 18446744073709551615)) = a
  bv_decide

/-- **Non-vacuity, `cond = 0`**: the select returns `b`. -/
theorem ctSelectArithCom_false (a b : BitVec 64) :
    Com.denote ctSelectArithCom (.cons (0 : BitVec 64) (.cons a (.cons b .nil))) = b := by
  rw [ctSelectArithCom_denote]
  show (a &&& ((0 : BitVec 64) - 0))
        ||| (b &&& (((0 : BitVec 64) - 0) ^^^ BitVec.ofNat 64 18446744073709551615)) = b
  bv_decide

/-- Emit-legality (mechanical, one constructor per op). -/
theorem ctSelectArithCom_ok : ArithOK64 ctSelectArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))))))

/-- The lowered jasmin kernel is in the supported fragment (rides `com_*_e2e`). -/
theorem ctSelectArithCom_lowered_ok : ComOK (lowerArithToJasmin ctSelectArithCom) :=
  lowerArithToJasmin_ComOK ctSelectArithCom_ok

/-- **Emitted AArch64**, from the neutral-`arith` source via the proven lowering. -/
theorem ctSelectArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin ctSelectArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin ctSelectArithCom) 3)
      = Com.denote (lowerArithToJasmin ctSelectArithCom) V :=
  com_arm_e2e ctSelectArithCom_lowered_ok allReg64_three V s hs

/-- **Emitted RISC-V** — same neutral source, same lowering. -/
theorem ctSelectArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin ctSelectArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin ctSelectArithCom) 3)
      = Com.denote (lowerArithToJasmin ctSelectArithCom) V :=
  com_riscv_e2e ctSelectArithCom_lowered_ok allReg64_three V s hs

/-- `allOnes := 0xFF…FF ; na := a ^ allOnes (= ~a) ; r := na & b ; ret r` over `[a, b]`.
    Neutral-`arith` twin of `BranchlessSelect.andnCom`. -/
def andnArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.constant 64 18446744073709551615) rfl .nil)
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.andi 64) rfl (.cons .here (.cons (.there (.there (.there .here))) .nil)))
    (.ret .here)))

/-- **Value proof at the source**: the and-not source denotes `(a ^ 0xFF…FF) & b`. -/
theorem andnArithCom_denote (a b : BitVec 64) :
    Com.denote andnArithCom (.cons a (.cons b .nil))
      = (a ^^^ BitVec.ofNat 64 18446744073709551615) &&& b := by
  simp only [andnArithCom]; arith_denote

/-- **Non-vacuity**: the and-not source computes `(~~~a) &&& b` (the `BIC`/`ANDN`). -/
theorem andnArithCom_spec (a b : BitVec 64) :
    Com.denote andnArithCom (.cons a (.cons b .nil)) = (~~~a) &&& b := by
  rw [andnArithCom_denote]
  show (a ^^^ BitVec.ofNat 64 18446744073709551615) &&& b = (~~~a) &&& b
  bv_decide

/-- Emit-legality (mechanical). -/
theorem andnArithCom_ok : ArithOK64 andnArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem andnArithCom_lowered_ok : ComOK (lowerArithToJasmin andnArithCom) :=
  lowerArithToJasmin_ComOK andnArithCom_ok

/-- **Emitted AArch64**. -/
theorem andnArithCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin andnArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin andnArithCom) 2)
      = Com.denote (lowerArithToJasmin andnArithCom) V :=
  com_arm_e2e andnArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **Emitted RISC-V**. -/
theorem andnArithCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin andnArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin andnArithCom) 2)
      = Com.denote (lowerArithToJasmin andnArithCom) V :=
  com_riscv_e2e andnArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-! ## 2. Branchless arithmetic shift-right `n = 1`, `n = 20`
    (lifted from `BranchlessSarGoldenPath`) -/

/-- `sgn := a >>> 63 ; lo := a >>> 1 ; zero := 0 ; mask := zero - sgn ;
    hi := mask <<< 63 ; r := lo ||| hi ; ret r` over `[a]`.
    Neutral-`arith` twin of `BranchlessSar.sar1Com`. -/
def sar1ArithCom : Com arithDialect [.int 64] (.int 64) :=
  .var (.mk (.shrui_imm 64 63) rfl (.cons .here .nil))
  (.var (.mk (.shrui_imm 64 1) rfl (.cons (.there .here) .nil))
  (.var (.mk (.constant 64 0) rfl .nil)
  (.var (.mk (.subi 64) rfl (.cons .here (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.shli_imm 64 63) rfl (.cons .here .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there (.there (.there .here))) (.cons .here .nil)))
    (.ret .here))))))

/-- **Value proof at the source.** `(a >>> 1) ||| ((0 - (a >>> 63)) <<< 63)`. -/
theorem sar1ArithCom_denote (a : BitVec 64) :
    Com.denote sar1ArithCom (.cons a .nil)
      = (a >>> 1) ||| (((0 : BitVec 64) - (a >>> 63)) <<< 63) := by
  simp only [sar1ArithCom]; arith_denote; rfl

/-- **The value step that names the operation**: `BitVec.sshiftRight a 1`. -/
theorem sar1ArithCom_spec (a : BitVec 64) :
    Com.denote sar1ArithCom (.cons a .nil) = BitVec.sshiftRight a 1 := by
  rw [sar1ArithCom_denote]
  show (_ : BitVec 64) = _
  bv_decide

/-- Emit-legality (mechanical). -/
theorem sar1ArithCom_ok : ArithOK64 sar1ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _))))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem sar1ArithCom_lowered_ok : ComOK (lowerArithToJasmin sar1ArithCom) :=
  lowerArithToJasmin_ComOK sar1ArithCom_ok

/-- **Emitted AArch64**. -/
theorem sar1ArithCom_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin sar1ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin sar1ArithCom) 1)
      = Com.denote (lowerArithToJasmin sar1ArithCom) V :=
  com_arm_e2e sar1ArithCom_lowered_ok allReg64_one V s hs

/-- **Emitted RISC-V**. -/
theorem sar1ArithCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin sar1ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin sar1ArithCom) 1)
      = Com.denote (lowerArithToJasmin sar1ArithCom) V :=
  com_riscv_e2e sar1ArithCom_lowered_ok allReg64_one V s hs

/-- The same branchless recipe with `n = 20`, `64 - n = 44`.
    Neutral-`arith` twin of `BranchlessSar.sar20Com`. -/
def sar20ArithCom : Com arithDialect [.int 64] (.int 64) :=
  .var (.mk (.shrui_imm 64 63) rfl (.cons .here .nil))
  (.var (.mk (.shrui_imm 64 20) rfl (.cons (.there .here) .nil))
  (.var (.mk (.constant 64 0) rfl .nil)
  (.var (.mk (.subi 64) rfl (.cons .here (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.shli_imm 64 44) rfl (.cons .here .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there (.there (.there .here))) (.cons .here .nil)))
    (.ret .here))))))

/-- **Value proof at the source.** `(a >>> 20) ||| ((0 - (a >>> 63)) <<< 44)`. -/
theorem sar20ArithCom_denote (a : BitVec 64) :
    Com.denote sar20ArithCom (.cons a .nil)
      = (a >>> 20) ||| (((0 : BitVec 64) - (a >>> 63)) <<< 44) := by
  simp only [sar20ArithCom]; arith_denote; rfl

/-- **The value step that names the operation**: `BitVec.sshiftRight a 20`. -/
theorem sar20ArithCom_spec (a : BitVec 64) :
    Com.denote sar20ArithCom (.cons a .nil) = BitVec.sshiftRight a 20 := by
  rw [sar20ArithCom_denote]
  show (_ : BitVec 64) = _
  bv_decide

/-- Emit-legality (mechanical). -/
theorem sar20ArithCom_ok : ArithOK64 sar20ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _))))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem sar20ArithCom_lowered_ok : ComOK (lowerArithToJasmin sar20ArithCom) :=
  lowerArithToJasmin_ComOK sar20ArithCom_ok

/-- **Emitted AArch64**. -/
theorem sar20ArithCom_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin sar20ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin sar20ArithCom) 1)
      = Com.denote (lowerArithToJasmin sar20ArithCom) V :=
  com_arm_e2e sar20ArithCom_lowered_ok allReg64_one V s hs

/-- **Emitted RISC-V**. -/
theorem sar20ArithCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin sar20ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin sar20ArithCom) 1)
      = Com.denote (lowerArithToJasmin sar20ArithCom) V :=
  com_riscv_e2e sar20ArithCom_lowered_ok allReg64_one V s hs

/-! ## 3. u32-via-masked-u64 ARX: add32, xor32, rotl32 (k=16, k=12), chacha quarter-step
    (lifted from `Width32EmitGoldenPath`) -/

/-- `s := a + b ; m := 0xFFFFFFFF ; r := s &&& m` over `[a, b]`.
    Neutral-`arith` twin of `Width32Emit.add32Com`. -/
def add32ArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.addi 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.constant 64 4294967295) rfl .nil)
  (.var (.mk (.andi 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)))

/-- **Value proof at the source** (the masked sum). -/
theorem add32ArithCom_denote (a b : BitVec 64) :
    Com.denote add32ArithCom (.cons a (.cons b .nil))
      = (b + a) &&& BitVec.ofNat 64 4294967295 := by
  simp only [add32ArithCom]; arith_denote

/-- **Recognizable u32 `_spec`.** The masked-u64 add equals the 32-bit add. -/
theorem add32ArithCom_spec (a b : BitVec 64) :
    Com.denote add32ArithCom (.cons a (.cons b .nil))
      = (a.setWidth 32 + b.setWidth 32).setWidth 64 := by
  rw [add32ArithCom_denote]
  show ((b + a) &&& BitVec.ofNat 64 4294967295) = _
  bv_decide

/-- Emit-legality (mechanical). -/
theorem add32ArithCom_ok : ArithOK64 add32ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem add32ArithCom_lowered_ok : ComOK (lowerArithToJasmin add32ArithCom) :=
  lowerArithToJasmin_ComOK add32ArithCom_ok

/-- **Emitted AArch64**. -/
theorem add32ArithCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin add32ArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin add32ArithCom) 2)
      = Com.denote (lowerArithToJasmin add32ArithCom) V :=
  com_arm_e2e add32ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **Emitted RISC-V**. -/
theorem add32ArithCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin add32ArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin add32ArithCom) 2)
      = Com.denote (lowerArithToJasmin add32ArithCom) V :=
  com_riscv_e2e add32ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- `t := a ^ b ; m := 0xFFFFFFFF ; r := t &&& m` over `[a, b]`.
    Neutral-`arith` twin of `Width32Emit.xor32Com`. -/
def xor32ArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.constant 64 4294967295) rfl .nil)
  (.var (.mk (.andi 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)))

/-- **Value proof at the source.** -/
theorem xor32ArithCom_denote (a b : BitVec 64) :
    Com.denote xor32ArithCom (.cons a (.cons b .nil))
      = (b ^^^ a) &&& BitVec.ofNat 64 4294967295 := by
  simp only [xor32ArithCom]; arith_denote

/-- **Recognizable u32 `_spec`.** The masked-u64 xor equals the 32-bit xor. -/
theorem xor32ArithCom_spec (a b : BitVec 64) :
    Com.denote xor32ArithCom (.cons a (.cons b .nil))
      = (a.setWidth 32 ^^^ b.setWidth 32).setWidth 64 := by
  rw [xor32ArithCom_denote]
  show ((b ^^^ a) &&& BitVec.ofNat 64 4294967295) = _
  bv_decide

/-- Emit-legality (mechanical). -/
theorem xor32ArithCom_ok : ArithOK64 xor32ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem xor32ArithCom_lowered_ok : ComOK (lowerArithToJasmin xor32ArithCom) :=
  lowerArithToJasmin_ComOK xor32ArithCom_ok

/-- **Emitted AArch64**. -/
theorem xor32ArithCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin xor32ArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin xor32ArithCom) 2)
      = Com.denote (lowerArithToJasmin xor32ArithCom) V :=
  com_arm_e2e xor32ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **Emitted RISC-V**. -/
theorem xor32ArithCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin xor32ArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin xor32ArithCom) 2)
      = Com.denote (lowerArithToJasmin xor32ArithCom) V :=
  com_riscv_e2e xor32ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- `m := 0xFFFFFFFF ; am := a &&& m ; hi := am <<< 16 ; lo := am >>> 16 ;
    u := hi ||| lo ; r := u &&& m` over `[a]`.
    Neutral-`arith` twin of `Width32Emit.rotl32Com_16`. -/
def rotl32ArithCom_16 : Com arithDialect [.int 64] (.int 64) :=
  .var (.mk (.constant 64 4294967295) rfl .nil)
  (.var (.mk (.andi 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shli_imm 64 16) rfl (.cons .here .nil))
  (.var (.mk (.shrui_imm 64 16) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.andi 64) rfl
          (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
    (.ret .here))))))

/-- **Value proof at the source.** -/
theorem rotl32ArithCom_16_denote (a : BitVec 64) :
    Com.denote rotl32ArithCom_16 (.cons a .nil)
      = (((a &&& BitVec.ofNat 64 4294967295) <<< 16)
          ||| ((a &&& BitVec.ofNat 64 4294967295) >>> 16))
          &&& BitVec.ofNat 64 4294967295 := by
  simp only [rotl32ArithCom_16]; arith_denote

/-- **Recognizable u32 `_spec`.** The masked shift-or equals 32-bit `rotateLeft 16`. -/
theorem rotl32ArithCom_16_spec (a : BitVec 64) :
    Com.denote rotl32ArithCom_16 (.cons a .nil)
      = ((a.setWidth 32).rotateLeft 16).setWidth 64 := by
  rw [rotl32ArithCom_16_denote]
  show ((((a &&& BitVec.ofNat 64 4294967295) <<< 16)
        ||| ((a &&& BitVec.ofNat 64 4294967295) >>> 16))
        &&& BitVec.ofNat 64 4294967295) = _
  bv_decide

/-- Emit-legality (mechanical). -/
theorem rotl32ArithCom_16_ok : ArithOK64 rotl32ArithCom_16 :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _))))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem rotl32ArithCom_16_lowered_ok : ComOK (lowerArithToJasmin rotl32ArithCom_16) :=
  lowerArithToJasmin_ComOK rotl32ArithCom_16_ok

/-- **Emitted AArch64**. -/
theorem rotl32ArithCom_16_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin rotl32ArithCom_16) 1))).regs)
        (comRetName (lowerArithToJasmin rotl32ArithCom_16) 1)
      = Com.denote (lowerArithToJasmin rotl32ArithCom_16) V :=
  com_arm_e2e rotl32ArithCom_16_lowered_ok allReg64_one V s hs

/-- **Emitted RISC-V**. -/
theorem rotl32ArithCom_16_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin rotl32ArithCom_16) 1))).regs)
        (comRetName (lowerArithToJasmin rotl32ArithCom_16) 1)
      = Com.denote (lowerArithToJasmin rotl32ArithCom_16) V :=
  com_riscv_e2e rotl32ArithCom_16_lowered_ok allReg64_one V s hs

/-- `rotl32 a 12` over `[a]`. Neutral-`arith` twin of `Width32Emit.rotl32Com_12`. -/
def rotl32ArithCom_12 : Com arithDialect [.int 64] (.int 64) :=
  .var (.mk (.constant 64 4294967295) rfl .nil)
  (.var (.mk (.andi 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shli_imm 64 12) rfl (.cons .here .nil))
  (.var (.mk (.shrui_imm 64 20) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.andi 64) rfl
          (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
    (.ret .here))))))

/-- **Value proof at the source.** -/
theorem rotl32ArithCom_12_denote (a : BitVec 64) :
    Com.denote rotl32ArithCom_12 (.cons a .nil)
      = (((a &&& BitVec.ofNat 64 4294967295) <<< 12)
          ||| ((a &&& BitVec.ofNat 64 4294967295) >>> 20))
          &&& BitVec.ofNat 64 4294967295 := by
  simp only [rotl32ArithCom_12]; arith_denote

/-- **Recognizable u32 `_spec`.** The masked shift-or equals 32-bit `rotateLeft 12`. -/
theorem rotl32ArithCom_12_spec (a : BitVec 64) :
    Com.denote rotl32ArithCom_12 (.cons a .nil)
      = ((a.setWidth 32).rotateLeft 12).setWidth 64 := by
  rw [rotl32ArithCom_12_denote]
  show ((((a &&& BitVec.ofNat 64 4294967295) <<< 12)
        ||| ((a &&& BitVec.ofNat 64 4294967295) >>> 20))
        &&& BitVec.ofNat 64 4294967295) = _
  bv_decide

/-- Emit-legality (mechanical). -/
theorem rotl32ArithCom_12_ok : ArithOK64 rotl32ArithCom_12 :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _))))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem rotl32ArithCom_12_lowered_ok : ComOK (lowerArithToJasmin rotl32ArithCom_12) :=
  lowerArithToJasmin_ComOK rotl32ArithCom_12_ok

/-- **Emitted AArch64**. -/
theorem rotl32ArithCom_12_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin rotl32ArithCom_12) 1))).regs)
        (comRetName (lowerArithToJasmin rotl32ArithCom_12) 1)
      = Com.denote (lowerArithToJasmin rotl32ArithCom_12) V :=
  com_arm_e2e rotl32ArithCom_12_lowered_ok allReg64_one V s hs

/-- **Emitted RISC-V**. -/
theorem rotl32ArithCom_12_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin rotl32ArithCom_12) 1))).regs)
        (comRetName (lowerArithToJasmin rotl32ArithCom_12) 1)
      = Com.denote (lowerArithToJasmin rotl32ArithCom_12) V :=
  com_riscv_e2e rotl32ArithCom_12_lowered_ok allReg64_one V s hs

/-- One ChaCha20 quarter-round component `(d ^ a) <<<₃₂ 16` over `[d, a]`.
    Neutral-`arith` twin of `Width32Emit.chachaQuarterStepCom`. -/
def chachaQuarterStepArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.xori 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.constant 64 4294967295) rfl .nil)
  (.var (.mk (.andi 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shli_imm 64 16) rfl (.cons .here .nil))
  (.var (.mk (.shrui_imm 64 16) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.andi 64) rfl
          (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
    (.ret .here)))))))

/-- **Value proof at the source.** -/
theorem chachaQuarterStepArithCom_denote (d a : BitVec 64) :
    Com.denote chachaQuarterStepArithCom (.cons d (.cons a .nil))
      = ((((d ^^^ a) &&& BitVec.ofNat 64 4294967295) <<< 16)
          ||| (((d ^^^ a) &&& BitVec.ofNat 64 4294967295) >>> 16))
          &&& BitVec.ofNat 64 4294967295 := by
  simp only [chachaQuarterStepArithCom]; arith_denote

/-- **Recognizable u32 `_spec`.** The whole step equals `rotateLeft 16` of the 32-bit
    xor `d ^ a`, zero-extended back to 64 bits — a real ChaCha20 component. -/
theorem chachaQuarterStepArithCom_spec (d a : BitVec 64) :
    Com.denote chachaQuarterStepArithCom (.cons d (.cons a .nil))
      = (((d.setWidth 32 ^^^ a.setWidth 32).rotateLeft 16)).setWidth 64 := by
  rw [chachaQuarterStepArithCom_denote]
  show ((((d ^^^ a) &&& BitVec.ofNat 64 4294967295) <<< 16)
        ||| (((d ^^^ a) &&& BitVec.ofNat 64 4294967295) >>> 16))
        &&& BitVec.ofNat 64 4294967295 = _
  bv_decide

/-- Emit-legality (mechanical). -/
theorem chachaQuarterStepArithCom_ok : ArithOK64 chachaQuarterStepArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem chachaQuarterStepArithCom_lowered_ok :
    ComOK (lowerArithToJasmin chachaQuarterStepArithCom) :=
  lowerArithToJasmin_ComOK chachaQuarterStepArithCom_ok

/-- **Emitted AArch64**. -/
theorem chachaQuarterStepArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin chachaQuarterStepArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin chachaQuarterStepArithCom) 2)
      = Com.denote (lowerArithToJasmin chachaQuarterStepArithCom) V :=
  com_arm_e2e chachaQuarterStepArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **Emitted RISC-V**. -/
theorem chachaQuarterStepArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin chachaQuarterStepArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin chachaQuarterStepArithCom) 2)
      = Com.denote (lowerArithToJasmin chachaQuarterStepArithCom) V :=
  com_riscv_e2e chachaQuarterStepArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-! ## 4. Constant-time fixed-table gather (AES S-box head)
    (lifted from `CtTableEmitGoldenPath`) -/

/-- The constant-time AES-S-box-head gather as a `Com arithDialect` over `[i]`.
    Neutral-`arith` twin of `CtTableEmit.ctTableLookupCom` (37 ops). -/
def ctTableLookupArithCom : Com arithDialect [.int 64] (.int 64) :=
  .var (.mk (.constant 64 0) rfl .nil)
  (.var (.mk (.constant 64 1) rfl .nil)
  -- entry k = 0
  (.var (.mk (.constant 64 0) rfl .nil)
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there .here))) (.cons .here .nil)))
  (.var (.mk (.subi 64) rfl
          (.cons (.there (.there (.there .here))) (.cons .here .nil)))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shrui_imm 64 63) rfl (.cons .here .nil))
  (.var (.mk (.subi 64) rfl
          (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  (.var (.mk (.constant 64 99) rfl .nil)
  (.var (.mk (.andi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- entry k = 1
  (.var (.mk (.constant 64 1) rfl .nil)
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
                    (.cons .here .nil)))
  (.var (.mk (.subi 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
                    (.cons .here .nil)))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shrui_imm 64 63) rfl (.cons .here .nil))
  (.var (.mk (.subi 64) rfl
          (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil)))
  (.var (.mk (.constant 64 124) rfl .nil)
  (.var (.mk (.andi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- entry k = 2
  (.var (.mk (.constant 64 2) rfl .nil)
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))
                    (.cons .here .nil)))
  (.var (.mk (.subi 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))
                    (.cons .here .nil)))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shrui_imm 64 63) rfl (.cons .here .nil))
  (.var (.mk (.subi 64) rfl
          (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) .nil)))
  (.var (.mk (.constant 64 119) rfl .nil)
  (.var (.mk (.andi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- entry k = 3
  (.var (.mk (.constant 64 3) rfl .nil)
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))
                    (.cons .here .nil)))
  (.var (.mk (.subi 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))
                    (.cons .here .nil)))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shrui_imm 64 63) rfl (.cons .here .nil))
  (.var (.mk (.subi 64) rfl
          (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))) .nil)))
  (.var (.mk (.constant 64 123) rfl .nil)
  (.var (.mk (.andi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- combine
  (.var (.mk (.ori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))
                    (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) .nil)))
  (.var (.mk (.ori 64) rfl
          (.cons .here
                    (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)))
  (.var (.mk (.ori 64) rfl (.cons .here (.cons (.there (.there .here)) .nil)))
    (.ret .here)))))))))))))))))))))))))))))))))))))

/-- **Value proof at the source.** The scan denotes the explicit branchless gather
    expression, OR-ed over the four entries. -/
theorem ctTableLookupArithCom_denote (i : BitVec 64) :
    Com.denote ctTableLookupArithCom (.cons i .nil)
      = (((BitVec.ofNat 64 99 &&&
            ((((i ^^^ BitVec.ofNat 64 0) ||| ((0 : BitVec 64) - (i ^^^ BitVec.ofNat 64 0))) >>> 63)
              - (1 : BitVec 64)))
        ||| (BitVec.ofNat 64 124 &&&
            ((((i ^^^ BitVec.ofNat 64 1) ||| ((0 : BitVec 64) - (i ^^^ BitVec.ofNat 64 1))) >>> 63)
              - (1 : BitVec 64))))
        ||| (BitVec.ofNat 64 119 &&&
            ((((i ^^^ BitVec.ofNat 64 2) ||| ((0 : BitVec 64) - (i ^^^ BitVec.ofNat 64 2))) >>> 63)
              - (1 : BitVec 64))))
        ||| (BitVec.ofNat 64 123 &&&
            ((((i ^^^ BitVec.ofNat 64 3) ||| ((0 : BitVec 64) - (i ^^^ BitVec.ofNat 64 3))) >>> 63)
              - (1 : BitVec 64))) := by
  unfold ctTableLookupArithCom; rfl

/-- **The recognizable table function** `S[0..3] = [0x63, 0x7c, 0x77, 0x7b]`
    (AES S-box head, FIPS 197 §5.1.1). -/
def aesSboxHead (n : Nat) : BitVec 64 :=
  if n = 0 then BitVec.ofNat 64 0x63
  else if n = 1 then BitVec.ofNat 64 0x7c
  else if n = 2 then BitVec.ofNat 64 0x77
  else BitVec.ofNat 64 0x7b

/-- **The non-vacuous correctness result.** For any public index `i < 4`, the emitted
    constant-time gather computes the table value `T[i] = AES S-box[i]`. -/
theorem ctTableLookupArithCom_spec (i : BitVec 64) (h : i.toNat < 4) :
    Com.denote ctTableLookupArithCom (.cons i .nil) = aesSboxHead i.toNat := by
  rw [ctTableLookupArithCom_denote]
  have hcase : i = 0#64 ∨ i = 1#64 ∨ i = 2#64 ∨ i = 3#64 := by
    rcases (show i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 by omega)
      with hk | hk | hk | hk <;>
      first
        | exact Or.inl (BitVec.eq_of_toNat_eq (by rw [hk]; decide))
        | exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by rw [hk]; decide)))
        | exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by rw [hk]; decide))))
        | exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq (by rw [hk]; decide))))
  rcases hcase with rfl | rfl | rfl | rfl <;> rfl

/-- Emit-legality (mechanical, 37 ops). -/
theorem ctTableLookupArithCom_ok : ArithOK64 ctTableLookupArithCom := by
  unfold ctTableLookupArithCom
  repeat' first
    | exact ArithOK64.ret _
    | refine ArithOK64.var rfl ?_

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem ctTableLookupArithCom_lowered_ok : ComOK (lowerArithToJasmin ctTableLookupArithCom) :=
  lowerArithToJasmin_ComOK ctTableLookupArithCom_ok

/-- **Emitted AArch64**. -/
theorem ctTableLookupArithCom_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin ctTableLookupArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin ctTableLookupArithCom) 1)
      = Com.denote (lowerArithToJasmin ctTableLookupArithCom) V :=
  com_arm_e2e ctTableLookupArithCom_lowered_ok allReg64_one V s hs

/-- **Emitted RISC-V**. -/
theorem ctTableLookupArithCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin ctTableLookupArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin ctTableLookupArithCom) 1)
      = Com.denote (lowerArithToJasmin ctTableLookupArithCom) V :=
  com_riscv_e2e ctTableLookupArithCom_lowered_ok allReg64_one V s hs

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithBitwiseGoldenPath
