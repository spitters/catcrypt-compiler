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
# Hash bit-functions lifted to the neutral `arith` dialect

Item 1 of the MLIR dialect-alignment: two crypto-primitive families that were
authored as `Com jasminDialect` (below the waist) are re-expressed one level up,
as `Com arithDialect` (the upstream-aligned neutral dialect), connected to emit
through the *proven* arith→jasmin lowering. This mirrors the field-add template
`ArithGoldenPathField.lean`, applied to:

1. **the SHA-512 round bit-functions** `Ch`, `Maj`, `Σ₀`, `Σ₁`, `σ₀`, `σ₁`
   (FIPS 180-4) — ported from `Sha512BitFuncsGoldenPath.lean`;
2. **the Keccak-f[1600] lane bit-ops** — the χ step and two ρ rotates (`r = 1`,
   `r = 44`) — ported from `KeccakBitGoldenPath.lean`.

Each kernel produces, exactly as the template:

* the `Com arithDialect` source (op-swapped from the jasmin twin, identical
  de-Bruijn structure);
* `denote = <BitVec expr>` — the same value the jasmin twin denotes (`arithDenote`
  was *defined* equal to the jasmin image, so the proof ports);
* the recognizable-spec proof tying the source to the textbook operator
  (`~~~`/`.rotateRight`/`.rotateLeft`) — `bv_decide` ports verbatim;
* `ArithOK64` (mechanical, one `ArithOK64.var rfl` per op) ⇒
  `lowerArithToJasmin_ComOK` ⇒ the lowered jasmin kernel is `ComOK`, so it rides
  the existing `com_arm_e2e` / `com_riscv_e2e` emit;
* the AArch64 + RISC-V e2e theorems through the proven lowering (no per-kernel
  backend proof).

The op-swap from the jasmin twin is mechanical: `.regArith .X 64 → .Xi 64`,
`.mulhi → .mului_extended_hi`, `.shrImm/.shlImm → .shrui_imm/.shli_imm`,
`.regConst → .constant`, type `.reg 64 → .int 64`; the `args` HVectors are copied
verbatim.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithHashesGoldenPath

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

/-! # 1. SHA-512 round bit-functions (FIPS 180-4) -/

/-! ## `Ch e f g = (e & f) ^ ((~e) & g)`

Args `[e, f, g]`. The logical-not `~e` is `e ^ 0xFFFF…FFFF` (`constant` all-ones). -/

/-- `Ch e f g = (e & f) ^ ((~e) & g)` over `[e, f, g]`, neutral-`arith`. -/
def shaChArithCom : Com arithDialect [.int 64, .int 64, .int 64] (.int 64) :=
  -- ones = 0xFFFF…FFFF
  .var (.mk (.constant 64 18446744073709551615) rfl .nil)
  -- ne = e ^ ones        (e = .there.here after the constant push)
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- ef = e & f           (e = .there.there.here, f = .there.there.there.here)
  (.var (.mk (.andi 64) rfl
          (.cons (.there (.there .here))
            (.cons (.there (.there (.there .here))) .nil)))
  -- neg = ne & g         (ne = .there.here, g = .there.there.there.there.there.here)
  (.var (.mk (.andi 64) rfl
          (.cons (.there .here)
            (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  -- r = ef ^ neg         (ef = .there.here, neg = .here)
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)))))

theorem shaChArithCom_denote (e f g : BitVec 64) :
    shaChArithCom.denote (.cons e (.cons f (.cons g .nil)))
      = (e &&& f) ^^^ ((e ^^^ BitVec.ofNat 64 18446744073709551615) &&& g) := by
  rfl

/-- Recognizable spec tying the source to `Ch e f g = (e & f) ^ ((~e) & g)`. -/
theorem shaChArithCom_spec (e f g : BitVec 64) :
    shaChArithCom.denote (.cons e (.cons f (.cons g .nil)))
      = (e &&& f) ^^^ ((~~~e) &&& g) := by
  rw [shaChArithCom_denote]; congr 1; bv_decide

theorem shaChArithCom_ok : ArithOK64 shaChArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))))

theorem shaChArithCom_lowered_ok : ComOK (lowerArithToJasmin shaChArithCom) :=
  lowerArithToJasmin_ComOK shaChArithCom_ok

theorem shaChArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin shaChArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin shaChArithCom) 3)
      = Com.denote (lowerArithToJasmin shaChArithCom) V :=
  com_arm_e2e shaChArithCom_lowered_ok FieldEmitGoldenPath.allReg64_three V s hs

theorem shaChArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin shaChArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin shaChArithCom) 3)
      = Com.denote (lowerArithToJasmin shaChArithCom) V :=
  com_riscv_e2e shaChArithCom_lowered_ok FieldEmitGoldenPath.allReg64_three V s hs

/-! ## `Maj a b c = (a & b) ^ (a & c) ^ (b & c)`

Args `[a, b, c]`. -/

/-- `Maj a b c = (a & b) ^ (a & c) ^ (b & c)` over `[a, b, c]`, neutral-`arith`. -/
def shaMajArithCom : Com arithDialect [.int 64, .int 64, .int 64] (.int 64) :=
  -- ab = a & b           (a = .here, b = .there.here)
  .var (.mk (.andi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- ac = a & c           (a = .there.here, c = .there.there.there.here)
  (.var (.mk (.andi 64) rfl
          (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)))
  -- bc = b & c           (b = .there.there.there.here, c = .there.there.there.there.here)
  (.var (.mk (.andi 64) rfl
          (.cons (.there (.there (.there .here)))
            (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- t = ab ^ ac          (ab = .there.there.here, ac = .there.here)
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- r = t ^ bc           (t = .here, bc = .there.here)
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)))))

theorem shaMajArithCom_denote (a b c : BitVec 64) :
    shaMajArithCom.denote (.cons a (.cons b (.cons c .nil)))
      = ((a &&& b) ^^^ (a &&& c)) ^^^ (b &&& c) := by
  rfl

/-- Recognizable spec (associativity of `^^^`). -/
theorem shaMajArithCom_spec (a b c : BitVec 64) :
    shaMajArithCom.denote (.cons a (.cons b (.cons c .nil)))
      = (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) := by
  rw [shaMajArithCom_denote]

theorem shaMajArithCom_ok : ArithOK64 shaMajArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))))

theorem shaMajArithCom_lowered_ok : ComOK (lowerArithToJasmin shaMajArithCom) :=
  lowerArithToJasmin_ComOK shaMajArithCom_ok

theorem shaMajArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin shaMajArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin shaMajArithCom) 3)
      = Com.denote (lowerArithToJasmin shaMajArithCom) V :=
  com_arm_e2e shaMajArithCom_lowered_ok FieldEmitGoldenPath.allReg64_three V s hs

theorem shaMajArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin shaMajArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin shaMajArithCom) 3)
      = Com.denote (lowerArithToJasmin shaMajArithCom) V :=
  com_riscv_e2e shaMajArithCom_lowered_ok FieldEmitGoldenPath.allReg64_three V s hs

/-! ## `Σ₀ a = ROTR^28 a ^ ROTR^34 a ^ ROTR^39 a`

Args `[a]`. Each `ROTR^n a = (a >>> n) ||| (a <<< (64-n))`. -/

/-- `Σ₀ a = ROTR^28 a ^ ROTR^34 a ^ ROTR^39 a` over `[a]`, neutral-`arith`. -/
def shaBigSigma0ArithCom : Com arithDialect [.int 64] (.int 64) :=
  -- r28: hi = a >>> 28 ; lo = a <<< 36 ; r28 = hi | lo
  .var (.mk (.shrui_imm 64 28) rfl (.cons .here .nil))
  (.var (.mk (.shli_imm 64 36) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- r34: hi = a >>> 34 ; lo = a <<< 30 ; r34 = hi | lo   (a now = .there.there.there.here)
  (.var (.mk (.shrui_imm 64 34) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.shli_imm 64 30) rfl (.cons (.there (.there (.there (.there .here)))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- r39: hi = a >>> 39 ; lo = a <<< 25 ; r39 = hi | lo   (a now = .there^6.here)
  (.var (.mk (.shrui_imm 64 39) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))
  (.var (.mk (.shli_imm 64 25) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- t = r28 ^ r34   (r28 = .there^6.here, r34 = .there^3.here)
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there .here))) .nil)))
  -- r = t ^ r39   (t = .here, r39 = .there.here)
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)))))))))))

theorem shaBigSigma0ArithCom_denote (a : BitVec 64) :
    shaBigSigma0ArithCom.denote (.cons a .nil)
      = (((a >>> 28) ||| (a <<< 36)) ^^^ ((a >>> 34) ||| (a <<< 30)))
          ^^^ ((a >>> 39) ||| (a <<< 25)) := by
  rfl

/-- Recognizable spec via `BitVec.rotateRight`. -/
theorem shaBigSigma0ArithCom_spec (a : BitVec 64) :
    shaBigSigma0ArithCom.denote (.cons a .nil)
      = a.rotateRight 28 ^^^ a.rotateRight 34 ^^^ a.rotateRight 39 := by
  rw [shaBigSigma0ArithCom_denote]; simp only [BitVec.rotateRight_def]

theorem shaBigSigma0ArithCom_ok : ArithOK64 shaBigSigma0ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
      (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
        (ArithOK64.ret _)))))))))))

theorem shaBigSigma0ArithCom_lowered_ok : ComOK (lowerArithToJasmin shaBigSigma0ArithCom) :=
  lowerArithToJasmin_ComOK shaBigSigma0ArithCom_ok

theorem shaBigSigma0ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin shaBigSigma0ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin shaBigSigma0ArithCom) 1)
      = Com.denote (lowerArithToJasmin shaBigSigma0ArithCom) V :=
  com_arm_e2e shaBigSigma0ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

theorem shaBigSigma0ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin shaBigSigma0ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin shaBigSigma0ArithCom) 1)
      = Com.denote (lowerArithToJasmin shaBigSigma0ArithCom) V :=
  com_riscv_e2e shaBigSigma0ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-! ## `Σ₁ e = ROTR^14 e ^ ROTR^18 e ^ ROTR^41 e`

Args `[e]`. Same `shr | shl` rotate shape as `Σ₀`. -/

/-- `Σ₁ e = ROTR^14 e ^ ROTR^18 e ^ ROTR^41 e` over `[e]`, neutral-`arith`. -/
def shaBigSigma1ArithCom : Com arithDialect [.int 64] (.int 64) :=
  -- r14: e >>> 14 ; e <<< 50 ; |
  .var (.mk (.shrui_imm 64 14) rfl (.cons .here .nil))
  (.var (.mk (.shli_imm 64 50) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- r18: e >>> 18 ; e <<< 46 ; |
  (.var (.mk (.shrui_imm 64 18) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.shli_imm 64 46) rfl (.cons (.there (.there (.there (.there .here)))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- r41: e >>> 41 ; e <<< 23 ; |
  (.var (.mk (.shrui_imm 64 41) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))
  (.var (.mk (.shli_imm 64 23) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- t = r14 ^ r18
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there .here))) .nil)))
  -- r = t ^ r41
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)))))))))))

theorem shaBigSigma1ArithCom_denote (e : BitVec 64) :
    shaBigSigma1ArithCom.denote (.cons e .nil)
      = (((e >>> 14) ||| (e <<< 50)) ^^^ ((e >>> 18) ||| (e <<< 46)))
          ^^^ ((e >>> 41) ||| (e <<< 23)) := by
  rfl

/-- Recognizable spec via `BitVec.rotateRight`. -/
theorem shaBigSigma1ArithCom_spec (e : BitVec 64) :
    shaBigSigma1ArithCom.denote (.cons e .nil)
      = e.rotateRight 14 ^^^ e.rotateRight 18 ^^^ e.rotateRight 41 := by
  rw [shaBigSigma1ArithCom_denote]; simp only [BitVec.rotateRight_def]

theorem shaBigSigma1ArithCom_ok : ArithOK64 shaBigSigma1ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
      (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
        (ArithOK64.ret _)))))))))))

theorem shaBigSigma1ArithCom_lowered_ok : ComOK (lowerArithToJasmin shaBigSigma1ArithCom) :=
  lowerArithToJasmin_ComOK shaBigSigma1ArithCom_ok

theorem shaBigSigma1ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin shaBigSigma1ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin shaBigSigma1ArithCom) 1)
      = Com.denote (lowerArithToJasmin shaBigSigma1ArithCom) V :=
  com_arm_e2e shaBigSigma1ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

theorem shaBigSigma1ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin shaBigSigma1ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin shaBigSigma1ArithCom) 1)
      = Com.denote (lowerArithToJasmin shaBigSigma1ArithCom) V :=
  com_riscv_e2e shaBigSigma1ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-! ## `σ₀ x = ROTR^1 x ^ ROTR^8 x ^ (x >>> 7)`

Args `[x]`. Two rotates plus a plain logical shift-right. -/

/-- `σ₀ x = ROTR^1 x ^ ROTR^8 x ^ (x >>> 7)` over `[x]`, neutral-`arith`. -/
def shaSmallSigma0ArithCom : Com arithDialect [.int 64] (.int 64) :=
  -- r1: x >>> 1 ; x <<< 63 ; |
  .var (.mk (.shrui_imm 64 1) rfl (.cons .here .nil))
  (.var (.mk (.shli_imm 64 63) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- r8: x >>> 8 ; x <<< 56 ; |
  (.var (.mk (.shrui_imm 64 8) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.shli_imm 64 56) rfl (.cons (.there (.there (.there (.there .here)))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- sh = x >>> 7        (x now = .there^6.here)
  (.var (.mk (.shrui_imm 64 7) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))
  -- t = r1 ^ r8        (r1 = .there^4.here, r8 = .there.here)
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there .here))))
            (.cons (.there .here) .nil)))
  -- r = t ^ sh        (t = .here, sh = .there.here)
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)))))))))

theorem shaSmallSigma0ArithCom_denote (x : BitVec 64) :
    shaSmallSigma0ArithCom.denote (.cons x .nil)
      = (((x >>> 1) ||| (x <<< 63)) ^^^ ((x >>> 8) ||| (x <<< 56))) ^^^ (x >>> 7) := by
  rfl

/-- Recognizable spec via `BitVec.rotateRight`. -/
theorem shaSmallSigma0ArithCom_spec (x : BitVec 64) :
    shaSmallSigma0ArithCom.denote (.cons x .nil)
      = x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ (x >>> 7) := by
  rw [shaSmallSigma0ArithCom_denote]; simp only [BitVec.rotateRight_def]

theorem shaSmallSigma0ArithCom_ok : ArithOK64 shaSmallSigma0ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
      (ArithOK64.var rfl (ArithOK64.ret _)))))))))

theorem shaSmallSigma0ArithCom_lowered_ok : ComOK (lowerArithToJasmin shaSmallSigma0ArithCom) :=
  lowerArithToJasmin_ComOK shaSmallSigma0ArithCom_ok

theorem shaSmallSigma0ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin shaSmallSigma0ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin shaSmallSigma0ArithCom) 1)
      = Com.denote (lowerArithToJasmin shaSmallSigma0ArithCom) V :=
  com_arm_e2e shaSmallSigma0ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

theorem shaSmallSigma0ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin shaSmallSigma0ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin shaSmallSigma0ArithCom) 1)
      = Com.denote (lowerArithToJasmin shaSmallSigma0ArithCom) V :=
  com_riscv_e2e shaSmallSigma0ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-! ## `σ₁ x = ROTR^19 x ^ ROTR^61 x ^ (x >>> 6)`

Args `[x]`. Same shape as `σ₀`, different offsets. -/

/-- `σ₁ x = ROTR^19 x ^ ROTR^61 x ^ (x >>> 6)` over `[x]`, neutral-`arith`. -/
def shaSmallSigma1ArithCom : Com arithDialect [.int 64] (.int 64) :=
  -- r19: x >>> 19 ; x <<< 45 ; |
  .var (.mk (.shrui_imm 64 19) rfl (.cons .here .nil))
  (.var (.mk (.shli_imm 64 45) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- r61: x >>> 61 ; x <<< 3 ; |
  (.var (.mk (.shrui_imm 64 61) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.shli_imm 64 3) rfl (.cons (.there (.there (.there (.there .here)))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- sh = x >>> 6
  (.var (.mk (.shrui_imm 64 6) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))
  -- t = r19 ^ r61
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there .here))))
            (.cons (.there .here) .nil)))
  -- r = t ^ sh
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)))))))))

theorem shaSmallSigma1ArithCom_denote (x : BitVec 64) :
    shaSmallSigma1ArithCom.denote (.cons x .nil)
      = (((x >>> 19) ||| (x <<< 45)) ^^^ ((x >>> 61) ||| (x <<< 3))) ^^^ (x >>> 6) := by
  rfl

/-- Recognizable spec via `BitVec.rotateRight`. -/
theorem shaSmallSigma1ArithCom_spec (x : BitVec 64) :
    shaSmallSigma1ArithCom.denote (.cons x .nil)
      = x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ (x >>> 6) := by
  rw [shaSmallSigma1ArithCom_denote]; simp only [BitVec.rotateRight_def]

theorem shaSmallSigma1ArithCom_ok : ArithOK64 shaSmallSigma1ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
      (ArithOK64.var rfl (ArithOK64.ret _)))))))))

theorem shaSmallSigma1ArithCom_lowered_ok : ComOK (lowerArithToJasmin shaSmallSigma1ArithCom) :=
  lowerArithToJasmin_ComOK shaSmallSigma1ArithCom_ok

theorem shaSmallSigma1ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin shaSmallSigma1ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin shaSmallSigma1ArithCom) 1)
      = Com.denote (lowerArithToJasmin shaSmallSigma1ArithCom) V :=
  com_arm_e2e shaSmallSigma1ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

theorem shaSmallSigma1ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin shaSmallSigma1ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin shaSmallSigma1ArithCom) 1)
      = Com.denote (lowerArithToJasmin shaSmallSigma1ArithCom) V :=
  com_riscv_e2e shaSmallSigma1ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-! # 2. Keccak-f[1600] lane bit-ops (FIPS 202) -/

/-! ## The χ step: `χ a b c = a ⊕ (¬b ∧ c)` per lane

Args `[a, b, c]`. `¬b` is `b ^ 0xFFFF…FF` (`constant` all-ones). -/

/-- The χ-step source over args `[a, b, c]`, neutral-`arith`:
    `ones := 2^64-1 ; nb := b ^ ones ; nbc := nb & c ; r := a ^ nbc ; ret r`. -/
def keccakChiArithCom : Com arithDialect [.int 64, .int 64, .int 64] (.int 64) :=
  -- ones = 2^64-1
  .var (.mk (.constant 64 18446744073709551615) rfl .nil)
  -- nb = b ^ ones   (= ¬b);  b = .there (.there .here), ones = .here
  (.var (.mk (.xori 64) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
  -- nbc = nb & c ;  nb = .here, c = .there (.there (.there (.there .here)))
  (.var (.mk (.andi 64) rfl
          (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- r = a ^ nbc ;  a = .there (.there (.there .here)), nbc = .here
  (.var (.mk (.xori 64) rfl (.cons (.there (.there (.there .here))) (.cons .here .nil)))
    (.ret .here))))

theorem keccakChiArithCom_denote (a b c : BitVec 64) :
    keccakChiArithCom.denote (.cons a (.cons b (.cons c .nil)))
      = a ^^^ ((b ^^^ BitVec.ofNat 64 18446744073709551615) &&& c) := by
  rfl

/-- Recognizable χ spec `a ⊕ (¬b ∧ c)`; `¬b = b ^ 0xFF…FF` certified by `bv_decide`. -/
theorem keccakChiArithCom_spec (a b c : BitVec 64) :
    keccakChiArithCom.denote (.cons a (.cons b (.cons c .nil)))
      = a ^^^ ((~~~b) &&& c) := by
  rw [keccakChiArithCom_denote]; show (_ : BitVec 64) = _; bv_decide

theorem keccakChiArithCom_ok : ArithOK64 keccakChiArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
    (ArithOK64.var rfl (ArithOK64.ret _))))

theorem keccakChiArithCom_lowered_ok : ComOK (lowerArithToJasmin keccakChiArithCom) :=
  lowerArithToJasmin_ComOK keccakChiArithCom_ok

theorem keccakChiArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin keccakChiArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin keccakChiArithCom) 3)
      = Com.denote (lowerArithToJasmin keccakChiArithCom) V :=
  com_arm_e2e keccakChiArithCom_lowered_ok FieldEmitGoldenPath.allReg64_three V s hs

theorem keccakChiArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin keccakChiArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin keccakChiArithCom) 3)
      = Com.denote (lowerArithToJasmin keccakChiArithCom) V :=
  com_riscv_e2e keccakChiArithCom_lowered_ok FieldEmitGoldenPath.allReg64_three V s hs

/-! ## The ρ rotations: `ρ_r a = a.rotateLeft r`

The left-rotate by `r` is `(a <<< r) ||| (a >>> (64 - r))`. Two example offsets,
`r = 1` and `r = 44`. -/

/-- ρ with offset 1 over arg `[a]`, neutral-`arith`:
    `sh := a <<< 1 ; shr := a >>> 63 ; r := sh | shr ; ret r`. -/
def keccakRho1ArithCom : Com arithDialect [.int 64] (.int 64) :=
  -- sh = a <<< 1 ;  a = .here
  .var (.mk (.shli_imm 64 1) rfl (.cons .here .nil))
  -- shr = a >>> 63 ;  a = .there .here
  (.var (.mk (.shrui_imm 64 63) rfl (.cons (.there .here) .nil))
  -- r = sh | shr ;  sh = .there .here, shr = .here
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)))

theorem keccakRho1ArithCom_denote (a : BitVec 64) :
    keccakRho1ArithCom.denote (.cons a .nil) = (a <<< 1) ||| (a >>> 63) := by
  rfl

/-- Recognizable ρ spec `a.rotateLeft 1`; shift-or synthesis certified by `bv_decide`. -/
theorem keccakRho1ArithCom_spec (a : BitVec 64) :
    keccakRho1ArithCom.denote (.cons a .nil) = a.rotateLeft 1 := by
  rw [keccakRho1ArithCom_denote]; show (_ : BitVec 64) = _; bv_decide

theorem keccakRho1ArithCom_ok : ArithOK64 keccakRho1ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))

theorem keccakRho1ArithCom_lowered_ok : ComOK (lowerArithToJasmin keccakRho1ArithCom) :=
  lowerArithToJasmin_ComOK keccakRho1ArithCom_ok

theorem keccakRho1ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin keccakRho1ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin keccakRho1ArithCom) 1)
      = Com.denote (lowerArithToJasmin keccakRho1ArithCom) V :=
  com_arm_e2e keccakRho1ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

theorem keccakRho1ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin keccakRho1ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin keccakRho1ArithCom) 1)
      = Com.denote (lowerArithToJasmin keccakRho1ArithCom) V :=
  com_riscv_e2e keccakRho1ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

/-- ρ with offset 44 over arg `[a]`, neutral-`arith`:
    `sh := a <<< 44 ; shr := a >>> 20 ; r := sh | shr ; ret r`. -/
def keccakRho44ArithCom : Com arithDialect [.int 64] (.int 64) :=
  -- sh = a <<< 44 ;  a = .here
  .var (.mk (.shli_imm 64 44) rfl (.cons .here .nil))
  -- shr = a >>> 20 ;  a = .there .here   (64 - 44 = 20)
  (.var (.mk (.shrui_imm 64 20) rfl (.cons (.there .here) .nil))
  -- r = sh | shr ;  sh = .there .here, shr = .here
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)))

theorem keccakRho44ArithCom_denote (a : BitVec 64) :
    keccakRho44ArithCom.denote (.cons a .nil) = (a <<< 44) ||| (a >>> 20) := by
  rfl

/-- Recognizable ρ spec `a.rotateLeft 44`; shift-or synthesis certified by `bv_decide`. -/
theorem keccakRho44ArithCom_spec (a : BitVec 64) :
    keccakRho44ArithCom.denote (.cons a .nil) = a.rotateLeft 44 := by
  rw [keccakRho44ArithCom_denote]; show (_ : BitVec 64) = _; bv_decide

theorem keccakRho44ArithCom_ok : ArithOK64 keccakRho44ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))

theorem keccakRho44ArithCom_lowered_ok : ComOK (lowerArithToJasmin keccakRho44ArithCom) :=
  lowerArithToJasmin_ComOK keccakRho44ArithCom_ok

theorem keccakRho44ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin keccakRho44ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin keccakRho44ArithCom) 1)
      = Com.denote (lowerArithToJasmin keccakRho44ArithCom) V :=
  com_arm_e2e keccakRho44ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

theorem keccakRho44ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin keccakRho44ArithCom) 1))).regs)
        (comRetName (lowerArithToJasmin keccakRho44ArithCom) 1)
      = Com.denote (lowerArithToJasmin keccakRho44ArithCom) V :=
  com_riscv_e2e keccakRho44ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_one V s hs

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithHashesGoldenPath
