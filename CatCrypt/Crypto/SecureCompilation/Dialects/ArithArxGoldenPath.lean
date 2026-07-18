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
set_option maxRecDepth 4000

/-!
# ARX cipher families at the neutral `arith` dialect — SipHash, SPECK128, Threefish MIX

Item 1 of the MLIR dialect-alignment restructure: three deployed ARX cipher
families, originally authored as `Com jasminDialect` kernels (below the waist),
re-expressed one level up as `Com arithDialect` (the upstream-aligned neutral
dialect), connected to emit through the *proven* arith→jasmin lowering.

For each kernel the pattern (mirroring `ArithGoldenPathField`) is:

* the kernel is `Com arithDialect` — the de Bruijn structure is **identical** to
  the jasmin twin, only the op names change (`.regArith .add 64 → .addi 64`,
  `.shrImm 64 k → .shrui_imm 64 k`, `.shlImm 64 k → .shli_imm 64 k`, etc.) and the
  context types are `.int 64` instead of `.reg 64`;
* `_denote = <explicit shift-or form>` — the arith denotation was *defined* equal
  to the jasmin image, so the value proof ports verbatim (a `rfl`, structurally
  unfolded for the deep SipHash words);
* `_spec` — the recognizable `rotateLeft`/`rotateRight` form, the shift-or rotate
  synthesis certified by `bv_decide`;
* `_ok : ArithOK64 …` (one `ArithOK64.var rfl` per op) ⇒ `lowerArithToJasmin_ComOK`
  ⇒ the lowered jasmin kernel is `ComOK`, so it rides the existing
  `com_arm_e2e` / `com_riscv_e2e` emit;
* `_arm_e2e` / `_riscv_e2e` — emitted AArch64 and RISC-V via the proven lowering,
  no per-kernel backend proof.

## The three families

* **SipHash `SipRound`** — the u64 ARX permutation behind the SipHash keyed PRF /
  MAC (hash-flooding defence, syncookies). Four output words `v0'..v3'` over inputs
  `[v0,v1,v2,v3]`; `v3'` is the deepest (~14 ops).
* **SPECK128** — the NSA lightweight block cipher round `x' = (ROTR(x,8)+y)^k`,
  `y' = ROTL(y,3)^x'` over `[x,y,k]`.
* **Threefish-512 MIX** — the Skein/Threefish ARX core `y0 = x0+x1`,
  `y1 = (x1 <<< R) ^ y0`, worked at rotation constants `R = 46` and `R = 33`.

Each lowers through the *same* `lowerArithToJasmin` + `comToReg_faithful`, so all
emit to both backends with no new machinery — only the neutral-`arith` kernel body.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithArxGoldenPath

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

/-- The 4-input SipHash state context `[v0,v1,v2,v3]` lowers to all-`reg 64`. -/
theorem allReg64_four :
    AllReg64 ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect) := by
  intro u hu
  rcases List.mem_cons.mp hu with h | h
  · exact h
  · rcases List.mem_cons.mp h with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact h
      · rcases List.mem_cons.mp h with h | h
        · exact h
        · exact absurd h List.not_mem_nil

/-! ## §1. SipHash `SipRound` — four output words over `[v0,v1,v2,v3]`

The arith context is `[.int 64, .int 64, .int 64, .int 64]`; the de Bruijn indices
are identical to `SipHashRound.sipV{0,1,2,3}Com`. -/

/-! ### `v0'` -/

/-- **`SipRound` output `v0'`** at the neutral `arith` level. -/
def sipV0ArithCom : Com arithDialect [.int 64, .int 64, .int 64, .int 64] (.int 64) :=
  .var (.mk (.addi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.shli_imm 64 32) rfl (.cons .here .nil))
  (.var (.mk (.shrui_imm 64 32) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.addi 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))
  (.var (.mk (.shli_imm 64 16) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))
  (.var (.mk (.shrui_imm 64 48) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.addi 64) rfl
          (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)))
    (.ret .here))))))))))

/-- Value proof at the neutral level (explicit shift-or rotate form). Deep kernel:
    a bare `rfl` overflows the whnf budget, so `unfold` reduces structurally. -/
theorem sipV0ArithCom_denote (v0 v1 v2 v3 : BitVec 64) :
    sipV0ArithCom.denote (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (((v0 + v1) <<< 32) ||| ((v0 + v1) >>> 32))
          + (((v3 <<< 16) ||| (v3 >>> 48)) ^^^ (v2 + v3)) := by
  unfold sipV0ArithCom; rfl

/-- **`v0'` spec**: `ROTL(v0+v1,32) + (ROTL(v3,16) ^^^ (v2+v3))`. -/
theorem sipV0ArithCom_spec (v0 v1 v2 v3 : BitVec 64) :
    sipV0ArithCom.denote (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = ((v0 + v1).rotateLeft 32) + ((v3.rotateLeft 16) ^^^ (v2 + v3)) := by
  rw [sipV0ArithCom_denote]; show (_ : BitVec 64) = _; bv_decide

/-- Emit-legality (one `ArithOK64.var rfl` per op). -/
theorem sipV0ArithCom_ok : ArithOK64 sipV0ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _))))))))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem sipV0ArithCom_lowered_ok : ComOK (lowerArithToJasmin sipV0ArithCom) :=
  lowerArithToJasmin_ComOK sipV0ArithCom_ok

/-- **`v0'` emits to AArch64**, from the neutral-`arith` source via the proven lowering. -/
theorem sipV0ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 4 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin sipV0ArithCom) 4))).regs)
        (comRetName (lowerArithToJasmin sipV0ArithCom) 4)
      = Com.denote (lowerArithToJasmin sipV0ArithCom) V :=
  com_arm_e2e sipV0ArithCom_lowered_ok allReg64_four V s hs

/-- **`v0'` emits to RISC-V** — same neutral source, same lowering. -/
theorem sipV0ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 4 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin sipV0ArithCom) 4))).regs)
        (comRetName (lowerArithToJasmin sipV0ArithCom) 4)
      = Com.denote (lowerArithToJasmin sipV0ArithCom) V :=
  com_riscv_e2e sipV0ArithCom_lowered_ok allReg64_four V s hs

/-! ### `v2'` -/

/-- **`SipRound` output `v2'`** at the neutral `arith` level. -/
def sipV2ArithCom : Com arithDialect [.int 64, .int 64, .int 64, .int 64] (.int 64) :=
  .var (.mk (.addi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.shli_imm 64 13) rfl (.cons (.there (.there .here)) .nil))
  (.var (.mk (.shrui_imm 64 51) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.addi 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))
  (.var (.mk (.addi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.shli_imm 64 32) rfl (.cons .here .nil))
  (.var (.mk (.shrui_imm 64 32) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here))))))))))

/-- Value proof at the neutral level (explicit shift-or rotate form). -/
theorem sipV2ArithCom_denote (v0 v1 v2 v3 : BitVec 64) :
    sipV2ArithCom.denote (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (let c1 := ((v1 <<< 13) ||| (v1 >>> 51)) ^^^ (v0 + v1)
         let e2 := (v2 + v3) + c1
         (e2 <<< 32) ||| (e2 >>> 32)) := by
  unfold sipV2ArithCom; rfl

/-- **`v2'` spec**: `ROTL((v2+v3) + (ROTL(v1,13) ^^^ (v0+v1)), 32)`. -/
theorem sipV2ArithCom_spec (v0 v1 v2 v3 : BitVec 64) :
    sipV2ArithCom.denote (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (((v2 + v3) + ((v1.rotateLeft 13) ^^^ (v0 + v1))).rotateLeft 32) := by
  rw [sipV2ArithCom_denote]; show (_ : BitVec 64) = _; bv_decide

/-- Emit-legality. -/
theorem sipV2ArithCom_ok : ArithOK64 sipV2ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _))))))))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem sipV2ArithCom_lowered_ok : ComOK (lowerArithToJasmin sipV2ArithCom) :=
  lowerArithToJasmin_ComOK sipV2ArithCom_ok

/-- **`v2'` emits to AArch64**. -/
theorem sipV2ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 4 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin sipV2ArithCom) 4))).regs)
        (comRetName (lowerArithToJasmin sipV2ArithCom) 4)
      = Com.denote (lowerArithToJasmin sipV2ArithCom) V :=
  com_arm_e2e sipV2ArithCom_lowered_ok allReg64_four V s hs

/-- **`v2'` emits to RISC-V**. -/
theorem sipV2ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 4 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin sipV2ArithCom) 4))).regs)
        (comRetName (lowerArithToJasmin sipV2ArithCom) 4)
      = Com.denote (lowerArithToJasmin sipV2ArithCom) V :=
  com_riscv_e2e sipV2ArithCom_lowered_ok allReg64_four V s hs

/-! ### `v1'` -/

/-- **`SipRound` output `v1'`** at the neutral `arith` level. -/
def sipV1ArithCom : Com arithDialect [.int 64, .int 64, .int 64, .int 64] (.int 64) :=
  .var (.mk (.addi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.shli_imm 64 13) rfl (.cons (.there (.there .here)) .nil))
  (.var (.mk (.shrui_imm 64 51) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.addi 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))
  (.var (.mk (.addi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.shli_imm 64 17) rfl (.cons (.there (.there .here)) .nil))
  (.var (.mk (.shrui_imm 64 47) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there (.there (.there .here))) .nil)))
    (.ret .here)))))))))))

/-- Value proof at the neutral level (explicit shift-or rotate form). -/
theorem sipV1ArithCom_denote (v0 v1 v2 v3 : BitVec 64) :
    sipV1ArithCom.denote (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (let c1 := ((v1 <<< 13) ||| (v1 >>> 51)) ^^^ (v0 + v1)
         let e2 := (v2 + v3) + c1
         ((c1 <<< 17) ||| (c1 >>> 47)) ^^^ e2) := by
  unfold sipV1ArithCom; rfl

/-- **`v1'` spec**: `ROTL(c1,17) ^^^ ((v2+v3)+c1)` with `c1 = ROTL(v1,13) ^^^ (v0+v1)`. -/
theorem sipV1ArithCom_spec (v0 v1 v2 v3 : BitVec 64) :
    sipV1ArithCom.denote (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (let c1 := (v1.rotateLeft 13) ^^^ (v0 + v1)
         (c1.rotateLeft 17) ^^^ ((v2 + v3) + c1)) := by
  rw [sipV1ArithCom_denote]; show (_ : BitVec 64) = _; bv_decide

/-- Emit-legality. -/
theorem sipV1ArithCom_ok : ArithOK64 sipV1ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _)))))))))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem sipV1ArithCom_lowered_ok : ComOK (lowerArithToJasmin sipV1ArithCom) :=
  lowerArithToJasmin_ComOK sipV1ArithCom_ok

/-- **`v1'` emits to AArch64**. -/
theorem sipV1ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 4 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin sipV1ArithCom) 4))).regs)
        (comRetName (lowerArithToJasmin sipV1ArithCom) 4)
      = Com.denote (lowerArithToJasmin sipV1ArithCom) V :=
  com_arm_e2e sipV1ArithCom_lowered_ok allReg64_four V s hs

/-- **`v1'` emits to RISC-V**. -/
theorem sipV1ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 4 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin sipV1ArithCom) 4))).regs)
        (comRetName (lowerArithToJasmin sipV1ArithCom) 4)
      = Com.denote (lowerArithToJasmin sipV1ArithCom) V :=
  com_riscv_e2e sipV1ArithCom_lowered_ok allReg64_four V s hs

/-! ### `v3'` — the deepest word (~14 ops) -/

/-- **`SipRound` output `v3'`** at the neutral `arith` level. -/
def sipV3ArithCom : Com arithDialect [.int 64, .int 64, .int 64, .int 64] (.int 64) :=
  .var (.mk (.addi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.shli_imm 64 32) rfl (.cons .here .nil))
  (.var (.mk (.shrui_imm 64 32) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.addi 64) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))
  (.var (.mk (.shli_imm 64 16) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))
  (.var (.mk (.shrui_imm 64 48) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.addi 64) rfl
          (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)))
  (.var (.mk (.shli_imm 64 21) rfl (.cons (.there .here) .nil))
  (.var (.mk (.shrui_imm 64 43) rfl (.cons (.there (.there .here)) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.xori 64) rfl (.cons .here (.cons (.there (.there (.there .here))) .nil)))
    (.ret .here))))))))))))))

/-- Value proof at the neutral level (explicit shift-or rotate form). -/
theorem sipV3ArithCom_denote (v0 v1 v2 v3 : BitVec 64) :
    sipV3ArithCom.denote (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (let c3 := ((v3 <<< 16) ||| (v3 >>> 48)) ^^^ (v2 + v3)
         let e0 := (((v0 + v1) <<< 32) ||| ((v0 + v1) >>> 32)) + c3
         ((c3 <<< 21) ||| (c3 >>> 43)) ^^^ e0) := by
  unfold sipV3ArithCom; rfl

/-- **`v3'` spec**: `ROTL(c3,21) ^^^ e0` with `c3 = ROTL(v3,16) ^^^ (v2+v3)` and
    `e0 = ROTL(v0+v1,32) + c3`. -/
theorem sipV3ArithCom_spec (v0 v1 v2 v3 : BitVec 64) :
    sipV3ArithCom.denote (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (let c3 := (v3.rotateLeft 16) ^^^ (v2 + v3)
         (c3.rotateLeft 21) ^^^ (((v0 + v1).rotateLeft 32) + c3)) := by
  rw [sipV3ArithCom_denote]; show (_ : BitVec 64) = _; bv_decide

/-- Emit-legality. -/
theorem sipV3ArithCom_ok : ArithOK64 sipV3ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.ret _))))))))))))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem sipV3ArithCom_lowered_ok : ComOK (lowerArithToJasmin sipV3ArithCom) :=
  lowerArithToJasmin_ComOK sipV3ArithCom_ok

/-- **`v3'` emits to AArch64**. -/
theorem sipV3ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 4 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin sipV3ArithCom) 4))).regs)
        (comRetName (lowerArithToJasmin sipV3ArithCom) 4)
      = Com.denote (lowerArithToJasmin sipV3ArithCom) V :=
  com_arm_e2e sipV3ArithCom_lowered_ok allReg64_four V s hs

/-- **`v3'` emits to RISC-V**. -/
theorem sipV3ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 4 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin sipV3ArithCom) 4))).regs)
        (comRetName (lowerArithToJasmin sipV3ArithCom) 4)
      = Com.denote (lowerArithToJasmin sipV3ArithCom) V :=
  com_riscv_e2e sipV3ArithCom_lowered_ok allReg64_four V s hs

/-! ## §2. SPECK128 round — `x'` and `y'` over `[x,y,k]`

`x' = (ROTR(x,8) + y) ^^^ k`, `y' = ROTL(y,3) ^^^ x'`. -/

/-! ### `x'` -/

/-- **SPECK128 round — the `x'` output** at the neutral `arith` level. -/
def speckXArithCom : Com arithDialect [.int 64, .int 64, .int 64] (.int 64) :=
  .var (.mk (.shrui_imm 64 8) rfl (.cons .here .nil))
  (.var (.mk (.shli_imm 64 56) rfl (.cons (.there .here) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.addi 64) rfl
          (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))
    (.ret .here)))))

/-- Value proof at the neutral level (explicit shift-or rotate form). -/
theorem speckXArithCom_denote (x y k : BitVec 64) :
    speckXArithCom.denote (.cons x (.cons y (.cons k .nil)))
      = (((x >>> 8) ||| (x <<< 56)) + y) ^^^ k := rfl

/-- **SPECK128 `x'` spec**: `((x.rotateRight 8) + y) ^^^ k`. -/
theorem speckXArithCom_spec (x y k : BitVec 64) :
    speckXArithCom.denote (.cons x (.cons y (.cons k .nil)))
      = ((x.rotateRight 8) + y) ^^^ k := by
  rw [speckXArithCom_denote]; show (_ : BitVec 64) = _; bv_decide

/-- Emit-legality. -/
theorem speckXArithCom_ok : ArithOK64 speckXArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.ret _)))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem speckXArithCom_lowered_ok : ComOK (lowerArithToJasmin speckXArithCom) :=
  lowerArithToJasmin_ComOK speckXArithCom_ok

/-- **SPECK128 `x'` emits to AArch64**. -/
theorem speckXArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin speckXArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin speckXArithCom) 3)
      = Com.denote (lowerArithToJasmin speckXArithCom) V :=
  com_arm_e2e speckXArithCom_lowered_ok FieldEmitGoldenPath.allReg64_three V s hs

/-- **SPECK128 `x'` emits to RISC-V**. -/
theorem speckXArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin speckXArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin speckXArithCom) 3)
      = Com.denote (lowerArithToJasmin speckXArithCom) V :=
  com_riscv_e2e speckXArithCom_lowered_ok FieldEmitGoldenPath.allReg64_three V s hs

/-! ### `y'` -/

/-- **SPECK128 round — the `y'` output** at the neutral `arith` level. -/
def speckYArithCom : Com arithDialect [.int 64, .int 64, .int 64] (.int 64) :=
  .var (.mk (.shli_imm 64 3) rfl (.cons (.there .here) .nil))
  (.var (.mk (.shrui_imm 64 61) rfl (.cons (.there (.there .here)) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.shrui_imm 64 8) rfl (.cons (.there (.there (.there .here))) .nil))
  (.var (.mk (.shli_imm 64 56) rfl (.cons (.there (.there (.there (.there .here)))) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.addi 64) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
              .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there
              (.there (.there .here))))))))) .nil)))
  (.var (.mk (.xori 64) rfl
          (.cons (.there (.there (.there (.there (.there .here)))))
            (.cons .here .nil)))
    (.ret .here)))))))))

/-- Value proof at the neutral level. The nine-binding `y'` body overflows the
    default heartbeat budget for a brute whole-body `rfl` applied to the folded
    definition, so `unfold` first reduces the binder skeleton structurally, after
    which the residual `rfl` checks cheaply (the same lesson as the deep SipHash
    words). -/
theorem speckYArithCom_denote (x y k : BitVec 64) :
    speckYArithCom.denote (.cons x (.cons y (.cons k .nil)))
      = ((y <<< 3) ||| (y >>> 61))
          ^^^ ((((x >>> 8) ||| (x <<< 56)) + y) ^^^ k) := by
  unfold speckYArithCom; rfl

/-- **SPECK128 `y'` spec**: `(y.rotateLeft 3) ^^^ (((x.rotateRight 8) + y) ^^^ k)`. -/
theorem speckYArithCom_spec (x y k : BitVec 64) :
    speckYArithCom.denote (.cons x (.cons y (.cons k .nil)))
      = (y.rotateLeft 3) ^^^ (((x.rotateRight 8) + y) ^^^ k) := by
  rw [speckYArithCom_denote]; show (_ : BitVec 64) = _; bv_decide

/-- Emit-legality. -/
theorem speckYArithCom_ok : ArithOK64 speckYArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.ret _)))))))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem speckYArithCom_lowered_ok : ComOK (lowerArithToJasmin speckYArithCom) :=
  lowerArithToJasmin_ComOK speckYArithCom_ok

/-- **SPECK128 `y'` emits to AArch64**. -/
theorem speckYArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin speckYArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin speckYArithCom) 3)
      = Com.denote (lowerArithToJasmin speckYArithCom) V :=
  com_arm_e2e speckYArithCom_lowered_ok FieldEmitGoldenPath.allReg64_three V s hs

/-- **SPECK128 `y'` emits to RISC-V**. -/
theorem speckYArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin speckYArithCom) 3))).regs)
        (comRetName (lowerArithToJasmin speckYArithCom) 3)
      = Com.denote (lowerArithToJasmin speckYArithCom) V :=
  com_riscv_e2e speckYArithCom_lowered_ok FieldEmitGoldenPath.allReg64_three V s hs

/-! ## §3. Threefish-512 MIX — `y0`/`y1` at rotations R = 46 and R = 33

`y0 = x0 + x1`, `y1 = (x1 <<< R) ^^^ y0`, over `[x0,x1]`. -/

/-! ### MIX(46) `y0` -/

/-- **MIX(46) — the `y0` output** at the neutral `arith` level. -/
def mix46_y0ArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.addi 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)

/-- Value proof at the neutral level. -/
theorem mix46_y0ArithCom_denote (x0 x1 : BitVec 64) :
    mix46_y0ArithCom.denote (.cons x0 (.cons x1 .nil)) = x1 + x0 := rfl

/-- Emit-legality. -/
theorem mix46_y0ArithCom_ok : ArithOK64 mix46_y0ArithCom :=
  ArithOK64.var rfl (ArithOK64.ret _)

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem mix46_y0ArithCom_lowered_ok : ComOK (lowerArithToJasmin mix46_y0ArithCom) :=
  lowerArithToJasmin_ComOK mix46_y0ArithCom_ok

/-- **MIX(46) `y0` emits to AArch64**. -/
theorem mix46_y0ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin mix46_y0ArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin mix46_y0ArithCom) 2)
      = Com.denote (lowerArithToJasmin mix46_y0ArithCom) V :=
  com_arm_e2e mix46_y0ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **MIX(46) `y0` emits to RISC-V**. -/
theorem mix46_y0ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin mix46_y0ArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin mix46_y0ArithCom) 2)
      = Com.denote (lowerArithToJasmin mix46_y0ArithCom) V :=
  com_riscv_e2e mix46_y0ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-! ### MIX(46) `y1` -/

/-- **MIX(46) — the `y1` output** at the neutral `arith` level. -/
def mix46_y1ArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.shli_imm 64 46) rfl (.cons (.there .here) .nil))
  (.var (.mk (.shrui_imm 64 18) rfl (.cons (.there (.there .here)) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.addi 64) rfl
          (.cons (.there (.there (.there (.there .here))))
            (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)))))

/-- Value proof at the neutral level (explicit shift-or rotate form). -/
theorem mix46_y1ArithCom_denote (x0 x1 : BitVec 64) :
    mix46_y1ArithCom.denote (.cons x0 (.cons x1 .nil))
      = ((x1 <<< 46) ||| (x1 >>> 18)) ^^^ (x1 + x0) := rfl

/-- **MIX(46) `y1` spec**: `(x1.rotateLeft 46) ^^^ (x1 + x0)`. -/
theorem mix46_y1ArithCom_spec (x0 x1 : BitVec 64) :
    mix46_y1ArithCom.denote (.cons x0 (.cons x1 .nil))
      = (x1.rotateLeft 46) ^^^ (x1 + x0) := by
  rw [mix46_y1ArithCom_denote]; show (_ : BitVec 64) = _; bv_decide

/-- Emit-legality. -/
theorem mix46_y1ArithCom_ok : ArithOK64 mix46_y1ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.ret _)))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem mix46_y1ArithCom_lowered_ok : ComOK (lowerArithToJasmin mix46_y1ArithCom) :=
  lowerArithToJasmin_ComOK mix46_y1ArithCom_ok

/-- **MIX(46) `y1` emits to AArch64**. -/
theorem mix46_y1ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin mix46_y1ArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin mix46_y1ArithCom) 2)
      = Com.denote (lowerArithToJasmin mix46_y1ArithCom) V :=
  com_arm_e2e mix46_y1ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **MIX(46) `y1` emits to RISC-V**. -/
theorem mix46_y1ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin mix46_y1ArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin mix46_y1ArithCom) 2)
      = Com.denote (lowerArithToJasmin mix46_y1ArithCom) V :=
  com_riscv_e2e mix46_y1ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-! ### MIX(33) `y0` -/

/-- **MIX(33) — the `y0` output** at the neutral `arith` level. -/
def mix33_y0ArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.addi 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)

/-- Value proof at the neutral level. -/
theorem mix33_y0ArithCom_denote (x0 x1 : BitVec 64) :
    mix33_y0ArithCom.denote (.cons x0 (.cons x1 .nil)) = x1 + x0 := rfl

/-- Emit-legality. -/
theorem mix33_y0ArithCom_ok : ArithOK64 mix33_y0ArithCom :=
  ArithOK64.var rfl (ArithOK64.ret _)

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem mix33_y0ArithCom_lowered_ok : ComOK (lowerArithToJasmin mix33_y0ArithCom) :=
  lowerArithToJasmin_ComOK mix33_y0ArithCom_ok

/-- **MIX(33) `y0` emits to AArch64**. -/
theorem mix33_y0ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin mix33_y0ArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin mix33_y0ArithCom) 2)
      = Com.denote (lowerArithToJasmin mix33_y0ArithCom) V :=
  com_arm_e2e mix33_y0ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **MIX(33) `y0` emits to RISC-V**. -/
theorem mix33_y0ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin mix33_y0ArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin mix33_y0ArithCom) 2)
      = Com.denote (lowerArithToJasmin mix33_y0ArithCom) V :=
  com_riscv_e2e mix33_y0ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-! ### MIX(33) `y1` -/

/-- **MIX(33) — the `y1` output** at the neutral `arith` level. -/
def mix33_y1ArithCom : Com arithDialect [.int 64, .int 64] (.int 64) :=
  .var (.mk (.shli_imm 64 33) rfl (.cons (.there .here) .nil))
  (.var (.mk (.shrui_imm 64 31) rfl (.cons (.there (.there .here)) .nil))
  (.var (.mk (.ori 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.addi 64) rfl
          (.cons (.there (.there (.there (.there .here))))
            (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.xori 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)))))

/-- Value proof at the neutral level (explicit shift-or rotate form). -/
theorem mix33_y1ArithCom_denote (x0 x1 : BitVec 64) :
    mix33_y1ArithCom.denote (.cons x0 (.cons x1 .nil))
      = ((x1 <<< 33) ||| (x1 >>> 31)) ^^^ (x1 + x0) := rfl

/-- **MIX(33) `y1` spec**: `(x1.rotateLeft 33) ^^^ (x1 + x0)`. -/
theorem mix33_y1ArithCom_spec (x0 x1 : BitVec 64) :
    mix33_y1ArithCom.denote (.cons x0 (.cons x1 .nil))
      = (x1.rotateLeft 33) ^^^ (x1 + x0) := by
  rw [mix33_y1ArithCom_denote]; show (_ : BitVec 64) = _; bv_decide

/-- Emit-legality. -/
theorem mix33_y1ArithCom_ok : ArithOK64 mix33_y1ArithCom :=
  ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl (ArithOK64.var rfl
  (ArithOK64.var rfl (ArithOK64.ret _)))))

/-- The lowered jasmin kernel is in the supported fragment. -/
theorem mix33_y1ArithCom_lowered_ok : ComOK (lowerArithToJasmin mix33_y1ArithCom) :=
  lowerArithToJasmin_ComOK mix33_y1ArithCom_ok

/-- **MIX(33) `y1` emits to AArch64**. -/
theorem mix33_y1ArithCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((armTarget.runOps s
        (armTarget.compile (comToRegProg (lowerArithToJasmin mix33_y1ArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin mix33_y1ArithCom) 2)
      = Com.denote (lowerArithToJasmin mix33_y1ArithCom) V :=
  com_arm_e2e mix33_y1ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **MIX(33) `y1` emits to RISC-V**. -/
theorem mix33_y1ArithCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((rvTarget.runOps s
        (rvTarget.compile (comToRegProg (lowerArithToJasmin mix33_y1ArithCom) 2))).regs)
        (comRetName (lowerArithToJasmin mix33_y1ArithCom) 2)
      = Com.denote (lowerArithToJasmin mix33_y1ArithCom) V :=
  com_riscv_e2e mix33_y1ArithCom_lowered_ok FieldEmitGoldenPath.allReg64_two V s hs

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithArxGoldenPath
