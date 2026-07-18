/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import Std.Tactic.BVDecide

/-!
# Golden path: the Ascon linear diffusion layer `Σ₀..Σ₄` as `Com jasminDialect`, emitted by the verified compiler

**This is the canonical pattern for emitting the Ascon permutation's linear diffusion
layer (NIST SP 800-232).** Each of the five linear functions `Σ₀`/`Σ₁`/`Σ₂`/`Σ₃`/`Σ₄`
is written ONCE as a `Com jasminDialect` source program over the all-`reg 64`
`regArith`/`shrImm`/`shlImm` alphabet, proven ONCE against its standard-`BitVec`-operator
spec, and the verified compiler emits the machine code — to AArch64 *and* RISC-V — with
**no per-kernel backend proof** (`comToReg_faithful` discharges it) and constant-time by
construction. The same recipe as `Sha512BitFuncsGoldenPath`; only the rotation constants
change.

Each Ascon linear function has the shape `Σᵢ x = x ^ ROTR^p x ^ ROTR^q x`, a three-term
XOR that **includes the identity term `x`** (no logical-not, no plain shift). The rotate
`ROTR^n x` is **branchless in the existing `reg 64` alphabet** as
`(x >>> n) ||| (x <<< (64 - n))` — `shrImm`/`shlImm`/`or`, every one in `SupportedOp`,
lowering through the same `comToReg_faithful` as the field ALU ops with no new dialect
machinery.

The recipe (one source → both backends), as in `Sha512BitFuncsGoldenPath`:
1. write the function as a `Com jasminDialect [.reg 64] (.reg 64)` over the
   `regArith`/`shrImm`/`shlImm` alphabet;
2. `ComOK` (mechanical — one constructor per op) + prove `Com.denote = <in-Com expr>`
   by cheap `rfl`, AND a recognizable-spec theorem `Com.denote = x ^^^ x.rotateRight p ^^^
   x.rotateRight q` (`simp only [BitVec.rotateRight_def]`) — the independent check tying
   the source to the textbook definition;
3. `com_arm_e2e` / `com_riscv_e2e` emit the verified backend block — both discharged by
   Step 1's `comToReg_faithful`.

The Ascon `Σ` rotation constants (NIST SP 800-232): `Σ₀ = (19,28)`, `Σ₁ = (61,39)`,
`Σ₂ = (1,6)`, `Σ₃ = (10,17)`, `Σ₄ = (7,41)`. -/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AsconLinear

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
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

/-! ## `Σ₀ x = x ^ ROTR^19 x ^ ROTR^28 x`

Args `[x]`. Each `ROTR^n x = (x >>> n) ||| (x <<< (64-n))`. Body:
`r19 := rot x 19 ; r28 := rot x 28 ; t := x ^ r19 ; r := t ^ r28`. -/

/-- `Σ₀ x = x ^ ROTR^19 x ^ ROTR^28 x` over `[x]`. -/
def asconSigma0Com : Com jasminDialect [.reg 64] (.reg 64) :=
  -- r19: hi = x >>> 19 ; lo = x <<< 45 ; r19 = hi | lo
  .var { op := .shrImm 64 19, retTy_eq := rfl, args := .cons .here .nil }
  (.var { op := .shlImm 64 45, retTy_eq := rfl, args := .cons (.there .here) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r28: hi = x >>> 28 ; lo = x <<< 36 ; r28 = hi | lo   (x now = .there^3.here)
  (.var { op := .shrImm 64 28, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) .nil }
  (.var { op := .shlImm 64 36, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- t = x ^ r19   (x now = .there^6.here, r19 = .there^3.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- r = t ^ r28   (t = .here, r28 = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here))))))))

/-- `asconSigma0Com` is in the supported straight-line fragment. -/
theorem asconSigma0Com_ok : ComOK asconSigma0Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))))))

/-- **Step 2 — in-Com value proof, cheap `rfl`** (the rotate as `shr | shl`). -/
theorem asconSigma0Com_denote (x : BitVec 64) :
    Com.denote asconSigma0Com (.cons x .nil)
      = (x ^^^ ((x >>> 19) ||| (x <<< 45))) ^^^ ((x >>> 28) ||| (x <<< 36)) := rfl

/-- **Step 2 — recognizable-spec proof.** Ties the `shr | shl` source to the textbook
    `ROTR` via `BitVec.rotateRight`. -/
theorem asconSigma0Com_spec (x : BitVec 64) :
    Com.denote asconSigma0Com (.cons x .nil)
      = x ^^^ x.rotateRight 19 ^^^ x.rotateRight 28 := by
  rw [asconSigma0Com_denote]; simp only [BitVec.rotateRight_def]

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem asconSigma0Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg asconSigma0Com 1))).regs)
        (comRetName asconSigma0Com 1)
      = Com.denote asconSigma0Com V :=
  com_arm_e2e asconSigma0Com_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem asconSigma0Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg asconSigma0Com 1))).regs)
        (comRetName asconSigma0Com 1)
      = Com.denote asconSigma0Com V :=
  com_riscv_e2e asconSigma0Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def asconSigma0Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 asconSigma0Com "ascon_sigma0"

/-! ## `Σ₁ x = x ^ ROTR^61 x ^ ROTR^39 x`

Args `[x]`. Same `shr | shl` rotate shape as `Σ₀`. -/

/-- `Σ₁ x = x ^ ROTR^61 x ^ ROTR^39 x` over `[x]`. -/
def asconSigma1Com : Com jasminDialect [.reg 64] (.reg 64) :=
  -- r61: x >>> 61 ; x <<< 3 ; |
  .var { op := .shrImm 64 61, retTy_eq := rfl, args := .cons .here .nil }
  (.var { op := .shlImm 64 3, retTy_eq := rfl, args := .cons (.there .here) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r39: x >>> 39 ; x <<< 25 ; |
  (.var { op := .shrImm 64 39, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) .nil }
  (.var { op := .shlImm 64 25, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- t = x ^ r61
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- r = t ^ r39
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here))))))))

/-- `asconSigma1Com` is in the supported straight-line fragment. -/
theorem asconSigma1Com_ok : ComOK asconSigma1Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))))))

/-- **Step 2 — in-Com value proof, cheap `rfl`.** -/
theorem asconSigma1Com_denote (x : BitVec 64) :
    Com.denote asconSigma1Com (.cons x .nil)
      = (x ^^^ ((x >>> 61) ||| (x <<< 3))) ^^^ ((x >>> 39) ||| (x <<< 25)) := rfl

/-- **Step 2 — recognizable-spec proof.** -/
theorem asconSigma1Com_spec (x : BitVec 64) :
    Com.denote asconSigma1Com (.cons x .nil)
      = x ^^^ x.rotateRight 61 ^^^ x.rotateRight 39 := by
  rw [asconSigma1Com_denote]; simp only [BitVec.rotateRight_def]

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem asconSigma1Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg asconSigma1Com 1))).regs)
        (comRetName asconSigma1Com 1)
      = Com.denote asconSigma1Com V :=
  com_arm_e2e asconSigma1Com_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem asconSigma1Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg asconSigma1Com 1))).regs)
        (comRetName asconSigma1Com 1)
      = Com.denote asconSigma1Com V :=
  com_riscv_e2e asconSigma1Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def asconSigma1Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 asconSigma1Com "ascon_sigma1"

/-! ## `Σ₂ x = x ^ ROTR^1 x ^ ROTR^6 x`

Args `[x]`. Same shape, small offsets. -/

/-- `Σ₂ x = x ^ ROTR^1 x ^ ROTR^6 x` over `[x]`. -/
def asconSigma2Com : Com jasminDialect [.reg 64] (.reg 64) :=
  -- r1: x >>> 1 ; x <<< 63 ; |
  .var { op := .shrImm 64 1, retTy_eq := rfl, args := .cons .here .nil }
  (.var { op := .shlImm 64 63, retTy_eq := rfl, args := .cons (.there .here) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r6: x >>> 6 ; x <<< 58 ; |
  (.var { op := .shrImm 64 6, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) .nil }
  (.var { op := .shlImm 64 58, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- t = x ^ r1
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- r = t ^ r6
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here))))))))

/-- `asconSigma2Com` is in the supported straight-line fragment. -/
theorem asconSigma2Com_ok : ComOK asconSigma2Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))))))

/-- **Step 2 — in-Com value proof, cheap `rfl`.** -/
theorem asconSigma2Com_denote (x : BitVec 64) :
    Com.denote asconSigma2Com (.cons x .nil)
      = (x ^^^ ((x >>> 1) ||| (x <<< 63))) ^^^ ((x >>> 6) ||| (x <<< 58)) := rfl

/-- **Step 2 — recognizable-spec proof.** -/
theorem asconSigma2Com_spec (x : BitVec 64) :
    Com.denote asconSigma2Com (.cons x .nil)
      = x ^^^ x.rotateRight 1 ^^^ x.rotateRight 6 := by
  rw [asconSigma2Com_denote]; simp only [BitVec.rotateRight_def]

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem asconSigma2Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg asconSigma2Com 1))).regs)
        (comRetName asconSigma2Com 1)
      = Com.denote asconSigma2Com V :=
  com_arm_e2e asconSigma2Com_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem asconSigma2Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg asconSigma2Com 1))).regs)
        (comRetName asconSigma2Com 1)
      = Com.denote asconSigma2Com V :=
  com_riscv_e2e asconSigma2Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def asconSigma2Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 asconSigma2Com "ascon_sigma2"

/-! ## `Σ₃ x = x ^ ROTR^10 x ^ ROTR^17 x`

Args `[x]`. Same shape, different offsets. -/

/-- `Σ₃ x = x ^ ROTR^10 x ^ ROTR^17 x` over `[x]`. -/
def asconSigma3Com : Com jasminDialect [.reg 64] (.reg 64) :=
  -- r10: x >>> 10 ; x <<< 54 ; |
  .var { op := .shrImm 64 10, retTy_eq := rfl, args := .cons .here .nil }
  (.var { op := .shlImm 64 54, retTy_eq := rfl, args := .cons (.there .here) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r17: x >>> 17 ; x <<< 47 ; |
  (.var { op := .shrImm 64 17, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) .nil }
  (.var { op := .shlImm 64 47, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- t = x ^ r10
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- r = t ^ r17
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here))))))))

/-- `asconSigma3Com` is in the supported straight-line fragment. -/
theorem asconSigma3Com_ok : ComOK asconSigma3Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))))))

/-- **Step 2 — in-Com value proof, cheap `rfl`.** -/
theorem asconSigma3Com_denote (x : BitVec 64) :
    Com.denote asconSigma3Com (.cons x .nil)
      = (x ^^^ ((x >>> 10) ||| (x <<< 54))) ^^^ ((x >>> 17) ||| (x <<< 47)) := rfl

/-- **Step 2 — recognizable-spec proof.** -/
theorem asconSigma3Com_spec (x : BitVec 64) :
    Com.denote asconSigma3Com (.cons x .nil)
      = x ^^^ x.rotateRight 10 ^^^ x.rotateRight 17 := by
  rw [asconSigma3Com_denote]; simp only [BitVec.rotateRight_def]

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem asconSigma3Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg asconSigma3Com 1))).regs)
        (comRetName asconSigma3Com 1)
      = Com.denote asconSigma3Com V :=
  com_arm_e2e asconSigma3Com_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem asconSigma3Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg asconSigma3Com 1))).regs)
        (comRetName asconSigma3Com 1)
      = Com.denote asconSigma3Com V :=
  com_riscv_e2e asconSigma3Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def asconSigma3Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 asconSigma3Com "ascon_sigma3"

/-! ## `Σ₄ x = x ^ ROTR^7 x ^ ROTR^41 x`

Args `[x]`. Same shape, different offsets. -/

/-- `Σ₄ x = x ^ ROTR^7 x ^ ROTR^41 x` over `[x]`. -/
def asconSigma4Com : Com jasminDialect [.reg 64] (.reg 64) :=
  -- r7: x >>> 7 ; x <<< 57 ; |
  .var { op := .shrImm 64 7, retTy_eq := rfl, args := .cons .here .nil }
  (.var { op := .shlImm 64 57, retTy_eq := rfl, args := .cons (.there .here) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r41: x >>> 41 ; x <<< 23 ; |
  (.var { op := .shrImm 64 41, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) .nil }
  (.var { op := .shlImm 64 23, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- t = x ^ r7
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- r = t ^ r41
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here))))))))

/-- `asconSigma4Com` is in the supported straight-line fragment. -/
theorem asconSigma4Com_ok : ComOK asconSigma4Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))))))

/-- **Step 2 — in-Com value proof, cheap `rfl`.** -/
theorem asconSigma4Com_denote (x : BitVec 64) :
    Com.denote asconSigma4Com (.cons x .nil)
      = (x ^^^ ((x >>> 7) ||| (x <<< 57))) ^^^ ((x >>> 41) ||| (x <<< 23)) := rfl

/-- **Step 2 — recognizable-spec proof.** -/
theorem asconSigma4Com_spec (x : BitVec 64) :
    Com.denote asconSigma4Com (.cons x .nil)
      = x ^^^ x.rotateRight 7 ^^^ x.rotateRight 41 := by
  rw [asconSigma4Com_denote]; simp only [BitVec.rotateRight_def]

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem asconSigma4Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg asconSigma4Com 1))).regs)
        (comRetName asconSigma4Com 1)
      = Com.denote asconSigma4Com V :=
  com_arm_e2e asconSigma4Com_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem asconSigma4Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg asconSigma4Com 1))).regs)
        (comRetName asconSigma4Com 1)
      = Com.denote asconSigma4Com V :=
  com_riscv_e2e asconSigma4Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def asconSigma4Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 asconSigma4Com "ascon_sigma4"

end CatCrypt.Crypto.SecureCompilation.AsconLinear
