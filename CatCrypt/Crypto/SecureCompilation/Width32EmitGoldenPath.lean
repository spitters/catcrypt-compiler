/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import Std.Tactic.BVDecide

/-!
# Golden path: u32 arithmetic emitted through the width-64 path by masked-u64 emulation

**This file makes 32-bit (`u32`) crypto arithmetic — ChaCha20, SHA-256, BLAKE2s, every
ARX cipher over 32-bit words — EMIT through the *unchanged* width-64 golden path, with
no new backend op, no dialect change, no `RegStmt` primitive, and no faithfulness
generalisation.** The idea is masked-u64 emulation: a `u32` value lives zero-extended in
a 64-bit register, and every operation masks its result back to 32 bits with
`&&& 0xFFFFFFFF` (the binding `regConst 64 4294967295`). The mask emulates 32-bit
wraparound; the zero-extended invariant is re-established after every op.

Because the mask, the add, the xor, the shifts and the or are *all* width-64
`SupportedOp`s — `.regArith .add/.xor/.and/.or 64`, `.shrImm`/`.shlImm 64 k`,
`.regConst 64 4294967295` — every `Com` here lowers through the *same*
`comToReg_faithful` that `FieldEmitGoldenPath` uses. The compiler emits each kernel to
AArch64 *and* RISC-V (via `com_arm_e2e` / `com_riscv_e2e`, reused verbatim) and to x86
ELF bytes, constant-time by construction, with **no per-kernel backend proof**.

The recipe is the `FieldEmitGoldenPath` / `Sha512BitFuncs` quartet, only the body
changes:
1. write the masked-u64 op as a `Com jasminDialect Γ (.reg 64)` over the width-64
   `regArith`/`shrImm`/`shlImm`/`regConst` alphabet;
2. `ComOK` (mechanical) + an in-`Com` `denote` `rfl` AND a **recognizable u32 `_spec`**
   proven by `bv_decide` — the spec ties the masked-u64 expression to the *genuine*
   32-bit operation expressed with `BitVec 32` (`setWidth 32`, `rotateLeft`), so the
   tie is non-vacuous: it says the emitted code computes the real `u32` value, not a
   restatement of the mask;
3. `com_arm_e2e` / `com_riscv_e2e` / `compileComToElf` emit the three backends.

The four primitives below — masked add (`add32`), masked xor (`xor32`), the two ChaCha
rotate amounts (`rotl32` `k = 16` and `k = 12`), and one ChaCha quarter-round component
(`chachaQuarterStep`) — are the ARX core: a real `u32` cipher step emitting via
masked-u64 through the width-64 path.

**Scope note.** This is the *portability* lever: it unblocks `u32` crypto on the
existing width-64 pipeline with zero new machinery. A *native* 32-bit register file
(half the mask traffic, narrower spills) remains a perf optimization, characterized
separately in `MultiWidthGoldenPath`; it is not needed for `u32` code to emit. -/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Width32Emit

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

/-- The 32-bit mask `0xFFFFFFFF`, as a width-64 `regConst` (decimal literal). -/
abbrev mask32 : BitVec 64 := BitVec.ofNat 64 4294967295

/-! ## Masked add: `add32 a b = (a + b) &&& 0xFFFFFFFF`

Args `[a, b]` (each a `u32` value zero-extended in a reg64). Body:
`s := a + b ; m := 0xFFFFFFFF ; r := s &&& m`. The mask emulates 32-bit
wraparound; the result is again zero-extended. -/

/-- `add32 a b = (a + b) &&& 0xFFFFFFFF` over `[a, b]`. -/
def add32Com : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  -- s = a + b      (a = .there.here, b = .here  ⇒  denote = b? see _denote)
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
  -- m = 0xFFFFFFFF
  (.var { op := .regConst 64 4294967295, retTy_eq := rfl, args := .nil }
  -- r = s &&& m    (s = .there.here, m = .here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))

/-- `add32Com` is in the supported straight-line fragment (add, regConst, and). -/
theorem add32Com_ok : ComOK add32Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))

/-- **Step 2 — in-`Com` value proof, cheap `rfl`** (the masked sum). -/
theorem add32Com_denote (a b : BitVec 64) :
    Com.denote add32Com (.cons a (.cons b .nil)) = (b + a) &&& mask32 := rfl

/-- **Step 2 — recognizable u32 `_spec`, `bv_decide`.** The masked-u64 add equals the
    genuine 32-bit add: truncate both inputs to `BitVec 32`, add, and zero-extend back
    to 64 bits. This is the real `u32` `wrapping_add`, not a restatement of the mask. -/
theorem add32Com_spec (a b : BitVec 64) :
    Com.denote add32Com (.cons a (.cons b .nil))
      = (a.setWidth 32 + b.setWidth 32).setWidth 64 := by
  rw [add32Com_denote]
  show ((b + a) &&& BitVec.ofNat 64 4294967295) = _
  bv_decide

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem add32Com_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg add32Com 2))).regs)
        (comRetName add32Com 2)
      = Com.denote add32Com V :=
  com_arm_e2e add32Com_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem add32Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg add32Com 2))).regs)
        (comRetName add32Com 2)
      = Com.denote add32Com V :=
  com_riscv_e2e add32Com_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier): the same source to ELF `.o` bytes. -/
def add32Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 add32Com "u32_add"

/-! ## Masked xor: `xor32 a b = (a ^ b) &&& 0xFFFFFFFF`

Args `[a, b]`. The xor of two zero-extended `u32` values needs no mask to stay
zero-extended; the mask is included for uniformity (and is harmless). The `_spec`
ties the source to the genuine 32-bit xor. -/

/-- `xor32 a b = (a ^ b) &&& 0xFFFFFFFF` over `[a, b]`. -/
def xor32Com : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  -- t = a ^ b
  .var { op := .regArith .xor 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
  -- m = 0xFFFFFFFF
  (.var { op := .regConst 64 4294967295, retTy_eq := rfl, args := .nil }
  -- r = t &&& m
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))

/-- `xor32Com` is in the supported straight-line fragment (xor, regConst, and). -/
theorem xor32Com_ok : ComOK xor32Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))

/-- **Step 2 — in-`Com` value proof, cheap `rfl`.** -/
theorem xor32Com_denote (a b : BitVec 64) :
    Com.denote xor32Com (.cons a (.cons b .nil)) = (b ^^^ a) &&& mask32 := rfl

/-- **Step 2 — recognizable u32 `_spec`, `bv_decide`.** The masked-u64 xor equals the
    genuine 32-bit xor (truncate, xor, zero-extend). -/
theorem xor32Com_spec (a b : BitVec 64) :
    Com.denote xor32Com (.cons a (.cons b .nil))
      = (a.setWidth 32 ^^^ b.setWidth 32).setWidth 64 := by
  rw [xor32Com_denote]
  show ((b ^^^ a) &&& BitVec.ofNat 64 4294967295) = _
  bv_decide

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem xor32Com_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg xor32Com 2))).regs)
        (comRetName xor32Com 2)
      = Com.denote xor32Com V :=
  com_arm_e2e xor32Com_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem xor32Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg xor32Com 2))).regs)
        (comRetName xor32Com 2)
      = Com.denote xor32Com V :=
  com_riscv_e2e xor32Com_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def xor32Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 xor32Com "u32_xor"

/-! ## 32-bit rotate-left: `rotl32 a k = ((am <<< k) ||| (am >>> (32 - k))) &&& 0xFFFFFFFF`

Args `[a]`. A `u32` rotate-left by `k` is, on the value `am := a &&& 0xFFFFFFFF`
(re-establishing the 32-bit-reduced invariant on entry), the high part `am <<< k`
or-ed with the low part `am >>> (32 - k)`, masked back to 32 bits. Body:
`m := 0xFFFFFFFF ; am := a &&& m ; hi := am <<< k ; lo := am >>> (32 - k) ;
 u := hi ||| lo ; r := u &&& m`. Masking the input first is what makes the emulation
hold for *every* register value, not just already-reduced ones — the `_spec` is then a
total equality with the genuine 32-bit rotate. We instantiate the two ChaCha20
quarter-round amounts, `k = 16` and `k = 12`. -/

/-- `rotl32 a 16` over `[a]` (input masked to 32 bits, then shift-or-rotate). -/
def rotl32Com_16 : Com jasminDialect [.reg 64] (.reg 64) :=
  -- m = 0xFFFFFFFF
  .var { op := .regConst 64 4294967295, retTy_eq := rfl, args := .nil }
  -- am = a &&& m           (a = .there.here, m = .here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- hi = am <<< 16         (am = .here)
  (.var { op := .shlImm 64 16, retTy_eq := rfl, args := .cons .here .nil }
  -- lo = am >>> 16         (am = .there.here)
  (.var { op := .shrImm 64 16, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- u = hi ||| lo          (hi = .there.here, lo = .here)
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r = u &&& m            (u = .here, m = .there.there.there.there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there (.there .here)))) .nil) }
    (.ret .here))))))

/-- `rotl32Com_16` is in the supported straight-line fragment (regConst, and, shlImm,
    shrImm, or, and). -/
theorem rotl32Com_16_ok : ComOK rotl32Com_16 :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))))

/-- **Step 2 — in-`Com` value proof, cheap `rfl`.** -/
theorem rotl32Com_16_denote (a : BitVec 64) :
    Com.denote rotl32Com_16 (.cons a .nil)
      = (((a &&& mask32) <<< 16) ||| ((a &&& mask32) >>> 16)) &&& mask32 := rfl

/-- **Step 2 — recognizable u32 `_spec`, `bv_decide`.** The masked shift-or equals the
    genuine 32-bit rotate-left by 16 (truncate to `BitVec 32`, `rotateLeft 16`,
    zero-extend) — totally, for every input. -/
theorem rotl32Com_16_spec (a : BitVec 64) :
    Com.denote rotl32Com_16 (.cons a .nil)
      = ((a.setWidth 32).rotateLeft 16).setWidth 64 := by
  rw [rotl32Com_16_denote]
  show ((((a &&& BitVec.ofNat 64 4294967295) <<< 16)
        ||| ((a &&& BitVec.ofNat 64 4294967295) >>> 16))
        &&& BitVec.ofNat 64 4294967295) = _
  bv_decide

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem rotl32Com_16_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg rotl32Com_16 1))).regs)
        (comRetName rotl32Com_16 1)
      = Com.denote rotl32Com_16 V :=
  com_arm_e2e rotl32Com_16_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem rotl32Com_16_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg rotl32Com_16 1))).regs)
        (comRetName rotl32Com_16 1)
      = Com.denote rotl32Com_16 V :=
  com_riscv_e2e rotl32Com_16_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def rotl32Com_16_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 rotl32Com_16 "u32_rotl16"

/-- `rotl32 a 12` over `[a]` (input masked to 32 bits, then shift-or-rotate). -/
def rotl32Com_12 : Com jasminDialect [.reg 64] (.reg 64) :=
  -- m = 0xFFFFFFFF
  .var { op := .regConst 64 4294967295, retTy_eq := rfl, args := .nil }
  -- am = a &&& m           (a = .there.here, m = .here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- hi = am <<< 12         (am = .here)
  (.var { op := .shlImm 64 12, retTy_eq := rfl, args := .cons .here .nil }
  -- lo = am >>> 20         (am = .there.here)
  (.var { op := .shrImm 64 20, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- u = hi ||| lo          (hi = .there.here, lo = .here)
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r = u &&& m            (u = .here, m = .there.there.there.there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there (.there .here)))) .nil) }
    (.ret .here))))))

/-- `rotl32Com_12` is in the supported straight-line fragment. -/
theorem rotl32Com_12_ok : ComOK rotl32Com_12 :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))))

/-- **Step 2 — in-`Com` value proof, cheap `rfl`.** -/
theorem rotl32Com_12_denote (a : BitVec 64) :
    Com.denote rotl32Com_12 (.cons a .nil)
      = (((a &&& mask32) <<< 12) ||| ((a &&& mask32) >>> 20)) &&& mask32 := rfl

/-- **Step 2 — recognizable u32 `_spec`, `bv_decide`.** The masked shift-or equals the
    genuine 32-bit rotate-left by 12 — totally, for every input. -/
theorem rotl32Com_12_spec (a : BitVec 64) :
    Com.denote rotl32Com_12 (.cons a .nil)
      = ((a.setWidth 32).rotateLeft 12).setWidth 64 := by
  rw [rotl32Com_12_denote]
  show ((((a &&& BitVec.ofNat 64 4294967295) <<< 12)
        ||| ((a &&& BitVec.ofNat 64 4294967295) >>> 20))
        &&& BitVec.ofNat 64 4294967295) = _
  bv_decide

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem rotl32Com_12_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg rotl32Com_12 1))).regs)
        (comRetName rotl32Com_12 1)
      = Com.denote rotl32Com_12 V :=
  com_arm_e2e rotl32Com_12_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem rotl32Com_12_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg rotl32Com_12 1))).regs)
        (comRetName rotl32Com_12 1)
      = Com.denote rotl32Com_12 V :=
  com_riscv_e2e rotl32Com_12_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def rotl32Com_12_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 rotl32Com_12 "u32_rotl12"

/-! ## A real ChaCha20 quarter-round component

The ChaCha20 quarter-round on `(a, b, c, d)` is four lines:
`a += b ; d ^= a ; d <<<= 16 ; c += d ; …`. The third line `d := (d ^ a) <<< 16`
fuses a masked xor with a 32-bit rotate-left by 16 — exactly the `d ^= a; d <<<= 16`
prefix — and is a recognizable component of the cipher. We emit it over `[d, a]` as a
masked-u64 `Com`:
`x := d ^ a ; m := 0xFFFFFFFF ; xm := x &&& m ; hi := xm <<< 16 ; lo := xm >>> 16 ;
 u := hi ||| lo ; r := u &&& m`.
The inner mask after the xor keeps `xm` zero-extended so the rotate is the genuine
32-bit rotate. The `_spec` ties the whole step to `rotl32 (d ^ a) 16` on `BitVec 32`. -/

/-- One ChaCha20 quarter-round component `(d ^ a) <<<₃₂ 16` over `[d, a]`. -/
def chachaQuarterStepCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  -- x = d ^ a            (d = .here, a = .there.here)
  .var { op := .regArith .xor 64, retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) .nil) }
  -- m = 0xFFFFFFFF
  (.var { op := .regConst 64 4294967295, retTy_eq := rfl, args := .nil }
  -- xm = x &&& m         (x = .there.here, m = .here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- hi = xm <<< 16       (xm = .here)
  (.var { op := .shlImm 64 16, retTy_eq := rfl, args := .cons .here .nil }
  -- lo = xm >>> 16       (xm = .there.here)
  (.var { op := .shrImm 64 16, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- u = hi ||| lo        (hi = .there.here, lo = .here)
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r = u &&& m          (u = .here, m = .there.there.there.there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here
            (.cons (.there (.there (.there (.there .here)))) .nil) }
    (.ret .here)))))))

/-- `chachaQuarterStepCom` is in the supported straight-line fragment (xor, regConst,
    and, shlImm, shrImm, or, and). -/
theorem chachaQuarterStepCom_ok : ComOK chachaQuarterStepCom :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))))))

/-- **Step 2 — in-`Com` value proof, cheap `rfl`.** -/
theorem chachaQuarterStepCom_denote (d a : BitVec 64) :
    Com.denote chachaQuarterStepCom (.cons d (.cons a .nil))
      = ((((d ^^^ a) &&& mask32) <<< 16) ||| (((d ^^^ a) &&& mask32) >>> 16)) &&& mask32 :=
  rfl

/-- **Step 2 — recognizable u32 `_spec`, `bv_decide`.** The whole step equals the
    genuine ChaCha20 component: 32-bit `rotateLeft 16` of the 32-bit xor `d ^ a`,
    zero-extended back to 64 bits. A real `u32` cipher step emitting via masked-u64. -/
theorem chachaQuarterStepCom_spec (d a : BitVec 64) :
    Com.denote chachaQuarterStepCom (.cons d (.cons a .nil))
      = (((d.setWidth 32 ^^^ a.setWidth 32).rotateLeft 16)).setWidth 64 := by
  rw [chachaQuarterStepCom_denote]
  show ((((d ^^^ a) &&& BitVec.ofNat 64 4294967295) <<< 16)
        ||| (((d ^^^ a) &&& BitVec.ofNat 64 4294967295) >>> 16))
        &&& BitVec.ofNat 64 4294967295 = _
  bv_decide

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem chachaQuarterStepCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg chachaQuarterStepCom 2))).regs)
        (comRetName chachaQuarterStepCom 2)
      = Com.denote chachaQuarterStepCom V :=
  com_arm_e2e chachaQuarterStepCom_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem chachaQuarterStepCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg chachaQuarterStepCom 2))).regs)
        (comRetName chachaQuarterStepCom 2)
      = Com.denote chachaQuarterStepCom V :=
  com_riscv_e2e chachaQuarterStepCom_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def chachaQuarterStepCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 chachaQuarterStepCom "chacha_qstep"

end CatCrypt.Crypto.SecureCompilation.Width32Emit
