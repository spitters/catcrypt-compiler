/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import CatCrypt.Crypto.SecureCompilation.RotateSynth
import Std.Tactic.BVDecide

/-!
# Golden path: Threefish-512 / Skein MIX as `Com jasminDialect`, emitted by the verified compiler

**The same canonical pattern as `FieldEmitGoldenPath` and `KeccakBitGoldenPath`, on the
Threefish-512 block cipher's MIX function** — the u64 ARX primitive at the core of the
Skein hash (a SHA-3 finalist). Each word is a `u64`; the MIX function is written ONCE as
`Com jasminDialect` source programs over the supported all-`reg 64` alphabet, proven ONCE
against its value spec, and the verified compiler emits the machine code — to AArch64
*and* RISC-V — with no per-kernel backend proof (`comToReg_faithful` discharges it) and
constant-time by construction.

The MIX function takes two words `x0`, `x1` and a per-round rotation constant `R`:
```
y0 := x0 + x1
y1 := (x1 <<< R) ^^^ y0    (rotate-LEFT x1 by R, then xor with the new y0)
```
The add (`y0`) and the rotate-xor (`y1`) are the only two operations — the same ARX shape
as ChaCha/BLAKE, here with Threefish's modular-add over u64. There is no rotate
`SupportedOp`, so the left-rotate by `R` is synthesised from the shift/or alphabet as
`(x1 <<< R) ||| (x1 >>> (64 - R))` (`shlImm`/`shrImm`/`or`); the source denotes that
explicit shift form by `rfl`, and `bv_decide` certifies it equals `BitVec.rotateLeft`.

Two instances are worked, with genuine Threefish-512 rotation constants **R = 46** and
**R = 33** (from the Threefish-512 rotation-constant table). Each MIX has two outputs, so
each instance gives two single-output `Com`s — `y0` (one `add`) and `y1` (rotate-xor).
Both lower through the *same* `comToReg_faithful` as the field/Keccak ops — so the
Threefish ARX words emit to both backends with no new machinery, only a new kernel body. -/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ThreefishMix

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
open CatCrypt.Crypto.SecureCompilation.RotateSynth

/-! ## MIX with rotation R = 46 (Threefish-512 round constant)

`y0 = x0 + x1`, `y1 = (x1 <<< 46) ^^^ y0`. -/

/-- **MIX(46) — the `y0` output**, over args `[x0, x1]`: `y0 := x1 + x0 ; ret y0`.
    A single `add` (the arg order `.cons (.there .here) (.cons .here .nil)` gives `x1 + x0`,
    matching `y0 = x0 + x1` by commutativity, exactly as `fieldAddCom`). -/
def mix46_y0Com : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)

/-- `mix46_y0Com` is in the supported straight-line fragment (one `add`). -/
theorem mix46_y0Com_ok : ComOK mix46_y0Com :=
  ComOK.var (by supported_op) (ComOK.ret _)

/-- **Step 2 — value proof, cheap `rfl`.** The `y0` source denotes the MIX sum `x1 + x0`. -/
theorem mix46_y0Com_denote (x0 x1 : BitVec 64) :
    Com.denote mix46_y0Com (.cons x0 (.cons x1 .nil)) = x1 + x0 := rfl

/-- **MIX(46) `y0` emits to AArch64**, discharged by `com_arm_e2e` via the single
    `comToReg_faithful`. -/
theorem mix46_y0Com_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg mix46_y0Com 2))).regs)
        (comRetName mix46_y0Com 2)
      = Com.denote mix46_y0Com V :=
  com_arm_e2e mix46_y0Com_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **MIX(46) `y0` emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem mix46_y0Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg mix46_y0Com 2))).regs)
        (comRetName mix46_y0Com 2)
      = Com.denote mix46_y0Com V :=
  com_riscv_e2e mix46_y0Com_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg** for MIX(46) `y0` (KAT-gated tier, as in
    `FieldEmitGoldenPath`): the same source to ELF `.o` bytes via the generic driver. -/
def mix46_y0Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 mix46_y0Com "threefish_mix46_y0"

/-- **MIX(46) — the `y1` output**, over args `[x0, x1]`:
    `sh := x1 <<< 46 ; shr := x1 >>> 18 ; rot := sh | shr ; y0 := x1 + x0 ; y1 := rot ^ y0`.
    The left-rotate of `x1` by 46 is `(x1 <<< 46) | (x1 >>> 18)` (`64 - 46 = 18`), then
    xored with `y0 = x1 + x0`. -/
def mix46_y1Com : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  -- sh = x1 <<< 46 ;  x1 = .there .here
  .var { op := .shlImm 64 46, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- shr = x1 >>> 18 ;  x1 = .there (.there .here)  (64 - 46 = 18)
  (.var { op := .shrImm 64 18, retTy_eq := rfl, args := .cons (.there (.there .here)) .nil }
  -- rot = sh | shr ;  sh = .there .here, shr = .here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- y0 = x1 + x0 ;  x1 = .there (.there (.there (.there .here))), x0 = .there (.there (.there .here))
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here))))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- y1 = rot ^ y0 ;  rot = .there .here, y0 = .here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))))

/-- `mix46_y1Com` is in the supported straight-line fragment (shlImm, shrImm, or, add, xor). -/
theorem mix46_y1Com_ok : ComOK mix46_y1Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))))

/-- **Step 2 — value proof at the source, cheap `rfl`** (the explicit shift-or rotate form). -/
theorem mix46_y1Com_denote (x0 x1 : BitVec 64) :
    Com.denote mix46_y1Com (.cons x0 (.cons x1 .nil))
      = ((x1 <<< 46) ||| (x1 >>> 18)) ^^^ (x1 + x0) := rfl

/-- **The recognizable MIX spec**: the emitted source computes the Threefish-512 `y1`
    value `(x1.rotateLeft 46) ^^^ (x1 + x0)`. The shift-or rotate synthesis is certified
    by the shared `rotl_synth` identity (no `bv_decide`). -/
theorem mix46_y1Com_spec (x0 x1 : BitVec 64) :
    Com.denote mix46_y1Com (.cons x0 (.cons x1 .nil))
      = (x1.rotateLeft 46) ^^^ (x1 + x0) := by
  rw [mix46_y1Com_denote, rotl_synth x1 46 (by decide) (by decide)]

/-- **MIX(46) `y1` emits to AArch64**, discharged by `com_arm_e2e`. -/
theorem mix46_y1Com_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg mix46_y1Com 2))).regs)
        (comRetName mix46_y1Com 2)
      = Com.denote mix46_y1Com V :=
  com_arm_e2e mix46_y1Com_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **MIX(46) `y1` emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem mix46_y1Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg mix46_y1Com 2))).regs)
        (comRetName mix46_y1Com 2)
      = Com.denote mix46_y1Com V :=
  com_riscv_e2e mix46_y1Com_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg** for MIX(46) `y1` (KAT-gated tier). -/
def mix46_y1Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 mix46_y1Com "threefish_mix46_y1"

/-! ## MIX with rotation R = 33 (Threefish-512 round constant)

`y0 = x0 + x1`, `y1 = (x1 <<< 33) ^^^ y0`. Same body, a different rotation immediate. -/

/-- **MIX(33) — the `y0` output**, over args `[x0, x1]`: `y0 := x1 + x0 ; ret y0`. -/
def mix33_y0Com : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)

/-- `mix33_y0Com` is in the supported straight-line fragment (one `add`). -/
theorem mix33_y0Com_ok : ComOK mix33_y0Com :=
  ComOK.var (by supported_op) (ComOK.ret _)

/-- **Step 2 — value proof, cheap `rfl`.** The `y0` source denotes the MIX sum `x1 + x0`. -/
theorem mix33_y0Com_denote (x0 x1 : BitVec 64) :
    Com.denote mix33_y0Com (.cons x0 (.cons x1 .nil)) = x1 + x0 := rfl

/-- **MIX(33) `y0` emits to AArch64**, discharged by `com_arm_e2e`. -/
theorem mix33_y0Com_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg mix33_y0Com 2))).regs)
        (comRetName mix33_y0Com 2)
      = Com.denote mix33_y0Com V :=
  com_arm_e2e mix33_y0Com_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **MIX(33) `y0` emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem mix33_y0Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg mix33_y0Com 2))).regs)
        (comRetName mix33_y0Com 2)
      = Com.denote mix33_y0Com V :=
  com_riscv_e2e mix33_y0Com_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg** for MIX(33) `y0` (KAT-gated tier). -/
def mix33_y0Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 mix33_y0Com "threefish_mix33_y0"

/-- **MIX(33) — the `y1` output**, over args `[x0, x1]`:
    `sh := x1 <<< 33 ; shr := x1 >>> 31 ; rot := sh | shr ; y0 := x1 + x0 ; y1 := rot ^ y0`.
    The left-rotate of `x1` by 33 is `(x1 <<< 33) | (x1 >>> 31)` (`64 - 33 = 31`). -/
def mix33_y1Com : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  -- sh = x1 <<< 33 ;  x1 = .there .here
  .var { op := .shlImm 64 33, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- shr = x1 >>> 31 ;  x1 = .there (.there .here)  (64 - 33 = 31)
  (.var { op := .shrImm 64 31, retTy_eq := rfl, args := .cons (.there (.there .here)) .nil }
  -- rot = sh | shr ;  sh = .there .here, shr = .here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- y0 = x1 + x0
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here))))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- y1 = rot ^ y0 ;  rot = .there .here, y0 = .here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))))

/-- `mix33_y1Com` is in the supported straight-line fragment (shlImm, shrImm, or, add, xor). -/
theorem mix33_y1Com_ok : ComOK mix33_y1Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))))

/-- **Step 2 — value proof at the source, cheap `rfl`** (the explicit shift-or rotate form). -/
theorem mix33_y1Com_denote (x0 x1 : BitVec 64) :
    Com.denote mix33_y1Com (.cons x0 (.cons x1 .nil))
      = ((x1 <<< 33) ||| (x1 >>> 31)) ^^^ (x1 + x0) := rfl

/-- **The recognizable MIX spec**: the emitted source computes the Threefish-512 `y1`
    value `(x1.rotateLeft 33) ^^^ (x1 + x0)`. The shift-or rotate synthesis is certified
    by the shared `rotl_synth` identity (no `bv_decide`). -/
theorem mix33_y1Com_spec (x0 x1 : BitVec 64) :
    Com.denote mix33_y1Com (.cons x0 (.cons x1 .nil))
      = (x1.rotateLeft 33) ^^^ (x1 + x0) := by
  rw [mix33_y1Com_denote, rotl_synth x1 33 (by decide) (by decide)]

/-- **MIX(33) `y1` emits to AArch64**, discharged by `com_arm_e2e`. -/
theorem mix33_y1Com_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg mix33_y1Com 2))).regs)
        (comRetName mix33_y1Com 2)
      = Com.denote mix33_y1Com V :=
  com_arm_e2e mix33_y1Com_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **MIX(33) `y1` emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem mix33_y1Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg mix33_y1Com 2))).regs)
        (comRetName mix33_y1Com 2)
      = Com.denote mix33_y1Com V :=
  com_riscv_e2e mix33_y1Com_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg** for MIX(33) `y1` (KAT-gated tier). -/
def mix33_y1Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 mix33_y1Com "threefish_mix33_y1"

end CatCrypt.Crypto.SecureCompilation.ThreefishMix
