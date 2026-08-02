/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfFull
import Std.Tactic.BVDecide

/-!
# Golden path: Keccak-f[1600] bit-ops as `Com jasminDialect`, emitted by the verified compiler

**The same canonical pattern as `FieldEmitGoldenPath`, on the FIPS 202 (Keccak/SHA-3)
permutation's per-lane bit primitives.** Each lane is a `u64`; the χ step and the ρ
rotations are written ONCE as `Com jasminDialect` source programs over the supported
all-`reg 64` alphabet, proven ONCE against their bit-vector value spec, and the verified
compiler emits the machine code — to AArch64 *and* RISC-V — with no per-kernel backend
proof (`comToReg_faithful` discharges it) and constant-time by construction.

Two Keccak-f[1600] primitives are worked below:

* **the χ step** `χ a b c = a ⊕ (¬b ∧ c)` per lane (the only non-linear step of Keccak;
  `a = A[x]`, `b = A[x+1]`, `c = A[x+2]`). The dialect has no bitwise-NOT `SupportedOp`,
  so `¬b` is expressed as `b ⊕ 0xFFFF…FF` (`xor` against the all-ones `regConst`); the
  in-`Com` source denotes that explicit form by `rfl`, and a `bv_decide` check certifies
  it equals the recognizable spec `a ^^^ ((~~~b) &&& c)`;

* **the ρ rotations** `ρ_r a = a.rotateLeft r` (two example offsets, `r = 1` and `r = 44`,
  both in the Keccak ρ offset table). The dialect has no rotate `SupportedOp`, so the
  left-rotate is synthesised from the shift/or alphabet as `(a <<< r) ||| (a >>> (64 - r))`
  (`shlImm`/`shrImm`/`or`); again the source denotes the explicit shift form by `rfl`, and
  `bv_decide` certifies it equals `BitVec.rotateLeft`.

All lower through the *same* `comToReg_faithful` as the field ops — so Keccak's lane
bit-ops emit to both backends with no new machinery, only a new kernel body. -/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.KeccakBit

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

/-! ## The χ step: `χ a b c = a ⊕ (¬b ∧ c)` per lane

The only non-linear step of Keccak-f. There is no bitwise-NOT in `SupportedOp`, so `¬b`
is `b ⊕ 0xFFFF…FF`. The body is:
```
ones := 0xFFFF…FF ;  nb := b ^ ones (= ¬b) ;  nbc := nb & c ;  r := a ^ nbc
```
all `regConst`/`regArith {xor, and}` — every one in `SupportedOp`, so the source denote
reduces by cheap `rfl` and `com_arm_e2e`/`com_riscv_e2e` emit both backends. -/

/-- **The χ-step source**, over args `[a, b, c]`:
    `ones := 2^64-1 ; nb := b ^ ones ; nbc := nb & c ; r := a ^ nbc ; ret r`. -/
def keccakChiCom : Com jasminDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- ones = 2^64-1
  .var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- nb = b ^ ones   (= ¬b);  b = .there (.there .here), ones = .here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there .here)) (.cons .here .nil) }
  -- nbc = nb & c ;  nb = .here, c = .there (.there (.there (.there .here)))
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here
            (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- r = a ^ nbc ;  a = .there (.there (.there .here)), nbc = .here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) (.cons .here .nil) }
    (.ret .here))))

/-- `keccakChiCom` is in the supported straight-line fragment (regConst, xor, and, xor). -/
theorem keccakChiCom_ok : ComOK keccakChiCom :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))

/-- **Step 2 — value proof at the source, cheap `rfl`** (the explicit `¬b = b ^ 0xFF…FF`
    form, all-ALU). -/
theorem keccakChiCom_denote (a b c : BitVec 64) :
    Com.denote keccakChiCom (.cons a (.cons b (.cons c .nil)))
      = a ^^^ ((b ^^^ BitVec.ofNat 64 18446744073709551615) &&& c) := rfl

/-- **The recognizable χ spec**: the emitted source computes the FIPS 202 χ value
    `a ⊕ (¬b ∧ c)`. The `¬b = b ^ 0xFF…FF` synthesis is certified by `bv_decide`. -/
theorem keccakChiCom_spec (a b c : BitVec 64) :
    Com.denote keccakChiCom (.cons a (.cons b (.cons c .nil)))
      = a ^^^ ((~~~b) &&& c) := by
  rw [keccakChiCom_denote]; show (_ : BitVec 64) = _; bv_decide

/-- **The χ step emits to AArch64**, discharged by `com_arm_e2e` via the single
    `comToReg_faithful`. -/
theorem keccakChiCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg keccakChiCom 3))).regs)
        (comRetName keccakChiCom 3)
      = Com.denote keccakChiCom V :=
  com_arm_e2e keccakChiCom_ok allReg64_three V s hs

/-- **The χ step emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem keccakChiCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg keccakChiCom 3))).regs)
        (comRetName keccakChiCom 3)
      = Com.denote keccakChiCom V :=
  com_riscv_e2e keccakChiCom_ok allReg64_three V s hs

/-- **The x86 owned-emit leg, via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/keccak_compare/`, not byte identity with `compileComToElf`. -/
def keccakChiCom_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf keccakChiCom "keccak_chi"

/-! ## The ρ rotations: `ρ_r a = a.rotateLeft r`

The ρ step rotates each lane left by a per-lane offset. There is no rotate `SupportedOp`,
so the left-rotate by `r` is synthesised from the shift/or alphabet:
```
sh := a <<< r ;  shr := a >>> (64 - r) ;  r := sh | shr
```
(`shlImm`/`shrImm`/`or`, all `SupportedOp`). Two example offsets from the Keccak ρ table,
`r = 1` and `r = 44`, are worked; any other offset is the same body with a different
immediate. The source denotes the explicit shift form by `rfl`, and `bv_decide` certifies
it equals `BitVec.rotateLeft`. -/

/-- **ρ with offset 1**, over arg `[a]`:
    `sh := a <<< 1 ; shr := a >>> 63 ; r := sh | shr ; ret r`. -/
def keccakRho1Com : Com jasminDialect [.reg 64] (.reg 64) :=
  -- sh = a <<< 1 ;  a = .here
  .var { op := .shlImm 64 1, retTy_eq := rfl, args := .cons .here .nil }
  -- shr = a >>> 63 ;  a = .there .here
  (.var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- r = sh | shr ;  sh = .there .here, shr = .here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))

/-- `keccakRho1Com` is in the supported straight-line fragment (shlImm, shrImm, or). -/
theorem keccakRho1Com_ok : ComOK keccakRho1Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))

/-- **Step 2 — value proof at the source, cheap `rfl`** (the explicit shift-or form). -/
theorem keccakRho1Com_denote (a : BitVec 64) :
    Com.denote keccakRho1Com (.cons a .nil) = (a <<< 1) ||| (a >>> 63) := rfl

/-- **The recognizable ρ spec**: the emitted source computes `a.rotateLeft 1`.
    The shift-or synthesis is certified by `bv_decide`. -/
theorem keccakRho1Com_spec (a : BitVec 64) :
    Com.denote keccakRho1Com (.cons a .nil) = a.rotateLeft 1 := by
  rw [keccakRho1Com_denote]; show (_ : BitVec 64) = _; bv_decide

/-- **ρ(1) emits to AArch64**, discharged by `com_arm_e2e`. -/
theorem keccakRho1Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg keccakRho1Com 1))).regs)
        (comRetName keccakRho1Com 1)
      = Com.denote keccakRho1Com V :=
  com_arm_e2e keccakRho1Com_ok allReg64_one V s hs

/-- **ρ(1) emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem keccakRho1Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg keccakRho1Com 1))).regs)
        (comRetName keccakRho1Com 1)
      = Com.denote keccakRho1Com V :=
  com_riscv_e2e keccakRho1Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg for ρ(1), via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/keccak_compare/`, not byte identity with `compileComToElf`. -/
def keccakRho1Com_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf keccakRho1Com "keccak_rho1"

/-- **ρ with offset 44**, over arg `[a]`:
    `sh := a <<< 44 ; shr := a >>> 20 ; r := sh | shr ; ret r`. -/
def keccakRho44Com : Com jasminDialect [.reg 64] (.reg 64) :=
  -- sh = a <<< 44 ;  a = .here
  .var { op := .shlImm 64 44, retTy_eq := rfl, args := .cons .here .nil }
  -- shr = a >>> 20 ;  a = .there .here   (64 - 44 = 20)
  (.var { op := .shrImm 64 20, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- r = sh | shr ;  sh = .there .here, shr = .here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))

/-- `keccakRho44Com` is in the supported straight-line fragment (shlImm, shrImm, or). -/
theorem keccakRho44Com_ok : ComOK keccakRho44Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))

/-- **Step 2 — value proof at the source, cheap `rfl`** (the explicit shift-or form). -/
theorem keccakRho44Com_denote (a : BitVec 64) :
    Com.denote keccakRho44Com (.cons a .nil) = (a <<< 44) ||| (a >>> 20) := rfl

/-- **The recognizable ρ spec**: the emitted source computes `a.rotateLeft 44`.
    The shift-or synthesis is certified by `bv_decide`. -/
theorem keccakRho44Com_spec (a : BitVec 64) :
    Com.denote keccakRho44Com (.cons a .nil) = a.rotateLeft 44 := by
  rw [keccakRho44Com_denote]; show (_ : BitVec 64) = _; bv_decide

/-- **ρ(44) emits to AArch64**, discharged by `com_arm_e2e`. -/
theorem keccakRho44Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg keccakRho44Com 1))).regs)
        (comRetName keccakRho44Com 1)
      = Com.denote keccakRho44Com V :=
  com_arm_e2e keccakRho44Com_ok allReg64_one V s hs

/-- **ρ(44) emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem keccakRho44Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg keccakRho44Com 1))).regs)
        (comRetName keccakRho44Com 1)
      = Com.denote keccakRho44Com V :=
  com_riscv_e2e keccakRho44Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg for ρ(44), via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/keccak_compare/`, not byte identity with `compileComToElf`. -/
def keccakRho44Com_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf keccakRho44Com "keccak_rho44"

end CatCrypt.Crypto.SecureCompilation.KeccakBit
