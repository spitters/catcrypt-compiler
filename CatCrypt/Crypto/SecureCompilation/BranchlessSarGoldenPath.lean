/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
public import Std.Tactic.BVDecide

/-!
# Golden path: branchless arithmetic shift-right, in the existing `reg 64` alphabet

The sign-extending (arithmetic) right shift `a >>>ₛ n` — the operation ML-DSA's
`reduce32`/`decompose` use to recover the sign of a centred residue — is **not** a
`SupportedOp`: the dialect has only the logical `shrImm`. **No dialect extension is
needed.** The arithmetic shift is *branchless* over the existing width-64 alphabet:

```
sgn  := a >>> 63                 -- shrImm 63   (the sign bit, 0 or 1)
zero := 0                        -- regConst 0
mask := zero - sgn               -- sub         (all-ones iff a < 0)
hi   := mask <<< (64 - n)        -- shlImm      (the n sign bits, in the top n positions)
lo   := a >>> n                  -- shrImm n
r    := lo ||| hi                -- or
```

so `sar a n = (a >>> n) ||| ((0 - (a >>> 63)) <<< (64 - n))`, every op in
`SupportedOp` (`shrImm`/`shlImm`/`regConst`/`regArith {sub, or}`). The source denote
is a cheap `rfl`, the value step is the library `BitVec.sshiftRight` proven by
`bv_decide`, and `com_arm_e2e`/`com_riscv_e2e` emit both backends from the one source
— **no `sarImm` op, no `RegStmt` primitive, no backend change, no faithfulness
generalisation**. This unblocks ML-DSA-style sign handling on the golden path, exactly
as `fieldCondSub251Com` unblocked the GF(251) reduction tail.

Two instances are worked below — `n = 1` (the halving used by `decompose`'s rounding)
and `n = 20` (a wide ML-DSA-scale shift) — to show the recipe is `n`-uniform: only the
two immediates (`n` and `64 - n`) change.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BranchlessSar

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

/-! ## Instance `n = 1`: arithmetic shift-right by one (the `decompose` halving) -/

/-- `sgn := a >>> 63 ; lo := a >>> 1 ; zero := 0 ; mask := zero - sgn ;
    hi := mask <<< 63 ; r := lo ||| hi ; ret r` over arg `[a]`. The branchless
    arithmetic shift-right by 1. -/
def sar1Com : Com jasminDialect [.reg 64] (.reg 64) :=
  .var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }          -- sgn = a >>> 63
  (.var { op := .shrImm 64 1, retTy_eq := rfl, args := .cons (.there .here) .nil } -- lo = a >>> 1
  (.var { op := .regConst 64 0, retTy_eq := rfl, args := .nil }                    -- zero = 0
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there .here)) .nil) }               -- mask = zero - sgn
  (.var { op := .shlImm 64 63, retTy_eq := rfl, args := .cons .here .nil }         -- hi = mask <<< 63
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) (.cons .here .nil) }      -- lo ||| hi
    (.ret .here))))))

/-- `sar1Com` is in the supported straight-line fragment (shrImm, shrImm, regConst,
    sub, shlImm, or). -/
theorem sar1Com_ok : ComOK sar1Com := by
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  exact ComOK.var (by supported_op) (ComOK.ret _)

/-- **Step 2 — value proof at the source, cheap `rfl`.** `sar1Com` denotes the
    branchless arithmetic-shift expression `(a >>> 1) ||| ((0 - (a >>> 63)) <<< 63)`. -/
theorem sar1Com_denote (a : BitVec 64) :
    Com.denote sar1Com (.cons a .nil)
      = (a >>> 1) ||| (((0 : BitVec 64) - (a >>> 63)) <<< 63) := rfl

/-- **The value step that names the operation**: the branchless source computes the
    library arithmetic shift-right `BitVec.sshiftRight a 1`. Closed by `bv_decide` —
    if the `64 - n` offset or the sign extraction were wrong, this would fail. -/
theorem sar1Com_spec (a : BitVec 64) :
    Com.denote sar1Com (.cons a .nil) = BitVec.sshiftRight a 1 := by
  rw [sar1Com_denote]
  show (_ : BitVec 64) = _
  bv_decide

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem sar1Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg sar1Com 1))).regs)
        (comRetName sar1Com 1)
      = Com.denote sar1Com V :=
  com_arm_e2e sar1Com_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, discharged by the same `comToReg_faithful`. -/
theorem sar1Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg sar1Com 1))).regs)
        (comRetName sar1Com 1)
      = Com.denote sar1Com V :=
  com_riscv_e2e sar1Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier, as the field golden path): the same
    source to ELF `.o` bytes via the generic driver. -/
def sar1Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 sar1Com "sar1"

/-! ## Instance `n = 20`: a wide ML-DSA-scale arithmetic shift-right -/

/-- The same branchless recipe with `n = 20`, `64 - n = 44`: `sgn := a >>> 63 ;
    lo := a >>> 20 ; zero := 0 ; mask := zero - sgn ; hi := mask <<< 44 ;
    r := lo ||| hi ; ret r` over arg `[a]`. -/
def sar20Com : Com jasminDialect [.reg 64] (.reg 64) :=
  .var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }           -- sgn = a >>> 63
  (.var { op := .shrImm 64 20, retTy_eq := rfl, args := .cons (.there .here) .nil } -- lo = a >>> 20
  (.var { op := .regConst 64 0, retTy_eq := rfl, args := .nil }                     -- zero = 0
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there .here)) .nil) }                -- mask = zero - sgn
  (.var { op := .shlImm 64 44, retTy_eq := rfl, args := .cons .here .nil }          -- hi = mask <<< 44
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) (.cons .here .nil) }       -- lo ||| hi
    (.ret .here))))))

/-- `sar20Com` is in the supported straight-line fragment (shrImm, shrImm, regConst,
    sub, shlImm, or). -/
theorem sar20Com_ok : ComOK sar20Com := by
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  exact ComOK.var (by supported_op) (ComOK.ret _)

/-- **Step 2 — value proof at the source, cheap `rfl`.** `sar20Com` denotes
    `(a >>> 20) ||| ((0 - (a >>> 63)) <<< 44)`. -/
theorem sar20Com_denote (a : BitVec 64) :
    Com.denote sar20Com (.cons a .nil)
      = (a >>> 20) ||| (((0 : BitVec 64) - (a >>> 63)) <<< 44) := rfl

/-- **The value step that names the operation**: the branchless source computes the
    library arithmetic shift-right `BitVec.sshiftRight a 20`, by `bv_decide`. -/
theorem sar20Com_spec (a : BitVec 64) :
    Com.denote sar20Com (.cons a .nil) = BitVec.sshiftRight a 20 := by
  rw [sar20Com_denote]
  show (_ : BitVec 64) = _
  bv_decide

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem sar20Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg sar20Com 1))).regs)
        (comRetName sar20Com 1)
      = Com.denote sar20Com V :=
  com_arm_e2e sar20Com_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, discharged by the same `comToReg_faithful`. -/
theorem sar20Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg sar20Com 1))).regs)
        (comRetName sar20Com 1)
      = Com.denote sar20Com V :=
  com_riscv_e2e sar20Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier): the same source to ELF `.o` bytes. -/
def sar20Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 sar20Com "sar20"

end CatCrypt.Crypto.SecureCompilation.BranchlessSar
