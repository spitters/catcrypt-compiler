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
# Golden path: constant-time SELECT and ANDN, branchless in the width-64 alphabet

**This is the canonical pattern for emitting constant-time bit-twiddle primitives** —
and the point of this file is that no compiler/dialect extension is needed: the
constant-time *select* (the conditional-move every secret-dependent branch must be
rewritten into) and *and-not* (the `BIC`/`ANDN` complement-and used throughout bitsliced
crypto) are already expressible over the EXISTING width-64 `SupportedOp` alphabet
(`regArith {add,sub,and,or,xor}`/`regConst`), so they ride `com_arm_e2e`/`com_riscv_e2e`
with **no new dialect op, no `RegStmt` primitive, no backend change**.

The recipe is the one from `FieldEmitGoldenPath` (one source → both backends), here on
two control-flow-free primitives:

1. `ctSelectCom` — `cond ? a : b` with `cond ∈ {0,1}`, branchless: form the all-ones
   mask `m := 0 - cond`, then `(a & m) | (b & ~m)`. The recognizable specs
   (`ctSelectCom_true` / `ctSelectCom_false`) pin it to `a` resp. `b` at the literal
   conditions — the non-vacuous correctness check that this really is a select.
2. `andnCom` — `~a & b` (the `BIC`/`ANDN`), branchless as `(a ^ allOnes) & b`.
   `andnCom_spec` pins it to `(~~~a) &&& b`.

Both lower through the *same* `comToReg_faithful`, so a constant-time conditional-move
and a complement-and emit to AArch64 *and* RISC-V with no new machinery — the
control-flow-elimination primitives the secret-independent (CT) compiler relies on are
already in the supported scalar fragment.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BranchlessSelect

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

/-! ## The constant-time select `cond ? a : b`

Over args `[cond, a, b]` with `cond ∈ {0,1}` a `reg 64`. Branchless via the all-ones
mask `m := 0 - cond` (so `m = 0xFF…FF` when `cond = 1`, `m = 0` when `cond = 0`):
`allOnes := 0xFF…FF ; m := 0 - cond ; nm := m ^ allOnes (= ~m) ;
 am := a & m ; bn := b & nm ; r := am | bn`.
All `regConst`/`regArith {sub,xor,and,or}`, every one in `SupportedOp`. -/

/-- `c0 := 0 ; m := c0 - cond ; allOnes := 0xFF…FF ; nm := m ^ allOnes ;
    am := a & m ; bn := b & nm ; r := am | bn ; ret r` over args `[cond, a, b]`. -/
def ctSelectCom : Com jasminDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- c0 = 0
  .var { op := .regConst 64 0, retTy_eq := rfl, args := .nil }
  -- m = c0 - cond     (c0 = .here, cond = .there.here)
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- allOnes = 0xFF…FF
  (.var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- nm = m ^ allOnes     (m = .there.here, allOnes = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- am = a & m     (a = 5×.there.here, m = .there.there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there .here)))))
                    (.cons (.there (.there .here)) .nil) }
  -- bn = b & nm     (b = 7×.there.here, nm = .there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                    (.cons (.there .here) .nil) }
  -- r = am | bn     (am = .there.here, bn = .here)
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))))))

/-- `ctSelectCom` is in the supported straight-line fragment (regConst, sub,
    regConst, xor, and, and, or). -/
theorem ctSelectCom_ok : ComOK ctSelectCom :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))))))

/-- **Step 2 — value proof at the source, cheap `rfl`** (all-ALU). With
    `m := 0 - cond`, the source denotes `(a & m) | (b & (m ^ 0xFF…FF))`. -/
theorem ctSelectCom_denote (cond a b : BitVec 64) :
    Com.denote ctSelectCom (.cons cond (.cons a (.cons b .nil)))
      = (a &&& ((0 : BitVec 64) - cond))
          ||| (b &&& (((0 : BitVec 64) - cond) ^^^ BitVec.ofNat 64 18446744073709551615)) := rfl

/-- **Non-vacuity, `cond = 1`**: the select returns `a`. -/
theorem ctSelectCom_true (a b : BitVec 64) :
    Com.denote ctSelectCom (.cons (1 : BitVec 64) (.cons a (.cons b .nil))) = a := by
  rw [ctSelectCom_denote]
  show (a &&& ((0 : BitVec 64) - 1))
        ||| (b &&& (((0 : BitVec 64) - 1) ^^^ BitVec.ofNat 64 18446744073709551615)) = a
  bv_decide

/-- **Non-vacuity, `cond = 0`**: the select returns `b`. -/
theorem ctSelectCom_false (a b : BitVec 64) :
    Com.denote ctSelectCom (.cons (0 : BitVec 64) (.cons a (.cons b .nil))) = b := by
  rw [ctSelectCom_denote]
  show (a &&& ((0 : BitVec 64) - 0))
        ||| (b &&& (((0 : BitVec 64) - 0) ^^^ BitVec.ofNat 64 18446744073709551615)) = b
  bv_decide

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem ctSelectCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg ctSelectCom 3))).regs)
        (comRetName ctSelectCom 3)
      = Com.denote ctSelectCom V :=
  com_arm_e2e ctSelectCom_ok allReg64_three V s hs

/-- **Emitted RISC-V** — same source, discharged by the same `comToReg_faithful`. -/
theorem ctSelectCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg ctSelectCom 3))).regs)
        (comRetName ctSelectCom 3)
      = Com.denote ctSelectCom V :=
  com_riscv_e2e ctSelectCom_ok allReg64_three V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier, as the field golden path): the same
    source to ELF `.o` bytes via the generic driver. -/
def ctSelectCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 ctSelectCom "ct_select"

/-! ## And-not `~a & b` (the `BIC`/`ANDN`)

The complement-and primitive of bitsliced/constant-time crypto, branchless as
`(a ^ 0xFF…FF) & b`: `regConst`/`regArith {xor, and}`, both in `SupportedOp`. -/

/-- `allOnes := 0xFF…FF ; na := a ^ allOnes (= ~a) ; r := na & b ; ret r` over `[a, b]`. -/
def andnCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  -- allOnes = 0xFF…FF
  .var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- na = a ^ allOnes     (a = .there.here, allOnes = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r = na & b     (na = .here, b = .there.there.there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there .here))) .nil) }
    (.ret .here)))

/-- `andnCom` is in the supported straight-line fragment (regConst, xor, and). -/
theorem andnCom_ok : ComOK andnCom :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))

/-- **Step 2 — value proof at the source, cheap `rfl`**: the and-not source denotes
    `(a ^ 0xFF…FF) & b`. -/
theorem andnCom_denote (a b : BitVec 64) :
    Com.denote andnCom (.cons a (.cons b .nil))
      = (a ^^^ BitVec.ofNat 64 18446744073709551615) &&& b := rfl

/-- **Non-vacuity**: the and-not source computes `(~~~a) &&& b` (the `BIC`/`ANDN`). -/
theorem andnCom_spec (a b : BitVec 64) :
    Com.denote andnCom (.cons a (.cons b .nil)) = (~~~a) &&& b := by
  rw [andnCom_denote]
  show (a ^^^ BitVec.ofNat 64 18446744073709551615) &&& b = (~~~a) &&& b
  bv_decide

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem andnCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg andnCom 2))).regs)
        (comRetName andnCom 2)
      = Com.denote andnCom V :=
  com_arm_e2e andnCom_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **Emitted RISC-V** — same source, discharged by the same `comToReg_faithful`. -/
theorem andnCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg andnCom 2))).regs)
        (comRetName andnCom 2)
      = Com.denote andnCom V :=
  com_riscv_e2e andnCom_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def andnCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 andnCom "andn"

end CatCrypt.Crypto.SecureCompilation.BranchlessSelect
