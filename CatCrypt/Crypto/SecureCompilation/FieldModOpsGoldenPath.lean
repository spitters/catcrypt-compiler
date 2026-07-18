/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import Std.Tactic.BVDecide

/-!
# Golden path: modular negate / double / conditional-negate over GF(251)

The field-arithmetic complements to the modular add/sub/reduce of
`FieldEmitGoldenPath`. Each primitive is written ONCE as a `Com jasminDialect`
source, proven ONCE against its `% q` value spec, and the verified compiler
emits the machine code — to AArch64 *and* RISC-V — with no per-kernel backend
proof (`comToReg_faithful` discharges it) and constant-time by construction.

The fixed prime is **q = 251** (GF(251), the same small Solinas prime as
`fieldCondSub251Com`): inputs are assumed already reduced (`a.toNat < 251`) and
the `% q` specs are decidable, so the branchless mask correctness closes by
`bv_decide`/`decide` + `omega`. Each op mirrors the branchless
conditional-subtract idiom of `fieldCondSub251Com`
(`t := … ; mask := 0 - (t >>> 63) ; r := t + (mask & q)`).

Three ops, single-input or single-output, width-64:

* `modDoubleCom a = (a + a) mod 251` — double then one conditional-subtract
  (`a < 251 ⇒ a + a < 502 < 2·251`, so one condsub reduces);
* `modNegCom a = (251 - a) mod 251` — `t := 251 - a` then one conditional-subtract
  (`a = 0 ⇒ t = 251`, condsub maps it to `0`; `a > 0 ⇒ t ∈ [1,251)`, condsub is
  a no-op);
* `condNegCom cond a = cond ? (251 - a) mod 251 : a` — constant-time select of
  `modNeg a` against `a` via the CT mask `mask := 0 - cond`
  (`r := (neg & mask) | (a & ~mask)`).

All lower through the *same* `comToReg_faithful`, exactly as the add/sub/reduce
primitives do; only the kernel body changes.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldModOps

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

/-! ## Op 1 — modular double `(a + a) mod 251` -/

/-- `t := a + a ; c251 := 251 ; d := t - c251 ; bit := d >>> 63 ; c0 := 0 ;
    m := c0 - bit ; masked := m & c251 ; r := d + masked ; ret r` over arg `[a]`.
    The doubled value `a + a` (for `a < 251`, `< 502 < 2·251`) needs exactly one
    branchless conditional-subtract of `251`. -/
def modDoubleCom : Com jasminDialect [.reg 64] (.reg 64) :=
  -- t = a + a
  .var { op := .regArith .add 64, retTy_eq := rfl, args := .cons .here (.cons .here .nil) }
  -- c251 = 251
  (.var { op := .regConst 64 251, retTy_eq := rfl, args := .nil }
  -- d = t - c251
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- bit = d >>> 63
  (.var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }
  -- c0 = 0
  (.var { op := .regConst 64 0, retTy_eq := rfl, args := .nil }
  -- m = c0 - bit
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- masked = m & c251
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here
            (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- r = d + masked   (masked=.here at 0, m=1, c0=2, bit=3, d=4)
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) (.cons .here .nil) }
    (.ret .here))))))))

theorem modDoubleCom_ok : ComOK modDoubleCom := by
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  exact ComOK.var (by supported_op) (ComOK.ret _)

/-- **Step 2 — value proof at the source, cheap `rfl`** (all-ALU, no `mul`). The
    source denotes the branchless double-and-conditional-subtract expression. -/
theorem modDoubleCom_denote (a : BitVec 64) :
    Com.denote modDoubleCom (.cons a .nil)
      = ((a + a) - (251 : BitVec 64))
          + (((0 : BitVec 64) - (((a + a) - (251 : BitVec 64)) >>> 63)) &&& (251 : BitVec 64)) :=
  rfl

/-- **The modular spec.** For a reduced input `a.toNat < 251`, the emitted source
    computes `(2 · a) mod 251` — the genuine modular-double value. -/
theorem modDoubleCom_spec (a : BitVec 64) (ha : a.toNat < 251) :
    (Com.denote modDoubleCom (.cons a .nil)).toNat = (2 * a.toNat) % 251 := by
  rw [modDoubleCom_denote]
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

theorem modDoubleCom_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg modDoubleCom 1))).regs)
        (comRetName modDoubleCom 1)
      = Com.denote modDoubleCom V :=
  com_arm_e2e modDoubleCom_ok FieldEmitGoldenPath.allReg64_one V s hs

theorem modDoubleCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg modDoubleCom 1))).regs)
        (comRetName modDoubleCom 1)
      = Com.denote modDoubleCom V :=
  com_riscv_e2e modDoubleCom_ok FieldEmitGoldenPath.allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier): the same source to ELF `.o`. -/
def modDoubleCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 modDoubleCom "field_mod_double251"

/-! ## Op 2 — modular negate `(251 - a) mod 251` -/

/-- `c251 := 251 ; t := c251 - a ; d := t - c251 ; bit := d >>> 63 ; c0 := 0 ;
    m := c0 - bit ; masked := m & c251 ; r := d + masked ; ret r` over arg `[a]`.
    `t = 251 - a` is in `[1, 251]` for `a ∈ [0, 250]`; the trailing
    conditional-subtract maps the `a = 0` case (`t = 251`) to `0` and leaves
    `a > 0` (`t ∈ [1, 251)`) unchanged. -/
def modNegCom : Com jasminDialect [.reg 64] (.reg 64) :=
  -- c251 = 251
  .var { op := .regConst 64 251, retTy_eq := rfl, args := .nil }
  -- t = c251 - a
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- d = t - c251
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- bit = d >>> 63
  (.var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }
  -- c0 = 0
  (.var { op := .regConst 64 0, retTy_eq := rfl, args := .nil }
  -- m = c0 - bit
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- masked = m & c251
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here
            (.cons (.there (.there (.there (.there (.there .here))))) .nil) }
  -- r = d + masked   (masked=0, m=1, c0=2, bit=3, d=4)
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) (.cons .here .nil) }
    (.ret .here))))))))

theorem modNegCom_ok : ComOK modNegCom := by
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  exact ComOK.var (by supported_op) (ComOK.ret _)

/-- **Step 2 — value proof at the source, cheap `rfl`** (all-ALU, no `mul`). -/
theorem modNegCom_denote (a : BitVec 64) :
    Com.denote modNegCom (.cons a .nil)
      = (((251 : BitVec 64) - a) - (251 : BitVec 64))
          + (((0 : BitVec 64) - ((((251 : BitVec 64) - a) - (251 : BitVec 64)) >>> 63))
              &&& (251 : BitVec 64)) :=
  rfl

/-- **The modular spec.** For a reduced input `a.toNat < 251`, the emitted source
    computes `(251 - a) mod 251` — the genuine modular-negate value (`0` at `a = 0`). -/
theorem modNegCom_spec (a : BitVec 64) (ha : a.toNat < 251) :
    (Com.denote modNegCom (.cons a .nil)).toNat = (251 - a.toNat) % 251 := by
  rw [modNegCom_denote]
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

theorem modNegCom_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg modNegCom 1))).regs)
        (comRetName modNegCom 1)
      = Com.denote modNegCom V :=
  com_arm_e2e modNegCom_ok FieldEmitGoldenPath.allReg64_one V s hs

theorem modNegCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg modNegCom 1))).regs)
        (comRetName modNegCom 1)
      = Com.denote modNegCom V :=
  com_riscv_e2e modNegCom_ok FieldEmitGoldenPath.allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier): the same source to ELF `.o`. -/
def modNegCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 modNegCom "field_mod_neg251"

/-! ## Op 3 — constant-time conditional negate `cond ? (251 - a) mod 251 : a` -/

/-- `neg := (251 - a) mod 251` (the `modNegCom` body) then a CT mask-select against
    `a`: `mask := 0 - cond ; r := (neg & mask) | (a & ~mask)`, with `~mask = mask ^
    (2^64-1)`. `cond` is a reg64 `0/1`; `cond = 1 ⇒ mask = all-ones ⇒ r = neg`,
    `cond = 0 ⇒ mask = 0 ⇒ r = a`. Args `[cond, a]`. -/
def condNegCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  -- de Bruijn after entry: cond = .here, a = .there .here
  -- c251 = 251
  .var { op := .regConst 64 251, retTy_eq := rfl, args := .nil }
  -- t = c251 - a         (c251 = .here, a = .there.there.here)
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there .here)) .nil) }
  -- d = t - c251         (t = .here, c251 = .there.here)
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- bit = d >>> 63
  (.var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }
  -- c0 = 0
  (.var { op := .regConst 64 0, retTy_eq := rfl, args := .nil }
  -- mm = c0 - bit        (c0 = .here, bit = .there.here)
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- masked = mm & c251   (mm = .here, c251 = .there^5 .here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here
            (.cons (.there (.there (.there (.there (.there .here))))) .nil) }
  -- neg = d + masked     (masked=0, mm=1, c0=2, bit=3, d=4)
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) (.cons .here .nil) }
  -- mask = c0 - cond     stack: neg=0, masked=1, mm=2, c0=3, bit=4, d=5, t=6,
  --                             c251=7, cond=8, a=9   (c0 = .there^3, cond = .there^8)
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here)))
                    (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) }
  -- ones = 2^64-1
  (.var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- nmask = mask ^ ones   (mask = .there.here, ones = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- nm = neg & mask       (neg = .there^3 .here, mask = .there.there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil) }
  -- am = a & nmask        (a = .there^13 .here, nmask = .there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))
                    (.cons (.there .here) .nil) }
  -- r = nm | am          (nm = .there.here, am = .here)
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here))))))))))))))

theorem condNegCom_ok : ComOK condNegCom := by
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  exact ComOK.var (by supported_op) (ComOK.ret _)

/-- **Step 2 — value proof at the source, cheap `rfl`** (all-ALU, no `mul`). -/
theorem condNegCom_denote (cond a : BitVec 64) :
    Com.denote condNegCom (.cons cond (.cons a .nil))
      = let neg := (((251 : BitVec 64) - a) - (251 : BitVec 64))
            + (((0 : BitVec 64) - ((((251 : BitVec 64) - a) - (251 : BitVec 64)) >>> 63))
                &&& (251 : BitVec 64))
        let mask := (0 : BitVec 64) - cond
        (neg &&& mask) ||| (a &&& (mask ^^^ (18446744073709551615 : BitVec 64))) :=
  rfl

/-- **The conditional-negate spec (the two branches).** For a reduced input
    `a.toNat < 251` and a `0/1` flag `cond`, the emitted source selects between
    the modular negate and the identity: `cond = 1 ⇒ (251 - a) mod 251`,
    `cond = 0 ⇒ a`. -/
theorem condNegCom_spec (cond a : BitVec 64) (ha : a.toNat < 251)
    (hc : cond = 0 ∨ cond = 1) :
    (Com.denote condNegCom (.cons cond (.cons a .nil))).toNat
      = if cond = 1 then (251 - a.toNat) % 251 else a.toNat := by
  rw [condNegCom_denote]
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
    -- cond = 1 ⇒ mask = all-ones ⇒ result = neg = modNeg a
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

theorem condNegCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg condNegCom 2))).regs)
        (comRetName condNegCom 2)
      = Com.denote condNegCom V :=
  com_arm_e2e condNegCom_ok FieldEmitGoldenPath.allReg64_two V s hs

theorem condNegCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg condNegCom 2))).regs)
        (comRetName condNegCom 2)
      = Com.denote condNegCom V :=
  com_riscv_e2e condNegCom_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier): the same source to ELF `.o`. -/
def condNegCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 condNegCom "field_cond_neg251"

end CatCrypt.Crypto.SecureCompilation.FieldModOps
