/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import Std.Tactic.BVDecide

/-!
# Golden path: a constant-time fixed-table gather, emitted through the width-64 path

**This file closes the table-lookup case of the memory gap for the useful instance —
without any backend or memory-model change.** `CtMemoryGoldenPath` packages the
*dialect-level* `stackLoad`/`stackStore` array access and proves it constant-time
*because* the index is public, but it stops at the dialect + CT-analysis level: the
neutral AArch64 / RISC-V `comToReg` backends do not lower the array ops. This file is
the **emitting** alternative for the common case of a *small fixed table whose entries
are compile-time constants* (the S-box / round-constant class).

The idea is the **constant-time gather** (`CMOV`-scan) idiom: a table read `T[i]` is
computed not by a data-dependent address but by **scanning every entry** and selecting
the matching one with a mask —

```
result = OR_k ( T_k &&& eqMask(i, k) )
```

where `T_k := regConst 64 <value>` are the compile-time table constants and
`eqMask(i, k)` is the branchless all-ones-iff-equal mask. The equality mask is built
with no branch and no comparison instruction:

```
d  := i ^^^ k          -- 0 iff i == k
sh := (d ||| (0 - d)) >>> 63   -- 1 iff d != 0  (the is-nonzero bit)
eqMask := sh - 1       -- 0xFF…FF iff i == k, else 0
```

Every op is a width-64 `SupportedOp` (`.regConst`, `.regArith {sub,or,and,xor}`,
`.shrImm`), so the whole scan rides `com_arm_e2e` / `com_riscv_e2e` and the x86 driver
**with no new dialect op, no `RegStmt` primitive, and no backend change** — exactly the
golden-path recipe of `FieldEmitGoldenPath`, only the body is the table scan.

This **is the constant-time way** to do a table lookup: the scan touches *every* entry,
so the memory/address trace is independent of `i` — there is no index-dependent access
to leak. The secret-index case is precisely the one `CtMemoryGoldenPath`'s dual
(`secretIdxLoad_rejected`) and `ArrayLoopCT` show must be rewritten this way; here the
same scan is demonstrated for a **public** index (so the explicit functional spec
`= T[i]` is provable), but the *form* is the register-scan that a secret index demands —
the emitting alternative to a `stackLoad`/memory backend op for a small fixed table.

The worked table is the first four entries of the AES S-box, `[0x63, 0x7c, 0x77, 0x7b]`
(FIPS 197 §5.1.1, the standard AES `SubBytes` substitution table, entries `S[0..3]`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CtTableEmit

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

/-! ## The constant-time fixed-table gather `T[i]` over the 4-entry AES S-box head

Over arg `[i]` (the public index, a `reg 64`). The table `T = [0x63,0x7c,0x77,0x7b]`
(`AES S-box[0..3]`, FIPS 197 §5.1.1) is materialised as four `regConst`. The scan, per
entry `k`: `d_k := i ^ k`; `nd_k := 0 - d_k`; `od_k := d_k | nd_k`; `sh_k := od_k >>> 63`
(`= 1` iff `i ≠ k`); `m_k := sh_k - 1` (`= 0xFF…FF` iff `i = k`); `mk_k := T_k & m_k`.
Then `OR_k mk_k`. Two shared constants `c0 := 0`, `one := 1` are bound once.

All ops are width-64 `SupportedOp` (`regConst`, `regArith {sub,or,and,xor}`, `shrImm`),
so the source emits through the unchanged golden path. -/

/-- The constant-time S-box-head gather as a `Com jasminDialect` over arg `[i]`.
    `c0 := 0 ; one := 1 ;` then per entry `k ∈ {0,1,2,3}`:
    `kc := k ; d := i ^ kc ; nd := c0 - d ; od := d | nd ; sh := od >>> 63 ;
     m := sh - one ; Tc := T_k ; mk := Tc & m ;` finally
    `OR_k mk ; ret`. Every op is a width-64 `SupportedOp`. -/
def ctTableLookupCom : Com jasminDialect [.reg 64] (.reg 64) :=
  -- idx1 c0 = 0
  .var { op := .regConst 64 0, retTy_eq := rfl, args := .nil }
  -- idx2 one = 1
  (.var { op := .regConst 64 1, retTy_eq := rfl, args := .nil }
  -- ===== entry k = 0 =====
  -- idx3 kc0 = 0
  (.var { op := .regConst 64 0, retTy_eq := rfl, args := .nil }
  -- idx4 d0 = i ^ kc0     (i = T(3), kc0 = T(0))
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) (.cons .here .nil) }
  -- idx5 nd0 = c0 - d0    (c0 = T(3), d0 = T(0))
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) (.cons .here .nil) }
  -- idx6 od0 = d0 | nd0   (d0 = T(1), nd0 = T(0))
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- idx7 sh0 = od0 >>> 63 (od0 = T(0))
  (.var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }
  -- idx8 m0 = sh0 - one   (sh0 = T(0), one = T(5))
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil) }
  -- idx9 Tc0 = 0x63
  (.var { op := .regConst 64 99, retTy_eq := rfl, args := .nil }
  -- idx10 mk0 = Tc0 & m0  (Tc0 = T(0), m0 = T(1))
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- ===== entry k = 1 =====
  -- idx11 kc1 = 1
  (.var { op := .regConst 64 1, retTy_eq := rfl, args := .nil }
  -- idx12 d1 = i ^ kc1    (i = T(11), kc1 = T(0))
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
                    (.cons .here .nil) }
  -- idx13 nd1 = c0 - d1   (c0 = T(11), d1 = T(0))
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
                    (.cons .here .nil) }
  -- idx14 od1 = d1 | nd1  (d1 = T(1), nd1 = T(0))
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- idx15 sh1 = od1 >>> 63 (od1 = T(0))
  (.var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }
  -- idx16 m1 = sh1 - one  (sh1 = T(0), one = T(13))
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil) }
  -- idx17 Tc1 = 0x7c
  (.var { op := .regConst 64 124, retTy_eq := rfl, args := .nil }
  -- idx18 mk1 = Tc1 & m1  (Tc1 = T(0), m1 = T(1))
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- ===== entry k = 2 =====
  -- idx19 kc2 = 2
  (.var { op := .regConst 64 2, retTy_eq := rfl, args := .nil }
  -- idx20 d2 = i ^ kc2    (i = T(19), kc2 = T(0))
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))
                    (.cons .here .nil) }
  -- idx21 nd2 = c0 - d2   (c0 = T(19), d2 = T(0))
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))
                    (.cons .here .nil) }
  -- idx22 od2 = d2 | nd2  (d2 = T(1), nd2 = T(0))
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- idx23 sh2 = od2 >>> 63 (od2 = T(0))
  (.var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }
  -- idx24 m2 = sh2 - one  (sh2 = T(0), one = T(21))
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) .nil) }
  -- idx25 Tc2 = 0x77
  (.var { op := .regConst 64 119, retTy_eq := rfl, args := .nil }
  -- idx26 mk2 = Tc2 & m2  (Tc2 = T(0), m2 = T(1))
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- ===== entry k = 3 =====
  -- idx27 kc3 = 3
  (.var { op := .regConst 64 3, retTy_eq := rfl, args := .nil }
  -- idx28 d3 = i ^ kc3    (i = T(27), kc3 = T(0))
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))
                    (.cons .here .nil) }
  -- idx29 nd3 = c0 - d3   (c0 = T(27), d3 = T(0))
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))
                    (.cons .here .nil) }
  -- idx30 od3 = d3 | nd3  (d3 = T(1), nd3 = T(0))
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- idx31 sh3 = od3 >>> 63 (od3 = T(0))
  (.var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }
  -- idx32 m3 = sh3 - one  (sh3 = T(0), one = T(29))
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))) .nil) }
  -- idx33 Tc3 = 0x7b
  (.var { op := .regConst 64 123, retTy_eq := rfl, args := .nil }
  -- idx34 mk3 = Tc3 & m3  (Tc3 = T(0), m3 = T(1))
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- ===== combine =====
  -- idx35 r01 = mk0 | mk1   (mk0 = T(24), mk1 = T(16))
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))
                    (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) .nil) }
  -- idx36 r012 = r01 | mk2  (r01 = T(0), mk2 = T(9))
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons .here
                    (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil) }
  -- idx37 r = r012 | mk3    (r012 = T(0), mk3 = T(2))
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there .here)) .nil) }
    (.ret .here)))))))))))))))))))))))))))))))))))))

/-- `ctTableLookupCom` is in the supported straight-line fragment (37 ops: the two
    shared constants, eight ops × four entries — `regConst`, `xor`, `sub`, `or`,
    `shrImm`, `sub`, `regConst`, `and` — and three combining `or`s). Every op is a
    width-64 `SupportedOp`. -/
theorem ctTableLookupCom_ok : ComOK ctTableLookupCom := by
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  -- entry 0
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  -- entry 1
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  -- entry 2
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  -- entry 3
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  -- combine
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  exact ComOK.ret _

/-- **Step 2 — value proof at the source.** The scan source denotes the explicit
    branchless gather expression: for each entry `k`, `T_k &&& eqMask(i,k)` with
    `eqMask(i,k) = (((i ^ k) ||| (0 - (i ^ k))) >>> 63) - 1`, OR-ed over the four
    entries. A `rfl` after `unfold` (the all-`reg64` ALU ops reduce structurally). -/
theorem ctTableLookupCom_denote (i : BitVec 64) :
    Com.denote ctTableLookupCom (.cons i .nil)
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
  unfold ctTableLookupCom; rfl

/-- **The recognizable table function** `S[0..3] = [0x63, 0x7c, 0x77, 0x7b]`
    (AES S-box head, FIPS 197 §5.1.1). -/
def aesSboxHead (n : Nat) : BitVec 64 :=
  if n = 0 then BitVec.ofNat 64 0x63
  else if n = 1 then BitVec.ofNat 64 0x7c
  else if n = 2 then BitVec.ofNat 64 0x77
  else BitVec.ofNat 64 0x7b

/-- **The non-vacuous correctness result.** For any public index `i < 4`, the emitted
    constant-time gather computes the genuine table value `T[i] = AES S-box[i]`. The
    mask scan really is the lookup: each `eqMask(i,k)` is all-ones exactly at the
    matching entry and zero elsewhere, so the OR selects `T[i]`. Proven by reducing the
    `i.toNat < 4` bound to the four concrete indices `i ∈ {0,1,2,3}` (each a BitVec
    equality via `BitVec.eq_of_toNat_eq`) and evaluating the scan at each. -/
theorem ctTableLookupCom_spec (i : BitVec 64) (h : i.toNat < 4) :
    Com.denote ctTableLookupCom (.cons i .nil) = aesSboxHead i.toNat := by
  rw [ctTableLookupCom_denote]
  have hcase : i = 0#64 ∨ i = 1#64 ∨ i = 2#64 ∨ i = 3#64 := by
    rcases (show i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 by omega)
      with hk | hk | hk | hk <;>
      first
        | exact Or.inl (BitVec.eq_of_toNat_eq (by rw [hk]; decide))
        | exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by rw [hk]; decide)))
        | exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by rw [hk]; decide))))
        | exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq (by rw [hk]; decide))))
  rcases hcase with rfl | rfl | rfl | rfl <;> rfl

/-! ## The emit quartet — the gather rides the unchanged golden path

`ctTableLookupCom` is over the single-input context `[.reg 64]`; the all-`reg 64`
witness is `FieldEmitGoldenPath.allReg64_one` and the per-input register valuation is
`envOf 1`. Both verified backends (and the x86 driver) emit it through the *same*
`comToReg_faithful` as the field kernels — no new machinery for the table gather. -/

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem ctTableLookupCom_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg ctTableLookupCom 1))).regs)
        (comRetName ctTableLookupCom 1)
      = Com.denote ctTableLookupCom V :=
  com_arm_e2e ctTableLookupCom_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, discharged by the same `comToReg_faithful`. -/
theorem ctTableLookupCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg ctTableLookupCom 1))).regs)
        (comRetName ctTableLookupCom 1)
      = Com.denote ctTableLookupCom V :=
  com_riscv_e2e ctTableLookupCom_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier, as the field golden path): the same
    `Com` source to ELF `.o` bytes via the generic driver. -/
def ctTableLookupCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 ctTableLookupCom "ct_table_lookup"

end CatCrypt.Crypto.SecureCompilation.CtTableEmit
