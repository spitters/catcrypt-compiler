/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.Mpn.Submul132Emit
public import CatCrypt.Crypto.Jasmin.Mpn.Add32Refines
public import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
public import CatCrypt.Crypto.Jasmin.Mpn.Submul1Prototype
public import CatCrypt.Crypto.Jasmin.Mpn.GenericWidth
public import CatCrypt.Crypto.Jasmin.Mpn.WidthInstances
public import CatCrypt.Crypto.Jasmin.BignumExec

@[expose] public section

set_option autoImplicit false

/-!
# `mpn_submul_1` Jasmin refinement at **U32 limb width**

The U32 MULX-then-SUB-existing mirror of
`Mpn.Submul1Prototype.MpnSubmul1JasminRefines`: the emitted U32
`mpn_submul_1_32` Jasmin kernel
(`Mpn.Submul132Emit.mpnSubmul132Fd`, body `bodySubmul32`) refines a U32
functional spec `mpnSubmul132` over byte memory at 4-byte stride.

The body shape per iteration (mirroring U64 `loopBodySubmul` with U32
arithmetic):

```
t       = [:u32 ap + 0];
hi, lo  = #MULX_32(b, t);
_, c1, _,_,_, lo  = #ADD_32(lo, cy);
w       = [:u32 op + 0];
_, b2, _,_,_, dlo = #SUB_32(w, lo);
[:u32 op + 0] = dlo;
cy = hi + c1;
cy = cy + b2;
ap += 4; op += 4; n -= 1;
```

All limb data (`t`, `hi`, `lo`, `w`, `dlo`, `c1`, `b2`, `cy`) live in
u32 registers — `BitVec 64` values with the high half zero.

## Specification

`MpnGenericWidth` does not define a width-parametric `mpnSubmulW`, so
we define `submul1Step32 : BitVec 32 → BitVec 32 → BitVec 32 →
BitVec 32 → BitVec 32 × BitVec 32` and `mpnSubmul132` locally,
following the shape of `Mpn.Submul1Prototype.submul1Step` /
`mpnSubmul1` at width 32.

## Scope

This file proves the **state-tracking bridge** — the emitted U32 loop
realises the pure `mpnSubmul132` over byte memory.  The *arithmetic
correctness* of `submul1Step32` (the U32 analogue of
`Mpn.Submul1Prototype.submul1Step_spec`) is a separate theorem and is
not needed by this bridge — it is left as future work alongside a
width-parametric `mpnSubmulW` spec.

## Reused U32 leaves (from `MpnAdd32Refines`)

* `memHoldsLimbs32`, `memHoldsLimbs32_store32_range_frame` — limb-list
  memory predicate and its frame lemma
* `resolveAddr_vr64` — address plumbing

## Reused stride-parametric helpers (from `MpnAddPrototype`)

* `regAddr_advance_at`, `range_op_head_tail_disjoint_4`,
  `bignumExecFuel_loop_step_generic`, `bignumExecFuel_loop_exit_generic`,
  `evalPExpr_neq_zero_true`, `evalPExpr_neq_zero_false`,
  `ofNat64_succ_ne_zero`, `ofNat64_succ_sub_one`, `disjoint_range_lt`,
  `disjoint_mono`, `storeMem32_mem_proj`, `storeMem32_regs_proj`
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.Submul132Refines

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.Submul132Emit
open CatCrypt.Crypto.Jasmin.Mpn.Add32Refines
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype

/-- Promote a `BitVec 32` to `BitVec 64` by zero-extension.  Mirrors
    `Mpn.Add32Refines.w64` (which is `private`). -/
def w64 (w : BitVec 32) : BitVec 64 := BitVec.ofNat 64 w.toNat

/-- The local `u32_load_roundtrip`: loading a `BitVec 32` limb from memory
    via `load32Mem` and decoding through `BitVec.ofNat 64 _.toNat`
    recovers `w64 w`.  Mirror of `Mpn.Add32Refines.u32_load_roundtrip`. -/
theorem u32_load_roundtrip' (w : BitVec 32) :
    BitVec.ofNat 64 (UInt64.ofNat w.toNat).toNat = w64 w := by
  have hw : w.toNat < 2 ^ 32 := w.isLt
  apply BitVec.eq_of_toNat_eq
  unfold w64
  simp only [BitVec.toNat_ofNat, UInt64.toNat_ofNat']
  omega

/-! ## §1  Directly provable facts about the emitted U32 kernel -/

/-- The emitted U32 `mpn_submul_1_32` body is constant-time-shaped. -/
theorem bodySubmul32_isCT : isCT_Cmd bodySubmul32 = true := by decide

/-- The U32 `FunDecl`'s body is literally `bodySubmul32`. -/
theorem mpnSubmul132Fd_body : mpnSubmul132Fd.body = bodySubmul32 := rfl

/-! ## §2  U32 pure functional spec — `submul1Step32` and `mpnSubmul132`

Mirror of `Mpn.Submul1Prototype.submul1Step` and `mpnSubmul1` at limb
width 32.  We *define* the step in terms of the executable intrinsics
`mulx32` / `addCarry32` / `subBorrow32` on `BitVec 64` registers, then
project the low 32 bits.  This makes the iteration step lemma a
straightforward state-tracking computation. -/

/-- One `mpn_submul_1` step on `BitVec 32` limb data, threading a u32
    carry stored in a `BitVec 64` register (the high half is unused —
    the executable intrinsics only consume `_ &&& mask32`).  Returns
    the pair `(out_limb_64, carry_out_64)` of `BitVec 64` values; the
    out-limb is masked to 32 bits by construction
    (`subBorrow32` returns `_ &&& mask32`).  The carry-out is the raw
    `BitVec 64` sum `hi + c1 + b2`; it lies in `BitVec 64` masked-u32
    form (proved by the U32 schoolbook bound, the analogue of
    `Mpn.Submul1Prototype.submul1Step_spec`), but the bridge does not
    need to dereference that fact. -/
noncomputable def submul1Step32 (out a : BitVec 32) (b cy : BitVec 64) :
    BitVec 64 × BitVec 64 :=
  let p := mulx32 b (w64 a)
  let q := addCarry32 p.2 cy
  let r := subBorrow32 (w64 out) q.2
  (r.2, p.1 + q.1 + r.1)

/-- Pure reference for U32 `mpn_submul_1`.  Threads a `BitVec 64`
    masked-u32 carry across the limb list.  The output limbs are also
    `BitVec 64` masked-u32 (the natural representation of u32 values
    on a u64 register). -/
noncomputable def mpnSubmul132 : List (BitVec 32) → List (BitVec 32) →
    BitVec 64 → BitVec 64 → (List (BitVec 64) × BitVec 64)
  | o :: os, a :: as, b, cy =>
      let s := submul1Step32 o a b cy
      let t := mpnSubmul132 os as b s.2
      (s.1 :: t.1, t.2)
  | _, _, _, cy => ([], cy)

/-- The result limb of one U32 submul1 step is masked to 32 bits (it
    is the `.2` projection of `subBorrow32`, which has `&&& mask32` as
    its final step). -/
theorem submul1Step32_limbFitsU32 (out a : BitVec 32) (b cy : BitVec 64) :
    (submul1Step32 out a b cy).1.toNat < 2 ^ 32 := by
  unfold submul1Step32 subBorrow32 mask32
  simp only [BitVec.toNat_and,
             show (0xFFFFFFFF : BitVec 64).toNat = (2 ^ 32 - 1) from by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

/-! ## §2b  U32 schoolbook arithmetic spec

The U32 analogue of `Mpn.Submul1Prototype.submul1Step_spec` /
`mpnSubmul1_spec`, mirroring the structure used by `MpnMul132Refines`
for `mul_1`.  The arithmetic identity per step is

```
(submul1Step32 out a b cy).1.toNat + a.toNat · b.toNat + cy.toNat
  = out.toNat + 2^32 · (submul1Step32 out a b cy).2.toNat
```

The carry register's `toNat` fits in u32 (the `carryFitsU32` bound),
mirroring the GMP / Intel `MULX_32` + `ADD_32` + `SUB_32` semantics:
`hi + c1 + b2 < 2^32`.

Proof strategy mirrors `submul1Step_spec`:
1. mulx32: `lo + 2^32·hi = b · a`
2. addCarry32: `lo' + 2^32·c1 = (lo & mask32) + (cy & mask32)`
3. subBorrow32: `dlo + (lo' & mask32) = (out & mask32) + 2^32·b2`
4. Combine + `dlo ≥ 0`, `out < 2^32` to get `hi + c1 + b2 < 2^32`. -/

/-- The `subBorrow32` identity on masked inputs.  `dlo + (b & mask32).toNat
    = (a & mask32).toNat + 2^32 · borrow`.  Mirrors
    `Mpn.Submul1Prototype.subBorrow_spec` at u32. -/
theorem subBorrow32_spec (a b : BitVec 64) :
    (subBorrow32 a b).2.toNat + (b &&& mask32).toNat
      = (a &&& mask32).toNat + 2 ^ 32 * (subBorrow32 a b).1.toNat := by
  unfold subBorrow32
  set am : BitVec 64 := a &&& mask32 with ham
  set bm : BitVec 64 := b &&& mask32 with hbm
  have ham_lt : am.toNat < 2 ^ 32 := by
    rw [ham]
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hbm_lt : bm.toNat < 2 ^ 32 := by
    rw [hbm]
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
  simp only [BitVec.toNat_and, BitVec.toNat_sub,
             show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  -- collapse outer `% 2^64 % 2^32` to just `% 2^32` (since `2^32 ∣ 2^64`).
  have hmod_collapse : ∀ x, x % 2 ^ 64 % 2 ^ 32 = x % 2 ^ 32 := by
    intro x
    rw [Nat.mod_mod_of_dvd _ (by rw [h64]; exact Dvd.intro (2 ^ 32) rfl)]
  rw [hmod_collapse]
  simp only [BitVec.ult, decide_eq_true_eq]
  by_cases hlt : am.toNat < bm.toNat
  · -- Underflow: `am - bm` wraps as `2^64 + am - bm`, which mod `2^32` = `am + 2^32 - bm`.
    have hwrap : (2 ^ 64 - bm.toNat + am.toNat) % 2 ^ 32 = am.toNat + 2 ^ 32 - bm.toNat := by
      have hkey : 2 ^ 64 - bm.toNat + am.toNat
            = (am.toNat + 2 ^ 32 - bm.toNat) + (2 ^ 32) * (2 ^ 32 - 1) := by
        omega
      rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hwrap]
    simp only [hlt, if_true,
               show ((1 : BitVec 64).toNat) = 1 from rfl]
    omega
  · -- No underflow: `am - bm + 2^64` < 2^64 only after mod; result is `am - bm`.
    have hge : am.toNat ≥ bm.toNat := by omega
    have hnowrap : (2 ^ 64 - bm.toNat + am.toNat) % 2 ^ 32 = am.toNat - bm.toNat := by
      have hkey : 2 ^ 64 - bm.toNat + am.toNat
            = (am.toNat - bm.toNat) + (2 ^ 32) * (2 ^ 32) := by
        -- bm ≤ am < 2^32 ≤ 2^64.
        omega
      rw [hkey, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hnowrap]
    have hbm_le : bm.toNat ≤ am.toNat := hge
    simp only [show ¬ am.toNat < bm.toNat from hlt, if_false,
               show ((0 : BitVec 64).toNat) = 0 from rfl]
    omega

/-- The `subBorrow32` borrow-out is at most 1. -/
theorem subBorrow32_borrow_le (a b : BitVec 64) : (subBorrow32 a b).1.toNat ≤ 1 := by
  show (if ((a &&& mask32).ult (b &&& mask32) = true) then (1 : BitVec 64) else 0).toNat ≤ 1
  split_ifs <;> simp

/-- The masked low word of `subBorrow32` is `< 2^32` (the `.2` is already
    masked, but stated as `toNat` for re-use). -/
theorem subBorrow32_lo_lt (a b : BitVec 64) :
    (subBorrow32 a b).2.toNat < 2 ^ 32 := by
  unfold subBorrow32
  simp only [BitVec.toNat_and,
             show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

/-- The masked low word of `addCarry32` is `< 2^32`. -/
theorem addCarry32_lo_lt (a b : BitVec 64) :
    (addCarry32 a b).2.toNat < 2 ^ 32 := by
  unfold addCarry32
  simp only [BitVec.toNat_and,
             show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

/-- The low word of `mulx32` is `< 2^32`. -/
theorem mulx32_lo_lt (a b : BitVec 64) :
    (mulx32 a b).2.toNat < 2 ^ 32 := by
  unfold mulx32
  simp only [BitVec.toNat_and,
             show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

/-- `w64`-mask: a `BitVec 32` zero-extended to `BitVec 64` is fixed by `&&& mask32`. -/
theorem w64_mask (w : BitVec 32) : (w64 w) &&& mask32 = w64 w := by
  unfold w64 mask32
  have hzx : (BitVec.ofNat 64 w.toNat) = BitVec.setWidth 64 w := by
    apply BitVec.eq_of_toNat_eq
    have hw : w.toNat < 2 ^ 32 := w.isLt
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  rw [hzx]
  bv_decide

/-- The `BitVec 64` denotation of `w64 w` equals `w.toNat`. -/
theorem w64_toNat (w : BitVec 32) : (w64 w).toNat = w.toNat := by
  unfold w64
  have hw : w.toNat < 2 ^ 32 := w.isLt
  simp only [BitVec.toNat_ofNat]
  omega

/-- Mirror of `Mpn.Mul132Refines.mulx32_hi_le`: high word of `mulx32` is
    bounded.  Restated for any `BitVec 64` inputs whose masked toNats fit
    in u32 (which is automatic — the function masks).  -/
theorem mulx32_hi_le_general (a b : BitVec 64) :
    (mulx32 a b).1.toNat ≤ 2 ^ 32 - 2 := by
  have ham_lt : (a &&& mask32).toNat < 2 ^ 32 := by
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hbm_lt : (b &&& mask32).toNat < 2 ^ 32 := by
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  unfold mulx32
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight]
  set am : BitVec 64 := a &&& mask32 with ham
  set bm : BitVec 64 := b &&& mask32 with hbm
  -- (am * bm) on BitVec 64: since both < 2^32, the product fits in 2^64.
  have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
  have hmul_lt : am.toNat * bm.toNat < 2 ^ 64 := by
    have := Nat.mul_lt_mul'' ham_lt hbm_lt; omega
  have hmul_eq : (am * bm).toNat = am.toNat * bm.toNat := by
    simp only [BitVec.toNat_mul, Nat.mod_eq_of_lt hmul_lt]
  rw [hmul_eq]
  rw [Nat.shiftRight_eq_div_pow]
  rw [show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have hp_le : am.toNat * bm.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hdiv_le : am.toNat * bm.toNat / 2 ^ 32 ≤ 2 ^ 32 - 2 := by
    calc am.toNat * bm.toNat / 2 ^ 32
        ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right hp_le
      _ = 2 ^ 32 - 2 := by norm_num
  rw [Nat.mod_eq_of_lt (by omega)]
  exact hdiv_le

/-- Mirror of `Mpn.Mul132Refines.mulx32_toNat`: full product identity. -/
theorem mulx32_toNat_general (a b : BitVec 64) :
    (mulx32 a b).2.toNat + 2 ^ 32 * (mulx32 a b).1.toNat
      = (a &&& mask32).toNat * (b &&& mask32).toNat := by
  have ham_lt : (a &&& mask32).toNat < 2 ^ 32 := by
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hbm_lt : (b &&& mask32).toNat < 2 ^ 32 := by
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  unfold mulx32
  set am : BitVec 64 := a &&& mask32 with ham
  set bm : BitVec 64 := b &&& mask32 with hbm
  have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
  have hmul_lt : am.toNat * bm.toNat < 2 ^ 64 := by
    have := Nat.mul_lt_mul'' ham_lt hbm_lt; omega
  have hmul_eq : (am * bm).toNat = am.toNat * bm.toNat := by
    simp only [BitVec.toNat_mul, Nat.mod_eq_of_lt hmul_lt]
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, hmul_eq,
             show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod _ 32,
      Nat.and_two_pow_sub_one_eq_mod _ 32,
      Nat.shiftRight_eq_div_pow]
  have hdiv_lt : am.toNat * bm.toNat / 2 ^ 32 < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
  rw [Nat.mod_eq_of_lt hdiv_lt]
  omega

/-- Carry-out of `addCarry32` is at most 1. -/
theorem addCarry32_carry_le_general (a b : BitVec 64) : (addCarry32 a b).1.toNat ≤ 1 := by
  unfold addCarry32
  simp only [BitVec.toNat_and,
             show ((1 : BitVec 64).toNat) = 1 from rfl]
  rw [Nat.and_two_pow_sub_one_eq_mod _ 1]
  omega

/-- `addCarry32` identity in masked-input form: `lo' + 2^32·cf = am + bm`. -/
theorem addCarry32_spec_masked (a b : BitVec 64) :
    (addCarry32 a b).2.toNat + 2 ^ 32 * (addCarry32 a b).1.toNat
      = (a &&& mask32).toNat + (b &&& mask32).toNat := by
  unfold addCarry32
  set am : BitVec 64 := a &&& mask32 with ham
  set bm : BitVec 64 := b &&& mask32 with hbm
  have ham_lt : am.toNat < 2 ^ 32 := by
    rw [ham]
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hbm_lt : bm.toNat < 2 ^ 32 := by
    rw [hbm]
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
  have hsum_lt : am.toNat + bm.toNat < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ushiftRight,
             show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide,
             show ((1 : BitVec 64).toNat) = 1 from rfl]
  rw [Nat.mod_eq_of_lt hsum_lt,
      Nat.and_two_pow_sub_one_eq_mod (am.toNat + bm.toNat) 32,
      Nat.and_two_pow_sub_one_eq_mod _ 1, Nat.shiftRight_eq_div_pow]
  have hdiv_lt : (am.toNat + bm.toNat) / 2 ^ 32 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    omega
  rw [show (2 : Nat) ^ 1 = 2 from rfl, Nat.mod_eq_of_lt hdiv_lt]
  omega

/-- **U32 schoolbook arithmetic identity.**  One `submul1Step32` satisfies
    `o' + a·b + cy = out + 2^32·cy'`, exactly as in
    `Mpn.Submul1Prototype.submul1Step_spec` at u64.  Requires the u64-encoded
    inputs `b`, `cy` to actually fit in u32 (which holds in the loop where
    `cy` is initialised to 0 and threaded through `submul1Step32` outputs). -/
theorem submul1Step32_spec (out a : BitVec 32) (b cy : BitVec 64)
    (hb_u32 : b.toNat < 2 ^ 32) (hcy_u32 : cy.toNat < 2 ^ 32) :
    (submul1Step32 out a b cy).1.toNat + a.toNat * b.toNat + cy.toNat
      = out.toNat + 2 ^ 32 * (submul1Step32 out a b cy).2.toNat := by
  -- Unfold the projections.
  rw [show (submul1Step32 out a b cy).1
        = (subBorrow32 (w64 out) (addCarry32 (mulx32 b (w64 a)).2 cy).2).2 from rfl,
      show (submul1Step32 out a b cy).2
        = (mulx32 b (w64 a)).1 + (addCarry32 (mulx32 b (w64 a)).2 cy).1
            + (subBorrow32 (w64 out) (addCarry32 (mulx32 b (w64 a)).2 cy).2).1 from rfl]
  set hi := (mulx32 b (w64 a)).1 with hhi
  set lo := (mulx32 b (w64 a)).2 with hlo
  set c1 := (addCarry32 lo cy).1 with hc1
  set lo1 := (addCarry32 lo cy).2 with hlo1
  set b2 := (subBorrow32 (w64 out) lo1).1 with hb2
  set dlo := (subBorrow32 (w64 out) lo1).2 with hdlo
  -- mulx32: lo + 2^32·hi = (b & mask32).toNat · (w64 a & mask32).toNat.
  have hmulx := mulx32_toNat_general b (w64 a)
  rw [← hhi, ← hlo] at hmulx
  -- `b & mask32` = b (b < 2^32).
  have hb_mask : (b &&& mask32).toNat = b.toNat := by
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hb_u32]
  have hwa_mask : ((w64 a) &&& mask32).toNat = a.toNat := by
    rw [w64_mask a, w64_toNat]
  rw [hb_mask, hwa_mask] at hmulx
  -- lo bounds.
  have hlo_lt : lo.toNat < 2 ^ 32 := by rw [hlo]; exact mulx32_lo_lt _ _
  -- addCarry32: lo1 + 2^32·c1 = (lo & mask32).toNat + (cy & mask32).toNat
  have hadd := addCarry32_spec_masked lo cy
  rw [← hc1, ← hlo1] at hadd
  have hlo_mask : (lo &&& mask32).toNat = lo.toNat := by
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlo_lt]
  have hcy_mask : (cy &&& mask32).toNat = cy.toNat := by
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hcy_u32]
  rw [hlo_mask, hcy_mask] at hadd
  -- lo1 bounds.
  have hlo1_lt : lo1.toNat < 2 ^ 32 := by rw [hlo1]; exact addCarry32_lo_lt _ _
  -- subBorrow32: dlo + (lo1 & mask32) = ((w64 out) & mask32) + 2^32·b2
  have hsub := subBorrow32_spec (w64 out) lo1
  rw [← hb2, ← hdlo] at hsub
  have hwout_mask : ((w64 out) &&& mask32).toNat = out.toNat := by
    rw [w64_mask out, w64_toNat]
  have hlo1_mask : (lo1 &&& mask32).toNat = lo1.toNat := by
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlo1_lt]
  rw [hwout_mask, hlo1_mask] at hsub
  -- Bounds.
  have hc1le : c1.toNat ≤ 1 := by rw [hc1]; exact addCarry32_carry_le_general lo cy
  have hb2le : b2.toNat ≤ 1 := by rw [hb2]; exact subBorrow32_borrow_le _ _
  have hhile : hi.toNat ≤ 2 ^ 32 - 2 := by rw [hhi]; exact mulx32_hi_le_general b (w64 a)
  -- dlo and out bounds.
  have hdlobound : dlo.toNat < 2 ^ 32 := by rw [hdlo]; exact subBorrow32_lo_lt _ _
  have houtbound : out.toNat < 2 ^ 32 := out.isLt
  have habound : a.toNat < 2 ^ 32 := a.isLt
  -- a·b ≤ (2^32-1)·(2^32-1).
  have ha_le : a.toNat ≤ 2 ^ 32 - 1 := by omega
  have hb_le : b.toNat ≤ 2 ^ 32 - 1 := by omega
  have hprodle : a.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul ha_le hb_le
  -- Combined identity.
  have hcombine : dlo.toNat + a.toNat * b.toNat + cy.toNat
      = out.toNat + 2 ^ 32 * (hi.toNat + c1.toNat + b2.toNat) := by
    -- hmulx: lo + 2^32·hi = b · a
    -- hadd : lo1 + 2^32·c1 = lo + cy
    -- hsub : dlo + lo1 = out + 2^32·b2
    -- Sum: dlo + 2^32·b2 + 2^32·c1 + 2^32·hi = out + lo + 2^32·c1 + 2^32·hi
    --                                       = out + (lo + 2^32·hi) + 2^32·c1
    --                                       = out + b·a + 2^32·c1
    -- and lo + cy = lo1 + 2^32·c1, so cy = lo1 + 2^32·c1 - lo.  Substitute...
    -- Simpler: linear combination of hmulx, hadd, hsub by 1 each.
    have hba : a.toNat * b.toNat = b.toNat * a.toNat := by ring
    rw [hba]
    omega
  -- Carry-fits-u32 bound.
  have hcarrybound : hi.toNat + c1.toNat + b2.toNat < 2 ^ 32 := by
    have hnum : (2 ^ 32 - 1) * (2 ^ 32 - 1) = 2 ^ 64 - 2 ^ 33 + 1 := by norm_num
    -- 2^32·(hi+c1+b2) = dlo + a·b + cy - out
    --                 ≤ (2^32 - 1) + (2^32-1)·(2^32-1) + (2^32-1) - 0
    --                 = 2·(2^32-1) + (2^32-1)² < 2^64
    -- a·b ≤ (2^32-1)² via hprodle.
    have hkey : 2 ^ 32 * (hi.toNat + c1.toNat + b2.toNat)
              = dlo.toNat + a.toNat * b.toNat + cy.toNat - out.toNat := by omega
    omega
  -- The three-summand sum never wraps.
  have hhc1 : (hi + c1).toNat = hi.toNat + c1.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
      omega)]
  have hsum : (hi + c1 + b2).toNat = hi.toNat + c1.toNat + b2.toNat := by
    rw [BitVec.toNat_add, hhc1, Nat.mod_eq_of_lt (by
      have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
      omega)]
  rw [hsum]
  omega

/-- **Carry-fits-u32 bound** for `submul1Step32`.  Mirror of
    `submul1Step_spec`'s implicit carry-bound discharge at u32: the
    three-summand register `hi + c1 + b2` fits in `2^32` whenever the
    inputs are u32-encoded (`b.toNat < 2^32`, `cy.toNat < 2^32`). -/
theorem submul1Step32_carryFitsU32 (out a : BitVec 32) (b cy : BitVec 64)
    (hb_u32 : b.toNat < 2 ^ 32) (hcy_u32 : cy.toNat < 2 ^ 32) :
    (submul1Step32 out a b cy).2.toNat < 2 ^ 32 := by
  -- From the spec: o' + a·b + cy = out + 2^32·cy', with o' < 2^32, out < 2^32,
  -- a·b ≤ (2^32-1)², cy < 2^32 ⇒ 2^32·cy' < (2^32-1)² + 2·(2^32-1) < 2^64.
  have hspec := submul1Step32_spec out a b cy hb_u32 hcy_u32
  have ho'_lt : (submul1Step32 out a b cy).1.toNat < 2 ^ 32 :=
    submul1Step32_limbFitsU32 out a b cy
  have hout_lt : out.toNat < 2 ^ 32 := out.isLt
  have ha_lt : a.toNat < 2 ^ 32 := a.isLt
  have hab_le : a.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hnum : (2 ^ 32 - 1) * (2 ^ 32 - 1) = 2 ^ 64 - 2 ^ 33 + 1 := by norm_num
  -- 2^32·cy' ≤ (2^32-1) + (2^32-1)² + (2^32-1) = (2^32-1)² + 2·(2^32-1) < 2^64,
  -- so cy' < 2^32.
  omega

/-! ### Little-endian denotation for masked-u32 limb lists -/

/-- Little-endian denotation over base `2^32` for a list of `BitVec 64`
    masked-u32 limbs.  Equals `Mpn.GenericWidth.toNatW 32 _` when the
    limbs are mapped to `BitVec 32`, but stated directly for the
    `BitVec 64`-valued result of `mpnSubmul132`. -/
def toNatU32 : List (BitVec 64) → Nat
  | []      => 0
  | x :: xs => x.toNat + 2 ^ 32 * toNatU32 xs

@[simp] theorem toNatU32_nil : toNatU32 [] = 0 := rfl

@[simp] theorem toNatU32_cons (x : BitVec 64) (xs : List (BitVec 64)) :
    toNatU32 (x :: xs) = x.toNat + 2 ^ 32 * toNatU32 xs := rfl

/-- Little-endian denotation for `List (BitVec 32)` at base `2^32`. -/
def toNat32 : List (BitVec 32) → Nat
  | []      => 0
  | x :: xs => x.toNat + 2 ^ 32 * toNat32 xs

@[simp] theorem toNat32_nil : toNat32 [] = 0 := rfl

@[simp] theorem toNat32_cons (x : BitVec 32) (xs : List (BitVec 32)) :
    toNat32 (x :: xs) = x.toNat + 2 ^ 32 * toNat32 xs := rfl

/-- The carry threaded through `mpnSubmul132` stays in u32 form, provided
    the inputs `b` and the initial `cy` were u32.  Used to discharge the
    per-step `cy_u32` precondition in the inductive arithmetic spec. -/
theorem mpnSubmul132_cy_u32 :
    ∀ (out as : List (BitVec 32)) (b cy : BitVec 64),
      out.length = as.length → b.toNat < 2 ^ 32 → cy.toNat < 2 ^ 32 →
      (mpnSubmul132 out as b cy).2.toNat < 2 ^ 32 := by
  intro out
  induction out with
  | nil =>
    intro as b cy hlen _ hcy
    cases as with
    | cons _ _ => simp at hlen
    | nil => simpa [mpnSubmul132] using hcy
  | cons o os ih =>
    intro as b cy hlen hb hcy
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have hlen' : os.length = as.length := by simpa using hlen
      have hstep := submul1Step32_carryFitsU32 o a b cy hb hcy
      simp only [mpnSubmul132]
      exact ih as b (submul1Step32 o a b cy).2 hlen' hb hstep

/-- **Multi-precision arithmetic spec.**  The denotation of the output
    limbs plus `toNat32 a · b` equals `toNat32 out` plus the carry-out
    shifted to bit `32·|a|`.  Mirror of
    `Mpn.Submul1Prototype.mpnSubmul1_spec` at width 32. -/
theorem mpnSubmul132_spec :
    ∀ (out as : List (BitVec 32)) (b cy : BitVec 64),
      out.length = as.length → b.toNat < 2 ^ 32 → cy.toNat < 2 ^ 32 →
      toNatU32 (mpnSubmul132 out as b cy).1 + toNat32 as * b.toNat + cy.toNat
      = toNat32 out + (2 ^ 32) ^ as.length * (mpnSubmul132 out as b cy).2.toNat := by
  intro out
  induction out with
  | nil =>
    intro as b cy hlen _ _
    cases as with
    | cons _ _ => simp at hlen
    | nil => simp [mpnSubmul132]
  | cons o os ih =>
    intro as b cy hlen hb hcy
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have hlen' : os.length = as.length := by simpa using hlen
      set p := submul1Step32 o a b cy with hp
      have hstep := submul1Step32_spec o a b cy hb hcy
      rw [← hp] at hstep
      have hp_cy : p.2.toNat < 2 ^ 32 := by
        rw [hp]; exact submul1Step32_carryFitsU32 o a b cy hb hcy
      set q := mpnSubmul132 os as b p.2 with hq
      have htail := ih as b p.2 hlen' hb hp_cy
      rw [← hq] at htail
      have hunfold : mpnSubmul132 (o :: os) (a :: as) b cy = (p.1 :: q.1, q.2) := by
        simp only [mpnSubmul132, hp, hq]
      rw [hunfold]
      simp only [toNatU32_cons, toNat32_cons, List.length_cons]
      have hpow : (2 ^ 32) ^ (as.length + 1) = 2 ^ 32 * (2 ^ 32) ^ as.length := by
        rw [pow_succ]; ring
      rw [hpow]
      -- IH scaled by 2^32 + head step close the linear goal.
      have hkey : 2 ^ 32 * toNatU32 q.1 + 2 ^ 32 * (toNat32 as * b.toNat) + 2 ^ 32 * p.2.toNat
          = 2 ^ 32 * toNat32 os + 2 ^ 32 * ((2 ^ 32) ^ as.length * q.2.toNat) := by
        have := congrArg (2 ^ 32 * ·) htail
        simpa [Nat.mul_add, Nat.add_assoc] using this
      have hmono : 2 ^ 32 * (2 ^ 32) ^ as.length * q.2.toNat
          = 2 ^ 32 * ((2 ^ 32) ^ as.length * q.2.toNat) := by ring
      rw [hmono]
      have hexpand : (a.toNat + 2 ^ 32 * toNat32 as) * b.toNat
          = a.toNat * b.toNat + 2 ^ 32 * (toNat32 as * b.toNat) := by ring
      rw [hexpand]
      omega

/-- The usual entry point: carry-in 0.  -/
theorem mpnSubmul132_spec_carryIn_zero (out as : List (BitVec 32))
    (hlen : out.length = as.length) (b : BitVec 64) (hb_u32 : b.toNat < 2 ^ 32) :
    toNatU32 (mpnSubmul132 out as b 0).1 + toNat32 as * b.toNat
      = toNat32 out + (2 ^ 32) ^ as.length * (mpnSubmul132 out as b 0).2.toNat := by
  have h := mpnSubmul132_spec out as b 0 hlen hb_u32 (by decide)
  simpa using h

/-! ## §3  U32 per-iteration step lemma

Per-iteration state update for `loopBodySubmul32`.  Mirror of the U64
`Mpn.Submul1Prototype.bignumExec_loopBodySubmul_step` at limb width 32. -/

/-- `loopBodySubmul32` is straight-line. -/
theorem loopBodySubmul32_straightLine : InstrR.bodyIsStraightLine loopBodySubmul32 := by
  simp only [loopBodySubmul32, load32At0, mulxCopn32, addCopn32, subCopn32,
             store32At0, regAdd32, ptrImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBodySubmul32` is non-control. -/
theorem loopBodySubmul32_nonControl : ∀ i ∈ loopBodySubmul32, i.isNonControl := by
  intro i hi
  simp only [loopBodySubmul32, load32At0, mulxCopn32, addCopn32, subCopn32,
             store32At0, regAdd32, ptrImm, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

set_option maxHeartbeats 1200000 in
set_option linter.unusedSimpArgs false in
theorem bignumExec_loopBodySubmul32_step (s : BignumState)
    (out a : BitVec 32) (b cy : BitVec 64)
    (hb : s.regs "b" = b)
    (hcy : s.regs "cy" = cy)
    (hap_mem : load32Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hop_mem : load32Mem s.mem (regAddr s "op") = some (UInt64.ofNat out.toNat)) :
    ∃ s', bignumExec loopBodySubmul32 s = some s' ∧
      s'.mem = Mem.store32 s.mem (regAddr s "op")
        (UInt64.ofNat (submul1Step32 out a b cy).1.toNat) ∧
      s'.regs "cy" = (submul1Step32 out a b cy).2 ∧
      s'.regs "ap" = s.regs "ap" + 4 ∧
      s'.regs "op" = s.regs "op" + 4 ∧
      s'.regs "n" = s.regs "n" - 1 ∧
      s'.regs "b" = s.regs "b" := by
  simp only [loopBodySubmul32, load32At0, mulxCopn32, addCopn32, subCopn32,
             store32At0, regAdd32, ptrImm,
             bignumExec, execInstr, evalPExpr, pv32, pv64,
             resolveAddr_vr64, vr32, vr64,
             setReg_mem, setReg_regs, storeMem32_mem_proj, storeMem32_regs_proj,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append,
             writeMulxBundle, writeSubBundle]
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem32_regs_proj, storeMem32_mem_proj,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             hap_mem, hop_mem, Option.bind_some, bind, Option.bind] at *
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [hap_mem]
  simp only [Option.bind_some, bind, Option.bind]
  simp only [setReg_regs, setReg_mem, String.reduceEq, ↓reduceIte, reduceIte,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             Option.bind_some, bind, Option.bind]
  rw [show s.regs "op" + 0 = s.regs "op" from by bv_decide]
  rw [hop_mem]
  simp only [Option.bind_some, bind, Option.bind]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [setReg_regs, setReg_mem, storeMem32_mem_proj, storeMem32_regs_proj,
               regAddr, String.reduceEq, ↓reduceIte, reduceIte, hcy, hb,
               submul1Step32, u32_load_roundtrip',
               show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 4 = (4 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]

/-! ## §4  Limb-list induction

Clone of `Mpn.Submul1Prototype.mpnSubmul1_loop` at limb width 32. -/

/-- A new memory predicate over `BitVec 64` masked-u32 limbs.  Used in
    the loop induction to track the spec's intermediate `BitVec 64`
    result limbs (`submul1Step32` returns them in u64 form).  Equivalent
    to `memHoldsLimbs32` when each limb is already in masked-u32 form
    (`v.toNat < 2^32`), which holds by construction for outputs of
    `subBorrow32` (and hence `submul1Step32`). -/
def memHoldsLimbs64Masked (m : MemoryModel.Mem) (base : UInt64) :
    List (BitVec 64) → Prop
  | []      => True
  | v :: vs =>
      load32Mem m base = some (UInt64.ofNat v.toNat) ∧
      memHoldsLimbs64Masked m (base + 4) vs

@[simp] theorem memHoldsLimbs64Masked_nil (m : Mem) (base : UInt64) :
    memHoldsLimbs64Masked m base [] = True := rfl

@[simp] theorem memHoldsLimbs64Masked_cons (m : Mem) (base : UInt64)
    (v : BitVec 64) (vs : List (BitVec 64)) :
    memHoldsLimbs64Masked m base (v :: vs) =
      (load32Mem m base = some (UInt64.ofNat v.toNat) ∧
       memHoldsLimbs64Masked m (base + 4) vs) := rfl

/-- Frame for `memHoldsLimbs64Masked` across a disjoint `Mem.store32`. -/
theorem memHoldsLimbs64Masked_store32_range_frame (m : Mem) (base st : UInt64)
    (v : UInt64) (vs : List (BitVec 64))
    (hdisj : MemoryModel.Disjoint (range st 4) (range base (4 * vs.length)))
    (hmem : memHoldsLimbs64Masked m base vs) :
    memHoldsLimbs64Masked (Mem.store32 m st v) base vs := by
  induction vs generalizing base with
  | nil => exact True.intro
  | cons w ws ih =>
    obtain ⟨hhead, htail⟩ := hmem
    refine ⟨?_, ?_⟩
    · have hdisj_head : MemoryModel.Disjoint (range base 4) (range st 4) := by
        refine MemoryModel.Disjoint.symm (disjoint_mono (fun a h => h) ?_ hdisj)
        intro a ⟨j, hj, haj⟩
        exact ⟨j, by simp [List.length_cons]; omega, haj⟩
      rw [load32Mem_store32_disjoint m base st v hdisj_head]
      exact hhead
    · refine ih (base + 4) ?_ htail
      refine disjoint_mono (fun a h => h) ?_ hdisj
      intro a ⟨j, hj, haj⟩
      refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
      rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
      rw [haj]; ac_rfl

set_option maxHeartbeats 800000 in
theorem mpnSubmul132_openLoop :
    ∀ (out as : List (BitVec 32)) (s : BignumState) (b cy : BitVec 64) (extra : Nat),
      out.length = as.length →
      s.regs "b" = b →
      s.regs "cy" = cy →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs32 s.mem (regAddr s "op") out →
      memHoldsLimbs32 s.mem (regAddr s "ap") as →
      MemoryModel.Disjoint (range (regAddr s "op") (4 * as.length))
        (range (regAddr s "ap") (4 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) loopBodySubmul32] s
              = some s' ∧
        memHoldsLimbs64Masked s'.mem (regAddr s "op") (mpnSubmul132 out as b cy).1 ∧
        s'.regs "cy" = (mpnSubmul132 out as b cy).2 ∧
        s'.regs "b" = s.regs "b" ∧
        (∀ bb, MemoryModel.Disjoint (range bb 4)
              (range (regAddr s "op") (4 * as.length)) →
            MemoryModel.Disjoint (range bb 4)
              (range (regAddr s "ap") (4 * as.length)) →
            load32Mem s'.mem bb = load32Mem s.mem bb) := by
  intro out
  induction out with
  | nil =>
    intro as s b cy extra hlen hb hcy hn _ _ _
    cases as with
    | cons _ _ => simp at hlen
    | nil =>
      have hn0 : s.regs "n" = 0 := by simpa using hn
      refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
      · have : 2 * ([] : List (BitVec 32)).length + 3 + extra = extra + 3 := by
          simp only [List.length_nil]; omega
        rw [this]
        have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) = some 0 :=
          evalPExpr_neq_zero_false s (pv64 "n")
            (by simp only [pv64, vr64, evalPExpr]; rw [hn0])
        exact bignumExecFuel_loop_exit_generic emptyRegistry extra _ loopBodySubmul32 s hcond
      · simp [mpnSubmul132]
      · simpa [mpnSubmul132] using hcy
      · rfl
      · intro bb _ _; rfl
  | cons o os ih =>
    intro as s b cy extra hlen hb hcy hn hop hap hdoa
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have hlen' : os.length = as.length := by simpa using hlen
      have hsize : 4 * (as.length + 1) < 2 ^ 64 := by
        simpa [List.length_cons] using
          disjoint_range_lt (regAddr s "op") (regAddr s "ap")
            (4 * (a :: as).length) (by simp only [List.length_cons]; omega)
            (by simpa using hdoa)
      have hLsucc : as.length + 1 < 2 ^ 64 := by omega
      have hn_ne : s.regs "n" ≠ 0 := by
        rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
      obtain ⟨hop_head, hop_tail⟩ := hop
      obtain ⟨hap_head, hap_tail⟩ := hap
      obtain ⟨s1, hs1, hs1_mem, hs1_cy, hs1_ap, hs1_op, hs1_n, hs1_b⟩ :=
        bignumExec_loopBodySubmul32_step s o a b cy hb hcy hap_head hop_head
      set op0 : UInt64 := regAddr s "op" with hop0
      have hadv : ∀ (bv : BitVec 64),
          UInt64.ofNat (bv + 4).toNat = UInt64.ofNat bv.toNat + 4 := by
        intro bv
        have h := regAddr_advance_at bv 4
        rw [show (BitVec.ofNat 64 4 : BitVec 64) = 4 from rfl,
            show (UInt64.ofNat 4 : UInt64) = 4 from rfl] at h
        exact h
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 4 := by
        simp only [regAddr, hs1_ap]; exact hadv _
      have hra_op : regAddr s1 "op" = op0 + 4 := by
        simp only [regAddr, hs1_op, hop0]; exact hadv _
      have hmem1 : s1.mem = Mem.store32 s.mem op0
          (UInt64.ofNat (submul1Step32 o a b cy).1.toNat) := by
        simpa [hop0, regAddr] using hs1_mem
      have hdoa_store_aptail :
          MemoryModel.Disjoint (range op0 4) (range (regAddr s "ap" + 4) (4 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · obtain ⟨j, hj, hxj⟩ := h
          exact ⟨j, by simp [List.length_cons]; omega, hxj⟩
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
      have hsep_op : MemoryModel.Disjoint (range op0 4) (range (op0 + 4) (4 * as.length)) :=
        range_op_head_tail_disjoint_4 op0 as.length (by omega)
      have hap1 : memHoldsLimbs32 s1.mem (regAddr s1 "ap") as := by
        rw [hra_ap, hmem1]
        exact memHoldsLimbs32_store32_range_frame s.mem (regAddr s "ap" + 4) op0 _ as
          hdoa_store_aptail hap_tail
      have hop1 : memHoldsLimbs32 s1.mem (regAddr s1 "op") os := by
        rw [hra_op, hmem1]
        exact memHoldsLimbs32_store32_range_frame s.mem (op0 + 4) op0 _ os
          (by rw [hlen']; exact hsep_op) hop_tail
      have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (4 * as.length))
          (range (regAddr s1 "ap") (4 * as.length)) := by
        rw [hra_op, hra_ap]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
      have hb1 : s1.regs "b" = b := by rw [hs1_b, hb]
      have hcy1 : s1.regs "cy" = (submul1Step32 o a b cy).2 := hs1_cy
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      obtain ⟨s', hs', hs'_mem, hs'_cy, hs'_b, hs'_frame⟩ :=
        ih as s1 b (submul1Step32 o a b cy).2 extra hlen' hb1 hcy1 hn1 hop1 hap1 hdoa1
      refine ⟨s', ?_, ?_, ?_, ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) = some 1 :=
          evalPExpr_neq_zero_true s (pv64 "n") (s.regs "n")
            (by simp only [pv64, vr64, evalPExpr]) hn_ne
        refine bignumExecFuel_loop_step_generic emptyRegistry
          (2 * as.length + 2 + extra) _ loopBodySubmul32 loopBodySubmul32_straightLine
          loopBodySubmul32_nonControl s s1 s' hcond hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · rw [hmem1] at hs'_frame
        refine ⟨?_, ?_⟩
        · rw [hs'_frame op0 (by rw [hra_op]; exact hsep_op)
                (by rw [hra_ap]; exact hdoa_store_aptail)]
          have hread := load32Mem_store32_same s.mem op0
            (UInt64.ofNat (submul1Step32 o a b cy).1.toNat)
          rw [hread]
          have hsum : (submul1Step32 o a b cy).1.toNat < 2 ^ 32 :=
            submul1Step32_limbFitsU32 o a b cy
          have hmask : (UInt64.ofNat (submul1Step32 o a b cy).1.toNat
              &&& 0xFFFFFFFF : UInt64)
              = UInt64.ofNat (submul1Step32 o a b cy).1.toNat := by
            apply UInt64.toNat.inj
            simp only [UInt64.toNat_and, UInt64.toNat_ofNat',
                       show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from by decide]
            rw [Nat.mod_eq_of_lt (by omega : (submul1Step32 o a b cy).1.toNat < 2 ^ 64),
                Nat.and_two_pow_sub_one_eq_mod _ 32, Nat.mod_eq_of_lt hsum]
          rw [hmask]
        · have hthis := hs'_mem
          rw [hra_op] at hthis
          exact hthis
      · rw [hs'_cy]; simp only [mpnSubmul132]
      · rw [hs'_b, hs1_b]
      · intro bb hbb_op hbb_ap
        rw [hmem1] at hs'_frame
        have hbb_op_tail : MemoryModel.Disjoint (range bb 4)
            (range (regAddr s1 "op") (4 * as.length)) := by
          rw [hra_op]
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb_op
          obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
        have hbb_ap_tail : MemoryModel.Disjoint (range bb 4)
            (range (regAddr s1 "ap") (4 * as.length)) := by
          rw [hra_ap]
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb_ap
          obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
        rw [hs'_frame bb hbb_op_tail hbb_ap_tail]
        have hbb_head : MemoryModel.Disjoint (range bb 4) (range (regAddr s "op") 4) := by
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb_op
          obtain ⟨j, hj, hxj⟩ := h
          exact ⟨j, by simp [List.length_cons]; omega, hxj⟩
        rw [load32Mem_store32_disjoint s.mem bb (regAddr s "op") _ hbb_head]

/-! ## §5  Full bridge `MpnSubmul132JasminRefines`

`bodySubmul32 = [cy := 0; while (n != 0) { loopBodySubmul32 }]`.
Prelude zeroes the U32 carry register, then the loop walks the limb
arrays.  Mirror of `Mpn.Submul1Prototype.MpnSubmul1JasminRefines`. -/

def MpnSubmul132RefinesStmt : Prop :=
  ∀ (s : BignumState) (out as : List (BitVec 32)) (b : BitVec 64) (fuel : Nat),
    out.length = as.length →
    s.regs "b" = b →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs32 s.mem (UInt64.ofNat (s.regs "op").toNat) out →
    memHoldsLimbs32 s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (4 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (4 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodySubmul32 s = some s' ∧
      memHoldsLimbs64Masked s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnSubmul132 out as b 0).1 ∧
      s'.regs "cy" = (mpnSubmul132 out as b 0).2

theorem MpnSubmul132JasminRefines : MpnSubmul132RefinesStmt := by
  intro s out as b fuel hlen hb hn hop hap hdoa hfuel
  set s0 : BignumState := setReg s "cy" 0 with hs0
  have hexec0 : execInstr s
      (.Cassgn (.Lvar { var := vr32 "cy" }) .AT_none (.sword .U32) (.Pconst 0))
      = some s0 := by
    simp only [execInstr, evalPExpr, vr32, bind, Option.bind, hs0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hcy0 : s0.regs "cy" = (0 : BitVec 64) := by
    rw [hs0]
    simp [setReg]
  have hreg0 : ∀ x, x ≠ "cy" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hra0 : ∀ x, x ≠ "cy" → regAddr s0 x = regAddr s x := by
    intro x hx; simp only [regAddr, hreg0 x hx]
  have hb0 : s0.regs "b" = b := by rw [hreg0 "b" (by decide)]; exact hb
  have hn0' : s0.regs "n" = BitVec.ofNat 64 as.length := by
    rw [hreg0 "n" (by decide), hn]
  have hop0 : memHoldsLimbs32 s0.mem (regAddr s0 "op") out := by
    rw [hmem0, hra0 "op" (by decide)]
    simp only [regAddr]
    exact hop
  have hap0 : memHoldsLimbs32 s0.mem (regAddr s0 "ap") as := by
    rw [hmem0, hra0 "ap" (by decide)]
    simp only [regAddr]
    exact hap
  have hdoa0 : MemoryModel.Disjoint (range (regAddr s0 "op") (4 * as.length))
      (range (regAddr s0 "ap") (4 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "ap" (by decide)]
    simp only [regAddr]
    exact hdoa
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_mem, hs'_cy, _, _⟩ :=
    mpnSubmul132_openLoop out as s0 b 0 extra hlen hb0 hcy0 hn0' hop0 hap0 hdoa0
  refine ⟨s', ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) bodySubmul32 s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) loopBodySubmul32] s0 := by
      conv_lhs => rw [bodySubmul32]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem
    simp only [regAddr] at hs'_mem
    exact hs'_mem
  · exact hs'_cy

/-! ## §6  Axiom audit -/

#print axioms bodySubmul32_isCT
#print axioms mpnSubmul132Fd_body
#print axioms submul1Step32_spec
#print axioms submul1Step32_carryFitsU32
#print axioms mpnSubmul132_spec
#print axioms MpnSubmul132JasminRefines

end CatCrypt.Crypto.Jasmin.Mpn.Submul132Refines
