/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnAddmul132Emit
import CatCrypt.Crypto.Jasmin.Examples.MpnAdd32Refines
import CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
import CatCrypt.Crypto.Jasmin.Examples.MpnMul132Refines
import CatCrypt.Crypto.Jasmin.BignumExec

set_option autoImplicit false

/-!
# `mpn_addmul_1` Jasmin refinement at **U32 limb width**

This file is the U32 analogue of
`MpnAddmul1Prototype.MpnAddmul1JasminRefines`: it proves that the emitted
U32 `mpn_addmul_1_32` Jasmin kernel (`MpnAddmul132Emit.mpnAddmul132Fd`,
body `MpnAddmul132Emit.bodyAddmul32`) refines a U32 pure functional
spec `mpnAddmul132` over byte memory at **4-byte limb stride**.

## Shape

Per iteration:

```
t       = [:u32 ap + 0];                -- load a[i]
hi, lo  = #MULX_32(b, t);               -- (hi, lo) = b · a[i]
_, c1, _,_,_, lo = #ADD_32(lo, cy);
w       = [:u32 op + 0];                -- READ out[i]
_, c2, _,_,_, lo = #ADD_32(lo, w);
[:u32 op + 0] = lo;                     -- store accumulated low word
cy      = hi + c1;                      -- recombine carry in two u32 reg-adds
cy      = cy + c2;
ap += 4; op += 4; n -= 1;
```

The pointers `op`/`ap` and the counter `n` are still `u64`; the scalar
`b`, the running carry `cy`, and all limb data (`t`/`hi`/`lo`/`w`/`c1`/`c2`)
are `u32` (held in `BitVec 64` registers with the high half cleared).

## Proof reuse

* **U32 memory algebra** from `BignumExec` (commit `cacca611`):
  `load32Mem_store32_same`, `load32Mem_store32_disjoint`,
  `loadByte_store32`, `loadByte_store32_frame`.
* **U32 plumbing** from `MpnAdd32Refines`: `w64`, `w64_mask`,
  `u32_load_roundtrip`, `resolveAddr_vr64`, `memHoldsLimbs32`,
  `memHoldsLimbs32_store32_range_frame`.
* **Stride-parametric helpers** from `MpnAddPrototype` §11:
  `regAddr_advance_at`, `range_op_head_tail_disjoint_4`,
  `bignumExecFuel_loop_step_generic`, `bignumExecFuel_loop_exit_generic`,
  `evalPExpr_neq_zero_true`/`_false`.
* **Proof shape** mirrored from `MpnAddmul1Prototype` (U64 bridge):
  one iteration step + limb-list induction + zero-carry prelude.

## TCB shrinkage

The U32 `mpn_addmul_1_32` emitter is out of the TCB for the
`USE_GMP=OFF` route (a): the emitted body provably computes the
pure functional spec `mpnAddmul132` over byte memory.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnAddmul132Refines

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddmul132Emit
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnAdd32Refines

/-- Local copy of the (private) `MpnAdd32Refines.w64`: promote a
    `BitVec 32` to `BitVec 64` by zero-extension via `ofNat _.toNat`. -/
def w64 (w : BitVec 32) : BitVec 64 := BitVec.ofNat 64 w.toNat

/-- A `w64`-encoded `BitVec 32` value masked to the low 32 bits is itself. -/
theorem w64_mask (w : BitVec 32) : w64 w &&& mask32 = w64 w := by
  unfold w64 mask32
  have hzx : (BitVec.ofNat 64 w.toNat) = BitVec.setWidth 64 w := by
    apply BitVec.eq_of_toNat_eq
    have hw : w.toNat < 2 ^ 32 := w.isLt
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth,
               Nat.mod_eq_of_lt (by omega : w.toNat < 2 ^ 64)]
  rw [hzx]
  bv_decide

/-- Loading a `BitVec 32` limb from memory and decoding through
    `BitVec.ofNat 64 _.toNat` recovers the `BitVec 64` zero-extension. -/
theorem u32_load_roundtrip (w : BitVec 32) :
    BitVec.ofNat 64 (UInt64.ofNat w.toNat).toNat = w64 w := by
  have hw : w.toNat < 2 ^ 32 := w.isLt
  apply BitVec.eq_of_toNat_eq
  unfold w64
  simp only [BitVec.toNat_ofNat, UInt64.toNat_ofNat']
  omega

/-! ## §1  Directly provable facts about the emitted U32 kernel -/

/-- The emitted U32 `mpn_addmul_1_32` body is constant-time-shaped: the
    `Cwhile` guard reads only the public length `n`. -/
theorem bodyAddmul32_isCT : isCT_Cmd bodyAddmul32 = true := by decide

/-- The U32 `FunDecl`'s body is *literally* `bodyAddmul32`. -/
theorem mpnAddmul132Fd_body : mpnAddmul132Fd.body = bodyAddmul32 := rfl

/-! ## §2  Pure U32 functional reference

`addmul1Step32` is the U32 analogue of
`MpnAddmul1Prototype.addmul1Step`.  It operates on `BitVec 64`
arguments interpreted as u32 values (high half zero); the result halves
`(lo2, hi + c1 + c2)` are likewise masked to 32 bits — `mulx32`,
`addCarry32`'s outputs are already masked, and the final `hi + c1 + c2`
add fits inside the low 32 bits because `hi ≤ 2^32 − 2`, `c1, c2 ≤ 1`,
and the full 64-bit accumulation `b·a + cy + out ≤ 2^64 − 1`. -/

/-- Single U32 `mpn_addmul_1` step.  Mirror of
    `MpnAddmul1Prototype.addmul1Step` with width 32: multiply `a · b`,
    add running carry `cy`, then add the existing `out`, splitting into
    a low-32 result and a (≤ 32-bit) carry. -/
def addmul1Step32 (out a b cy : BitVec 64) : BitVec 64 × BitVec 64 :=
  let (hi, lo) := mulx32 b a
  let (c1, lo1) := addCarry32 lo cy
  let (c2, lo2) := addCarry32 lo1 out
  (lo2, hi + c1 + c2)

/-- Pure U32 reference walk: a list of `BitVec 32` accumulator limbs
    `out`, a list of `BitVec 32` multiplicand limbs `as`, a scalar `b`
    (`BitVec 32`), and a `BitVec 32` running carry. -/
def mpnAddmul132 :
    List (BitVec 32) → List (BitVec 32) → BitVec 32 → BitVec 32 →
    (List (BitVec 32) × BitVec 32)
  | o :: os, a :: as, b, cy =>
      let p := addmul1Step32 (w64 o) (w64 a) (w64 b) (w64 cy)
      -- Truncate the BitVec 64 outputs back to BitVec 32.
      let r32 : BitVec 32 := BitVec.ofNat 32 p.1.toNat
      let cy32 : BitVec 32 := BitVec.ofNat 32 p.2.toNat
      let (rs, fcy) := mpnAddmul132 os as b cy32
      (r32 :: rs, fcy)
  | _, _, _, cy => ([], cy)

/-! ## §3  Mask invariants and roundtrips

The bridge from the executable `addmul1Step32` (in `BitVec 64`) to the
pure `mpnAddmul132` (in `BitVec 32`) uses three small facts:

* `mulx32` / `addCarry32` outputs are already masked to 32 bits
  (`& mask32 = id`).
* The combined carry `hi + c1 + c2` fits in 32 bits (since
  `b·a + cy + out ≤ 2^64 − 1`).
* Round-tripping a `BitVec 32` through `w64` and `& mask32` is
  identity (already proved as `MpnAdd32Refines.w64_mask`).
-/

/-- `mulx32`'s low half is masked to 32 bits. -/
theorem mulx32_lo_mask (a b : BitVec 64) :
    (mulx32 a b).2 &&& mask32 = (mulx32 a b).2 := by
  unfold mulx32 mask32; bv_decide

/-- `mulx32`'s high half is masked to 32 bits. -/
theorem mulx32_hi_mask (a b : BitVec 64) :
    (mulx32 a b).1 &&& mask32 = (mulx32 a b).1 := by
  unfold mulx32 mask32; bv_decide

/-- `addCarry32`'s carry-out is `0` or `1`. -/
theorem addCarry32_carry_mask (a b : BitVec 64) :
    (addCarry32 a b).1 &&& mask32 = (addCarry32 a b).1 := by
  unfold addCarry32 mask32; bv_decide

/-- `addCarry32`'s sum is masked to 32 bits. -/
theorem addCarry32_sum_mask (a b : BitVec 64) :
    (addCarry32 a b).2 &&& mask32 = (addCarry32 a b).2 := by
  unfold addCarry32 mask32; bv_decide

/-! ### Arithmetic facts about `addmul1Step32`

These lift the U64-style `MpnAddmul1Prototype.addmul1Step_spec` to U32, using
the existing `MpnMul132Refines.mulx32_hi_le`, `MpnMul132Refines.mulx32_toNat`,
and `MpnMul132Refines.addCarry32_carry_le`, `MpnMul132Refines.addCarry32_spec`
imports. -/

/-- The single-step U32 MUL-ACC identity, on `Nat`:
    `addmul1Step32 out a b cy` produces `(o', cy')` with
    `o'.toNat + 2^32 · cy'.toNat = a.toNat · b.toNat + cy.toNat + out.toNat`,
    where all inputs are u32-encoded into `BitVec 64`. -/
theorem addmul1Step32_spec (out a b cy : BitVec 32) :
    (addmul1Step32 (w64 out) (w64 a) (w64 b) (w64 cy)).1.toNat
      + 2 ^ 32 * (addmul1Step32 (w64 out) (w64 a) (w64 b) (w64 cy)).2.toNat
      = a.toNat * b.toNat + cy.toNat + out.toNat := by
  -- Unfold the four definitional projections.
  rw [show (addmul1Step32 (w64 out) (w64 a) (w64 b) (w64 cy)).1
        = (addCarry32 (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).2
                      (w64 out)).2 from rfl,
      show (addmul1Step32 (w64 out) (w64 a) (w64 b) (w64 cy)).2
        = (mulx32 (w64 b) (w64 a)).1
            + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1
            + (addCarry32 (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).2
                          (w64 out)).1 from rfl]
  set hi := (mulx32 (w64 b) (w64 a)).1 with hhi
  set lo := (mulx32 (w64 b) (w64 a)).2 with hlo
  set c1 := (addCarry32 lo (w64 cy)).1 with hc1
  set lo1 := (addCarry32 lo (w64 cy)).2 with hlo1
  set c2 := (addCarry32 lo1 (w64 out)).1 with hc2
  set lo2 := (addCarry32 lo1 (w64 out)).2 with hlo2
  -- (1) mulx32: lo + 2^32·hi = b·a (over Nat).
  have hmulx : lo.toNat + 2 ^ 32 * hi.toNat = b.toNat * a.toNat := by
    rw [hlo, hhi]; exact MpnMul132Refines.mulx32_toNat a b
  -- (2) first addCarry32: lo1 + 2^32·c1 = (lo & mask32) + (w64 cy & mask32).
  --     lo is masked (mulx32_lo_mask); w64 cy is masked (w64_mask cy).
  have hadd1 : lo1.toNat + 2 ^ 32 * c1.toNat
      = lo.toNat + (w64 cy).toNat := by
    rw [hlo1, hc1]
    have h := MpnMul132Refines.addCarry32_spec lo (w64 cy)
    -- lo &&& mask32 = lo
    have hlo_mask : (lo &&& mask32) = lo := by rw [hlo]; exact mulx32_lo_mask _ _
    -- w64 cy &&& mask32 = w64 cy
    have hcy_mask : ((w64 cy) &&& mask32) = w64 cy := w64_mask cy
    rw [hlo_mask, hcy_mask] at h
    exact h
  -- (3) second addCarry32: lo2 + 2^32·c2 = (lo1 & mask32) + (w64 out & mask32).
  have hadd2 : lo2.toNat + 2 ^ 32 * c2.toNat
      = lo1.toNat + (w64 out).toNat := by
    rw [hlo2, hc2]
    have h := MpnMul132Refines.addCarry32_spec lo1 (w64 out)
    have hlo1_mask : (lo1 &&& mask32) = lo1 := by rw [hlo1]; exact addCarry32_sum_mask _ _
    have hout_mask : ((w64 out) &&& mask32) = w64 out := w64_mask out
    rw [hlo1_mask, hout_mask] at h
    exact h
  -- Bounds.
  have hc1le : c1.toNat ≤ 1 := by
    rw [hc1]; exact MpnMul132Refines.addCarry32_carry_le lo (w64 cy)
  have hc2le : c2.toNat ≤ 1 := by
    rw [hc2]; exact MpnMul132Refines.addCarry32_carry_le lo1 (w64 out)
  have hhile : hi.toNat ≤ 2 ^ 32 - 2 := by
    rw [hhi]; exact MpnMul132Refines.mulx32_hi_le a b
  -- w64 cy.toNat = cy.toNat, w64 out.toNat = out.toNat.
  have hwcy : (w64 cy).toNat = cy.toNat := by
    unfold w64
    have := cy.isLt
    simp only [BitVec.toNat_ofNat]; omega
  have hwout : (w64 out).toNat = out.toNat := by
    unfold w64
    have := out.isLt
    simp only [BitVec.toNat_ofNat]; omega
  -- The (hi + c1 + c2) sum never wraps; high half zero.
  have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
  have hsum01 : (hi + c1).toNat = hi.toNat + c1.toNat := by
    have hbnd : hi.toNat + c1.toNat < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hbnd]
  have hsum : (hi + c1 + c2).toNat = hi.toNat + c1.toNat + c2.toNat := by
    have hbnd : (hi + c1).toNat + c2.toNat < 2 ^ 64 := by rw [hsum01]; omega
    rw [BitVec.toNat_add, hsum01, Nat.mod_eq_of_lt (by rw [← hsum01]; exact hbnd)]
  -- Expand the carry's toNat and the w64-encoded inputs in the goal.
  rw [hsum]
  have hadd1' : lo1.toNat + 2 ^ 32 * c1.toNat = lo.toNat + cy.toNat := by
    rw [← hwcy]; exact hadd1
  have hadd2' : lo2.toNat + 2 ^ 32 * c2.toNat = lo1.toNat + out.toNat := by
    rw [← hwout]; exact hadd2
  -- Commute a·b to match hmulx's b·a.
  have hcomm : a.toNat * b.toNat = b.toNat * a.toNat := by ring
  rw [hcomm]
  -- omega closes via linear combination of hmulx, hadd1', hadd2'.
  clear hsum hsum01 hadd1 hadd2 hwcy hwout hcomm
  omega

/-- The `BitVec 64` carry-out of one U32 multiply-accumulate step has
    `.toNat < 2^32` (its high half is zero).  Derived from
    `addmul1Step32_spec` plus the masked-low-half bound. -/
theorem addmul1Step32_carry_lt (out a b cy : BitVec 32) :
    (addmul1Step32 (w64 out) (w64 a) (w64 b) (w64 cy)).2.toNat < 2 ^ 32 := by
  -- From the spec, lo + 2^32 · carry = a·b + cy + out ≤ 2^64 - 1.
  -- And lo ≥ 0.  So 2^32 · carry < 2^64, i.e. carry < 2^32.
  have hspec := addmul1Step32_spec out a b cy
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  have hcy : cy.toNat < 2 ^ 32 := cy.isLt
  have hout : out.toNat < 2 ^ 32 := out.isLt
  have hrhs : a.toNat * b.toNat + cy.toNat + out.toNat < 2 ^ 64 := by
    have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
    have hmul : a.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h_arith : (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) + (2 ^ 32 - 1) < 2 ^ 32 * 2 ^ 32 := by
      decide
    omega
  -- p.1.toNat is masked, so < 2^32.
  have hlo_lt : (addmul1Step32 (w64 out) (w64 a) (w64 b) (w64 cy)).1.toNat < 2 ^ 32 := by
    rw [show (addmul1Step32 (w64 out) (w64 a) (w64 b) (w64 cy)).1
          = (addCarry32 (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).2
                        (w64 out)).2 from rfl]
    unfold addCarry32
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod _ 32]
    have hpos : (0 : Nat) < 2 ^ 32 := by positivity
    exact Nat.mod_lt _ hpos
  -- Combine.
  omega

/-- Pure U32 reference walk in `Nat` form (toNat-friendly).  This is the
    multi-precision identity over the limb list, mirror of
    `MpnAddmul1Prototype.mpnAddmul1_spec` at U32. -/
theorem mpnAddmul132_spec :
    ∀ (out as : List (BitVec 32)), out.length = as.length →
      ∀ (b cy : BitVec 32),
        MpnGenericWidth.toNatW 32 (mpnAddmul132 out as b cy).1
          + (2 ^ 32) ^ as.length * (mpnAddmul132 out as b cy).2.toNat
        = MpnGenericWidth.toNatW 32 out
          + MpnGenericWidth.toNatW 32 as * b.toNat
          + cy.toNat := by
  intro out
  induction out with
  | nil =>
    intro as hlen b cy
    cases as with
    | nil => simp [mpnAddmul132, MpnGenericWidth.toNatW]
    | cons _ _ => simp at hlen
  | cons o os ih =>
    intro as hlen b cy
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have hlen' : os.length = as.length := by simpa using hlen
      -- Per-step identity.
      have hstep := addmul1Step32_spec o a b cy
      set p := addmul1Step32 (w64 o) (w64 a) (w64 b) (w64 cy) with hp
      -- p.2 has high half zero — re-encode through BitVec.ofNat 32 _.toNat.
      have hp2_lt : p.2.toNat < 2 ^ 32 := by
        rw [hp]; exact addmul1Step32_carry_lt o a b cy
      have hp1_lt : p.1.toNat < 2 ^ 32 := by
        rw [hp]
        rw [show (addmul1Step32 (w64 o) (w64 a) (w64 b) (w64 cy)).1
              = (addCarry32 (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).2
                            (w64 o)).2 from rfl]
        unfold addCarry32
        simp only [BitVec.toNat_and,
                   show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
        rw [Nat.and_two_pow_sub_one_eq_mod _ 32]
        have hpos : (0 : Nat) < 2 ^ 32 := by positivity
        exact Nat.mod_lt _ hpos
      -- The truncated tail-carry, as a BitVec 32.
      set cy' : BitVec 32 := BitVec.ofNat 32 p.2.toNat with hcy'
      set r32 : BitVec 32 := BitVec.ofNat 32 p.1.toNat with hr32
      have htail := ih as hlen' b cy'
      set q := mpnAddmul132 os as b cy' with hq
      have hunfold : mpnAddmul132 (o :: os) (a :: as) b cy = (r32 :: q.1, q.2) := by
        simp only [mpnAddmul132, hp, hcy', hr32, hq]
      rw [hunfold]
      simp only [MpnGenericWidth.toNatW, List.length_cons]
      have hpow : (2 ^ 32) ^ (as.length + 1) = 2 ^ 32 * (2 ^ 32) ^ as.length := by
        rw [pow_succ]; ring
      rw [hpow]
      -- r32.toNat = p.1.toNat (since p.1.toNat < 2^32).
      have hr32_toNat : r32.toNat = p.1.toNat := by
        rw [hr32]; simp only [BitVec.toNat_ofNat]; omega
      have hcy'_toNat : cy'.toNat = p.2.toNat := by
        rw [hcy']; simp only [BitVec.toNat_ofNat]; omega
      rw [hr32_toNat]
      -- htail in canonical form
      rw [hcy'_toNat] at htail
      -- linear combination.
      have hkey : 2 ^ 32 * MpnGenericWidth.toNatW 32 q.1
          + 2 ^ 32 * ((2 ^ 32) ^ as.length * q.2.toNat)
          = 2 ^ 32 * (MpnGenericWidth.toNatW 32 os
                       + MpnGenericWidth.toNatW 32 as * b.toNat + p.2.toNat) := by
        rw [← htail]; ring
      have hmono : 2 ^ 32 * (2 ^ 32) ^ as.length * q.2.toNat
          = 2 ^ 32 * ((2 ^ 32) ^ as.length * q.2.toNat) := by ring
      rw [hmono]
      have hexpand : (a.toNat + 2 ^ 32 * MpnGenericWidth.toNatW 32 as) * b.toNat
          = a.toNat * b.toNat + 2 ^ 32 * (MpnGenericWidth.toNatW 32 as * b.toNat) := by ring
      rw [hexpand]
      omega

/-! ## §4  One U32 loop iteration as an explicit state update

The U32 analogue of `MpnAddmul1Prototype.bignumExec_loopBodyAddmul_step`.
The big symbolic-execution simp list mirrors the U64 version, with
U32 builders (`load32At0`/`mulxCopn32`/`addCopn32`/`store32At0`/
`regAdd32`/`ptrImm`) and U32 memory projections
(`storeMem32_mem_proj`/`storeMem32_regs_proj`). -/

/-- `loopBodyAddmul32` is straight-line (only `Cassgn`/`Copn`). -/
theorem loopBodyAddmul32_straightLine :
    InstrR.bodyIsStraightLine loopBodyAddmul32 := by
  simp only [loopBodyAddmul32, load32At0, mulxCopn32, addCopn32, store32At0,
             regAdd32, ptrImm, InstrR.bodyIsStraightLine,
             InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBodyAddmul32` is non-control. -/
theorem loopBodyAddmul32_nonControl :
    ∀ i ∈ loopBodyAddmul32, i.isNonControl := by
  intro i hi
  simp only [loopBodyAddmul32, load32At0, mulxCopn32, addCopn32, store32At0,
             regAdd32, ptrImm, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem bignumExec_loopBodyAddmul32_step
    (s : BignumState) (out a : BitVec 32) (cy : BitVec 64)
    (hcy : s.regs "cy" = cy)
    (ha : load32Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hout : load32Mem s.mem (regAddr s "op") = some (UInt64.ofNat out.toNat)) :
    ∃ s', bignumExec loopBodyAddmul32 s = some s' ∧
      s'.mem = Mem.store32 s.mem (regAddr s "op")
        (UInt64.ofNat (addmul1Step32 (w64 out) (w64 a) (s.regs "b") cy).1.toNat) ∧
      s'.regs "cy" = (addmul1Step32 (w64 out) (w64 a) (s.regs "b") cy).2 ∧
      s'.regs "ap" = s.regs "ap" + 4 ∧
      s'.regs "op" = s.regs "op" + 4 ∧
      s'.regs "n" = s.regs "n" - 1 ∧
      s'.regs "b" = s.regs "b" := by
  -- Unfold the body, the semantic dispatchers, and the projection simp lemmas.
  simp only [loopBodyAddmul32, load32At0, mulxCopn32, addCopn32, store32At0,
             regAdd32, ptrImm,
             bignumExec, execInstr, evalPExpr, pv32, pv64,
             resolveAddr_vr64, vr32, vr64,
             setReg_mem, setReg_regs, storeMem32_mem_proj, storeMem32_regs_proj,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append,
             writeMulxBundle, writeSubBundle]
  -- Resolve the `ap` load (offset 0), fire it (`ha`), decode the word.
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem32_regs_proj, storeMem32_mem_proj,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             ha, Option.bind_some, bind, Option.bind] at *
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [ha]
  simp only [Option.bind_some, bind, Option.bind]
  -- Now the `op` load (offset 0): only `t, hi, lo, c1` have been written;
  -- `mem` is unchanged, `op` is unchanged.  Push projections through.
  simp only [setReg_regs, setReg_mem, String.reduceEq, ↓reduceIte, reduceIte]
  rw [show s.regs "op" + 0 = s.regs "op" from by bv_decide]
  rw [hout]
  simp only [Option.bind_some, bind, Option.bind]
  -- The witness state is now fully concrete.
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [setReg_regs, setReg_mem, storeMem32_mem_proj, storeMem32_regs_proj,
               regAddr, String.reduceEq, ↓reduceIte, reduceIte, hcy, addmul1Step32,
               show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 4 = (4 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl,
               u32_load_roundtrip]

/-! ## §5  One `Cwhile` iteration over `bignumExecFuel`

We reuse the generic forward/exit rules from `MpnAddPrototype` §11
(`bignumExecFuel_loop_step_generic` / `_exit_generic`), instantiating
the body with `loopBodyAddmul32`. -/

/-! ## §6  The U32 outer loop, by induction on the limb list

Mirror of `MpnAddmul1Prototype.mpnAddmul1_loop` at width 32, with 4-byte
stride and `BitVec 32` limbs.  `op` plays a dual role (read-modify-write)
just as in the U64 file. -/

theorem mpnAddmul132_loop :
    ∀ (out as : List (BitVec 32)) (s : BignumState) (b cy : BitVec 32) (extra : Nat),
      out.length = as.length →
      s.regs "b" = w64 b →
      s.regs "cy" = w64 cy →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs32 s.mem (regAddr s "op") out →
      memHoldsLimbs32 s.mem (regAddr s "ap") as →
      MemoryModel.Disjoint (range (regAddr s "op") (4 * as.length))
        (range (regAddr s "ap") (4 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0))
                       loopBodyAddmul32] s
              = some s' ∧
        memHoldsLimbs32 s'.mem (regAddr s "op")
          (mpnAddmul132 out as b cy).1 ∧
        s'.regs "cy" = w64 (mpnAddmul132 out as b cy).2 ∧
        s'.regs "b" = s.regs "b" ∧
        (∀ bb, MemoryModel.Disjoint (range bb 4)
              (range (regAddr s "op") (4 * as.length)) →
            MemoryModel.Disjoint (range bb 4)
              (range (regAddr s "ap") (4 * as.length)) →
            load32Mem s'.mem bb = load32Mem s.mem bb) := by
  intro out
  induction out with
  | nil =>
    intro as s b cy extra hlen _hb hcy hn _ _ _
    cases as with
    | cons _ _ => simp at hlen
    | nil =>
      have hn0 : s.regs "n" = 0 := by simpa using hn
      have hfuelEq : 2 * ([] : List (BitVec 32)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [hfuelEq]
      have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) = some 0 :=
        evalPExpr_neq_zero_false s (pv64 "n")
          (by simp only [pv64, vr64, evalPExpr]; rw [hn0])
      refine ⟨s, bignumExecFuel_loop_exit_generic emptyRegistry extra _
              loopBodyAddmul32 s hcond, ?_, ?_, rfl, ?_⟩
      · simp [mpnAddmul132, memHoldsLimbs32]
      · simpa [mpnAddmul132] using hcy
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
      -- One U32 iteration: reads `out`-head from `op`, `a`-head from `ap`.
      obtain ⟨s1, hs1, _hs1_mem, _hs1_cy, hs1_ap, hs1_op, hs1_n, hs1_b⟩ :=
        bignumExec_loopBodyAddmul32_step s o a (w64 cy) hcy hap_head hop_head
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
      -- Re-express the iteration's memory store and carry using `w64 b`.
      have hmem1 : s1.mem = Mem.store32 s.mem op0
          (UInt64.ofNat (addmul1Step32 (w64 o) (w64 a) (w64 b) (w64 cy)).1.toNat) := by
        have h := _hs1_mem
        rw [hb] at h
        simpa [hop0, regAddr] using h
      have hcy1_64 : s1.regs "cy"
          = (addmul1Step32 (w64 o) (w64 a) (w64 b) (w64 cy)).2 := by
        rw [_hs1_cy, hb]
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
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      -- Re-encode the carry as `w64 cy'` where cy' is the BitVec 32 truncation.
      set p := addmul1Step32 (w64 o) (w64 a) (w64 b) (w64 cy) with hp
      have hp2_lt : p.2.toNat < 2 ^ 32 := by
        rw [hp]; exact addmul1Step32_carry_lt o a b cy
      set cy' : BitVec 32 := BitVec.ofNat 32 p.2.toNat with hcy'
      have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
      have hp2_eq_w64 : p.2 = w64 cy' := by
        apply BitVec.eq_of_toNat_eq
        unfold w64
        rw [hcy']
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt hp2_lt, Nat.mod_eq_of_lt (by omega)]
      have hcy1 : s1.regs "cy" = w64 cy' := by
        rw [hcy1_64]; exact hp2_eq_w64
      have hb1 : s1.regs "b" = w64 b := by rw [hs1_b]; exact hb
      -- Apply IH on the tail.
      obtain ⟨s', hs', hs'_mem, hs'_cy, hs'_b, hs'_frame⟩ :=
        ih as s1 b cy' extra hlen' hb1 hcy1 hn1 hop1 hap1 hdoa1
      -- The head limb that was stored at op0.
      set headLimb : BitVec 32 := BitVec.ofNat 32 p.1.toNat with hheadLimb
      -- Unfold mpnAddmul132 (o::os) (a::as) b cy to (headLimb :: tail, finalCy).
      have hunfold :
          mpnAddmul132 (o :: os) (a :: as) b cy
            = (headLimb :: (mpnAddmul132 os as b cy').1,
               (mpnAddmul132 os as b cy').2) := by
        simp only [mpnAddmul132, hp, hcy', hheadLimb]
      refine ⟨s', ?_, ?_, ?_, ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) = some 1 :=
          evalPExpr_neq_zero_true s (pv64 "n") (s.regs "n")
            (by simp only [pv64, vr64, evalPExpr]) hn_ne
        refine bignumExecFuel_loop_step_generic emptyRegistry
          (2 * as.length + 2 + extra) _ loopBodyAddmul32 loopBodyAddmul32_straightLine
          loopBodyAddmul32_nonControl s s1 s' hcond hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · -- Memory at op: head limb at op0 (preserved by IH frame), tail by IH.
        rw [hunfold]
        refine ⟨?_, ?_⟩
        · -- Head limb at op0.  Use IH frame: op0's 4-byte block is disjoint
          -- from BOTH the tail op-region (op0+4..) and the tail ap-region (ap+4..).
          rw [hs'_frame op0 (by rw [hra_op]; exact hsep_op)
                              (by rw [hra_ap]; exact hdoa_store_aptail)]
          -- Now read back from s1.mem = s.mem.store32 op0 _.
          rw [hmem1]
          have hread := load32Mem_store32_same s.mem op0
            (UInt64.ofNat p.1.toNat)
          rw [hp] at hread
          rw [hread]
          -- Goal: some (UInt64.ofNat p.1.toNat &&& 0xFFFFFFFF) = some (UInt64.ofNat headLimb.toNat).
          have hp1_lt : p.1.toNat < 2 ^ 32 := by
            rw [hp]
            rw [show (addmul1Step32 (w64 o) (w64 a) (w64 b) (w64 cy)).1
                  = (addCarry32 (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).2
                                (w64 o)).2 from rfl]
            unfold addCarry32
            simp only [BitVec.toNat_and,
                       show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
            rw [Nat.and_two_pow_sub_one_eq_mod _ 32]
            have hpos : (0 : Nat) < 2 ^ 32 := by positivity
            exact Nat.mod_lt _ hpos
          have hmask : (UInt64.ofNat p.1.toNat &&& 0xFFFFFFFF : UInt64)
              = UInt64.ofNat p.1.toNat := by
            apply UInt64.toNat.inj
            simp only [UInt64.toNat_and, UInt64.toNat_ofNat',
                       show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from by decide]
            rw [Nat.mod_eq_of_lt (by omega : p.1.toNat < 2 ^ 64),
                Nat.and_two_pow_sub_one_eq_mod _ 32, Nat.mod_eq_of_lt hp1_lt]
          rw [hmask]
          congr 1
          -- UInt64.ofNat p.1.toNat = UInt64.ofNat headLimb.toNat
          -- headLimb = BitVec.ofNat 32 p.1.toNat, so headLimb.toNat = p.1.toNat (mod 2^32) = p.1.toNat.
          rw [hheadLimb]
          apply UInt64.toNat.inj
          simp only [UInt64.toNat_ofNat', BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega : p.1.toNat < 2 ^ 64),
              Nat.mod_eq_of_lt hp1_lt,
              Nat.mod_eq_of_lt (by omega : p.1.toNat < 2 ^ 64)]
        · -- Tail at op0+4 — from IH.
          have hthis := hs'_mem
          rw [hra_op] at hthis
          exact hthis
      · -- Carry-out: chain of addmul steps.
        rw [hunfold, hs'_cy]
      · rw [hs'_b, hs1_b]
      · -- Frame: bb-block disjoint from both op and ap regions ⇒ unchanged.
        intro bb hbb_op hbb_ap
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
        -- And the head store at op0 doesn't touch bb.
        have hbb_head : MemoryModel.Disjoint (range bb 4) (range (regAddr s "op") 4) := by
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb_op
          obtain ⟨j, hj, hxj⟩ := h
          exact ⟨j, by simp [List.length_cons]; omega, hxj⟩
        rw [hmem1]
        rw [load32Mem_store32_disjoint s.mem bb op0 _ (by rw [hop0]; exact hbb_head)]

/-! ## §7  Bridge `Prop` and the full theorem

The bridge statement: the emitted U32 `mpn_addmul_1_32` body, run on a
state whose memory holds accumulator `out` at `op` and multiplicand `as`
at `ap` with `n = |as|` and `op` disjoint from `ap` (each `4·|as|`
bytes), and whose `cy` register starts unconstrained (the body's
`cy := 0` prelude zeroes it), terminates and lands a state with the
fuel-allowance `> 2·|as| + 2` (the loop's per-iteration cost plus
prelude). -/

def MpnAddmul132RefinesStmt : Prop :=
  ∀ (s : BignumState) (out as : List (BitVec 32)) (b : BitVec 32) (fuel : Nat),
    out.length = as.length →
    s.regs "b" = w64 b →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs32 s.mem (UInt64.ofNat (s.regs "op").toNat) out →
    memHoldsLimbs32 s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (4 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (4 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodyAddmul32 s = some s' ∧
      memHoldsLimbs32 s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnAddmul132 out as b 0).1 ∧
      s'.regs "cy" = w64 (mpnAddmul132 out as b 0).2

/-- **The bridge, fully proved.**  `mpnAddmul132Fd.body` (the emitted
    `cy := 0; while (n != 0) { loopBodyAddmul32 }`) refines (in the
    Jasmin operational semantics) the U32 multiply-accumulate kernel
    over byte memory at 4-byte stride.  Mirror of
    `MpnAddmul1Prototype.MpnAddmul1JasminRefines`. -/
theorem MpnAddmul132JasminRefines : MpnAddmul132RefinesStmt := by
  intro s out as b fuel hlen hb hn hop hap hdoa hfuel
  -- Step 1: the `cy := 0` prelude.
  set s0 : BignumState := setReg s "cy" 0 with hs0
  have hexec0 : execInstr s
      (.Cassgn (.Lvar { var := vr32 "cy" }) .AT_none (.sword .U32) (.Pconst 0))
      = some s0 := by
    simp only [execInstr, evalPExpr, vr32, bind, Option.bind, hs0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hcy0 : s0.regs "cy" = w64 0 := by
    rw [hs0]
    simp only [setReg, if_pos, if_true]
    apply BitVec.eq_of_toNat_eq
    simp only [w64, BitVec.toNat_ofNat]
    decide
  have hreg0 : ∀ x, x ≠ "cy" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hra0 : ∀ x, x ≠ "cy" → regAddr s0 x = regAddr s x := by
    intro x hx; simp only [regAddr, hreg0 x hx]
  have hb0 : s0.regs "b" = w64 b := by
    rw [hreg0 "b" (by decide)]; exact hb
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
    mpnAddmul132_loop out as s0 b 0 extra hlen hb0 hcy0 hn0' hop0 hap0 hdoa0
  refine ⟨s', ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) bodyAddmul32 s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0))
                       loopBodyAddmul32] s0 := by
      conv_lhs => rw [bodyAddmul32]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem
    simp only [regAddr] at hs'_mem
    exact hs'_mem
  · exact hs'_cy

/-! ## §8  Axiom audit -/

#print axioms bodyAddmul32_isCT
#print axioms mpnAddmul132Fd_body
#print axioms loopBodyAddmul32_straightLine
#print axioms loopBodyAddmul32_nonControl
#print axioms addmul1Step32_spec
#print axioms addmul1Step32_carry_lt
#print axioms mpnAddmul132_spec
#print axioms MpnAddmul132JasminRefines

end CatCrypt.Crypto.Jasmin.Examples.MpnAddmul132Refines
