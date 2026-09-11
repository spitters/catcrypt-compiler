/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.Mpn.Mul132Emit
public import CatCrypt.Crypto.Jasmin.Mpn.Add32Refines
public import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
public import CatCrypt.Crypto.Jasmin.BignumExec

@[expose] public section

set_option autoImplicit false

/-!
# `mpn_mul_1` Jasmin refinement at **U32 limb width**

This file is the U32 analogue of `Mpn.Mul1Prototype.MpnMul1JasminRefines`:
the emitted U32 `mpn_mul_1_32` kernel (`Mpn.Mul132Emit.mpnMul132Fd`, body
`Mpn.Mul132Emit.bodyMul32`) refines a pure functional spec
`mpnMul132 : List (BitVec 32) → BitVec 32 → BitVec 32 → List (BitVec 32) × BitVec 32`
over byte memory at 4-byte stride.

## Structure (mirrors `MpnMul1Prototype`)

* §2: pure reference `mul1Step32` / `mpnMul132` on `BitVec 32`.
* §3: the per-limb identity (`mul1Step32_spec`), built from the executable
  `BignumExec.mulx32` / `BignumExec.addCarry32` (the U32 analogues of the
  u64 `mulx` / `addCarry` that the U64 file consumed).  The carry register
  is stored in `BitVec 64` with its high half zero — the natural memory
  encoding used by the rest of the U32 ladder (matching how the U32 add
  bridge in `MpnAdd32Refines` encodes its `cf` GPR).
* §4: bridges between the executable U32 intrinsics and the pure step.
* §5: one-iteration step lemma `bignumExec_loopBodyMul32_step` — analogue
  of `bignumExec_loopBodyMul_step` at U32 stride (loads via `load32Mem`,
  stores via `Mem.store32`, advances by 4 bytes).
* §6: limb-list induction `mpnMul132_loop` — analogue of `mpnMul1_loop`
  at width 32.
* §7: the full bridge theorem `MpnMul132JasminRefines`.

## Reused U32 plumbing (from `MpnAdd32Refines`)

* `w64` / `w64_mask` / `u32_load_roundtrip` — the `BitVec 32 → BitVec 64`
  encoding lemmas.
* `memHoldsLimbs32` / `memHoldsLimbs32_store32_range_frame` — the U32
  memory predicate and its range-based frame.
* `resolveAddr_vr64` — `resolveAddr` of a U64 register at offset 0 yields
  `regAddr`.

## Reused stride-parametric helpers (from `MpnAddPrototype`)

* `regAddr_advance_at` — U32 stride-4 address advance.
* `range_op_head_tail_disjoint_4` — U32 op-buffer self-separation.
* `bignumExecFuel_loop_step_generic` / `bignumExecFuel_loop_exit_generic`
  — generic `Cwhile` step/exit rules (work for any straight-line body).
* `evalPExpr_neq_zero_true` / `evalPExpr_neq_zero_false` — the U64 `n !=
  0` loop guard.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.Mul132Refines

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.Mul132Emit
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
open CatCrypt.Crypto.Jasmin.Mpn.Add32Refines

/-! ## §0  Local U32-encoding helpers (mirror `MpnAdd32Refines`'s private
    `w64` / `w64_mask` / `u32_load_roundtrip`, which are file-local).

These small private definitions re-establish the `BitVec 32 → BitVec 64`
encoding lemmas this file needs — `MpnAdd32Refines` keeps them `private`,
so we declare local copies (same shape, same proofs).  Keeping them
`private` to this file preserves the same scope hygiene. -/

/-- Promote a `BitVec 32` value `w` to a `BitVec 64` (zero-extend). -/
def w64 (w : BitVec 32) : BitVec 64 := BitVec.ofNat 64 w.toNat

/-- A `w64`-encoded `BitVec 32` value masked to the low 32 bits is itself. -/
theorem w64_mask (w : BitVec 32) : w64 w &&& mask32 = w64 w := by
  unfold w64 mask32
  have hzx : (BitVec.ofNat 64 w.toNat) = BitVec.setWidth 64 w := by
    apply BitVec.eq_of_toNat_eq
    have hw : w.toNat < 2 ^ 32 := w.isLt
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth,
               Nat.mod_eq_of_lt (by omega : w.toNat < 2 ^ 64),
               Nat.mod_eq_of_lt hw]
  rw [hzx]
  bv_decide

/-- Loading a `BitVec 32` limb from memory and decoding through
    `BitVec.ofNat 64 _.toNat` recovers `w64 w`. -/
theorem u32_load_roundtrip (w : BitVec 32) :
    BitVec.ofNat 64 (UInt64.ofNat w.toNat).toNat = w64 w := by
  have hw : w.toNat < 2 ^ 32 := w.isLt
  apply BitVec.eq_of_toNat_eq
  unfold w64
  simp only [BitVec.toNat_ofNat, UInt64.toNat_ofNat']
  omega

/-! ## §1  Directly provable facts about the emitted U32 kernel -/

/-- The emitted U32 `mpn_mul_1_32` body is constant-time-shaped: the
    `Cwhile` guard reads only the public length `n`. -/
theorem bodyMul32_isCT : isCT_Cmd bodyMul32 = true := by decide

/-- The U32 `FunDecl`'s body is *literally* `bodyMul32`. -/
theorem mpnMul132Fd_body : mpnMul132Fd.body = bodyMul32 := rfl

/-! ## §2  Pure functional reference for U32 mul_1

`mul1Step32 a b cy = (out, cy')` on `BitVec 32`: a single limb of the
scalar multiplication, threaded with a `BitVec 32` running carry.  The
identity `out + 2^32 · cy' = a·b + cy` (in `Nat`) is the §3 leaf. -/

/-- One u32 mul_1 step on `BitVec 32`: multiply limb `a` by the scalar
    `b`, add the running carry `cy`, and split into `(out, cy')`.
    `out = (a·b + cy) mod 2^32`, `cy' = (a·b + cy) div 2^32`. -/
def mul1Step32 (a b cy : BitVec 32) : BitVec 32 × BitVec 32 :=
  let prod : Nat := a.toNat * b.toNat + cy.toNat
  (BitVec.ofNat 32 (prod % 2 ^ 32), BitVec.ofNat 32 (prod / 2 ^ 32))

/-- Pure reference for `mpn_mul_1` at u32: multiply a u32 limb list by a
    scalar `b`, threading a u32 carry `cy`.  Returns `(result limbs,
    final carry-out)`. -/
def mpnMul132 : List (BitVec 32) → BitVec 32 → BitVec 32 →
    (List (BitVec 32) × BitVec 32)
  | a :: as, b, cy =>
      let (r, cy') := mul1Step32 a b cy
      let (rs, fcy) := mpnMul132 as b cy'
      (r :: rs, fcy)
  | [], _, cy => ([], cy)

/-! ## §3  Functional spec: the carry-chain invariant on `Nat` -/

/-- The output of `mul1Step32` denotes the unique split of `a·b + cy`
    into low/high u32 halves.  Both halves are `< 2^32`. -/
theorem mul1Step32_lt (a b cy : BitVec 32) :
    (mul1Step32 a b cy).1.toNat < 2 ^ 32 ∧
    (mul1Step32 a b cy).2.toNat < 2 ^ 32 := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [mul1Step32, BitVec.toNat_ofNat]
    have hpos : (0 : Nat) < 2 ^ 32 := by positivity
    exact Nat.mod_lt _ hpos

/-- Single-step MUL identity on `Nat`:
    `mul1Step32 a b cy` produces `(out, cy')` with
    `out + 2^32 · cy' = a · b + cy`. -/
theorem mul1Step32_spec (a b cy : BitVec 32) :
    (mul1Step32 a b cy).1.toNat + 2 ^ 32 * (mul1Step32 a b cy).2.toNat
      = a.toNat * b.toNat + cy.toNat := by
  simp only [mul1Step32, BitVec.toNat_ofNat]
  -- prod = a·b + cy < (2^32-1)·(2^32-1) + (2^32-1) < 2^64.
  set prod : Nat := a.toNat * b.toNat + cy.toNat with hprod
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  have hcy : cy.toNat < 2 ^ 32 := cy.isLt
  have hprod_lt : prod < 2 ^ 64 := by
    have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
    have hmul : a.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h_arith : (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) < 2 ^ 32 * 2 ^ 32 := by decide
    omega
  have hdiv_lt : prod / 2 ^ 32 < 2 ^ 32 := by
    have hpos : (0 : Nat) < 2 ^ 32 := by positivity
    have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
    rw [Nat.div_lt_iff_lt_mul hpos]
    omega
  rw [Nat.mod_eq_of_lt hdiv_lt]
  omega

/-- Main functional spec — proved by induction on the limb list. -/
theorem mpnMul132_spec :
    ∀ (a : List (BitVec 32)) (b cy : BitVec 32),
      Mpn.GenericWidth.toNatW 32 (mpnMul132 a b cy).1
        + (2 ^ 32) ^ a.length * (mpnMul132 a b cy).2.toNat
      = Mpn.GenericWidth.toNatW 32 a * b.toNat + cy.toNat := by
  intro a
  induction a with
  | nil =>
    intro b cy
    simp [mpnMul132, Mpn.GenericWidth.toNatW]
  | cons a as ih =>
    intro b cy
    set p := mul1Step32 a b cy with hp
    have hstep := mul1Step32_spec a b cy
    rw [← hp] at hstep
    set q := mpnMul132 as b p.2 with hq
    have htail := ih b p.2
    rw [← hq] at htail
    have hunfold : mpnMul132 (a :: as) b cy = (p.1 :: q.1, q.2) := by
      simp only [mpnMul132, hp, hq]
    rw [hunfold]
    simp only [Mpn.GenericWidth.toNatW, List.length_cons]
    have hpow : (2 ^ 32) ^ (as.length + 1) = 2 ^ 32 * (2 ^ 32) ^ as.length := by
      rw [pow_succ]; ring
    rw [hpow]
    -- IH scaled by 2^32 + head step close the linear goal.
    have hkey : 2 ^ 32 * Mpn.GenericWidth.toNatW 32 q.1
        + 2 ^ 32 * ((2 ^ 32) ^ as.length * q.2.toNat)
        = 2 ^ 32 * (Mpn.GenericWidth.toNatW 32 as * b.toNat + p.2.toNat) := by
      rw [← htail]; ring
    have hmono : 2 ^ 32 * (2 ^ 32) ^ as.length * q.2.toNat
        = 2 ^ 32 * ((2 ^ 32) ^ as.length * q.2.toNat) := by ring
    rw [hmono]
    have hexpand : (a.toNat + 2 ^ 32 * Mpn.GenericWidth.toNatW 32 as) * b.toNat
        = a.toNat * b.toNat + 2 ^ 32 * (Mpn.GenericWidth.toNatW 32 as * b.toNat) := by ring
    rw [hexpand]
    omega

/-! ## §4  MULX/ADD bridges: executable U32 intrinsics match the pure step

The emitted `#MULX_32` runs `BignumExec.mulx32`; `#ADD_32` runs
`BignumExec.addCarry32`.  Bridge these to the pure `mul1Step32`. -/

/-- The high word of `mulx32 b a` is at most `2^32 - 2` (the schoolbook
    fact that lets `cy' = hi + c` not overflow into bit 32). -/
theorem mulx32_hi_le (a b : BitVec 32) :
    (mulx32 (w64 b) (w64 a)).1.toNat ≤ 2 ^ 32 - 2 := by
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  -- The high word equals `(b.toNat * a.toNat) / 2^32`.
  unfold mulx32
  rw [w64_mask a, w64_mask b]
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight]
  -- (w64 b * w64 a) on BitVec 64 = b.toNat * a.toNat (no wrap, since both < 2^32).
  have hwmul : (w64 b * w64 a).toNat = b.toNat * a.toNat := by
    unfold w64
    have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
    have hba_lt : b.toNat * a.toNat < 2 ^ 64 := by
      have := Nat.mul_lt_mul'' hb ha; omega
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat,
               Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64),
               Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 64),
               Nat.mod_eq_of_lt hba_lt]
  rw [hwmul]
  -- ((b·a) >>> 32) & mask32 . toNat = ((b·a) / 2^32) % 2^32, and that ≤ 2^32 - 2.
  rw [Nat.shiftRight_eq_div_pow]
  rw [show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod _ 32]
  have hp_le : b.toNat * a.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hdiv_le : b.toNat * a.toNat / 2 ^ 32 ≤ 2 ^ 32 - 2 := by
    have hpos : (0 : Nat) < 2 ^ 32 := by positivity
    calc b.toNat * a.toNat / 2 ^ 32
        ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right hp_le
      _ = 2 ^ 32 - 2 := by norm_num
  -- And `(b·a / 2^32) % 2^32 = b·a / 2^32` since `b·a / 2^32 < 2^32`.
  rw [Nat.mod_eq_of_lt (by omega)]
  exact hdiv_le

/-- `mulx32_toNat` recombination: `hi · 2^32 + lo = b · a` (the full
    32×32→64 product, split little-endian).  Stated on the natural
    numbers of the low/high `BitVec 64` words.  -/
theorem mulx32_toNat (a b : BitVec 32) :
    (mulx32 (w64 b) (w64 a)).2.toNat
      + 2 ^ 32 * (mulx32 (w64 b) (w64 a)).1.toNat
      = b.toNat * a.toNat := by
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  unfold mulx32
  rw [w64_mask a, w64_mask b]
  -- The full product fits in 64 bits.
  have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
  have hba_lt : b.toNat * a.toNat < 2 ^ 64 := by
    have := Nat.mul_lt_mul'' hb ha; omega
  have hwmul : (w64 b * w64 a).toNat = b.toNat * a.toNat := by
    unfold w64
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat,
               Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64),
               Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 64),
               Nat.mod_eq_of_lt hba_lt]
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, hwmul,
             show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod _ 32,
      Nat.and_two_pow_sub_one_eq_mod _ 32,
      Nat.shiftRight_eq_div_pow]
  -- (b·a) % 2^32 + 2^32 * ((b·a / 2^32) % 2^32) = b·a.
  have hdiv_lt : b.toNat * a.toNat / 2 ^ 32 < 2 ^ 32 := by
    have hpos : (0 : Nat) < 2 ^ 32 := by positivity
    rw [Nat.div_lt_iff_lt_mul hpos]; omega
  rw [Nat.mod_eq_of_lt hdiv_lt]
  omega

/-- `addCarry32` carry-out is a single bit. -/
theorem addCarry32_carry_le (a b : BitVec 64) : (addCarry32 a b).1.toNat ≤ 1 := by
  unfold addCarry32
  simp only [BitVec.toNat_and,
             show ((1 : BitVec 64).toNat) = 1 from rfl]
  rw [Nat.and_two_pow_sub_one_eq_mod _ 1]
  omega

/-- `addCarry32` low word identity for u32-encoded operands:
    `lo' + 2^32 · cf = (a &&& mask32).toNat + (b &&& mask32).toNat`. -/
theorem addCarry32_spec (a b : BitVec 64) :
    (addCarry32 a b).2.toNat + 2 ^ 32 * (addCarry32 a b).1.toNat
      = (a &&& mask32).toNat + (b &&& mask32).toNat := by
  unfold addCarry32
  -- Let `am, bm` be the masked inputs.  am, bm < 2^32; sum am+bm < 2^33 < 2^64.
  set am : BitVec 64 := a &&& mask32 with ham
  set bm : BitVec 64 := b &&& mask32 with hbm
  have ham_lt : am.toNat < 2 ^ 32 := by
    rw [ham]
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    have hpos : (0 : Nat) < 2 ^ 32 := by positivity
    exact Nat.mod_lt _ hpos
  have hbm_lt : bm.toNat < 2 ^ 32 := by
    rw [hbm]
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    have hpos : (0 : Nat) < 2 ^ 32 := by positivity
    exact Nat.mod_lt _ hpos
  have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
  have hsum_lt : am.toNat + bm.toNat < 2 ^ 64 := by omega
  -- Compute the BitVec 64 sum and its split.
  simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ushiftRight,
             show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide,
             show ((1 : BitVec 64).toNat) = 1 from rfl]
  rw [Nat.mod_eq_of_lt hsum_lt,
      Nat.and_two_pow_sub_one_eq_mod (am.toNat + bm.toNat) 32,
      Nat.and_two_pow_sub_one_eq_mod _ 1, Nat.shiftRight_eq_div_pow]
  have hdiv_lt : (am.toNat + bm.toNat) / 2 ^ 32 < 2 := by
    have hpos : (0 : Nat) < 2 ^ 32 := by positivity
    have h33 : (2 : Nat) ^ 33 = 2 * 2 ^ 32 := by decide
    rw [Nat.div_lt_iff_lt_mul hpos]
    omega
  rw [show (2 : Nat) ^ 1 = 2 from rfl, Nat.mod_eq_of_lt hdiv_lt]
  omega

/-! ## §5  The bridge: composed `mulx32` + `addCarry32` matches `mul1Step32`

The emitted body computes:
```
(hi, lo) = mulx32 b t
(cf, lo') = addCarry32 lo cy
out = lo'
cy_new = hi + cf
```
We show `(out, cy_new)` equals `mul1Step32 a b cy` (in the natural u32
representation).  Stated on `BitVec 64` shapes (the runtime form). -/

/-- `w64`-encoded `BitVec 32` value's `BitVec.toNat` equals its u32
    `.toNat`. -/
theorem w64_toNat (w : BitVec 32) : (w64 w).toNat = w.toNat := by
  unfold w64
  have hw : w.toNat < 2 ^ 32 := w.isLt
  simp only [BitVec.toNat_ofNat]
  omega

/-- The composed body: full natural-number identity.
    `out.toNat + 2^32 · cy_new.toNat = a.toNat · b.toNat + cy.toNat`
    where `out`, `cy_new` are the runtime `BitVec 64` outputs (high half
    zero) of the chain, and the registers `a`, `b`, `cy` are u32-encoded. -/
theorem mul1Body32_natIdentity (a b cy : BitVec 32) :
    (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).2.toNat
      + 2 ^ 32 * ((mulx32 (w64 b) (w64 a)).1
                  + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1).toNat
      = a.toNat * b.toNat + cy.toNat := by
  -- 1. `mulx32 b a`: lo + 2^32 · hi = b · a (via mulx32_toNat).
  have hmul := mulx32_toNat a b
  have hhi_le := mulx32_hi_le a b
  -- lo is masked, so lo < 2^32.
  have hlo_lt : (mulx32 (w64 b) (w64 a)).2.toNat < 2 ^ 32 := by
    unfold mulx32
    simp only [BitVec.toNat_and, BitVec.toNat_mul,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    have hpos : (0 : Nat) < 2 ^ 32 := by positivity
    exact Nat.mod_lt _ hpos
  -- 2. `addCarry32 lo (w64 cy)`: lo' + 2^32 · cf = (lo & mask32) + (w64 cy & mask32).
  have hadd := addCarry32_spec (mulx32 (w64 b) (w64 a)).2 (w64 cy)
  -- Since lo < 2^32, `lo &&& mask32 = lo`; and `(w64 cy) &&& mask32 = w64 cy` by `w64_mask`.
  have hlo_mask : ((mulx32 (w64 b) (w64 a)).2 &&& mask32).toNat
      = (mulx32 (w64 b) (w64 a)).2.toNat := by
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlo_lt]
  have hcy_mask : ((w64 cy) &&& mask32).toNat = (w64 cy).toNat := by
    rw [w64_mask cy]
  rw [hlo_mask, hcy_mask] at hadd
  have hcf_le := addCarry32_carry_le (mulx32 (w64 b) (w64 a)).2 (w64 cy)
  -- 3. `cy_new = hi + cf`: no wrap (hi ≤ 2^32 - 2, cf ≤ 1).
  have hcy_new_toNat : ((mulx32 (w64 b) (w64 a)).1
        + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1).toNat
      = (mulx32 (w64 b) (w64 a)).1.toNat
        + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1.toNat := by
    have hbound : (mulx32 (w64 b) (w64 a)).1.toNat
        + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1.toNat < 2 ^ 64 := by
      have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
      omega
    simp only [BitVec.toNat_add, Nat.mod_eq_of_lt hbound]
  rw [hcy_new_toNat, w64_toNat cy] at *
  -- Combine: lo' + 2^32 · hi + 2^32 · cf = (lo + cy) + 2^32 · hi = b · a + cy = a · b + cy.
  have hcy_lt : cy.toNat < 2 ^ 32 := cy.isLt
  have ha_lt : a.toNat < 2 ^ 32 := a.isLt
  have hb_lt : b.toNat < 2 ^ 32 := b.isLt
  have hcommute : a.toNat * b.toNat = b.toNat * a.toNat := by ring
  rw [hcommute]
  omega

/-- The composed body's outputs equal the u32-encoded `mul1Step32`. -/
theorem mul1Body32_eq_step (a b cy : BitVec 32) :
    (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).2 = w64 (mul1Step32 a b cy).1 ∧
    (mulx32 (w64 b) (w64 a)).1 + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1
      = w64 (mul1Step32 a b cy).2 := by
  -- Reduce to the natural-number identity + `< 2^32` bounds on both sides.
  -- Bounds: hi ≤ 2^32-2 (mulx32_hi_le), cf ≤ 1 (addCarry32_carry_le).
  have hhi_le : (mulx32 (w64 b) (w64 a)).1.toNat ≤ 2 ^ 32 - 2 := mulx32_hi_le a b
  have hcf_le : (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1.toNat ≤ 1 :=
    addCarry32_carry_le _ _
  -- lo' is masked, lo' < 2^32.
  have hlo'_lt : (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).2.toNat < 2 ^ 32 := by
    unfold addCarry32
    simp only [BitVec.toNat_and,
               show (mask32 : BitVec 64).toNat = 2 ^ 32 - 1 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    have hpos : (0 : Nat) < 2 ^ 32 := by positivity
    exact Nat.mod_lt _ hpos
  -- cy_new < 2^32.
  have hcyn_toNat : ((mulx32 (w64 b) (w64 a)).1
        + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1).toNat
      = (mulx32 (w64 b) (w64 a)).1.toNat
        + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1.toNat := by
    have h64 : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
    have hbound : (mulx32 (w64 b) (w64 a)).1.toNat
        + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1.toNat < 2 ^ 64 := by omega
    simp only [BitVec.toNat_add, Nat.mod_eq_of_lt hbound]
  have hcyn_lt : ((mulx32 (w64 b) (w64 a)).1
        + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1).toNat < 2 ^ 32 := by
    rw [hcyn_toNat]; omega
  -- The full identity in Nat (from `mul1Body32_natIdentity`).
  have hbody := mul1Body32_natIdentity a b cy
  have hstep := mul1Step32_spec a b cy
  have hmout_lt : (mul1Step32 a b cy).1.toNat < 2 ^ 32 := (mul1Step32 a b cy).1.isLt
  have hmcy_lt : (mul1Step32 a b cy).2.toNat < 2 ^ 32 := (mul1Step32 a b cy).2.isLt
  -- Combine: lo' + 2^32 · cy_new = mout + 2^32 · mcy with both halves < 2^32 ⇒ equal.
  have hcombo : (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).2.toNat
      + 2 ^ 32 * ((mulx32 (w64 b) (w64 a)).1
                  + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1).toNat
      = (mul1Step32 a b cy).1.toNat + 2 ^ 32 * (mul1Step32 a b cy).2.toNat := by
    omega
  -- Uniqueness of the split.
  have hlo'_eq : (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).2.toNat
      = (mul1Step32 a b cy).1.toNat := by
    have h1 : ((addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).2.toNat
          + 2 ^ 32 * ((mulx32 (w64 b) (w64 a)).1
                      + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1).toNat) % 2 ^ 32
        = (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).2.toNat :=
      by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo'_lt]
    have h2 : ((mul1Step32 a b cy).1.toNat + 2 ^ 32 * (mul1Step32 a b cy).2.toNat) % 2 ^ 32
        = (mul1Step32 a b cy).1.toNat :=
      by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmout_lt]
    rw [← h1, ← h2, hcombo]
  have hcyn_eq : ((mulx32 (w64 b) (w64 a)).1
        + (addCarry32 (mulx32 (w64 b) (w64 a)).2 (w64 cy)).1).toNat
      = (mul1Step32 a b cy).2.toNat := by
    omega
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [hlo'_eq, w64_toNat]
  · apply BitVec.eq_of_toNat_eq
    rw [hcyn_eq, w64_toNat]

/-! ## §6  One U32 mul_1 iteration as an explicit state update -/

/-- `loopBodyMul32` consists only of `Cassgn`/`Copn` — it is straight-line. -/
theorem loopBodyMul32_straightLine : InstrR.bodyIsStraightLine loopBodyMul32 := by
  simp only [loopBodyMul32, load32At0, mulxCopn32, addCopn32, store32At0,
             regAdd32, ptrImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBodyMul32` is non-control. -/
theorem loopBodyMul32_nonControl : ∀ i ∈ loopBodyMul32, i.isNonControl := by
  intro i hi
  simp only [loopBodyMul32, load32At0, mulxCopn32, addCopn32, store32At0,
             regAdd32, ptrImm, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

set_option maxHeartbeats 1200000 in
set_option linter.unusedSimpArgs false in
/-- **One U32 iteration of `loopBodyMul32` as a state update.**
    Loads `a` from `ap`, computes `MULX_32 b t = (hi, lo)`, adds carry
    `ADD_32 lo cy = (c, lo')`, stores `lo'` at `op`, recombines
    `cy := hi + c`, advances `ap, op` by 4 bytes, decrements `n` by 1.

    The carry register `cy` is u32-encoded in `BitVec 64` (high half zero)
    and the scalar `b` lives in a u32 register encoded as `w64 b`; both
    are read-only across iterations (only `cy` is updated; `b` is invariant).
-/
theorem bignumExec_loopBodyMul32_step (s : BignumState) (a b cy : BitVec 32)
    (hb : s.regs "b" = w64 b)
    (hcy : s.regs "cy" = w64 cy)
    (ha : load32Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat)) :
    ∃ s', bignumExec loopBodyMul32 s = some s' ∧
      s'.mem = Mem.store32 s.mem (regAddr s "op")
        (UInt64.ofNat (mul1Step32 a b cy).1.toNat) ∧
      s'.regs "cy" = w64 (mul1Step32 a b cy).2 ∧
      s'.regs "ap" = s.regs "ap" + 4 ∧
      s'.regs "op" = s.regs "op" + 4 ∧
      s'.regs "n" = s.regs "n" - 1 ∧
      s'.regs "b" = s.regs "b" := by
  -- Unfold the body and the dispatchers.
  simp only [loopBodyMul32, load32At0, mulxCopn32, addCopn32, store32At0,
             regAdd32, ptrImm,
             bignumExec, execInstr, evalPExpr, pv32, pv64,
             resolveAddr_vr64, vr32, vr64,
             setReg_mem, setReg_regs, storeMem32_mem_proj, storeMem32_regs_proj,
             Option.bind_some, bind, Option.bind,
             writeMulxBundle, writeSubBundle]
  -- Resolve the load address (offset 0), fire the load.
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem32_regs_proj, storeMem32_mem_proj,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             ha, Option.bind_some, bind, Option.bind] at *
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [ha]
  simp only [Option.bind_some, bind, Option.bind]
  -- The witness state is now fully concrete.
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [setReg_regs, setReg_mem, storeMem32_mem_proj, storeMem32_regs_proj,
               regAddr, String.reduceEq, ↓reduceIte, reduceIte, hcy, hb,
               show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 4 = (4 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]
  · -- Memory: stored value equals `UInt64.ofNat (mul1Step32 a b cy).1.toNat`.
    rw [u32_load_roundtrip a]
    have hstep := (mul1Body32_eq_step a b cy).1
    -- hstep: addCarry32 ... = w64 (mul1Step32 ...).1.
    -- Goal: UInt64.ofNat lo'.toNat = UInt64.ofNat (mul1Step32 a b cy).1.toNat.
    congr 1
    rw [hstep, w64_toNat]
  · -- Carry register: `hi + cf = w64 (mul1Step32 ...).2`.
    rw [u32_load_roundtrip a]
    exact (mul1Body32_eq_step a b cy).2

/-! ## §7  The U32 loop, by induction on the limb list -/

/-- Range-based U32 frame for `memHoldsLimbs32` (imported via the alias). -/
theorem memHoldsLimbs32_store32_range_frame' (m : Mem) (base st : UInt64)
    (v : UInt64) (ws : List (BitVec 32))
    (hdisj : MemoryModel.Disjoint (range st 4) (range base (4 * ws.length)))
    (hmem : memHoldsLimbs32 m base ws) :
    memHoldsLimbs32 (Mem.store32 m st v) base ws :=
  memHoldsLimbs32_store32_range_frame m base st v ws hdisj hmem

/-- **The U32 mul_1 loop, by induction on the limb list.**  Clone of
    `Mpn.Mul1Prototype.mpnMul1_loop` at limb width 32.  Single-buffer
    (scalar `b` is read-only). -/
theorem mpnMul132_loop :
    ∀ (as : List (BitVec 32)) (s : BignumState) (b cy : BitVec 32) (extra : Nat),
      s.regs "b" = w64 b →
      s.regs "cy" = w64 cy →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs32 s.mem (regAddr s "ap") as →
      MemoryModel.Disjoint (range (regAddr s "op") (4 * as.length))
        (range (regAddr s "ap") (4 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) loopBodyMul32] s
              = some s' ∧
        memHoldsLimbs32 s'.mem (regAddr s "op") (mpnMul132 as b cy).1 ∧
        s'.regs "cy" = w64 (mpnMul132 as b cy).2 ∧
        s'.regs "b" = s.regs "b" ∧
        (∀ bb, MemoryModel.Disjoint (range bb 4)
              (range (regAddr s "op") (4 * as.length)) →
            load32Mem s'.mem bb = load32Mem s.mem bb) := by
  intro as
  induction as with
  | nil =>
    intro s b cy extra _ hcy hn _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 32)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) = some 0 :=
        evalPExpr_neq_zero_false s (pv64 "n")
          (by simp only [pv64, vr64, evalPExpr]; rw [hn0])
      exact bignumExecFuel_loop_exit_generic emptyRegistry extra _ loopBodyMul32 s hcond
    · simp [mpnMul132]
    · simpa [mpnMul132] using hcy
    · rfl
    · intro bb _; rfl
  | cons a as ih =>
    intro s b cy extra hb hcy hn hap hdoa
    have hsize : 4 * (as.length + 1) < 2 ^ 64 := by
      simpa [List.length_cons] using
        disjoint_range_lt (regAddr s "op") (regAddr s "ap")
          (4 * (a :: as).length) (by simp only [List.length_cons]; omega)
          (by simpa using hdoa)
    have hLsucc : as.length + 1 < 2 ^ 64 := by omega
    have hn_ne : s.regs "n" ≠ 0 := by
      rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
    obtain ⟨hap_head, hap_tail⟩ := hap
    -- One U32 iteration.
    obtain ⟨s1, hs1, hs1_mem, hs1_cy, hs1_ap, hs1_op, hs1_n, hs1_b⟩ :=
      bignumExec_loopBodyMul32_step s a b cy hb hcy hap_head
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
        (UInt64.ofNat (mul1Step32 a b cy).1.toNat) := by
      simpa [hop0, regAddr] using hs1_mem
    -- Frame the tail of `ap` across the head store at `op0`.
    have hdoa_store_aptail :
        MemoryModel.Disjoint (range op0 4) (range (regAddr s "ap" + 4) (4 * as.length)) := by
      refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
      · obtain ⟨j, hj, hxj⟩ := h
        exact ⟨j, by simp [List.length_cons]; omega, hxj⟩
      · obtain ⟨j, hj, hxj⟩ := h
        refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
        rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
        rw [hxj]; ac_rfl
    have hap1 : memHoldsLimbs32 s1.mem (regAddr s1 "ap") as := by
      rw [hra_ap, hmem1]
      exact memHoldsLimbs32_store32_range_frame s.mem (regAddr s "ap" + 4) op0 _ as
        hdoa_store_aptail hap_tail
    -- Disjointness for the IH (tail op-region vs. tail ap-region).
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
    have hcy1 : s1.regs "cy" = w64 (mul1Step32 a b cy).2 := hs1_cy
    have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
      rw [hs1_n, hn]
      simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
    have hb1 : s1.regs "b" = w64 b := by rw [hs1_b]; exact hb
    -- Apply the IH on the tail with carry `(mul1Step32 ...).2`.
    obtain ⟨s', hs', hs'_mem, hs'_cy, hs'_b, hs'_frame⟩ :=
      ih s1 b (mul1Step32 a b cy).2 extra hb1 hcy1 hn1 hap1 hdoa1
    refine ⟨s', ?_, ?_, ?_, ?_, ?_⟩
    · -- Fuel: 2·(L+1)+3+extra = (2·L+2+extra)+3.
      have hfuel : 2 * (a :: as).length + 3 + extra
          = (2 * as.length + 2 + extra) + 3 := by
        simp only [List.length_cons]; ring
      rw [hfuel]
      have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) = some 1 :=
        evalPExpr_neq_zero_true s (pv64 "n") (s.regs "n")
          (by simp only [pv64, vr64, evalPExpr]) hn_ne
      refine bignumExecFuel_loop_step_generic emptyRegistry
        (2 * as.length + 2 + extra) _ loopBodyMul32 loopBodyMul32_straightLine
        loopBodyMul32_nonControl s s1 s' hcond hs1 ?_
      simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
              from by omega] using hs'
    · -- Memory at op: head limb at `op0` (preserved by IH frame), tail by IH.
      rw [hmem1] at hs'_frame
      have hsep : MemoryModel.Disjoint (range op0 4) (range (op0 + 4) (4 * as.length)) :=
        range_op_head_tail_disjoint_4 op0 as.length (by omega)
      refine ⟨?_, ?_⟩
      · -- Head limb at `op0`.
        rw [hs'_frame op0 (by rw [hra_op]; exact hsep)]
        have hread := load32Mem_store32_same s.mem op0
          (UInt64.ofNat (mul1Step32 a b cy).1.toNat)
        rw [hread]
        -- `UInt64.ofNat (sum.toNat) &&& 0xFFFFFFFF = UInt64.ofNat sum.toNat`,
        -- since sum : BitVec 32 has high half zero.
        have hsum : (mul1Step32 a b cy).1.toNat < 2 ^ 32 := (mul1Step32 a b cy).1.isLt
        have hmask : (UInt64.ofNat (mul1Step32 a b cy).1.toNat
            &&& 0xFFFFFFFF : UInt64)
            = UInt64.ofNat (mul1Step32 a b cy).1.toNat := by
          apply UInt64.toNat.inj
          simp only [UInt64.toNat_and, UInt64.toNat_ofNat',
                     show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from by decide]
          rw [Nat.mod_eq_of_lt (by omega : (mul1Step32 a b cy).1.toNat < 2 ^ 64),
              Nat.and_two_pow_sub_one_eq_mod _ 32, Nat.mod_eq_of_lt hsum]
        rw [hmask]
        -- The head of `(mpnMul132 (a::as) b cy).1` is `(mul1Step32 a b cy).1`.
        rfl
      · -- Tail: from IH (op base `op0+4`).
        have hthis := hs'_mem
        rw [hra_op] at hthis
        exact hthis
    · -- Carry-out: chain of `mul1Step32`s.
      rw [hs'_cy]; simp only [mpnMul132]
    · -- `b` register invariant.
      rw [hs'_b, hs1_b]
    · -- Frame.
      intro bb hbb
      rw [hmem1] at hs'_frame
      have hbb_tail : MemoryModel.Disjoint (range bb 4)
          (range (regAddr s1 "op") (4 * as.length)) := by
        rw [hra_op]
        refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
        obtain ⟨j, hj, hxj⟩ := h
        refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
        rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
        rw [hxj]; ac_rfl
      rw [hs'_frame bb hbb_tail]
      have hbb_head : MemoryModel.Disjoint (range bb 4) (range (regAddr s "op") 4) := by
        refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
        obtain ⟨j, hj, hxj⟩ := h
        exact ⟨j, by simp [List.length_cons]; omega, hxj⟩
      rw [load32Mem_store32_disjoint s.mem bb (regAddr s "op") _ hbb_head]

/-! ## §8  Assembly: `MpnMul132JasminRefines` -/

/-- The bridge statement: starting from a state whose memory holds
    `as : List (BitVec 32)` at `ap`, with `n = |as|`, with the U32 `op`
    output region disjoint from the U32 `ap` input region (each
    `4·|as|` bytes), with the scalar `b : BitVec 32` u32-encoded into
    register `b` via `w64 b`, running `bodyMul32` under `emptyRegistry`
    lands a state whose memory at `op` holds `(mpnMul132 as b 0).1` and
    whose `cy` register holds `w64 (mpnMul132 as b 0).2`. -/
def MpnMul132RefinesStmt : Prop :=
  ∀ (s : BignumState) (as : List (BitVec 32)) (b : BitVec 32) (fuel : Nat),
    s.regs "b" = w64 b →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs32 s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (4 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (4 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodyMul32 s = some s' ∧
      memHoldsLimbs32 s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnMul132 as b 0).1 ∧
      s'.regs "cy" = w64 (mpnMul132 as b 0).2

/-- **The U32 bridge, fully proved.**  The emitted U32 `mpn_mul_1_32`
    Jasmin kernel (`bodyMul32 = [cy := 0; while (n != 0) loopBodyMul32]`)
    refines the pure reference `mpnMul132` over byte memory at 4-byte
    stride.  Mirror of `Mpn.Mul1Prototype.MpnMul1JasminRefines`. -/
theorem MpnMul132JasminRefines : MpnMul132RefinesStmt := by
  intro s as b fuel hb hn hap hdoa hfuel
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
    mpnMul132_loop as s0 b 0 extra hb0 hcy0 hn0' hap0 hdoa0
  refine ⟨s', ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) bodyMul32 s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) loopBodyMul32] s0 := by
      conv_lhs => rw [bodyMul32]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem
    simp only [regAddr] at hs'_mem
    exact hs'_mem
  · exact hs'_cy

/-! ## §9  Axiom audit -/

#print axioms bodyMul32_isCT
#print axioms mpnMul132Fd_body
#print axioms mul1Step32_spec
#print axioms mpnMul132_spec
#print axioms MpnMul132JasminRefines

end CatCrypt.Crypto.Jasmin.Mpn.Mul132Refines
