/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.BigInt
public import CatCrypt.Crypto.SecureCompilation.BigNatShift
public import CatCrypt.Crypto.SecureCompilation.ToomInterpolation

/-!
# Recursive integer Toom-Cook-3 multiplication on the `BigNat` carrier

A recursive Toom-Cook-3 multiply over the variable-width limb-list carrier
`bignumVal` (little-endian base `2^64`), with the value-correctness statement
`bignumVal (toom3 a b) = bignumVal a * bignumVal b`.  Above a fixed crossover
the algorithm splits each operand into three chunks, evaluates the two operands
at the five points `{0, 1, -1, -2, ∞}` through the signed `BigInt` carrier,
recurses on the five point-products, interpolates the six-scaled schoolbook
coefficients and divides by six, then recombines at base `(2^64)^m`; below the
crossover it uses the Karatsuba/schoolbook `mulDispatch`.

The five-point evaluation is at `{0, 1, -1, -2, ∞}`; the six-scaled
interpolation coefficients are the Bodrato identities.  The three-way
recombination reuses `toom3_schoolbook_split` from
`SecureCompilation.ToomInterpolation`.

## Main results

* `norm_length_le`, `bnSub_length_le`, `mkBigInt_mag` — carrier length bounds
  used for termination.
* `ev1` / `evm1` / `evm2` and their value (`ev1_val`, …) and length
  (`ev1_length`, …) lemmas — the signed operand-evaluations at `{1, -1, -2}`.
* `toom3Combine` / `toom3Combine_val` — the non-recursive interpolation and
  base-`(2^64)^m` recombination of the five point-products.
* `toom3` / `toom3_val` — the recursive multiply and its value correctness
  `bignumVal (toom3 a b) = bignumVal a * bignumVal b`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNatToom3

open CatCrypt.Crypto.SecureCompilation
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.ToomInterpolation (toom3_schoolbook_split)

/-! ## Carrier length bounds -/

/-- Normalization does not increase the limb count. -/
theorem norm_length_le : ∀ l : List (BitVec 64), (BigNat.norm l).length ≤ l.length
  | [] => Nat.le_refl 0
  | x :: xs => by
      have ih := norm_length_le xs
      cases hxs : BigNat.norm xs with
      | nil =>
          simp only [BigNat.norm, hxs]
          split <;> simp
      | cons y ys =>
          simp only [BigNat.norm, hxs]
          rw [hxs] at ih
          simp only [List.length_cons] at ih ⊢
          omega

/-- The magnitude of a smart-constructed integer is the normalized input. -/
theorem mkBigInt_mag (ng : Bool) (m : List (BitVec 64)) :
    (BigInt.mkBigInt ng m).mag = BigNat.norm m := by
  unfold BigInt.mkBigInt
  cases h : BigNat.norm m with
  | nil => simp
  | cons n ns => simp

/-- `selLimbs` never produces more limbs than its second operand. -/
theorem selLimbs_length_le (mask : BitVec 64) :
    ∀ (a b : List (BitVec 64)), (selLimbs mask a b).length ≤ b.length
  | [], b => by simp [selLimbs]
  | _ :: _, [] => by simp [selLimbs]
  | _ :: as, _ :: bs => by
      simp only [selLimbs, List.length_cons]
      have := selLimbs_length_le mask as bs
      omega

/-- Saturating subtraction does not exceed the first operand's length. -/
theorem satSub_length_le (a b : List (BitVec 64)) :
    (BigNat.satSub a b).length ≤ a.length := by
  simp only [BigNat.satSub]
  exact le_trans (selLimbs_length_le _ _ _) (by rw [List.length_replicate])

/-- Exact carrier subtraction does not exceed the wider operand. -/
theorem bnSub_length_le (a b : List (BitVec 64)) :
    (BigNatKaratsuba.bnSub a b).length ≤ max a.length b.length := by
  simp only [BigNatKaratsuba.bnSub]
  refine le_trans (satSub_length_le _ _) ?_
  rw [List.length_append, List.length_replicate]
  omega

/-- Signed addition widens the magnitude by at most one limb. -/
theorem add_mag_length_le (x y : BigInt) :
    (BigInt.add x y).mag.length ≤ max x.mag.length y.mag.length + 1 := by
  unfold BigInt.add
  by_cases hs : (x.neg == y.neg) = true
  · simp only [hs, cond_true, mkBigInt_mag]
    exact le_trans (norm_length_le _)
      (le_of_eq (BigNatKaratsuba.add_length x.mag y.mag))
  · rw [Bool.not_eq_true] at hs
    simp only [hs, cond_false]
    by_cases hb : BigNatCompare.ble x.mag y.mag = true
    · simp only [hb, cond_true, mkBigInt_mag]
      refine le_trans (norm_length_le _) (le_trans (bnSub_length_le _ _) ?_)
      omega
    · rw [Bool.not_eq_true] at hb
      simp only [hb, cond_false, mkBigInt_mag]
      refine le_trans (norm_length_le _) (le_trans (bnSub_length_le _ _) ?_)
      omega

/-- Negation preserves the magnitude length up to normalization. -/
theorem negate_mag_length_le (y : BigInt) :
    (BigInt.negate y).mag.length ≤ y.mag.length := by
  rw [BigInt.negate, mkBigInt_mag]; exact norm_length_le _

/-- Signed subtraction widens the magnitude by at most one limb. -/
theorem sub_mag_length_le (x y : BigInt) :
    (BigInt.sub x y).mag.length ≤ max x.mag.length y.mag.length + 1 := by
  rw [BigInt.sub]
  have h := add_mag_length_le x (BigInt.negate y)
  have hn := negate_mag_length_le y
  omega

/-! ## Signed operand-evaluations at `{1, -1, -2}` -/

/-- Evaluation of a three-chunk operand at the point `1`: `c₀ + c₁ + c₂`. -/
def ev1 (c0 c1 c2 : List (BitVec 64)) : BigInt :=
  BigInt.add (BigInt.add ⟨false, c0⟩ ⟨false, c1⟩) ⟨false, c2⟩

/-- Evaluation of a three-chunk operand at the point `-1`: `c₀ - c₁ + c₂`. -/
def evm1 (c0 c1 c2 : List (BitVec 64)) : BigInt :=
  BigInt.add (BigInt.sub ⟨false, c0⟩ ⟨false, c1⟩) ⟨false, c2⟩

/-- Evaluation of a three-chunk operand at the point `-2`:
    `c₀ - 2·c₁ + 4·c₂`, using repeated addition for the small scalars. -/
def evm2 (c0 c1 c2 : List (BitVec 64)) : BigInt :=
  BigInt.add
    (BigInt.sub ⟨false, c0⟩ (BigInt.add ⟨false, c1⟩ ⟨false, c1⟩))
    (BigInt.add (BigInt.add ⟨false, c2⟩ ⟨false, c2⟩)
      (BigInt.add ⟨false, c2⟩ ⟨false, c2⟩))

/-- The value of a nonnegative lift is the magnitude value. -/
theorem intVal_mk_false (c : List (BitVec 64)) :
    BigInt.intVal ⟨false, c⟩ = (bignumVal c : Int) := rfl

theorem ev1_val (c0 c1 c2 : List (BitVec 64)) :
    BigInt.intVal (ev1 c0 c1 c2)
      = (bignumVal c0 : Int) + bignumVal c1 + bignumVal c2 := by
  rw [ev1, BigInt.add_val, BigInt.add_val, intVal_mk_false, intVal_mk_false,
    intVal_mk_false]

theorem evm1_val (c0 c1 c2 : List (BitVec 64)) :
    BigInt.intVal (evm1 c0 c1 c2)
      = (bignumVal c0 : Int) - bignumVal c1 + bignumVal c2 := by
  rw [evm1, BigInt.add_val, BigInt.sub_val, intVal_mk_false, intVal_mk_false,
    intVal_mk_false]

theorem evm2_val (c0 c1 c2 : List (BitVec 64)) :
    BigInt.intVal (evm2 c0 c1 c2)
      = (bignumVal c0 : Int) - 2 * bignumVal c1 + 4 * bignumVal c2 := by
  rw [evm2]
  simp only [BigInt.add_val, BigInt.sub_val, intVal_mk_false]
  ring

theorem ev1_length (c0 c1 c2 : List (BitVec 64)) :
    (ev1 c0 c1 c2).mag.length ≤ max (max c0.length c1.length) c2.length + 2 := by
  have h1 := add_mag_length_le (⟨false, c0⟩ : BigInt) ⟨false, c1⟩
  have h2 := add_mag_length_le (BigInt.add (⟨false, c0⟩ : BigInt) ⟨false, c1⟩)
    (⟨false, c2⟩ : BigInt)
  simp only [ev1] at *
  omega

theorem evm1_length (c0 c1 c2 : List (BitVec 64)) :
    (evm1 c0 c1 c2).mag.length ≤ max (max c0.length c1.length) c2.length + 2 := by
  have h1 := sub_mag_length_le (⟨false, c0⟩ : BigInt) ⟨false, c1⟩
  have h2 := add_mag_length_le (BigInt.sub (⟨false, c0⟩ : BigInt) ⟨false, c1⟩)
    (⟨false, c2⟩ : BigInt)
  simp only [evm1] at *
  omega

theorem evm2_length (c0 c1 c2 : List (BitVec 64)) :
    (evm2 c0 c1 c2).mag.length ≤ max (max c0.length c1.length) c2.length + 3 := by
  have h1 := add_mag_length_le (⟨false, c1⟩ : BigInt) ⟨false, c1⟩
  have h2 := sub_mag_length_le (⟨false, c0⟩ : BigInt)
    (BigInt.add (⟨false, c1⟩ : BigInt) ⟨false, c1⟩)
  have h3 := add_mag_length_le (⟨false, c2⟩ : BigInt) ⟨false, c2⟩
  have h4 := add_mag_length_le (BigInt.add (⟨false, c2⟩ : BigInt) ⟨false, c2⟩)
    (BigInt.add (⟨false, c2⟩ : BigInt) ⟨false, c2⟩)
  have h5 := add_mag_length_le
    (BigInt.sub (⟨false, c0⟩ : BigInt) (BigInt.add ⟨false, c1⟩ ⟨false, c1⟩))
    (BigInt.add (BigInt.add (⟨false, c2⟩ : BigInt) ⟨false, c2⟩)
      (BigInt.add ⟨false, c2⟩ ⟨false, c2⟩))
  simp only [evm2] at *
  omega

/-! ## Sign-tracking product and exact division helpers -/

/-- A signed product whose magnitude is supplied externally (the recursive
    multiply), tagged with the exclusive-or of the operand signs. -/
theorem mulBI_val (x y : BigInt) (prod : List (BitVec 64))
    (h : bignumVal prod = bignumVal x.mag * bignumVal y.mag) :
    BigInt.intVal ⟨xor x.neg y.neg, prod⟩ = BigInt.intVal x * BigInt.intVal y := by
  rw [BigInt.intVal_eq, BigInt.intVal_eq x, BigInt.intVal_eq y]
  cases x.neg <;> cases y.neg <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false,
      cond_true, cond_false] <;>
    rw [h] <;> push_cast <;> ring

/-- Division of a signed integer by a small `Nat` divisor, carrying the sign
    through the smart constructor. -/
def divRaw (x : BigInt) (d : Nat) : BigInt :=
  BigInt.mkBigInt x.neg (BigNatDivMod.div x.mag (BigNat.ofNat d))

/-- Value of an exact division: when `d ∣ intVal x`, `divRaw x d` is `intVal x / d`. -/
theorem divRaw_val (x : BigInt) (d : Nat) (h : (d : Int) ∣ BigInt.intVal x) :
    BigInt.intVal (divRaw x d) = BigInt.intVal x / (d : Int) := by
  rw [divRaw, BigInt.intVal_mkBigInt, BigNatDivMod.div_val, BigNat.toNat_ofNat,
    BigInt.intVal_eq]
  cases hx : x.neg with
  | false => simp only [cond_false]; rw [Int.natCast_div]
  | true =>
      rw [BigInt.intVal_eq, hx] at h
      simp only [cond_true] at h
      have hd : (d : Int) ∣ (bignumVal x.mag : Int) := (dvd_neg).mp h
      simp only [cond_true]
      rw [Int.natCast_div, Int.neg_ediv_of_dvd hd]

/-- The magnitude value equals the absolute value of the signed value. -/
theorem natAbs_intVal (z : BigInt) :
    (BigInt.intVal z).natAbs = bignumVal z.mag := by
  rw [BigInt.intVal_eq]
  cases z.neg <;> simp

/-! ## Interpolation and recombination of the five point-products -/

/-- From the five signed point-products, interpolate the six-scaled schoolbook
    coefficients (`toom3Interpolate6`), divide each by six, and recombine at
    base `(2^64)^m`. -/
def toom3Combine (v0 v1 vm1 vm2 vinf : BigInt) (m : Nat) : List (BitVec 64) :=
  let i0 := BigInt.smul 6 v0
  let i1 := BigInt.sub (BigInt.add (BigInt.add (BigInt.smul 2 v1) (BigInt.smul 3 v0)) vm2)
    (BigInt.add (BigInt.smul 6 vm1) (BigInt.smul 12 vinf))
  let i2 := BigInt.sub (BigInt.add (BigInt.smul 3 v1) (BigInt.smul 3 vm1))
    (BigInt.add (BigInt.smul 6 v0) (BigInt.smul 6 vinf))
  let i3 := BigInt.add (BigInt.sub (BigInt.add v1 (BigInt.smul 3 vm1))
    (BigInt.add vm2 (BigInt.smul 3 v0))) (BigInt.smul 12 vinf)
  let i4 := BigInt.smul 6 vinf
  let h0 := divRaw i0 6
  let h1 := divRaw i1 6
  let h2 := divRaw i2 6
  let h3 := divRaw i3 6
  let h4 := divRaw i4 6
  BigNat.add h0.mag
    (BigNat.add (BigNatKaratsuba.shiftBy m h1.mag)
      (BigNat.add (BigNatKaratsuba.shiftBy (2 * m) h2.mag)
        (BigNat.add (BigNatKaratsuba.shiftBy (3 * m) h3.mag)
          (BigNatKaratsuba.shiftBy (4 * m) h4.mag))))

/-- **Interpolation + recombination value.**  Given the five point-products'
    signed values, `toom3Combine` computes the exact base-`(2^64)^m`
    recombination of the schoolbook coefficients. -/
theorem toom3Combine_val (v0 v1 vm1 vm2 vinf : BigInt) (m A0 A1 A2 B0 B1 B2 : Nat)
    (hv0 : BigInt.intVal v0 = (A0 : Int) * B0)
    (hv1 : BigInt.intVal v1 = ((A0 : Int) + A1 + A2) * ((B0 : Int) + B1 + B2))
    (hvm1 : BigInt.intVal vm1 = ((A0 : Int) - A1 + A2) * ((B0 : Int) - B1 + B2))
    (hvm2 : BigInt.intVal vm2
      = ((A0 : Int) - 2 * A1 + 4 * A2) * ((B0 : Int) - 2 * B1 + 4 * B2))
    (hvinf : BigInt.intVal vinf = (A2 : Int) * B2) :
    bignumVal (toom3Combine v0 v1 vm1 vm2 vinf m)
      = A0 * B0
        + (2 ^ 64) ^ m * (A0 * B1 + A1 * B0)
        + (2 ^ 64) ^ m * (2 ^ 64) ^ m * (A0 * B2 + A1 * B1 + A2 * B0)
        + (2 ^ 64) ^ m * (2 ^ 64) ^ m * (2 ^ 64) ^ m * (A1 * B2 + A2 * B1)
        + (2 ^ 64) ^ m * (2 ^ 64) ^ m * (2 ^ 64) ^ m * (2 ^ 64) ^ m * (A2 * B2) := by
  -- Each six-scaled interpolated coefficient equals `6 ·` the schoolbook one
  -- (the Bodrato interpolation identities, discharged by `ring`).
  have e0 : BigInt.intVal (BigInt.smul 6 v0) = 6 * ((A0 * B0 : Nat) : Int) := by
    rw [BigInt.smul_val, hv0]; push_cast; ring
  have e1 : BigInt.intVal
      (BigInt.sub (BigInt.add (BigInt.add (BigInt.smul 2 v1) (BigInt.smul 3 v0)) vm2)
        (BigInt.add (BigInt.smul 6 vm1) (BigInt.smul 12 vinf)))
      = 6 * ((A0 * B1 + A1 * B0 : Nat) : Int) := by
    simp only [BigInt.sub_val, BigInt.add_val, BigInt.smul_val, hv0, hv1, hvm1,
      hvm2, hvinf]
    push_cast; ring
  have e2 : BigInt.intVal
      (BigInt.sub (BigInt.add (BigInt.smul 3 v1) (BigInt.smul 3 vm1))
        (BigInt.add (BigInt.smul 6 v0) (BigInt.smul 6 vinf)))
      = 6 * ((A0 * B2 + A1 * B1 + A2 * B0 : Nat) : Int) := by
    simp only [BigInt.sub_val, BigInt.add_val, BigInt.smul_val, hv0, hv1, hvm1,
      hvinf]
    push_cast; ring
  have e3 : BigInt.intVal
      (BigInt.add (BigInt.sub (BigInt.add v1 (BigInt.smul 3 vm1))
        (BigInt.add vm2 (BigInt.smul 3 v0))) (BigInt.smul 12 vinf))
      = 6 * ((A1 * B2 + A2 * B1 : Nat) : Int) := by
    simp only [BigInt.add_val, BigInt.sub_val, BigInt.smul_val, hv0, hv1, hvm1,
      hvm2, hvinf]
    push_cast; ring
  have e4 : BigInt.intVal (BigInt.smul 6 vinf) = 6 * ((A2 * B2 : Nat) : Int) := by
    rw [BigInt.smul_val, hvinf]; push_cast; ring
  -- Each `divRaw _ 6` recovers the schoolbook coefficient exactly.
  have div6 : ∀ (z : BigInt) (c : Nat), BigInt.intVal z = 6 * ((c : Nat) : Int) →
      bignumVal (divRaw z 6).mag = c := by
    intro z c hz
    have hdvd : ((6 : Nat) : Int) ∣ BigInt.intVal z :=
      ⟨(c : Int), by rw [hz]; push_cast; ring⟩
    have hval : BigInt.intVal (divRaw z 6) = (c : Int) := by
      rw [divRaw_val z 6 hdvd, hz]; push_cast
      rw [Int.mul_ediv_cancel_left _ (by norm_num)]
    rw [← natAbs_intVal, hval, Int.natAbs_natCast]
  have m0 := div6 _ _ e0
  have m1 := div6 _ _ e1
  have m2 := div6 _ _ e2
  have m3 := div6 _ _ e3
  have m4 := div6 _ _ e4
  -- Assemble the recombination.
  simp only [toom3Combine]
  rw [BigNat.add_val, BigNat.add_val, BigNat.add_val, BigNat.add_val,
    BigNatKaratsuba.shiftBy_val, BigNatKaratsuba.shiftBy_val,
    BigNatKaratsuba.shiftBy_val, BigNatKaratsuba.shiftBy_val,
    m0, m1, m2, m3, m4]
  have p2 : (2 ^ 64 : Nat) ^ (2 * m) = (2 ^ 64) ^ m * (2 ^ 64) ^ m := by
    rw [two_mul, pow_add]
  have p3 : (2 ^ 64 : Nat) ^ (3 * m)
      = (2 ^ 64) ^ m * (2 ^ 64) ^ m * (2 ^ 64) ^ m := by
    rw [show 3 * m = m + m + m by ring, pow_add, pow_add]
  have p4 : (2 ^ 64 : Nat) ^ (4 * m)
      = (2 ^ 64) ^ m * (2 ^ 64) ^ m * (2 ^ 64) ^ m * (2 ^ 64) ^ m := by
    rw [show 4 * m = m + m + m + m by ring, pow_add, pow_add, pow_add]
  rw [p2, p3, p4]; ring

/-! ## The recursive Toom-Cook-3 multiply -/

/-- Recursive integer Toom-Cook-3 multiplication.  Below the crossover (wider
    operand under 48 limbs) it uses `mulDispatch`; otherwise it splits each
    operand into three chunks of width `m = n / 3`, evaluates the two operands
    at `{0, 1, -1, -2, ∞}` through `BigInt`, recurses on the five point-products,
    interpolates and recombines. -/
def toom3 (a b : List (BitVec 64)) : List (BitVec 64) :=
  if _h : max a.length b.length < 48 then BigNatKaratsuba.mulDispatch a b
  else
    let m := max a.length b.length / 3
    let a0 := a.take m
    let a1 := (a.drop m).take m
    let a2 := a.drop (2 * m)
    let b0 := b.take m
    let b1 := (b.drop m).take m
    let b2 := b.drop (2 * m)
    let ea1 := ev1 a0 a1 a2
    let eb1 := ev1 b0 b1 b2
    let eam1 := evm1 a0 a1 a2
    let ebm1 := evm1 b0 b1 b2
    let eam2 := evm2 a0 a1 a2
    let ebm2 := evm2 b0 b1 b2
    let v0 : BigInt := ⟨false, toom3 a0 b0⟩
    let v1 : BigInt := ⟨xor ea1.neg eb1.neg, toom3 ea1.mag eb1.mag⟩
    let vm1 : BigInt := ⟨xor eam1.neg ebm1.neg, toom3 eam1.mag ebm1.mag⟩
    let vm2 : BigInt := ⟨xor eam2.neg ebm2.neg, toom3 eam2.mag ebm2.mag⟩
    let vinf : BigInt := ⟨false, toom3 a2 b2⟩
    toom3Combine v0 v1 vm1 vm2 vinf m
termination_by max a.length b.length
decreasing_by
  · simp only [List.length_take]; omega
  · refine lt_of_le_of_lt (max_le_max (ev1_length _ _ _) (ev1_length _ _ _)) ?_
    simp only [List.length_take, List.length_drop]; omega
  · refine lt_of_le_of_lt (max_le_max (evm1_length _ _ _) (evm1_length _ _ _)) ?_
    simp only [List.length_take, List.length_drop]; omega
  · refine lt_of_le_of_lt (max_le_max (evm2_length _ _ _) (evm2_length _ _ _)) ?_
    simp only [List.length_take, List.length_drop]; omega
  · simp only [List.length_drop]; omega

/-! ## Value correctness -/

/-- The three-way split of a limb list's value at base `(2^64)^m`. -/
theorem split3 (a : List (BitVec 64)) (m : Nat) :
    bignumVal a
      = bignumVal (a.take m) + (2 ^ 64) ^ m * bignumVal ((a.drop m).take m)
        + (2 ^ 64) ^ m * ((2 ^ 64) ^ m * bignumVal (a.drop (2 * m))) := by
  conv_lhs => rw [bignumVal_take_drop m a]
  rw [bignumVal_take_drop m (a.drop m)]
  have hdd : (a.drop m).drop m = a.drop (2 * m) := by
    rw [List.drop_drop]; congr 1; omega
  rw [hdd]; ring

/-- **Value correctness.**  `bignumVal (toom3 a b) = bignumVal a * bignumVal b`. -/
theorem toom3_val (a b : List (BitVec 64)) :
    bignumVal (toom3 a b) = bignumVal a * bignumVal b := by
  suffices H : ∀ N : Nat, ∀ a b : List (BitVec 64),
      max a.length b.length ≤ N →
      bignumVal (toom3 a b) = bignumVal a * bignumVal b by
    exact H (max a.length b.length) a b (Nat.le_refl _)
  intro N
  induction N with
  | zero =>
      intro a b hN
      have hlt : max a.length b.length < 48 := by omega
      rw [toom3, dif_pos hlt]; exact BigNatKaratsuba.mulDispatch_val a b
  | succ N ih =>
      intro a b hN
      rw [toom3]
      by_cases hg : max a.length b.length < 48
      · rw [dif_pos hg]; exact BigNatKaratsuba.mulDispatch_val a b
      · rw [dif_neg hg]
        extract_lets m a0 a1 a2 b0 b1 b2 ea1 eb1 eam1 ebm1 eam2 ebm2
          v0 v1 vm1 vm2 vinf
        -- Chunk length facts.
        have hm : m = max a.length b.length / 3 := rfl
        have hla0 : a0.length ≤ m := by
          rw [show a0 = a.take m from rfl, List.length_take]; omega
        have hla1 : a1.length ≤ m := by
          rw [show a1 = (a.drop m).take m from rfl, List.length_take]; omega
        have hla2 : a2.length ≤ a.length - 2 * m := by
          rw [show a2 = a.drop (2 * m) from rfl, List.length_drop]
        have hlb0 : b0.length ≤ m := by
          rw [show b0 = b.take m from rfl, List.length_take]; omega
        have hlb1 : b1.length ≤ m := by
          rw [show b1 = (b.drop m).take m from rfl, List.length_take]; omega
        have hlb2 : b2.length ≤ b.length - 2 * m := by
          rw [show b2 = b.drop (2 * m) from rfl, List.length_drop]
        have hlaN : a.length ≤ max a.length b.length := le_max_left _ _
        have hlbN : b.length ≤ max a.length b.length := le_max_right _ _
        -- Recursive-call measure bounds.
        have bnd0 : max a0.length b0.length ≤ N := by omega
        have bnd1 : max ea1.mag.length eb1.mag.length ≤ N := by
          have la := ev1_length a0 a1 a2
          have lb := ev1_length b0 b1 b2
          rw [show ea1 = ev1 a0 a1 a2 from rfl, show eb1 = ev1 b0 b1 b2 from rfl]
          omega
        have bndm1 : max eam1.mag.length ebm1.mag.length ≤ N := by
          have la := evm1_length a0 a1 a2
          have lb := evm1_length b0 b1 b2
          rw [show eam1 = evm1 a0 a1 a2 from rfl, show ebm1 = evm1 b0 b1 b2 from rfl]
          omega
        have bndm2 : max eam2.mag.length ebm2.mag.length ≤ N := by
          have la := evm2_length a0 a1 a2
          have lb := evm2_length b0 b1 b2
          rw [show eam2 = evm2 a0 a1 a2 from rfl, show ebm2 = evm2 b0 b1 b2 from rfl]
          omega
        have bndinf : max a2.length b2.length ≤ N := by omega
        -- The five point-product values.
        have hp0 : BigInt.intVal v0
            = ((bignumVal a0 : Int)) * (bignumVal b0) := by
          show BigInt.intVal ⟨false, toom3 a0 b0⟩ = _
          rw [intVal_mk_false, ih a0 b0 bnd0]; push_cast; ring
        have hp1 : BigInt.intVal v1
            = ((bignumVal a0 : Int) + bignumVal a1 + bignumVal a2)
              * ((bignumVal b0 : Int) + bignumVal b1 + bignumVal b2) := by
          show BigInt.intVal ⟨xor ea1.neg eb1.neg, toom3 ea1.mag eb1.mag⟩ = _
          rw [mulBI_val ea1 eb1 _ (ih ea1.mag eb1.mag bnd1)]
          show BigInt.intVal (ev1 a0 a1 a2) * BigInt.intVal (ev1 b0 b1 b2) = _
          rw [ev1_val, ev1_val]
        have hpm1 : BigInt.intVal vm1
            = ((bignumVal a0 : Int) - bignumVal a1 + bignumVal a2)
              * ((bignumVal b0 : Int) - bignumVal b1 + bignumVal b2) := by
          show BigInt.intVal ⟨xor eam1.neg ebm1.neg, toom3 eam1.mag ebm1.mag⟩ = _
          rw [mulBI_val eam1 ebm1 _ (ih eam1.mag ebm1.mag bndm1)]
          show BigInt.intVal (evm1 a0 a1 a2) * BigInt.intVal (evm1 b0 b1 b2) = _
          rw [evm1_val, evm1_val]
        have hpm2 : BigInt.intVal vm2
            = ((bignumVal a0 : Int) - 2 * bignumVal a1 + 4 * bignumVal a2)
              * ((bignumVal b0 : Int) - 2 * bignumVal b1 + 4 * bignumVal b2) := by
          show BigInt.intVal ⟨xor eam2.neg ebm2.neg, toom3 eam2.mag ebm2.mag⟩ = _
          rw [mulBI_val eam2 ebm2 _ (ih eam2.mag ebm2.mag bndm2)]
          show BigInt.intVal (evm2 a0 a1 a2) * BigInt.intVal (evm2 b0 b1 b2) = _
          rw [evm2_val, evm2_val]
        have hpinf : BigInt.intVal vinf
            = ((bignumVal a2 : Int)) * (bignumVal b2) := by
          show BigInt.intVal ⟨false, toom3 a2 b2⟩ = _
          rw [intVal_mk_false, ih a2 b2 bndinf]; push_cast; ring
        -- Recombination equals the product via the three-way split.
        rw [show (bignumVal (toom3Combine v0 v1 vm1 vm2 vinf m)) = _ from
          toom3Combine_val v0 v1 vm1 vm2 vinf m (bignumVal a0) (bignumVal a1)
            (bignumVal a2) (bignumVal b0) (bignumVal b1) (bignumVal b2)
            hp0 hp1 hpm1 hpm2 hpinf]
        have hsplit := toom3_schoolbook_split (bignumVal a0) (bignumVal a1)
          (bignumVal a2) (bignumVal b0) (bignumVal b1) (bignumVal b2) ((2 ^ 64) ^ m)
        rw [← hsplit, split3 a m, split3 b m]
        rw [show a0 = a.take m from rfl, show a1 = (a.drop m).take m from rfl,
          show a2 = a.drop (2 * m) from rfl, show b0 = b.take m from rfl,
          show b1 = (b.drop m).take m from rfl, show b2 = b.drop (2 * m) from rfl]
        ring

end CatCrypt.Crypto.SecureCompilation.BigNatToom3
