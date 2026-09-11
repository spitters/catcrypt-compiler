/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.BigNatKaratsuba
public import CatCrypt.Crypto.SecureCompilation.BigNatDivMod

/-!
# BigInt: a signed sign-magnitude big-integer carrier

A signed big-integer carrier built on the unsigned `BigNat` magnitude
(`bignumVal`, little-endian base `2^64`).  A value is a sign flag `neg` and a
magnitude limb list `mag`; its abstraction to `Int` is `intVal`.  The smart
constructor `mkBigInt` normalizes the magnitude (`BigNat.norm`) and collapses
the sign of zero, so `intVal` is well-defined on canonical values.  Each
carrier operation is proven to compute the corresponding `Int` operation.

## Main results

* `mkBigInt`, `intVal`, `intVal_mkBigInt` — the smart constructor and the master
  equation `intVal (mkBigInt ng m) = if ng then -(bignumVal m) else bignumVal m`.
* `ofNat`, `neg`, `intVal_ofNat`, `intVal_neg` — embedding of `Nat` and negation.
* `add` / `add_val` — sign-magnitude addition, `intVal (add x y) = intVal x + intVal y`.
* `sub` / `sub_val` — subtraction, `intVal (sub x y) = intVal x - intVal y`.
* `mul` / `mul_val` — multiplication via the fast magnitude multiply,
  `intVal (mul x y) = intVal x * intVal y`.
* `smul` / `smul_val` — multiplication by a small `Int` constant,
  `intVal (smul c x) = c * intVal x`.
* `divExactSmall` / `divExactSmall_val` — exact division by a small `Nat`,
  `intVal (divExactSmall x d h) = intVal x / d`, given `(d : Int) ∣ intVal x`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)

/-- A signed big integer as a sign flag and an unsigned magnitude limb list
    (little-endian base `2^64`). -/
structure BigInt where
  neg : Bool
  mag : List (BitVec 64)

namespace BigInt

/-- Signed value: the magnitude `bignumVal mag`, negated when `neg`. -/
def intVal (x : BigInt) : Int :=
  bif x.neg then -(bignumVal x.mag : Int) else (bignumVal x.mag : Int)

theorem intVal_eq (x : BigInt) :
    intVal x = bif x.neg then -(bignumVal x.mag : Int) else (bignumVal x.mag : Int) := rfl

/-- Smart constructor: normalize the magnitude and force `neg = false` on zero,
    so that each represented value has a canonical carrier. -/
def mkBigInt (ng : Bool) (m : List (BitVec 64)) : BigInt :=
  match BigNat.norm m with
  | [] => ⟨false, []⟩
  | n :: ns => ⟨ng, n :: ns⟩

/-- **Master equation.** The value of a smart-constructed integer is the signed
    magnitude value; the zero-collapsing branch agrees because a zero magnitude
    normalizes to `[]`. -/
theorem intVal_mkBigInt (ng : Bool) (m : List (BitVec 64)) :
    intVal (mkBigInt ng m) = bif ng then -(bignumVal m : Int) else (bignumVal m : Int) := by
  have hv : bignumVal (BigNat.norm m) = bignumVal m := BigNat.bignumVal_norm m
  unfold mkBigInt
  cases hm : BigNat.norm m with
  | nil =>
    rw [hm] at hv
    have h0 : bignumVal m = 0 := by rw [← hv]; rfl
    simp only [intVal, h0, Nat.cast_zero, neg_zero, Bool.cond_self]
    cases ng <;> rfl
  | cons n ns =>
    rw [hm] at hv
    simp only [intVal]
    rw [hv]

/-! ## Embedding and negation -/

/-- Embed a `Nat` as a nonnegative big integer. -/
def ofNat (n : Nat) : BigInt := mkBigInt false (BigNat.ofNat n)

/-- `intVal (ofNat n) = n`. -/
theorem intVal_ofNat (n : Nat) : intVal (ofNat n) = (n : Int) := by
  rw [ofNat, intVal_mkBigInt]; simp [BigNat.toNat_ofNat]

/-- Negation: flip the sign flag (through the smart constructor, so `-0 = 0`). -/
def negate (x : BigInt) : BigInt := mkBigInt (!x.neg) x.mag

/-- `intVal (negate x) = - intVal x`. -/
theorem intVal_neg (x : BigInt) : intVal (negate x) = - intVal x := by
  rw [negate, intVal_mkBigInt, intVal_eq]
  cases x.neg <;> simp

/-! ## Addition and subtraction -/

/-- Sign-magnitude addition: with equal signs, add the magnitudes and keep the
    sign; with opposite signs, subtract the smaller magnitude from the larger and
    take the larger operand's sign. -/
def add (x y : BigInt) : BigInt :=
  bif x.neg == y.neg then
    mkBigInt x.neg (BigNat.add x.mag y.mag)
  else bif BigNatCompare.ble x.mag y.mag then
    mkBigInt y.neg (BigNatKaratsuba.bnSub y.mag x.mag)
  else
    mkBigInt x.neg (BigNatKaratsuba.bnSub x.mag y.mag)

/-- **Addition.** `intVal (add x y) = intVal x + intVal y`. -/
theorem add_val (x y : BigInt) : intVal (add x y) = intVal x + intVal y := by
  unfold add
  rw [intVal_eq x, intVal_eq y]
  have hle : bignumVal x.mag ≤ bignumVal y.mag ↔ BigNatCompare.ble x.mag y.mag = true :=
    (BigNatCompare.ble_eq_true_iff x.mag y.mag).symm
  cases hx : x.neg <;> cases hy : y.neg <;> simp only [cond_true, cond_false]
  · -- both nonneg: add magnitudes, same sign
    rw [beq_self_eq_true, cond_true, intVal_mkBigInt, BigNat.add_val, cond_false]
    push_cast; ring
  · -- x nonneg, y negative: opposite signs
    rw [show ((false : Bool) == true) = false from rfl, cond_false]
    cases hb : BigNatCompare.ble x.mag y.mag
    · rw [cond_false, intVal_mkBigInt, BigNatKaratsuba.bnSub_val, cond_false]
      rw [Nat.cast_sub (by
        have hn : ¬ bignumVal x.mag ≤ bignumVal y.mag := by rw [hle, hb]; decide
        omega)]; ring
    · rw [cond_true, intVal_mkBigInt, BigNatKaratsuba.bnSub_val, cond_true]
      rw [Nat.cast_sub (hle.mpr hb)]; ring
  · -- x negative, y nonneg: opposite signs
    rw [show ((true : Bool) == false) = false from rfl, cond_false]
    cases hb : BigNatCompare.ble x.mag y.mag
    · rw [cond_false, intVal_mkBigInt, BigNatKaratsuba.bnSub_val, cond_true]
      rw [Nat.cast_sub (by
        have hn : ¬ bignumVal x.mag ≤ bignumVal y.mag := by rw [hle, hb]; decide
        omega)]; ring
    · rw [cond_true, intVal_mkBigInt, BigNatKaratsuba.bnSub_val, cond_false]
      rw [Nat.cast_sub (hle.mpr hb)]; ring
  · -- both negative: add magnitudes, same sign
    rw [beq_self_eq_true, cond_true, intVal_mkBigInt, BigNat.add_val, cond_true]
    push_cast; ring

/-- Subtraction: `sub x y = add x (negate y)`. -/
def sub (x y : BigInt) : BigInt := add x (negate y)

/-- **Subtraction.** `intVal (sub x y) = intVal x - intVal y`. -/
theorem sub_val (x y : BigInt) : intVal (sub x y) = intVal x - intVal y := by
  rw [sub, add_val, intVal_neg]; ring

/-! ## Multiplication -/

/-- Multiplication: the result sign is the exclusive-or of the operand signs, its
    magnitude the fast magnitude multiply. -/
def mul (x y : BigInt) : BigInt :=
  mkBigInt (xor x.neg y.neg) (BigNatKaratsuba.mulDispatch x.mag y.mag)

/-- **Multiplication.** `intVal (mul x y) = intVal x * intVal y`. -/
theorem mul_val (x y : BigInt) : intVal (mul x y) = intVal x * intVal y := by
  rw [mul, intVal_mkBigInt, BigNatKaratsuba.mulDispatch_val, intVal_eq x, intVal_eq y]
  cases x.neg <;> cases y.neg <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false,
      cond_true, cond_false] <;>
    push_cast <;> ring

/-! ## Scalar multiplication by a small constant -/

/-- Embed an `Int` constant as a big integer. -/
def ofInt (c : Int) : BigInt := mkBigInt (decide (c < 0)) (BigNat.ofNat c.natAbs)

/-- `intVal (ofInt c) = c`. -/
theorem intVal_ofInt (c : Int) : intVal (ofInt c) = c := by
  rw [ofInt, intVal_mkBigInt, BigNat.toNat_ofNat]
  by_cases hc : c < 0
  · simp only [hc, decide_true, cond_true]
    rw [Int.ofNat_natAbs_of_nonpos (le_of_lt hc)]; ring
  · simp only [hc, decide_false, cond_false]
    exact Int.natAbs_of_nonneg (not_lt.mp hc)

/-- Multiply by a small `Int` constant (e.g. Toom-3/Toom-4 interpolation
    coefficients). -/
def smul (c : Int) (x : BigInt) : BigInt := mul (ofInt c) x

/-- **Scalar multiplication.** `intVal (smul c x) = c * intVal x`. -/
theorem smul_val (c : Int) (x : BigInt) : intVal (smul c x) = c * intVal x := by
  rw [smul, mul_val, intVal_ofInt]

/-! ## Exact division by a small constant -/

/-- Exact division by a small positive `Nat` divisor (e.g. Toom-3 `/6`,
    Toom-4 `/720`): divide the magnitude and carry the sign.  The divisibility
    hypothesis makes the truncating division exact, so the sign is preserved. -/
def divExactSmall (x : BigInt) (d : Nat) (_h : (d : Int) ∣ intVal x) : BigInt :=
  mkBigInt x.neg (BigNatDivMod.div x.mag (BigNat.ofNat d))

/-- **Exact division.** `intVal (divExactSmall x d h) = intVal x / d`. -/
theorem divExactSmall_val (x : BigInt) (d : Nat) (h : (d : Int) ∣ intVal x) :
    intVal (divExactSmall x d h) = intVal x / (d : Int) := by
  rw [divExactSmall, intVal_mkBigInt, BigNatDivMod.div_val, BigNat.toNat_ofNat, intVal_eq]
  cases hx : x.neg with
  | false =>
    simp only [cond_false]
    rw [Int.natCast_div]
  | true =>
    rw [intVal_eq, hx] at h
    simp only [cond_true] at h
    have hd : (d : Int) ∣ (bignumVal x.mag : Int) := (dvd_neg).mp h
    simp only [cond_true]
    rw [Int.natCast_div, Int.neg_ediv_of_dvd hd]

/-- Sanity: `(-6) * 4 + 24 = 0` at the carrier level. -/
example :
    intVal (add (mul (ofInt (-6)) (ofNat 4)) (ofNat 24)) = 0 := by
  rw [add_val, mul_val, intVal_ofInt, intVal_ofNat, intVal_ofNat]; norm_num

end BigInt

end CatCrypt.Crypto.SecureCompilation
