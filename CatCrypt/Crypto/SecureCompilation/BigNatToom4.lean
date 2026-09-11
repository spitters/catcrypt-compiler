/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.BigInt
public import CatCrypt.Crypto.SecureCompilation.ToomInterpolation

/-!
# Recursive integer Toom-Cook-4 multiplication on the `BigNat` carrier

A recursive Toom-Cook-4 multiply over the variable-width limb-list carrier
`bignumVal` (little-endian base `2^64`), with the value-correctness statement
`bignumVal (toom4 a b) = bignumVal a * bignumVal b`.  Above a fixed crossover
the algorithm splits each operand into four chunks, evaluates each at the seven
signed points `{0, 1, -1, 2, -2, 3, ∞}` through the signed `BigInt` carrier,
computes seven sub-products, interpolates the seven schoolbook coefficients
(scaled by the Vandermonde determinant `720 = 2⁴·3²·5`), divides them back down,
and recombines at base `2^{64 m}`; below the crossover it falls back to the
Karatsuba dispatcher.  The seven-point interpolation algebra is reused from
`SecureCompilation.ToomInterpolation` (`toom4Interpolate720`,
`toom4_recombine_int_h0..h6`).

Termination is by a structural fuel parameter (`toom4Aux`): each recursive level
consumes one unit of fuel and the base case falls back to the correct
`mulDispatch`, so value correctness holds for every fuel value and the top-level
`toom4` supplies `max a.length b.length` units — far more than the `log₄`-depth
the recursion needs.

## Main results

* `combineShift` / `combineShift_val` — weighted recombination of seven
  coefficients at base `2^{64 m}`.
* `bignumVal_split4` — the four-way carrier split at base `2^{64 m}`.
* `mkBigInt_xor_val` — the sign-magnitude product value for any magnitude
  multiply, generalizing `BigInt.mul_val`.
* `toom4Recombine` / `toom4Recombine_correct` — the one-level interpolation,
  exact division by `720`, and recombination, and its value correctness given
  the seven evaluated sub-products.
* `toom4` / `toom4_val` — the recursive multiply and its value correctness
  `bignumVal (toom4 a b) = bignumVal a * bignumVal b`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNatToom4

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.BigInt
open CatCrypt.Crypto.SecureCompilation.ToomInterpolation
  (evalsInt4 subProductsInt4 toom4Interpolate720
   toom4_recombine_int_h0 toom4_recombine_int_h1 toom4_recombine_int_h2
   toom4_recombine_int_h3 toom4_recombine_int_h4 toom4_recombine_int_h5
   toom4_recombine_int_h6)

/-! ## Small `BigInt` helpers -/

/-- A nonnegative big integer from a magnitude limb list. -/
def ofMag (m : List (BitVec 64)) : BigInt := mkBigInt false m

/-- `intVal (ofMag m) = bignumVal m`. -/
theorem intVal_ofMag (m : List (BitVec 64)) : intVal (ofMag m) = (bignumVal m : ℤ) := by
  simp [ofMag, intVal_mkBigInt]

/-- The magnitude value is the absolute value of the signed value. -/
theorem bignumVal_mag_abs (x : BigInt) : (bignumVal x.mag : ℤ) = |intVal x| := by
  rw [intVal_eq]
  cases x.neg with
  | false => simp [abs_of_nonneg]
  | true => simp [abs_of_nonpos]

/-- Exact division by `720`, a proof-free wrapper over `BigInt.divExactSmall`. -/
def divBy720 (x : BigInt) : BigInt :=
  mkBigInt x.neg (BigNatDivMod.div x.mag (BigNat.ofNat 720))

/-- **Exact division by 720.**  When `720 ∣ intVal x`, `intVal (divBy720 x) =
    intVal x / 720`. -/
theorem divBy720_val (x : BigInt) (h : (720 : ℤ) ∣ intVal x) :
    intVal (divBy720 x) = intVal x / (720 : ℤ) := by
  have hh : ((720 : ℕ) : ℤ) ∣ intVal x := by exact_mod_cast h
  have := divExactSmall_val x 720 hh
  simpa [divBy720, divExactSmall] using this

/-- The magnitude of an exact division by `720` of a nonnegative multiple of
    `720`. -/
theorem bignumVal_divBy720_mag (x : BigInt) (g : ℤ) (hg : 0 ≤ g)
    (hx : intVal x = 720 * g) : (bignumVal (divBy720 x).mag : ℤ) = g := by
  have hdvd : (720 : ℤ) ∣ intVal x := ⟨g, hx⟩
  have hc : intVal (divBy720 x) = g := by
    rw [divBy720_val x hdvd, hx, Int.mul_ediv_cancel_left g (by norm_num)]
  rw [bignumVal_mag_abs, hc, abs_of_nonneg hg]

/-- **Sign-magnitude product value.**  For any magnitude multiply `r` that
    computes the product of the magnitudes, the sign-magnitude wrapper computes
    the signed product.  Generalizes `BigInt.mul_val` (whose `r` is
    `mulDispatch`). -/
theorem mkBigInt_xor_val (x y : BigInt) (r : List (BitVec 64))
    (hr : bignumVal r = bignumVal x.mag * bignumVal y.mag) :
    intVal (mkBigInt (xor x.neg y.neg) r) = intVal x * intVal y := by
  rw [intVal_mkBigInt, hr, intVal_eq x, intVal_eq y]
  cases x.neg <;> cases y.neg <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false,
      cond_true, cond_false] <;>
    push_cast <;> ring

/-! ## The four-way carrier split -/

/-- **Four-way split.**  Splitting `xs` into the four chunks
    `xs.take m`, `(xs.drop m).take m`, `(xs.drop 2m).take m`, `xs.drop 3m`
    decomposes its value at base `2^{64 m}`. -/
theorem bignumVal_split4 (xs : List (BitVec 64)) (m : Nat) :
    (bignumVal xs : ℤ)
      = (bignumVal (xs.take m) : ℤ)
        + ((2 : ℤ) ^ 64) ^ m * (bignumVal ((xs.drop m).take m) : ℤ)
        + (((2 : ℤ) ^ 64) ^ m) ^ 2 * (bignumVal ((xs.drop (2 * m)).take m) : ℤ)
        + (((2 : ℤ) ^ 64) ^ m) ^ 3 * (bignumVal (xs.drop (3 * m)) : ℤ) := by
  have hdd1 : (xs.drop m).drop m = xs.drop (2 * m) := by
    rw [List.drop_drop]; congr 1; omega
  have hdd2 : (xs.drop (2 * m)).drop m = xs.drop (3 * m) := by
    rw [List.drop_drop]; congr 1; omega
  have s1 : (bignumVal xs : ℤ)
      = (bignumVal (xs.take m) : ℤ) + ((2 : ℤ) ^ 64) ^ m * (bignumVal (xs.drop m) : ℤ) := by
    exact_mod_cast bignumVal_take_drop m xs
  have s2 : (bignumVal (xs.drop m) : ℤ)
      = (bignumVal ((xs.drop m).take m) : ℤ)
        + ((2 : ℤ) ^ 64) ^ m * (bignumVal (xs.drop (2 * m)) : ℤ) := by
    have h := bignumVal_take_drop m (xs.drop m)
    rw [hdd1] at h
    exact_mod_cast h
  have s3 : (bignumVal (xs.drop (2 * m)) : ℤ)
      = (bignumVal ((xs.drop (2 * m)).take m) : ℤ)
        + ((2 : ℤ) ^ 64) ^ m * (bignumVal (xs.drop (3 * m)) : ℤ) := by
    have h := bignumVal_take_drop m (xs.drop (2 * m))
    rw [hdd2] at h
    exact_mod_cast h
  rw [s1, s2, s3]; ring

/-! ## Weighted recombination -/

/-- Recombine seven coefficients at base `2^{64 m}`. -/
def combineShift (m : Nat) (c0 c1 c2 c3 c4 c5 c6 : List (BitVec 64)) : List (BitVec 64) :=
  BigNat.add c0
    (BigNat.add (BigNatKaratsuba.shiftBy m c1)
      (BigNat.add (BigNatKaratsuba.shiftBy (2 * m) c2)
        (BigNat.add (BigNatKaratsuba.shiftBy (3 * m) c3)
          (BigNat.add (BigNatKaratsuba.shiftBy (4 * m) c4)
            (BigNat.add (BigNatKaratsuba.shiftBy (5 * m) c5)
              (BigNatKaratsuba.shiftBy (6 * m) c6))))))

/-- **Recombination value.** -/
theorem combineShift_val (m : Nat) (c0 c1 c2 c3 c4 c5 c6 : List (BitVec 64)) :
    (bignumVal (combineShift m c0 c1 c2 c3 c4 c5 c6) : ℤ)
      = (bignumVal c0 : ℤ)
        + ((2 : ℤ) ^ 64) ^ m * (bignumVal c1 : ℤ)
        + (((2 : ℤ) ^ 64) ^ m) ^ 2 * (bignumVal c2 : ℤ)
        + (((2 : ℤ) ^ 64) ^ m) ^ 3 * (bignumVal c3 : ℤ)
        + (((2 : ℤ) ^ 64) ^ m) ^ 4 * (bignumVal c4 : ℤ)
        + (((2 : ℤ) ^ 64) ^ m) ^ 5 * (bignumVal c5 : ℤ)
        + (((2 : ℤ) ^ 64) ^ m) ^ 6 * (bignumVal c6 : ℤ) := by
  simp only [combineShift, BigNat.add_val, BigNatKaratsuba.shiftBy_val]
  push_cast
  ring

/-! ## One-level interpolation and recombination -/

/-- Interpolate the seven `720`-scaled schoolbook coefficients from the seven
    sub-products, divide each by `720`, and recombine at base `2^{64 m}`. -/
def toom4Recombine (m : Nat) (v0 v1 vm1 v2 vm2 v3 vinf : BigInt) : List (BitVec 64) :=
  let H0 := smul 720 v0
  let H1 := add (smul (-240) v0) (add (smul 720 v1) (add (smul (-360) vm1)
              (add (smul (-180) v2) (add (smul 36 vm2) (add (smul 24 v3) (smul (-8640) vinf))))))
  let H2 := add (smul (-900) v0) (add (smul 480 v1) (add (smul 480 vm1)
              (add (smul (-30) v2) (add (smul (-30) vm2) (smul 2880 vinf)))))
  let H3 := add (smul 300 v0) (add (smul (-420) v1) (add (smul (-30) vm1)
              (add (smul 210 v2) (add (smul (-30) vm2) (add (smul (-30) v3) (smul 10800 vinf))))))
  let H4 := add (smul 180 v0) (add (smul (-120) v1) (add (smul (-120) vm1)
              (add (smul 30 v2) (add (smul 30 vm2) (smul (-3600) vinf)))))
  let H5 := add (smul (-60) v0) (add (smul 60 v1) (add (smul 30 vm1)
              (add (smul (-30) v2) (add (smul (-6) vm2) (add (smul 6 v3) (smul (-2160) vinf))))))
  let H6 := smul 720 vinf
  combineShift m (divBy720 H0).mag (divBy720 H1).mag (divBy720 H2).mag
    (divBy720 H3).mag (divBy720 H4).mag (divBy720 H5).mag (divBy720 H6).mag

/-! ## The recursive multiply -/

/-- Recursive integer Toom-Cook-4 multiplication with a structural fuel bound.
    At `fuel = 0`, or below the crossover (`max |a| |b| < 120`), it falls back to
    the Karatsuba dispatcher; otherwise it splits both operands into four chunks,
    evaluates each at the seven signed points, takes seven recursive
    sub-products, interpolates, and recombines. -/
def toom4Aux : Nat → List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | 0, a, b => BigNatKaratsuba.mulDispatch a b
  | fuel + 1, a, b =>
    let n := max a.length b.length
    if n < 120 then BigNatKaratsuba.mulDispatch a b
    else
      let m := n / 4
      let a0 := ofMag (a.take m)
      let a1 := ofMag ((a.drop m).take m)
      let a2 := ofMag ((a.drop (2 * m)).take m)
      let a3 := ofMag (a.drop (3 * m))
      let b0 := ofMag (b.take m)
      let b1 := ofMag ((b.drop m).take m)
      let b2 := ofMag ((b.drop (2 * m)).take m)
      let b3 := ofMag (b.drop (3 * m))
      let av1 := add (add (add a0 a1) a2) a3
      let avm1 := sub (add (sub a0 a1) a2) a3
      let av2 := add (add (add a0 (smul 2 a1)) (smul 4 a2)) (smul 8 a3)
      let avm2 := sub (add (sub a0 (smul 2 a1)) (smul 4 a2)) (smul 8 a3)
      let av3 := add (add (add a0 (smul 3 a1)) (smul 9 a2)) (smul 27 a3)
      let bv1 := add (add (add b0 b1) b2) b3
      let bvm1 := sub (add (sub b0 b1) b2) b3
      let bv2 := add (add (add b0 (smul 2 b1)) (smul 4 b2)) (smul 8 b3)
      let bvm2 := sub (add (sub b0 (smul 2 b1)) (smul 4 b2)) (smul 8 b3)
      let bv3 := add (add (add b0 (smul 3 b1)) (smul 9 b2)) (smul 27 b3)
      let v0 := mkBigInt (xor a0.neg b0.neg) (toom4Aux fuel a0.mag b0.mag)
      let v1 := mkBigInt (xor av1.neg bv1.neg) (toom4Aux fuel av1.mag bv1.mag)
      let vm1 := mkBigInt (xor avm1.neg bvm1.neg) (toom4Aux fuel avm1.mag bvm1.mag)
      let v2 := mkBigInt (xor av2.neg bv2.neg) (toom4Aux fuel av2.mag bv2.mag)
      let vm2 := mkBigInt (xor avm2.neg bvm2.neg) (toom4Aux fuel avm2.mag bvm2.mag)
      let v3 := mkBigInt (xor av3.neg bv3.neg) (toom4Aux fuel av3.mag bv3.mag)
      let vinf := mkBigInt (xor a3.neg b3.neg) (toom4Aux fuel a3.mag b3.mag)
      toom4Recombine m v0 v1 vm1 v2 vm2 v3 vinf

/-- Recursive integer Toom-Cook-4 multiplication. -/
def toom4 (a b : List (BitVec 64)) : List (BitVec 64) :=
  toom4Aux (max a.length b.length) a b

/-- **One-level Toom-4 correctness.**  Given seven sub-products whose values are
    the seven evaluated products (as `subProductsInt4` of the eight nonnegative
    chunk values), the interpolate/divide/recombine step computes the product of
    the two four-way splits at base `2^{64 m}`.  The seven `720`-scaled
    coefficients are recovered through the surviving `toom4_recombine_int_h0..h6`
    identities. -/
theorem toom4Recombine_correct (m : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : ℤ)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3)
    (v0 v1 vm1 v2 vm2 v3 vinf : BigInt)
    (ev0 : intVal v0 = (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (ev1 : intVal v1 = (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.1)
    (evm1 : intVal vm1 = (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
    (ev2 : intVal v2 = (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
    (evm2 : intVal vm2 = (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)
    (ev3 : intVal v3 = (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.1)
    (evinf : intVal vinf = (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.2) :
    (bignumVal (toom4Recombine m v0 v1 vm1 v2 vm2 v3 vinf) : ℤ)
      = (a0 + ((2 : ℤ) ^ 64) ^ m * a1 + (((2 : ℤ) ^ 64) ^ m) ^ 2 * a2
          + (((2 : ℤ) ^ 64) ^ m) ^ 3 * a3)
        * (b0 + ((2 : ℤ) ^ 64) ^ m * b1 + (((2 : ℤ) ^ 64) ^ m) ^ 2 * b2
          + (((2 : ℤ) ^ 64) ^ m) ^ 3 * b3) := by
  have hx0 : intVal (smul 720 v0) = 720 * (a0 * b0) := by
    have step : intVal (smul 720 v0)
        = (toom4Interpolate720 (intVal v0) (intVal v1) (intVal vm1) (intVal v2)
            (intVal vm2) (intVal v3) (intVal vinf)).1 := by
      simp only [toom4Interpolate720, smul_val]
    rw [step, ev0, ev1, evm1, ev2, evm2, ev3, evinf]
    exact toom4_recombine_int_h0 a0 a1 a2 a3 b0 b1 b2 b3
  have hx1 : intVal (add (smul (-240) v0) (add (smul 720 v1) (add (smul (-360) vm1)
        (add (smul (-180) v2) (add (smul 36 vm2) (add (smul 24 v3) (smul (-8640) vinf)))))))
      = 720 * (a0 * b1 + a1 * b0) := by
    have step : intVal (add (smul (-240) v0) (add (smul 720 v1) (add (smul (-360) vm1)
          (add (smul (-180) v2) (add (smul 36 vm2) (add (smul 24 v3) (smul (-8640) vinf)))))))
        = (toom4Interpolate720 (intVal v0) (intVal v1) (intVal vm1) (intVal v2)
            (intVal vm2) (intVal v3) (intVal vinf)).2.1 := by
      simp only [toom4Interpolate720, add_val, smul_val]; ring
    rw [step, ev0, ev1, evm1, ev2, evm2, ev3, evinf]
    exact toom4_recombine_int_h1 a0 a1 a2 a3 b0 b1 b2 b3
  have hx2 : intVal (add (smul (-900) v0) (add (smul 480 v1) (add (smul 480 vm1)
        (add (smul (-30) v2) (add (smul (-30) vm2) (smul 2880 vinf))))))
      = 720 * (a0 * b2 + a1 * b1 + a2 * b0) := by
    have step : intVal (add (smul (-900) v0) (add (smul 480 v1) (add (smul 480 vm1)
          (add (smul (-30) v2) (add (smul (-30) vm2) (smul 2880 vinf))))))
        = (toom4Interpolate720 (intVal v0) (intVal v1) (intVal vm1) (intVal v2)
            (intVal vm2) (intVal v3) (intVal vinf)).2.2.1 := by
      simp only [toom4Interpolate720, add_val, smul_val]; ring
    rw [step, ev0, ev1, evm1, ev2, evm2, ev3, evinf]
    exact toom4_recombine_int_h2 a0 a1 a2 a3 b0 b1 b2 b3
  have hx3 : intVal (add (smul 300 v0) (add (smul (-420) v1) (add (smul (-30) vm1)
        (add (smul 210 v2) (add (smul (-30) vm2) (add (smul (-30) v3) (smul 10800 vinf)))))))
      = 720 * (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) := by
    have step : intVal (add (smul 300 v0) (add (smul (-420) v1) (add (smul (-30) vm1)
          (add (smul 210 v2) (add (smul (-30) vm2) (add (smul (-30) v3) (smul 10800 vinf)))))))
        = (toom4Interpolate720 (intVal v0) (intVal v1) (intVal vm1) (intVal v2)
            (intVal vm2) (intVal v3) (intVal vinf)).2.2.2.1 := by
      simp only [toom4Interpolate720, add_val, smul_val]; ring
    rw [step, ev0, ev1, evm1, ev2, evm2, ev3, evinf]
    exact toom4_recombine_int_h3 a0 a1 a2 a3 b0 b1 b2 b3
  have hx4 : intVal (add (smul 180 v0) (add (smul (-120) v1) (add (smul (-120) vm1)
        (add (smul 30 v2) (add (smul 30 vm2) (smul (-3600) vinf))))))
      = 720 * (a1 * b3 + a2 * b2 + a3 * b1) := by
    have step : intVal (add (smul 180 v0) (add (smul (-120) v1) (add (smul (-120) vm1)
          (add (smul 30 v2) (add (smul 30 vm2) (smul (-3600) vinf))))))
        = (toom4Interpolate720 (intVal v0) (intVal v1) (intVal vm1) (intVal v2)
            (intVal vm2) (intVal v3) (intVal vinf)).2.2.2.2.1 := by
      simp only [toom4Interpolate720, add_val, smul_val]; ring
    rw [step, ev0, ev1, evm1, ev2, evm2, ev3, evinf]
    exact toom4_recombine_int_h4 a0 a1 a2 a3 b0 b1 b2 b3
  have hx5 : intVal (add (smul (-60) v0) (add (smul 60 v1) (add (smul 30 vm1)
        (add (smul (-30) v2) (add (smul (-6) vm2) (add (smul 6 v3) (smul (-2160) vinf)))))))
      = 720 * (a2 * b3 + a3 * b2) := by
    have step : intVal (add (smul (-60) v0) (add (smul 60 v1) (add (smul 30 vm1)
          (add (smul (-30) v2) (add (smul (-6) vm2) (add (smul 6 v3) (smul (-2160) vinf)))))))
        = (toom4Interpolate720 (intVal v0) (intVal v1) (intVal vm1) (intVal v2)
            (intVal vm2) (intVal v3) (intVal vinf)).2.2.2.2.2.1 := by
      simp only [toom4Interpolate720, add_val, smul_val]; ring
    rw [step, ev0, ev1, evm1, ev2, evm2, ev3, evinf]
    exact toom4_recombine_int_h5 a0 a1 a2 a3 b0 b1 b2 b3
  have hx6 : intVal (smul 720 vinf) = 720 * (a3 * b3) := by
    have step : intVal (smul 720 vinf)
        = (toom4Interpolate720 (intVal v0) (intVal v1) (intVal vm1) (intVal v2)
            (intVal vm2) (intVal v3) (intVal vinf)).2.2.2.2.2.2 := by
      simp only [toom4Interpolate720, smul_val]
    rw [step, ev0, ev1, evm1, ev2, evm2, ev3, evinf]
    exact toom4_recombine_int_h6 a0 a1 a2 a3 b0 b1 b2 b3
  simp only [toom4Recombine]
  rw [combineShift_val,
    bignumVal_divBy720_mag _ (a0 * b0) (mul_nonneg ha0 hb0) hx0,
    bignumVal_divBy720_mag _ (a0 * b1 + a1 * b0)
      (add_nonneg (mul_nonneg ha0 hb1) (mul_nonneg ha1 hb0)) hx1,
    bignumVal_divBy720_mag _ (a0 * b2 + a1 * b1 + a2 * b0)
      (add_nonneg (add_nonneg (mul_nonneg ha0 hb2) (mul_nonneg ha1 hb1)) (mul_nonneg ha2 hb0)) hx2,
    bignumVal_divBy720_mag _ (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0)
      (add_nonneg (add_nonneg (add_nonneg (mul_nonneg ha0 hb3) (mul_nonneg ha1 hb2))
        (mul_nonneg ha2 hb1)) (mul_nonneg ha3 hb0)) hx3,
    bignumVal_divBy720_mag _ (a1 * b3 + a2 * b2 + a3 * b1)
      (add_nonneg (add_nonneg (mul_nonneg ha1 hb3) (mul_nonneg ha2 hb2)) (mul_nonneg ha3 hb1)) hx4,
    bignumVal_divBy720_mag _ (a2 * b3 + a3 * b2)
      (add_nonneg (mul_nonneg ha2 hb3) (mul_nonneg ha3 hb2)) hx5,
    bignumVal_divBy720_mag _ (a3 * b3) (mul_nonneg ha3 hb3) hx6]
  ring

/-! ## The seven signed evaluation value-lemmas -/

/-- Evaluation at `1`: `intVal` of `x0 + x1 + x2 + x3`. -/
theorem intVal_eval1 (x0 x1 x2 x3 : BigInt) :
    intVal (add (add (add x0 x1) x2) x3)
      = intVal x0 + intVal x1 + intVal x2 + intVal x3 := by
  simp only [add_val]

/-- Evaluation at `-1`: `intVal` of `x0 - x1 + x2 - x3`. -/
theorem intVal_evalm1 (x0 x1 x2 x3 : BigInt) :
    intVal (sub (add (sub x0 x1) x2) x3)
      = intVal x0 - intVal x1 + intVal x2 - intVal x3 := by
  simp only [add_val, sub_val]

/-- Evaluation at `2`: `intVal` of `x0 + 2·x1 + 4·x2 + 8·x3`. -/
theorem intVal_eval2 (x0 x1 x2 x3 : BigInt) :
    intVal (add (add (add x0 (smul 2 x1)) (smul 4 x2)) (smul 8 x3))
      = intVal x0 + 2 * intVal x1 + 4 * intVal x2 + 8 * intVal x3 := by
  simp only [add_val, smul_val]

/-- Evaluation at `-2`: `intVal` of `x0 - 2·x1 + 4·x2 - 8·x3`. -/
theorem intVal_evalm2 (x0 x1 x2 x3 : BigInt) :
    intVal (sub (add (sub x0 (smul 2 x1)) (smul 4 x2)) (smul 8 x3))
      = intVal x0 - 2 * intVal x1 + 4 * intVal x2 - 8 * intVal x3 := by
  simp only [add_val, sub_val, smul_val]

/-- Evaluation at `3`: `intVal` of `x0 + 3·x1 + 9·x2 + 27·x3`. -/
theorem intVal_eval3 (x0 x1 x2 x3 : BigInt) :
    intVal (add (add (add x0 (smul 3 x1)) (smul 9 x2)) (smul 27 x3))
      = intVal x0 + 3 * intVal x1 + 9 * intVal x2 + 27 * intVal x3 := by
  simp only [add_val, smul_val]

/-! ## Recursive value correctness -/

/-- **Value correctness of the fuel-indexed recursion.**  For every fuel value,
    `bignumVal (toom4Aux fuel a b) = bignumVal a * bignumVal b`. -/
theorem toom4Aux_val (fuel : Nat) (a b : List (BitVec 64)) :
    bignumVal (toom4Aux fuel a b) = bignumVal a * bignumVal b := by
  fun_induction toom4Aux fuel a b with
  | case1 a b => exact BigNatKaratsuba.mulDispatch_val a b
  | case2 fuel a b n hn => exact BigNatKaratsuba.mulDispatch_val a b
  | case3 fuel a b n hn m a0 a1 a2 a3 b0 b1 b2 b3 av1 avm1 av2 avm2 av3
      bv1 bvm1 bv2 bvm2 bv3 v0 v1 vm1 v2 vm2 v3 vinf ih7 ih6 ih5 ih4 ih3 ih2 ih1 =>
    have ha0v : intVal a0 = (bignumVal (a.take m) : ℤ) := intVal_ofMag _
    have ha1v : intVal a1 = (bignumVal ((a.drop m).take m) : ℤ) := intVal_ofMag _
    have ha2v : intVal a2 = (bignumVal ((a.drop (2 * m)).take m) : ℤ) := intVal_ofMag _
    have ha3v : intVal a3 = (bignumVal (a.drop (3 * m)) : ℤ) := intVal_ofMag _
    have hb0v : intVal b0 = (bignumVal (b.take m) : ℤ) := intVal_ofMag _
    have hb1v : intVal b1 = (bignumVal ((b.drop m).take m) : ℤ) := intVal_ofMag _
    have hb2v : intVal b2 = (bignumVal ((b.drop (2 * m)).take m) : ℤ) := intVal_ofMag _
    have hb3v : intVal b3 = (bignumVal (b.drop (3 * m)) : ℤ) := intVal_ofMag _
    have hav1 : intVal av1 = intVal a0 + intVal a1 + intVal a2 + intVal a3 :=
      intVal_eval1 a0 a1 a2 a3
    have havm1 : intVal avm1 = intVal a0 - intVal a1 + intVal a2 - intVal a3 :=
      intVal_evalm1 a0 a1 a2 a3
    have hav2 : intVal av2 = intVal a0 + 2 * intVal a1 + 4 * intVal a2 + 8 * intVal a3 :=
      intVal_eval2 a0 a1 a2 a3
    have havm2 : intVal avm2 = intVal a0 - 2 * intVal a1 + 4 * intVal a2 - 8 * intVal a3 :=
      intVal_evalm2 a0 a1 a2 a3
    have hav3 : intVal av3 = intVal a0 + 3 * intVal a1 + 9 * intVal a2 + 27 * intVal a3 :=
      intVal_eval3 a0 a1 a2 a3
    have hbv1 : intVal bv1 = intVal b0 + intVal b1 + intVal b2 + intVal b3 :=
      intVal_eval1 b0 b1 b2 b3
    have hbvm1 : intVal bvm1 = intVal b0 - intVal b1 + intVal b2 - intVal b3 :=
      intVal_evalm1 b0 b1 b2 b3
    have hbv2 : intVal bv2 = intVal b0 + 2 * intVal b1 + 4 * intVal b2 + 8 * intVal b3 :=
      intVal_eval2 b0 b1 b2 b3
    have hbvm2 : intVal bvm2 = intVal b0 - 2 * intVal b1 + 4 * intVal b2 - 8 * intVal b3 :=
      intVal_evalm2 b0 b1 b2 b3
    have hbv3 : intVal bv3 = intVal b0 + 3 * intVal b1 + 9 * intVal b2 + 27 * intVal b3 :=
      intVal_eval3 b0 b1 b2 b3
    have hv0 : intVal v0 = intVal a0 * intVal b0 := mkBigInt_xor_val a0 b0 _ ih7
    have hv1 : intVal v1 = intVal av1 * intVal bv1 := mkBigInt_xor_val av1 bv1 _ ih6
    have hvm1 : intVal vm1 = intVal avm1 * intVal bvm1 := mkBigInt_xor_val avm1 bvm1 _ ih5
    have hv2 : intVal v2 = intVal av2 * intVal bv2 := mkBigInt_xor_val av2 bv2 _ ih4
    have hvm2 : intVal vm2 = intVal avm2 * intVal bvm2 := mkBigInt_xor_val avm2 bvm2 _ ih3
    have hv3 : intVal v3 = intVal av3 * intVal bv3 := mkBigInt_xor_val av3 bv3 _ ih2
    have hvinf : intVal vinf = intVal a3 * intVal b3 := mkBigInt_xor_val a3 b3 _ ih1
    have main := toom4Recombine_correct m
      (bignumVal (a.take m) : ℤ) (bignumVal ((a.drop m).take m) : ℤ)
      (bignumVal ((a.drop (2 * m)).take m) : ℤ) (bignumVal (a.drop (3 * m)) : ℤ)
      (bignumVal (b.take m) : ℤ) (bignumVal ((b.drop m).take m) : ℤ)
      (bignumVal ((b.drop (2 * m)).take m) : ℤ) (bignumVal (b.drop (3 * m)) : ℤ)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      v0 v1 vm1 v2 vm2 v3 vinf
      (by rw [hv0, ha0v, hb0v]; simp only [subProductsInt4, evalsInt4])
      (by rw [hv1, hav1, hbv1, ha0v, ha1v, ha2v, ha3v, hb0v, hb1v, hb2v, hb3v]
          simp only [subProductsInt4, evalsInt4])
      (by rw [hvm1, havm1, hbvm1, ha0v, ha1v, ha2v, ha3v, hb0v, hb1v, hb2v, hb3v]
          simp only [subProductsInt4, evalsInt4])
      (by rw [hv2, hav2, hbv2, ha0v, ha1v, ha2v, ha3v, hb0v, hb1v, hb2v, hb3v]
          simp only [subProductsInt4, evalsInt4])
      (by rw [hvm2, havm2, hbvm2, ha0v, ha1v, ha2v, ha3v, hb0v, hb1v, hb2v, hb3v]
          simp only [subProductsInt4, evalsInt4])
      (by rw [hv3, hav3, hbv3, ha0v, ha1v, ha2v, ha3v, hb0v, hb1v, hb2v, hb3v]
          simp only [subProductsInt4, evalsInt4])
      (by rw [hvinf, ha3v, hb3v]; simp only [subProductsInt4, evalsInt4])
    have goalZ : (bignumVal (toom4Recombine m v0 v1 vm1 v2 vm2 v3 vinf) : ℤ)
        = (bignumVal a : ℤ) * (bignumVal b : ℤ) := by
      rw [main, ← bignumVal_split4 a m, ← bignumVal_split4 b m]
    exact_mod_cast goalZ

/-- **Value correctness.**  `bignumVal (toom4 a b) = bignumVal a * bignumVal b`. -/
theorem toom4_val (a b : List (BitVec 64)) :
    bignumVal (toom4 a b) = bignumVal a * bignumVal b :=
  toom4Aux_val (max a.length b.length) a b

/-- The fuel base case is the Karatsuba dispatcher. -/
example (a b : List (BitVec 64)) : toom4Aux 0 a b = BigNatKaratsuba.mulDispatch a b := rfl

end CatCrypt.Crypto.SecureCompilation.BigNatToom4
