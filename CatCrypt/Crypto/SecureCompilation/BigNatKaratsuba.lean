/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.BigNat
import CatCrypt.Crypto.SecureCompilation.BigNatShift

/-!
# Recursive integer Karatsuba multiplication on the `BigNat` carrier

A recursive Karatsuba multiply over the variable-width limb-list carrier
`bignumVal` (little-endian base `2^64`), with the value-correctness statement
`bignumVal (karatsuba a b) = bignumVal a * bignumVal b`.  Above a fixed
crossover the algorithm splits each operand at the half-limb point, recurses on
three sub-products, and recombines with the three-multiply identity; below the
crossover it uses the schoolbook `BigNat.mul`.

## Main results

* `bnSub` / `bnSub_val` — exact (truncating) carrier subtraction built on the
  saturating `BigNat.satSub`, `bignumVal (bnSub a b) = bignumVal a - bignumVal b`.
* `shiftBy` / `shiftBy_val` — whole-limb left shift, `bignumVal (shiftBy m xs) =
  (2^64)^m * bignumVal xs`.
* `karatsuba_recombine` — the three-multiply Karatsuba recombination identity
  over `Nat`.
* `karatsuba` / `karatsuba_val` — the recursive multiply and its value
  correctness `bignumVal (karatsuba a b) = bignumVal a * bignumVal b`.
* `mulDispatch` / `mulDispatch_val` — a size dispatcher wrapping `karatsuba`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNatKaratsuba

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.BigNat
open CatCrypt.Crypto.SecureCompilation.BigNatShift

/-! ## Value of an appended limb list -/

/-- Concatenation scales the high part by the whole-limb factor. -/
theorem bignumVal_append : ∀ (xs ys : List (BitVec 64)),
    bignumVal (xs ++ ys) = bignumVal xs + (2 ^ 64) ^ xs.length * bignumVal ys
  | [], ys => by simp [bignumVal]
  | x :: xs, ys => by
      simp only [List.cons_append, bignumVal, List.length_cons, pow_succ]
      rw [bignumVal_append xs ys]; ring

/-- The carrier-add output length: one limb wider than the wider operand. -/
theorem add_length (a b : List (BitVec 64)) :
    (BigNat.add a b).length = max a.length b.length + 1 := by
  simp only [BigNat.add]; exact bnAdd_length a b 0

/-! ## Exact carrier subtraction -/

/-- Exact (truncating) carrier subtraction.  Both operands are zero-padded to
    their common maximum length, then the saturating `BigNat.satSub` (which is
    exact for equal-length inputs) is applied. -/
def bnSub (a b : List (BitVec 64)) : List (BitVec 64) :=
  BigNat.satSub (a ++ List.replicate (max a.length b.length - a.length) 0)
                (b ++ List.replicate (max a.length b.length - b.length) 0)

/-- **Exact subtraction.**  `bignumVal (bnSub a b) = bignumVal a - bignumVal b`
    (truncating `Nat` subtraction), with no length hypothesis. -/
theorem bnSub_val (a b : List (BitVec 64)) :
    bignumVal (bnSub a b) = bignumVal a - bignumVal b := by
  have hla : (a ++ List.replicate (max a.length b.length - a.length) 0).length
      = max a.length b.length := by
    simp only [List.length_append, List.length_replicate]; omega
  have hlb : (b ++ List.replicate (max a.length b.length - b.length) 0).length
      = max a.length b.length := by
    simp only [List.length_append, List.length_replicate]; omega
  rw [bnSub, BigNat.satSub_val _ _ (by rw [hla, hlb]),
    bignumVal_append, bignumVal_append,
    BigNat.bignumVal_replicate_zero, BigNat.bignumVal_replicate_zero]
  simp

/-! ## Whole-limb left shift -/

/-- Whole-limb left shift: prepend `m` zero limbs. -/
def shiftBy (m : Nat) (xs : List (BitVec 64)) : List (BitVec 64) :=
  List.replicate m 0 ++ xs

/-- **Left shift value.**  `bignumVal (shiftBy m xs) = (2^64)^m * bignumVal xs`. -/
theorem shiftBy_val (m : Nat) (xs : List (BitVec 64)) :
    bignumVal (shiftBy m xs) = (2 ^ 64) ^ m * bignumVal xs :=
  bignumVal_replicate_append m xs

/-! ## The three-multiply recombination identity -/

/-- **The Karatsuba three-multiply identity over `Nat`.**  Splitting
    `A = a0 + Bm·a1` and `B = b0 + Bm·b1`, the product is recovered from the
    three sub-products `a0·b0`, `a1·b1`, `(a0+a1)·(b0+b1)`. -/
theorem karatsuba_recombine (a0 a1 b0 b1 Bm : Nat) :
    (a0 + Bm * a1) * (b0 + Bm * b1)
      = a0 * b0 + Bm * ((a0 + a1) * (b0 + b1) - a0 * b0 - a1 * b1)
        + Bm * Bm * (a1 * b1) := by
  have h1 : (a0 + a1) * (b0 + b1) - a0 * b0 - a1 * b1 = a0 * b1 + a1 * b0 := by
    have hexpand : (a0 + a1) * (b0 + b1) = a0 * b0 + a0 * b1 + a1 * b0 + a1 * b1 := by
      ring
    omega
  rw [h1]; ring

/-! ## Recursive Karatsuba multiplication -/

/-- Recursive integer Karatsuba multiplication.  Below the crossover (wider
    operand under 16 limbs) it uses the schoolbook `BigNat.mul`; otherwise it
    splits at the half-limb point, recurses on three sub-products, and
    recombines. -/
def karatsuba (a b : List (BitVec 64)) : List (BitVec 64) :=
  let n := max a.length b.length
  if h : n < 16 then BigNat.mul a b
  else
    let m := n / 2
    let a0 := a.take m
    let a1 := a.drop m
    let b0 := b.take m
    let b1 := b.drop m
    let z0 := karatsuba a0 b0
    let z2 := karatsuba a1 b1
    let z1 := bnSub (bnSub (karatsuba (BigNat.add a0 a1) (BigNat.add b0 b1)) z0) z2
    BigNat.add z0 (BigNat.add (shiftBy m z1) (shiftBy (2 * m) z2))
termination_by max a.length b.length
decreasing_by
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega
  · simp only [add_length, List.length_take, List.length_drop]; omega

/-- **Value correctness.**  `bignumVal (karatsuba a b) = bignumVal a * bignumVal b`. -/
theorem karatsuba_val (a b : List (BitVec 64)) :
    bignumVal (karatsuba a b) = bignumVal a * bignumVal b := by
  fun_induction karatsuba a b with
  | case1 a b _n _hg => exact BigNat.mul_val a b
  | case2 a b _n _hg m a0 a1 b0 b1 z0 z2 z1 ihz0 ihz2 ihz1 =>
    -- Expand the let-bound sub-products to their bodies (definitional).
    rw [show z1 = bnSub (bnSub (karatsuba (BigNat.add a0 a1) (BigNat.add b0 b1))
            (karatsuba a0 b0)) (karatsuba a1 b1) from rfl,
      show z0 = karatsuba a0 b0 from rfl,
      show z2 = karatsuba a1 b1 from rfl]
    rw [BigNat.add_val, BigNat.add_val, shiftBy_val, shiftBy_val,
      bnSub_val, bnSub_val, ihz0, ihz2, ihz1, BigNat.add_val, BigNat.add_val]
    -- Split the two operands at the half-limb point `m` (definitional folds).
    have hsplitA : bignumVal a = bignumVal a0 + (2 ^ 64) ^ m * bignumVal a1 :=
      bignumVal_take_drop m a
    have hsplitB : bignumVal b = bignumVal b0 + (2 ^ 64) ^ m * bignumVal b1 :=
      bignumVal_take_drop m b
    rw [hsplitA, hsplitB]
    have hBm2 : (2 ^ 64 : ℕ) ^ (2 * m)
        = (2 ^ 64) ^ m * (2 ^ 64) ^ m := by rw [two_mul, pow_add]
    rw [hBm2, karatsuba_recombine]
    omega

/-! ## Size dispatcher -/

/-- Size-dispatched multiply: the Karatsuba recursion.  Interchangeable with the
    schoolbook `BigNat.mul` at the value level. -/
def mulDispatch (a b : List (BitVec 64)) : List (BitVec 64) := karatsuba a b

/-- **Dispatcher value correctness.** -/
theorem mulDispatch_val (a b : List (BitVec 64)) :
    bignumVal (mulDispatch a b) = bignumVal a * bignumVal b :=
  karatsuba_val a b

end CatCrypt.Crypto.SecureCompilation.BigNatKaratsuba
