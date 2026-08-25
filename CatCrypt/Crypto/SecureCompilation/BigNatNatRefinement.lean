/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.BigNatMulLadder
import CatCrypt.Crypto.SecureCompilation.BigNatBitwise
import CatCrypt.Crypto.SecureCompilation.BigNatShift
import CatCrypt.Crypto.SecureCompilation.BigNatPow
import CatCrypt.Crypto.SecureCompilation.BigNatCompare
import CatCrypt.Crypto.SecureCompilation.BigNatDivMod
import CatCrypt.Crypto.SecureCompilation.BigNatGcd

set_option autoImplicit false

/-!
# Nat-level refinement of the verified limb kernels

The limb kernels (`BigNat.add`, `BigNat.mul`, `BigNatMulLadder.mulLadder`,
`BigNatBitwise.land`/`lor`/`xor`) operate on `List (BitVec 64)`. A caller that
starts from a `Nat` marshals it in with `BigNat.ofNat`, runs the kernel, and
reads the result back with `MultiLimbKernel.bignumVal`. This module proves that
the round trip equals the corresponding `Nat` operation.

Two forms of statement:

* **Grounded refinement** (`*_ofNat`): `bignumVal (kernel (ofNat a) (ofNat b))`
  equals the `Nat` reference operation on `a` and `b`. This is the composite
  `verifiedNat<Op>Impl a b = Nat.<op> a b`, where the implementation marshals in
  through `ofNat`, computes with the kernel, and reads back through `bignumVal`.
* **Interpreter equivalence** (`mulLadder_eq_schoolbook`): the size-dispatched
  Karatsuba/Toom ladder and the schoolbook multiply agree on every limb input,
  independent of any marshalling. The optimized multiply refines the naive one.

The refinements compose the per-kernel value specs (`BigNat.add_val`,
`BigNat.mul_val`, `BigNatMulLadder.mulLadder_val`, `BigNatKaratsuba.karatsuba_val`,
`BigNatBitwise.land_val`/`lor_val`/`xor_val`) with the round-trip lemma
`BigNat.toNat_ofNat`.

## Main results

* `BigNatNatRefinement.add_ofNat` — `bignumVal (add (ofNat a) (ofNat b)) = a + b`.
* `BigNatNatRefinement.mul_ofNat` — schoolbook multiply refines `Nat` `*`.
* `BigNatNatRefinement.mulLadder_ofNat` — the optimized ladder refines `Nat` `*`.
* `BigNatNatRefinement.land_ofNat`/`lor_ofNat`/`xor_ofNat` — bitwise refinements.
* `BigNatNatRefinement.shl_ofNat`/`shr_ofNat` — shift refinements to `a * 2 ^ y`
  and `a / 2 ^ y`.
* `BigNatNatRefinement.pow_ofNat` — exponentiation refines `Nat` `^`.
* `BigNatNatRefinement.beq_ofNat`/`ble_ofNat` — comparison refinements to
  `Nat.beq` and `Nat.ble`.
* `BigNatNatRefinement.div_ofNat`/`mod_ofNat` — Euclidean division and remainder
  refinements to `Nat` `/` and `%`.
* `BigNatNatRefinement.gcd_ofNat` — greatest common divisor refines `Nat.gcd`.
* `BigNatNatRefinement.mulLadder_eq_schoolbook` — ladder and schoolbook agree on
  all limb inputs.
-/

namespace CatCrypt.Crypto.SecureCompilation.BigNatNatRefinement

open CatCrypt.Crypto.SecureCompilation

local notation "bignumVal" => MultiLimbKernel.bignumVal

/-- Schoolbook addition, marshalled through `Nat`, computes `a + b`. -/
theorem add_ofNat (a b : Nat) :
    bignumVal (BigNat.add (BigNat.ofNat a) (BigNat.ofNat b)) = a + b := by
  rw [BigNat.add_val, BigNat.toNat_ofNat, BigNat.toNat_ofNat]

/-- Schoolbook multiplication, marshalled through `Nat`, computes `a * b`. -/
theorem mul_ofNat (a b : Nat) :
    bignumVal (BigNat.mul (BigNat.ofNat a) (BigNat.ofNat b)) = a * b := by
  rw [BigNat.mul_val, BigNat.toNat_ofNat, BigNat.toNat_ofNat]

/-- The size-dispatched Karatsuba/Toom ladder, marshalled through `Nat`,
    computes `a * b`. This is the refinement the verified-mpn `@[implemented_by]`
    multiply seam asserts: the optimized kernel equals `Nat.mul`. -/
theorem mulLadder_ofNat (a b : Nat) :
    bignumVal (BigNatMulLadder.mulLadder (BigNat.ofNat a) (BigNat.ofNat b)) = a * b := by
  rw [BigNatMulLadder.mulLadder_val, BigNat.toNat_ofNat, BigNat.toNat_ofNat]

/-- Bitwise AND, marshalled through `Nat`, computes `Nat.land a b`. -/
theorem land_ofNat (a b : Nat) :
    bignumVal (BigNatBitwise.land (BigNat.ofNat a) (BigNat.ofNat b)) = Nat.land a b := by
  rw [BigNatBitwise.land_val, BigNat.toNat_ofNat, BigNat.toNat_ofNat]

/-- Bitwise OR, marshalled through `Nat`, computes `Nat.lor a b`. -/
theorem lor_ofNat (a b : Nat) :
    bignumVal (BigNatBitwise.lor (BigNat.ofNat a) (BigNat.ofNat b)) = Nat.lor a b := by
  rw [BigNatBitwise.lor_val, BigNat.toNat_ofNat, BigNat.toNat_ofNat]

/-- Bitwise XOR, marshalled through `Nat`, computes `Nat.xor a b`. -/
theorem xor_ofNat (a b : Nat) :
    bignumVal (BigNatBitwise.xor (BigNat.ofNat a) (BigNat.ofNat b)) = Nat.xor a b := by
  rw [BigNatBitwise.xor_val, BigNat.toNat_ofNat, BigNat.toNat_ofNat]

/-- Left shift, marshalled through `Nat`, computes `a * 2 ^ y`. -/
theorem shl_ofNat (a : Nat) (y : Nat) :
    bignumVal (BigNatShift.shl (BigNat.ofNat a) y) = a * 2 ^ y := by
  rw [BigNatShift.shl_val, BigNat.toNat_ofNat]

/-- Right shift, marshalled through `Nat`, computes `a / 2 ^ y`. -/
theorem shr_ofNat (a : Nat) (y : Nat) :
    bignumVal (BigNatShift.shr (BigNat.ofNat a) y) = a / 2 ^ y := by
  rw [BigNatShift.shr_val, BigNat.toNat_ofNat]

/-- Exponentiation, marshalled through `Nat`, computes `a ^ n`. -/
theorem pow_ofNat (a : Nat) (n : Nat) :
    bignumVal (BigNat.pow (BigNat.ofNat a) n) = a ^ n := by
  rw [BigNat.pow_val, BigNat.toNat_ofNat]

/-- Equality test, marshalled through `Nat`, computes `Nat.beq a b`. -/
theorem beq_ofNat (a b : Nat) :
    BigNatCompare.beq (BigNat.ofNat a) (BigNat.ofNat b) = Nat.beq a b := by
  rw [BigNatCompare.beq_val, BigNat.toNat_ofNat, BigNat.toNat_ofNat]

/-- Less-or-equal test, marshalled through `Nat`, computes `Nat.ble a b`. -/
theorem ble_ofNat (a b : Nat) :
    BigNatCompare.ble (BigNat.ofNat a) (BigNat.ofNat b) = Nat.ble a b := by
  rw [BigNatCompare.ble_val, BigNat.toNat_ofNat, BigNat.toNat_ofNat]

/-- Euclidean division, marshalled through `Nat`, computes `a / b`. -/
theorem div_ofNat (a b : Nat) :
    bignumVal (BigNatDivMod.div (BigNat.ofNat a) (BigNat.ofNat b)) = a / b := by
  rw [BigNatDivMod.div_val, BigNat.toNat_ofNat, BigNat.toNat_ofNat]

/-- Euclidean remainder, marshalled through `Nat`, computes `a % b`. -/
theorem mod_ofNat (a b : Nat) :
    bignumVal (BigNatDivMod.mod (BigNat.ofNat a) (BigNat.ofNat b)) = a % b := by
  rw [BigNatDivMod.mod_val, BigNat.toNat_ofNat, BigNat.toNat_ofNat]

/-- Greatest common divisor, marshalled through `Nat`, computes `Nat.gcd a b`. -/
theorem gcd_ofNat (a b : Nat) :
    bignumVal (BigNatGcd.gcd (BigNat.ofNat a) (BigNat.ofNat b)) = Nat.gcd a b := by
  rw [BigNatGcd.gcd_val, BigNat.toNat_ofNat, BigNat.toNat_ofNat]

/-- **Interpreter equivalence.** The optimized ladder and the schoolbook multiply
    produce the same value on every pair of limb lists. Both equal the product, so
    replacing schoolbook with the ladder preserves the result exactly. -/
theorem mulLadder_eq_schoolbook (a b : List (BitVec 64)) :
    bignumVal (BigNatMulLadder.mulLadder a b) = bignumVal (BigNat.mul a b) := by
  rw [BigNatMulLadder.mulLadder_val, BigNat.mul_val]

end CatCrypt.Crypto.SecureCompilation.BigNatNatRefinement
