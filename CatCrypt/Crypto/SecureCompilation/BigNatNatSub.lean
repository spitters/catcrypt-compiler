/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.BigNatBitwise

set_option autoImplicit false

/-!
# Truncated `Nat` subtraction on the `BigNat` limb carrier

`BigNat.satSub` computes the saturating difference of two limb lists, but its
value spec `BigNat.satSub_val` requires equal-length operands. For `ofNat`
marshalling the two operands generally have different limb lengths. This module
pads both operands with high zero limbs to their common length and lifts the
value spec to arbitrary lengths, then to the `Nat` truncated subtraction
`a - b` (which is `0` when `b ≥ a`, matching lean4lean's `reduceNat` on
`Nat.sub`).

## Main results

* `natSub` — truncated subtraction on `List (BitVec 64)`: pad both operands to
  their common length, then `BigNat.satSub`.
* `natSub_val` — `bignumVal (natSub a b) = bignumVal a - bignumVal b` for
  arbitrary limb lengths (no length hypothesis).
* `sub_ofNat` — `bignumVal (natSub (ofNat a) (ofNat b)) = a - b`, the grounded
  refinement of truncated `Nat` subtraction.
-/

namespace CatCrypt.Crypto.SecureCompilation.BigNatNatSub

open CatCrypt.Crypto.SecureCompilation

local notation "bignumVal" => MultiLimbKernel.bignumVal

/-- Truncated subtraction of two limb lists: pad both operands with high zero
    limbs to their common length, then take the saturating difference. -/
def natSub (a b : List (BitVec 64)) : List (BitVec 64) :=
  let n := max a.length b.length
  BigNat.satSub (a ++ List.replicate (n - a.length) 0)
    (b ++ List.replicate (n - b.length) 0)

/-- **Truncated subtraction.** `bignumVal (natSub a b) = bignumVal a - bignumVal b`
    (truncated `Nat` subtraction), for arbitrary limb lengths. -/
theorem natSub_val (a b : List (BitVec 64)) :
    bignumVal (natSub a b) = bignumVal a - bignumVal b := by
  simp only [natSub]
  rw [BigNat.satSub_val _ _ (BigNatBitwise.padLen a b),
    BigNatBitwise.bignumVal_pad, BigNatBitwise.bignumVal_pad]

/-- Truncated subtraction, marshalled through `Nat`, computes `a - b`. -/
theorem sub_ofNat (a b : Nat) :
    bignumVal (natSub (BigNat.ofNat a) (BigNat.ofNat b)) = a - b := by
  rw [natSub_val, BigNat.toNat_ofNat, BigNat.toNat_ofNat]

end CatCrypt.Crypto.SecureCompilation.BigNatNatSub
