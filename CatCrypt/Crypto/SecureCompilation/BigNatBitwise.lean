/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.BigNat

/-!
# Bitwise operations on the `BigNat` limb carrier

The three bitwise operations `land`, `lor`, `xor` on little-endian
`List (BitVec 64)` limb lists, each composing to the corresponding `Nat`
operation under `bignumVal`.

`Nat.land`, `Nat.lor`, `Nat.xor` are bit-indexed, while a limb list groups the
bits into base-`2^64` blocks. The bridge is the block-split lemma: a bit
operation on `x + 2^64 * X` and `y + 2^64 * Y` (with `x, y < 2^64`) acts on the
low limbs and the high blocks independently. The operations pad the shorter
operand with zero limbs to a common length, matching the zero-extension in the
`Nat` operations.

## Main results

* `block_split` — for a bit-indexed `Nat` operation, the base-`2^64` block
  decomposition `natOp (x + 2^64·X) (y + 2^64·Y) = natOp x y + 2^64 · natOp X Y`
  when `x, y < 2^64`.
* `bignumVal_zipWith` — a limb-wise `List.zipWith` of a `BitVec` operation over
  equal-length lists evaluates to the `Nat` operation of the two values.
* `land_val`, `lor_val`, `xor_val` — `bignumVal (land a b) = Nat.land
  (bignumVal a) (bignumVal b)` and the `lor` / `xor` analogues, for arbitrary
  limb lengths.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNatBitwise

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## The block-split bridge -/

/-- **Block split.** A `Nat` operation whose bit `k` is `bop` of the operands'
    bit `k` decomposes across a base-`2^64` block boundary: on the low limbs
    `x, y < 2^64` and on the high blocks `X, Y` independently. -/
theorem block_split
    (natOp : Nat → Nat → Nat) (bop : Bool → Bool → Bool)
    (hbit : ∀ m n k, (natOp m n).testBit k = bop (m.testBit k) (n.testBit k))
    (hrange : ∀ x y, x < 2 ^ 64 → y < 2 ^ 64 → natOp x y < 2 ^ 64)
    (x X y Y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    natOp (x + 2 ^ 64 * X) (y + 2 ^ 64 * Y) = natOp x y + 2 ^ 64 * natOp X Y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [hbit, Nat.add_comm x (2 ^ 64 * X), Nat.add_comm y (2 ^ 64 * Y),
      Nat.add_comm (natOp x y) (2 ^ 64 * natOp X Y),
      Nat.testBit_two_pow_mul_add X hx, Nat.testBit_two_pow_mul_add Y hy,
      Nat.testBit_two_pow_mul_add (natOp X Y) (hrange x y hx hy)]
  by_cases hj : j < 64
  · simp only [if_pos hj]; exact (hbit x y j).symm
  · simp only [if_neg hj]; exact (hbit X Y (j - 64)).symm

/-! ## Appending and zero-padding limb lists -/

/-- `bignumVal` of an append: the high list scales by `2^(64·len)` of the low. -/
theorem bignumVal_append : ∀ (a b : List (BitVec 64)),
    bignumVal (a ++ b) = bignumVal a + (2 ^ 64) ^ a.length * bignumVal b
  | [], b => by simp [bignumVal]
  | x :: xs, b => by
      simp only [List.cons_append, bignumVal, List.length_cons, pow_succ]
      rw [bignumVal_append xs b]; ring

/-- Appending zero limbs preserves the value. -/
theorem bignumVal_pad (l : List (BitVec 64)) (k : Nat) :
    bignumVal (l ++ List.replicate k 0) = bignumVal l := by
  rw [bignumVal_append, BigNat.bignumVal_replicate_zero]; simp

/-! ## The limb-wise driver -/

/-- **Limb-wise operation.** For equal-length limb lists, a `List.zipWith` of a
    `BitVec` operation `op` whose value tracks a bit-indexed `Nat` operation
    `natOp` evaluates to `natOp` of the two limb-list values. -/
theorem bignumVal_zipWith
    (op : BitVec 64 → BitVec 64 → BitVec 64)
    (natOp : Nat → Nat → Nat) (bop : Bool → Bool → Bool)
    (hbit : ∀ m n k, (natOp m n).testBit k = bop (m.testBit k) (n.testBit k))
    (hrange : ∀ x y, x < 2 ^ 64 → y < 2 ^ 64 → natOp x y < 2 ^ 64)
    (hlimb : ∀ x y : BitVec 64, (op x y).toNat = natOp x.toNat y.toNat)
    (hnat0 : natOp 0 0 = 0) :
    ∀ a b : List (BitVec 64), a.length = b.length →
      bignumVal (List.zipWith op a b) = natOp (bignumVal a) (bignumVal b)
  | [], [], _ => by simp [bignumVal, hnat0]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [List.zipWith_cons_cons, bignumVal]
      rw [block_split natOp bop hbit hrange x.toNat (bignumVal xs) y.toNat (bignumVal ys)
            x.isLt y.isLt, bignumVal_zipWith op natOp bop hbit hrange hlimb hnat0 xs ys h,
          hlimb]

/-! ## Length matching after zero-padding -/

/-- Padding both operands to `max` of their lengths equalizes them. -/
theorem padLen (a b : List (BitVec 64)) :
    (a ++ List.replicate (max a.length b.length - a.length) 0).length
      = (b ++ List.replicate (max a.length b.length - b.length) 0).length := by
  simp only [List.length_append, List.length_replicate]; omega

/-! ## The three operations -/

/-- Bitwise AND of two limb lists: pad to a common length, then limb-wise AND. -/
def land (a b : List (BitVec 64)) : List (BitVec 64) :=
  let n := max a.length b.length
  List.zipWith (· &&& ·) (a ++ List.replicate (n - a.length) 0)
    (b ++ List.replicate (n - b.length) 0)

/-- Bitwise OR of two limb lists: pad to a common length, then limb-wise OR. -/
def lor (a b : List (BitVec 64)) : List (BitVec 64) :=
  let n := max a.length b.length
  List.zipWith (· ||| ·) (a ++ List.replicate (n - a.length) 0)
    (b ++ List.replicate (n - b.length) 0)

/-- Bitwise XOR of two limb lists: pad to a common length, then limb-wise XOR. -/
def xor (a b : List (BitVec 64)) : List (BitVec 64) :=
  let n := max a.length b.length
  List.zipWith (· ^^^ ·) (a ++ List.replicate (n - a.length) 0)
    (b ++ List.replicate (n - b.length) 0)

/-- **AND.** `bignumVal (land a b) = Nat.land (bignumVal a) (bignumVal b)`. -/
theorem land_val (a b : List (BitVec 64)) :
    bignumVal (land a b) = Nat.land (bignumVal a) (bignumVal b) := by
  simp only [land]
  rw [bignumVal_zipWith (· &&& ·) Nat.land (· && ·) Nat.testBit_and
        (fun x _ _ hy => Nat.and_lt_two_pow x hy) (fun x y => BitVec.toNat_and x y)
        (by simp) _ _ (padLen a b), bignumVal_pad, bignumVal_pad]

/-- **OR.** `bignumVal (lor a b) = Nat.lor (bignumVal a) (bignumVal b)`. -/
theorem lor_val (a b : List (BitVec 64)) :
    bignumVal (lor a b) = Nat.lor (bignumVal a) (bignumVal b) := by
  simp only [lor]
  rw [bignumVal_zipWith (· ||| ·) Nat.lor (· || ·) Nat.testBit_or
        (fun _ _ hx hy => Nat.or_lt_two_pow hx hy) (fun x y => BitVec.toNat_or x y)
        (by simp) _ _ (padLen a b), bignumVal_pad, bignumVal_pad]

/-- **XOR.** `bignumVal (xor a b) = Nat.xor (bignumVal a) (bignumVal b)`. -/
theorem xor_val (a b : List (BitVec 64)) :
    bignumVal (xor a b) = Nat.xor (bignumVal a) (bignumVal b) := by
  simp only [xor]
  rw [bignumVal_zipWith (· ^^^ ·) Nat.xor (· ^^ ·) Nat.testBit_xor
        (fun _ _ hx hy => Nat.xor_lt_two_pow hx hy) (fun x y => BitVec.toNat_xor x y)
        (by simp) _ _ (padLen a b), bignumVal_pad, bignumVal_pad]

end CatCrypt.Crypto.SecureCompilation.BigNatBitwise
