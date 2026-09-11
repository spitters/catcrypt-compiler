/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.BigNat
public import CatCrypt.Crypto.SecureCompilation.BigNatDivMod
public import CatCrypt.Crypto.SecureCompilation.BigNatCompare
public import CatCrypt.Crypto.SecureCompilation.BigNatKaratsuba

/-!
# Recursive divide-and-conquer division on the `BigNat` carrier

An executable recursive Burnikel-Ziegler-style division over the little-endian
limb-list carrier `bignumVal`. The dividend is split into a low block and a high
block; the high block is divided recursively, its remainder is recombined with
the low block, and that is divided recursively again. The Knuth Algorithm D base
case `BigNatDivMod.div` / `BigNatDivMod.mod` closes the recursion below the
split threshold and when the structural fuel is exhausted.

The recombination is exact: each recursive divide returns an exact Euclidean
quotient and remainder, so no trial-quotient add-back correction is needed and
the value theorem follows from Euclidean uniqueness. This realizes the outer
`divTwoByOne` recursion of Burnikel-Ziegler with Knuth-D as the per-block base
divide; the inner `divThreeByTwo` divisor recursion with add-back is not part of
this module.

## Main results

* `bzAux` — the fuel-indexed recursive divide-and-conquer step: base case falls
  back to `BigNatDivMod.div` / `BigNatDivMod.mod`, recursive case splits the
  dividend at its midpoint and recurses twice.
* `bzDivMod` — the top-level driver `bzAux (max a.length b.length) a b`, the fuel
  chosen large enough that the recursion always bottoms out at the base case.
* `bzAux_val`, `bzDivMod_val` — the value theorem
  `bignumVal q = bignumVal a / bignumVal b ∧ bignumVal r = bignumVal a % bignumVal b`
  for `bignumVal b ≠ 0`, by induction on the fuel and Euclidean uniqueness.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNatBurnikelZiegler

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal bignumVal_take_drop)
open CatCrypt.Crypto.SecureCompilation.BigNatDivMod (div mod div_val mod_val div_of_euclid mod_of_euclid)
open CatCrypt.Crypto.SecureCompilation.BigNatKaratsuba (shiftBy shiftBy_val)

/-! ## The recursive divide-and-conquer step -/

/-- Fuel-indexed recursive division. The base case (`fuel = 0`, or a dividend too
    short to split) is the verified Knuth-D `div` / `mod`. The recursive case
    splits the dividend `a` at `k = a.length / 2` into a low block `a.take k` and
    a high block `a.drop k`, divides the high block, recombines its remainder
    `rhi` with the low block as `rhi · 2^(64k) + a.take k`, and divides that. The
    quotient is `qhi · 2^(64k) + qlo`. -/
def bzAux : Nat → List (BitVec 64) → List (BitVec 64) → List (BitVec 64) × List (BitVec 64)
  | 0, a, b => (div a b, mod a b)
  | fuel + 1, a, b =>
    if a.length ≤ 1 then
      (div a b, mod a b)
    else
      let k := a.length / 2
      let hi := bzAux fuel (a.drop k) b
      let mid := BigNat.add (shiftBy k hi.2) (a.take k)
      let lo := bzAux fuel mid b
      (BigNat.add (shiftBy k hi.1) lo.1, lo.2)

/-- The top-level driver. The fuel `max a.length b.length` bounds the recursion
    depth (each recursive call divides the dividend length), so the recursion
    always reaches the Knuth-D base case. -/
def bzDivMod (a b : List (BitVec 64)) : List (BitVec 64) × List (BitVec 64) :=
  bzAux (max a.length b.length) a b

/-! ## The value theorem -/

/-- The value theorem for the fuel-indexed step, for every fuel. Both quotient
    and remainder read out the Euclidean `bignumVal a / bignumVal b` and
    `bignumVal a % bignumVal b`. -/
theorem bzAux_val : ∀ (fuel : Nat) (a b : List (BitVec 64)), bignumVal b ≠ 0 →
    bignumVal (bzAux fuel a b).1 = bignumVal a / bignumVal b ∧
    bignumVal (bzAux fuel a b).2 = bignumVal a % bignumVal b
  | 0, a, b, _ => ⟨div_val a b, mod_val a b⟩
  | fuel + 1, a, b, hb => by
    by_cases hcond : a.length ≤ 1
    · have hunf : bzAux (fuel + 1) a b = (div a b, mod a b) := by
        show (if a.length ≤ 1 then (div a b, mod a b) else _) = _
        rw [if_pos hcond]
      rw [hunf]; exact ⟨div_val a b, mod_val a b⟩
    · have hbpos : 0 < bignumVal b := Nat.pos_of_ne_zero hb
      set k := a.length / 2 with hk
      have ihhi := bzAux_val fuel (a.drop k) b hb
      set hi := bzAux fuel (a.drop k) b with hhi
      obtain ⟨ihhi1, ihhi2⟩ := ihhi
      set mid := BigNat.add (shiftBy k hi.2) (a.take k) with hmid
      have ihlo := bzAux_val fuel mid b hb
      set lo := bzAux fuel mid b with hlo
      obtain ⟨ihlo1, ihlo2⟩ := ihlo
      have hunf : bzAux (fuel + 1) a b = (BigNat.add (shiftBy k hi.1) lo.1, lo.2) := by
        show (if a.length ≤ 1 then (div a b, mod a b)
              else (BigNat.add (shiftBy k hi.1) lo.1, lo.2)) = _
        rw [if_neg hcond]
      have hmidval : bignumVal mid = (2 ^ 64) ^ k * bignumVal hi.2 + bignumVal (a.take k) := by
        rw [hmid, BigNat.add_val, shiftBy_val]
      have hqval : bignumVal (BigNat.add (shiftBy k hi.1) lo.1)
          = (2 ^ 64) ^ k * bignumVal hi.1 + bignumVal lo.1 := by
        rw [BigNat.add_val, shiftBy_val]
      have hahi : bignumVal (a.drop k)
          = bignumVal b * bignumVal hi.1 + bignumVal hi.2 := by
        rw [ihhi1, ihhi2]; exact (Nat.div_add_mod (bignumVal (a.drop k)) (bignumVal b)).symm
      have hmidsplit : bignumVal mid
          = bignumVal b * bignumVal lo.1 + bignumVal lo.2 := by
        rw [ihlo1, ihlo2]; exact (Nat.div_add_mod (bignumVal mid) (bignumVal b)).symm
      have hmideq : (2 ^ 64) ^ k * bignumVal hi.2 + bignumVal (a.take k)
          = bignumVal b * bignumVal lo.1 + bignumVal lo.2 := by
        rw [← hmidval, hmidsplit]
      have hR : bignumVal lo.2 < bignumVal b := by rw [ihlo2]; exact Nat.mod_lt _ hbpos
      have key : bignumVal a = bignumVal b * (2 ^ 64) ^ k * bignumVal hi.1
          + ((2 ^ 64) ^ k * bignumVal hi.2 + bignumVal (a.take k)) := by
        rw [bignumVal_take_drop k a, hahi]; ring
      rw [hmideq] at key
      have heq : ((2 ^ 64) ^ k * bignumVal hi.1 + bignumVal lo.1) * bignumVal b
          + bignumVal lo.2 = bignumVal a := by
        rw [key]; ring
      rw [hunf]
      refine ⟨?_, ?_⟩
      · show bignumVal (BigNat.add (shiftBy k hi.1) lo.1) = bignumVal a / bignumVal b
        rw [hqval]; exact (div_of_euclid hbpos heq hR).symm
      · show bignumVal lo.2 = bignumVal a % bignumVal b
        exact (mod_of_euclid heq hR).symm

/-- **Division/modulo value spec.** For `bignumVal b ≠ 0`,
    `bignumVal (bzDivMod a b).1 = bignumVal a / bignumVal b` and
    `bignumVal (bzDivMod a b).2 = bignumVal a % bignumVal b`. -/
theorem bzDivMod_val (a b : List (BitVec 64)) (hb : bignumVal b ≠ 0) :
    bignumVal (bzDivMod a b).1 = bignumVal a / bignumVal b ∧
    bignumVal (bzDivMod a b).2 = bignumVal a % bignumVal b :=
  bzAux_val (max a.length b.length) a b hb

end CatCrypt.Crypto.SecureCompilation.BigNatBurnikelZiegler
