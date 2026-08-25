/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.BigNat
import CatCrypt.Crypto.SecureCompilation.BigNatDivMod
import CatCrypt.Crypto.SecureCompilation.BigNatCompare
import CatCrypt.Crypto.SecureCompilation.BigNatKaratsuba

/-!
# The inner Burnikel-Ziegler `divThreeByTwo` step with trial-quotient correction

The inner divisor recursion of Burnikel-Ziegler division. A three-block dividend
`[a2, a1, a0]` (values `a2·β² + a1·β + a0` with `β = 2^(64n)`) is divided by a
two-block divisor `[b1, b0]` (value `b1·β + b0`). The trial quotient comes from
`divTwoByOne [a2, a1] b1`, and the trial remainder is corrected by an add-back
loop `while rhat < q·b0 : q -= 1; rhat += b`. Under the Burnikel-Ziegler
normalization (the divisor's top block satisfies `β ≤ 2·b1`, and the dividend's
top block satisfies `a2 < b1`), the trial quotient overestimates the true
quotient by at most two, so the loop is unrolled to two conditional corrections.

The outer dividend-split recursion is `BigNatBurnikelZiegler.bzDivMod`, which
uses the Knuth-D base divide and needs no add-back. This module supplies the
complementary inner step.

## Main results

* `divTwoByOne` / `divTwoByOne_val` — the two-block-by-one-block base divide and
  its Euclidean value spec.
* `tbtStep` — one add-back correction: a conditional decrement of the quotient
  and increment of the running remainder.
* `divThreeByTwo` — the inner step: the trial divide followed by two `tbtStep`
  corrections and the final subtraction.
* `tbtTwoStep` — the two-correction invariant: given the initial Euclidean
  invariant `A + d = q·b + r`, the bound `r < b`, and the normalization bound
  `d < 2·b`, two corrections settle the running remainder into `[d, d + b)`.
* `divThreeByTwo_val` — the value spec:
  `a2·β² + a1·β + a0 = q·(b1·β + b0) + r` with `r < b1·β + b0`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNatBZThreeByTwo

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.BigNatDivMod (div mod div_val mod_val)
open CatCrypt.Crypto.SecureCompilation.BigNatKaratsuba (shiftBy shiftBy_val bnSub bnSub_val)
open CatCrypt.Crypto.SecureCompilation.BigNatCompare (ble ble_eq_true_iff)

/-! ## The two-block-by-one-block base divide -/

/-- Divide the two-block value `β·a2 + a1` (with `β = 2^(64n)`) by the single
    block `b1`, returning the Knuth-D quotient and remainder. -/
def divTwoByOne (a2 a1 b1 : List (BitVec 64)) (n : Nat) :
    List (BitVec 64) × List (BitVec 64) :=
  (div (BigNat.add (shiftBy n a2) a1) b1, mod (BigNat.add (shiftBy n a2) a1) b1)

/-- The Euclidean value spec for `divTwoByOne`: quotient and remainder read out
    the Euclidean division of `β·a2 + a1` by `b1`. -/
theorem divTwoByOne_val (a2 a1 b1 : List (BitVec 64)) (n : Nat) :
    bignumVal (divTwoByOne a2 a1 b1 n).1
        = ((2 ^ 64) ^ n * bignumVal a2 + bignumVal a1) / bignumVal b1
    ∧ bignumVal (divTwoByOne a2 a1 b1 n).2
        = ((2 ^ 64) ^ n * bignumVal a2 + bignumVal a1) % bignumVal b1 := by
  refine ⟨?_, ?_⟩
  · show bignumVal (div (BigNat.add (shiftBy n a2) a1) b1) = _
    rw [div_val, BigNat.add_val, shiftBy_val]
  · show bignumVal (mod (BigNat.add (shiftBy n a2) a1) b1) = _
    rw [mod_val, BigNat.add_val, shiftBy_val]

/-! ## One add-back correction -/

/-- One trial-quotient correction. When the running remainder `r` is already at
    least the trial deficit `d`, the state is unchanged; otherwise the quotient
    is decremented and the divisor `bb` is added back to `r`. -/
def tbtStep (bb d q r : List (BitVec 64)) : List (BitVec 64) × List (BitVec 64) :=
  if ble d r then (q, r)
  else (bnSub q [(1 : BitVec 64)], BigNat.add r bb)

/-- Value of the single-limb constant `1`. -/
theorem bignumVal_one : bignumVal [(1 : BitVec 64)] = 1 := by decide

/-! ## The two-correction invariant -/

/-- Two add-back corrections settle the running remainder into `[d, d + bb)`.

    The initial Euclidean invariant `A + d = q₀·bb + r₀`, the size bound
    `r₀ < bb`, and the normalization bound `d < 2·bb` together imply that after
    two `tbtStep` corrections the running remainder `c₂.2` satisfies
    `d ≤ c₂.2 < d + bb`, so `A = c₂.1·bb + (c₂.2 - d)` is the exact Euclidean
    decomposition with remainder below `bb`. -/
theorem tbtTwoStep (bb d q0 r0 : List (BitVec 64)) (A : Nat)
    (_hbv : 0 < bignumVal bb)
    (hinv : A + bignumVal d = bignumVal q0 * bignumVal bb + bignumVal r0)
    (hr0 : bignumVal r0 < bignumVal bb)
    (hd2 : bignumVal d < 2 * bignumVal bb) :
    bignumVal d ≤ bignumVal (tbtStep bb d (tbtStep bb d q0 r0).1 (tbtStep bb d q0 r0).2).2
    ∧ A = bignumVal (tbtStep bb d (tbtStep bb d q0 r0).1 (tbtStep bb d q0 r0).2).1 * bignumVal bb
          + (bignumVal (tbtStep bb d (tbtStep bb d q0 r0).1 (tbtStep bb d q0 r0).2).2
              - bignumVal d)
    ∧ bignumVal (tbtStep bb d (tbtStep bb d q0 r0).1 (tbtStep bb d q0 r0).2).2 - bignumVal d
        < bignumVal bb := by
  set c1 := tbtStep bb d q0 r0 with hc1def
  set c2 := tbtStep bb d c1.1 c1.2 with hc2def
  by_cases hA : ble d r0 = true
  · -- No correction on the first step; the second is a no-op too.
    have hc1eq : c1 = (q0, r0) := by rw [hc1def]; unfold tbtStep; rw [if_pos hA]
    have hc2eq : c2 = (q0, r0) := by
      rw [hc2def, hc1eq]; unfold tbtStep; dsimp only; rw [if_pos hA]
    have hArle : bignumVal d ≤ bignumVal r0 := (ble_eq_true_iff d r0).mp hA
    rw [hc2eq]; dsimp only
    refine ⟨hArle, ?_, ?_⟩
    · omega
    · omega
  · -- First correction fires: decrement, add back.
    have hr0d : bignumVal r0 < bignumVal d := by
      have hiff := ble_eq_true_iff d r0
      by_contra hc
      exact hA (hiff.mpr (by omega))
    have hc1eq : c1 = (bnSub q0 [(1 : BitVec 64)], BigNat.add r0 bb) := by
      rw [hc1def]; unfold tbtStep; rw [if_neg hA]
    have hq0pos : 1 ≤ bignumVal q0 := by
      rcases Nat.eq_zero_or_pos (bignumVal q0) with h0 | h0
      · exfalso; rw [h0, Nat.zero_mul] at hinv; omega
      · exact h0
    have hc1_1v : bignumVal c1.1 = bignumVal q0 - 1 := by
      rw [hc1eq]; dsimp only; rw [bnSub_val, bignumVal_one]
    have hc1_2v : bignumVal c1.2 = bignumVal r0 + bignumVal bb := by
      rw [hc1eq]; dsimp only; rw [BigNat.add_val]
    have hmul : (bignumVal q0 - 1) * bignumVal bb + bignumVal bb
        = bignumVal q0 * bignumVal bb := by
      have hsucc : bignumVal q0 - 1 + 1 = bignumVal q0 := Nat.sub_add_cancel hq0pos
      calc (bignumVal q0 - 1) * bignumVal bb + bignumVal bb
          = (bignumVal q0 - 1 + 1) * bignumVal bb := by rw [Nat.add_mul, Nat.one_mul]
        _ = bignumVal q0 * bignumVal bb := by rw [hsucc]
    have hI1 : A + bignumVal d
        = bignumVal c1.1 * bignumVal bb + bignumVal c1.2 := by
      rw [hc1_1v, hc1_2v]; omega
    by_cases hB : ble d c1.2 = true
    · -- Second step is a no-op.
      have hc2eq : c2 = (c1.1, c1.2) := by
        rw [hc2def]; unfold tbtStep; rw [if_pos hB]
      have hBrle : bignumVal d ≤ bignumVal c1.2 := (ble_eq_true_iff d c1.2).mp hB
      rw [hc2eq]; dsimp only
      refine ⟨hBrle, ?_, ?_⟩
      · omega
      · rw [hc1_2v]; omega
    · -- Second correction fires.
      have hc1_2d : bignumVal c1.2 < bignumVal d := by
        have hiff := ble_eq_true_iff d c1.2
        by_contra hc
        exact hB (hiff.mpr (by omega))
      have hq1pos : 1 ≤ bignumVal c1.1 := by
        rcases Nat.eq_zero_or_pos (bignumVal c1.1) with h0 | h0
        · exfalso; rw [h0, Nat.zero_mul] at hI1; omega
        · exact h0
      have hc2eq : c2 = (bnSub c1.1 [(1 : BitVec 64)], BigNat.add c1.2 bb) := by
        rw [hc2def]; unfold tbtStep; rw [if_neg hB]
      have hc2_1v : bignumVal c2.1 = bignumVal c1.1 - 1 := by
        rw [hc2eq]; dsimp only; rw [bnSub_val, bignumVal_one]
      have hc2_2v : bignumVal c2.2 = bignumVal c1.2 + bignumVal bb := by
        rw [hc2eq]; dsimp only; rw [BigNat.add_val]
      have hmul1 : (bignumVal c1.1 - 1) * bignumVal bb + bignumVal bb
          = bignumVal c1.1 * bignumVal bb := by
        have hsucc : bignumVal c1.1 - 1 + 1 = bignumVal c1.1 := Nat.sub_add_cancel hq1pos
        calc (bignumVal c1.1 - 1) * bignumVal bb + bignumVal bb
            = (bignumVal c1.1 - 1 + 1) * bignumVal bb := by rw [Nat.add_mul, Nat.one_mul]
          _ = bignumVal c1.1 * bignumVal bb := by rw [hsucc]
      have hI2 : A + bignumVal d
          = bignumVal c2.1 * bignumVal bb + bignumVal c2.2 := by
        rw [hc2_1v, hc2_2v]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hc2_2v, hc1_2v]; omega
      · rw [hc2_2v]; omega
      · rw [hc2_2v]; omega

/-! ## The inner divisor step -/

/-- The inner Burnikel-Ziegler step. Divide the three-block value
    `β²·a2 + β·a1 + a0` by the two-block value `β·b1 + b0` (`β = 2^(64n)`): take
    the trial quotient from `divTwoByOne [a2, a1] b1`, form the running remainder
    `β·r1 + a0`, then apply two `tbtStep` corrections against the trial deficit
    `q·b0` and the divisor `β·b1 + b0`, returning the corrected quotient and the
    final remainder. -/
def divThreeByTwo (a2 a1 a0 b1 b0 : List (BitVec 64)) (n : Nat) :
    List (BitVec 64) × List (BitVec 64) :=
  let qr := divTwoByOne a2 a1 b1 n
  let bb := BigNat.add (shiftBy n b1) b0
  let d := BigNat.mul qr.1 b0
  let rhat0 := BigNat.add (shiftBy n qr.2) a0
  let c1 := tbtStep bb d qr.1 rhat0
  let c2 := tbtStep bb d c1.1 c1.2
  (c2.1, bnSub c2.2 d)

/-! ## The value theorem -/

/-- **Inner-step value spec.** With `β = 2^(64n)`, under the Burnikel-Ziegler
    normalization preconditions — each low block below `β`, the dividend top
    block below the divisor top block, and the divisor normalized (`β ≤ 2·b1`) —
    the inner step computes the exact Euclidean quotient and remainder:
    `β²·a2 + β·a1 + a0 = q·(β·b1 + b0) + r` with `r < β·b1 + b0`. -/
theorem divThreeByTwo_val (a2 a1 a0 b1 b0 : List (BitVec 64)) (n : Nat)
    (ha1 : bignumVal a1 < (2 ^ 64) ^ n)
    (ha0 : bignumVal a0 < (2 ^ 64) ^ n)
    (hb0 : bignumVal b0 < (2 ^ 64) ^ n)
    (ha2 : bignumVal a2 < bignumVal b1)
    (hnorm : (2 ^ 64) ^ n ≤ 2 * bignumVal b1) :
    ((2 ^ 64) ^ n) ^ 2 * bignumVal a2 + (2 ^ 64) ^ n * bignumVal a1 + bignumVal a0
        = bignumVal (divThreeByTwo a2 a1 a0 b1 b0 n).1
            * ((2 ^ 64) ^ n * bignumVal b1 + bignumVal b0)
          + bignumVal (divThreeByTwo a2 a1 a0 b1 b0 n).2
      ∧ bignumVal (divThreeByTwo a2 a1 a0 b1 b0 n).2
          < (2 ^ 64) ^ n * bignumVal b1 + bignumVal b0 := by
  have hbpos : 0 < (2 ^ 64) ^ n := by positivity
  have hb1pos : 0 < bignumVal b1 := by omega
  -- The divisor block value.
  have hbbv : bignumVal (BigNat.add (shiftBy n b1) b0)
      = (2 ^ 64) ^ n * bignumVal b1 + bignumVal b0 := by
    rw [BigNat.add_val, shiftBy_val]
  have hbbpos : 0 < bignumVal (BigNat.add (shiftBy n b1) b0) := by
    rw [hbbv]; nlinarith [hbpos, hb1pos]
  -- Abbreviate the trial quotient and remainder values.
  set Q0 := ((2 ^ 64) ^ n * bignumVal a2 + bignumVal a1) / bignumVal b1 with hQ0def
  set R1 := ((2 ^ 64) ^ n * bignumVal a2 + bignumVal a1) % bignumVal b1 with hR1def
  have hqr1v : bignumVal (divTwoByOne a2 a1 b1 n).1 = Q0 := by
    rw [hQ0def]; exact (divTwoByOne_val a2 a1 b1 n).1
  have hqr2v : bignumVal (divTwoByOne a2 a1 b1 n).2 = R1 := by
    rw [hR1def]; exact (divTwoByOne_val a2 a1 b1 n).2
  have hdm : bignumVal b1 * Q0 + R1 = (2 ^ 64) ^ n * bignumVal a2 + bignumVal a1 := by
    rw [hQ0def, hR1def]; exact Nat.div_add_mod _ _
  have hR1lt : R1 < bignumVal b1 := by rw [hR1def]; exact Nat.mod_lt _ hb1pos
  -- The trial quotient is below β.
  have hle : (2 ^ 64) ^ n * bignumVal a2 + (2 ^ 64) ^ n ≤ (2 ^ 64) ^ n * bignumVal b1 := by
    have h := Nat.mul_le_mul (Nat.le_refl ((2 ^ 64) ^ n))
      (show bignumVal a2 + 1 ≤ bignumVal b1 by omega)
    rw [Nat.mul_add, Nat.mul_one] at h; exact h
  have hhilt : (2 ^ 64) ^ n * bignumVal a2 + bignumVal a1 < (2 ^ 64) ^ n * bignumVal b1 := by
    omega
  have hQ0lt : Q0 < (2 ^ 64) ^ n := by
    rw [hQ0def]
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm (bignumVal b1) ((2 ^ 64) ^ n)]; exact hhilt)
  -- The normalization bound d < 2·b.
  have hd2 : Q0 * bignumVal b0 < 2 * ((2 ^ 64) ^ n * bignumVal b1 + bignumVal b0) := by
    have h1 : Q0 * bignumVal b0 < (2 ^ 64) ^ n * (2 ^ 64) ^ n :=
      Nat.mul_lt_mul_of_lt_of_le hQ0lt (Nat.le_of_lt hb0) hbpos
    have h2 : (2 ^ 64) ^ n * (2 ^ 64) ^ n ≤ 2 * ((2 ^ 64) ^ n * bignumVal b1) := by
      calc (2 ^ 64) ^ n * (2 ^ 64) ^ n
          ≤ (2 ^ 64) ^ n * (2 * bignumVal b1) := Nat.mul_le_mul (Nat.le_refl _) hnorm
        _ = 2 * ((2 ^ 64) ^ n * bignumVal b1) := by ring
    omega
  -- The initial Euclidean invariant.
  have hinv0 : ((2 ^ 64) ^ n) ^ 2 * bignumVal a2 + (2 ^ 64) ^ n * bignumVal a1 + bignumVal a0
        + Q0 * bignumVal b0
      = Q0 * ((2 ^ 64) ^ n * bignumVal b1 + bignumVal b0)
        + ((2 ^ 64) ^ n * R1 + bignumVal a0) := by
    calc ((2 ^ 64) ^ n) ^ 2 * bignumVal a2 + (2 ^ 64) ^ n * bignumVal a1 + bignumVal a0
          + Q0 * bignumVal b0
        = (2 ^ 64) ^ n * ((2 ^ 64) ^ n * bignumVal a2 + bignumVal a1) + bignumVal a0
            + Q0 * bignumVal b0 := by ring
      _ = (2 ^ 64) ^ n * (bignumVal b1 * Q0 + R1) + bignumVal a0 + Q0 * bignumVal b0 := by
            rw [← hdm]
      _ = Q0 * ((2 ^ 64) ^ n * bignumVal b1 + bignumVal b0)
            + ((2 ^ 64) ^ n * R1 + bignumVal a0) := by ring
  -- Assemble the hypotheses of the two-step invariant.
  have hinv' : ((2 ^ 64) ^ n) ^ 2 * bignumVal a2 + (2 ^ 64) ^ n * bignumVal a1 + bignumVal a0
        + bignumVal (BigNat.mul (divTwoByOne a2 a1 b1 n).1 b0)
      = bignumVal (divTwoByOne a2 a1 b1 n).1 * bignumVal (BigNat.add (shiftBy n b1) b0)
        + bignumVal (BigNat.add (shiftBy n (divTwoByOne a2 a1 b1 n).2) a0) := by
    rw [BigNat.mul_val, hqr1v, hbbv, BigNat.add_val, shiftBy_val, hqr2v]
    exact hinv0
  have hr0' : bignumVal (BigNat.add (shiftBy n (divTwoByOne a2 a1 b1 n).2) a0)
      < bignumVal (BigNat.add (shiftBy n b1) b0) := by
    rw [BigNat.add_val, shiftBy_val, hqr2v, hbbv]
    have hRle : (2 ^ 64) ^ n * R1 + (2 ^ 64) ^ n ≤ (2 ^ 64) ^ n * bignumVal b1 := by
      have h := Nat.mul_le_mul (Nat.le_refl ((2 ^ 64) ^ n))
        (show R1 + 1 ≤ bignumVal b1 by omega)
      rw [Nat.mul_add, Nat.mul_one] at h; exact h
    omega
  have hd2' : bignumVal (BigNat.mul (divTwoByOne a2 a1 b1 n).1 b0)
      < 2 * bignumVal (BigNat.add (shiftBy n b1) b0) := by
    rw [BigNat.mul_val, hqr1v, hbbv]; exact hd2
  have result := tbtTwoStep (BigNat.add (shiftBy n b1) b0)
    (BigNat.mul (divTwoByOne a2 a1 b1 n).1 b0)
    (divTwoByOne a2 a1 b1 n).1
    (BigNat.add (shiftBy n (divTwoByOne a2 a1 b1 n).2) a0)
    (((2 ^ 64) ^ n) ^ 2 * bignumVal a2 + (2 ^ 64) ^ n * bignumVal a1 + bignumVal a0)
    hbbpos hinv' hr0' hd2'
  obtain ⟨_, hEq, hlt2⟩ := result
  refine ⟨?_, ?_⟩
  · simp only [divThreeByTwo]
    rw [bnSub_val, ← hbbv]
    exact hEq
  · simp only [divThreeByTwo]
    rw [bnSub_val, ← hbbv]
    exact hlt2

end CatCrypt.Crypto.SecureCompilation.BigNatBZThreeByTwo
