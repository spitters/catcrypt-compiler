/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NarrowField

/-!
# Single-word multiplication at the 31-bit fields of zero-knowledge provers

`WordField` instances at KoalaBear (`p = 2 ^ 31 − 2 ^ 24 + 1`) and Mersenne-31
(`p = 2 ^ 31 − 1`) in 32-bit words, with the Montgomery, Barrett and Plantard certificates
of `NarrowField`, and the Mersenne fold multiply.

The fold multiply `foldBlk w k` forms `t = a · b` at `2 w` bits and replaces `t` twice by
`(t mod 2 ^ k) + ⌊t / 2 ^ k⌋`, which is congruent to `t` modulo `2 ^ k − 1`. It lies in the
exact fragment of `ComRangeExact`, so its word theorem combines the algebraic theorem
`foldZ_cast` with `run2_eq_denoteZ`. At Mersenne-31 in 32-bit words the bound `2 ^ 31` is
both an input and an output bound, so fold multiplies chain without a final subtraction.

The Plantard instances `babyBearFieldP` and `koalaBearFieldP` take the input bound `p`,
the output bound of the Plantard block, so that Plantard multiplies chain.

At Goldilocks (`p = 2 ^ 64 − 2 ^ 32 + 1`, `w = 64`) none of the three blocks of
`NarrowField` passes its certificate with input bound `p − 1`: the Montgomery sum
`t + m · p` exceeds `2 ^ 128`, the Barrett remainder bound `3 p − 2` exceeds `2 ^ 64` at
the narrowing cast, and `(p − 1) ^ 2 + 2 ^ 64 · p ≥ 2 ^ 128` fails the Plantard
condition.

## Main definitions

* `koalaBearField`, `mersenne31Field`: the instances with input bound `p − 1`.
* `babyBearFieldP`, `koalaBearFieldP`: the Plantard instances with input bound `p`.
* `foldBlk`, `foldZ`: the Mersenne fold multiply and its integer semantics.
* `foldOk`: its decidable side condition.

## Main results

* `koalaBearField_montOk`, …, `mersenne31Field_plantOk`: the instance certificates.
* `babyBearFieldP_plantOk`, `koalaBearFieldP_plantOk`: the Plantard chain certificates.
* `foldZ_cast`: the fold multiply is congruent to `a · b` modulo `2 ^ k − 1`.
* `mulFold_rep`: on words representing `u`, `v` the fold output represents `u · v`.
* `mersenne31_foldOk`: the fold certificate at `k = 31`, `w = 32`, bound `2 ^ 31`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NarrowField

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate (constE binE castE shrE Rw)

/-! ## 1. Instances -/

/-- KoalaBear, `p = 2 ^ 31 − 2 ^ 24 + 1` in 32-bit words. -/
def koalaBearField : WordField 32 2130706433 :=
  ⟨2130706432, 2130706431, 3187736576, 29, 33, 2164392967, 2766543874,
    4539909897235464193⟩

/-- Mersenne-31, `p = 2 ^ 31 − 1` in 32-bit words. -/
def mersenne31Field : WordField 32 2147483647 :=
  ⟨2147483646, 2147483649, 3221225468, 29, 33, 2147483649, 2684354559,
    13835058053134680063⟩

theorem koalaBearField_montOk : koalaBearField.montOk = true := by decide +kernel
theorem koalaBearField_barOk : koalaBearField.barOk = true := by decide +kernel
theorem koalaBearField_plantOk : koalaBearField.plantOk = true := by decide +kernel
theorem mersenne31Field_montOk : mersenne31Field.montOk = true := by decide +kernel
theorem mersenne31Field_barOk : mersenne31Field.barOk = true := by decide +kernel
theorem mersenne31Field_plantOk : mersenne31Field.plantOk = true := by decide +kernel

/-- BabyBear with input bound `p`, for chained Plantard multiplies. -/
def babyBearFieldP : WordField 32 2013265921 := { babyBearField with inMax := 2013265921 }

/-- KoalaBear with input bound `p`, for chained Plantard multiplies. -/
def koalaBearFieldP : WordField 32 2130706433 := { koalaBearField with inMax := 2130706433 }

theorem babyBearFieldP_plantOk : babyBearFieldP.plantOk = true := by decide +kernel
theorem koalaBearFieldP_plantOk : koalaBearFieldP.plantOk = true := by decide +kernel

/-! ## 2. The Mersenne fold multiply -/

/-- The fold multiply modulo `2 ^ k − 1`, products at `2 w` bits: `t = a · b`,
`r = (t mod 2 ^ k) + ⌊t / 2 ^ k⌋`, result `(r mod 2 ^ k) + ⌊r / 2 ^ k⌋`. -/
def foldBlk (w k : ℕ) : Com jasminDialect (C2 w) (.reg w) :=
  .var (castE w (2 * w) .here) <|
  .var (castE w (2 * w) (.there (.there .here))) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (constE (2 * w) (2 ^ k - 1)) <|
  .var (binE .and (2 * w) (.there .here) .here) <|
  .var (shrE (2 * w) k (.there (.there .here))) <|
  .var (binE .add (2 * w) (.there .here) .here) <|
  .var (binE .and (2 * w) .here (.there (.there (.there .here)))) <|
  .var (shrE (2 * w) k (.there .here)) <|
  .var (binE .add (2 * w) (.there .here) .here) <|
  .var (castE (2 * w) w .here) <|
  .ret .here

/-- The integer semantics of `foldBlk`. -/
def foldZ (w k : ℕ) (a b : ℤ) : ℤ :=
  andZ (andZ (a * b) (cW (2 * w) (2 ^ k - 1)) + a * b / 2 ^ k) (cW (2 * w) (2 ^ k - 1)) +
    (andZ (a * b) (cW (2 * w) (2 ^ k - 1)) + a * b / 2 ^ k) / 2 ^ k

theorem foldBlk_denoteZ (w k : ℕ) (a b : ℤ) :
    (foldBlk w k).denoteZ (.cons a (.cons b .nil)) = foldZ w k a b := rfl

/-- `2 ^ k` is `1` modulo `2 ^ k − 1`. -/
theorem two_pow_cast_mersenne (k : ℕ) : ((2 : ℤ) ^ k : ZMod (2 ^ k - 1)) = 1 := by
  have h := ZMod.natCast_self (2 ^ k - 1)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  push_cast [Nat.cast_sub h1] at h
  push_cast
  linear_combination h

/-- One fold `(t mod 2 ^ k) + ⌊t / 2 ^ k⌋` is congruent to `t` modulo `2 ^ k − 1`. -/
theorem fold_cast (k : ℕ) (t : ℤ) :
    ((t % 2 ^ k + t / 2 ^ k : ℤ) : ZMod (2 ^ k - 1)) = t := by
  have e : t = t / 2 ^ k * 2 ^ k + t % 2 ^ k := (Int.ediv_mul_add_emod t _).symm
  conv_rhs => rw [e]
  push_cast
  rw [show ((2 : ZMod (2 ^ k - 1)) ^ k) = 1 by exact_mod_cast two_pow_cast_mersenne k]
  ring

/-- **Fold.** The fold multiply of nonnegative operands is congruent to `a · b` modulo
`2 ^ k − 1`. -/
theorem foldZ_cast (w k : ℕ) (hk : 2 ^ k - 1 < 2 ^ (2 * w)) {a b : ℤ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) : ((foldZ w k a b : ℤ) : ZMod (2 ^ k - 1)) = a * b := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hR : (0 : ℤ) < 2 ^ k := by positivity
  have hr : 0 ≤ a * b % 2 ^ k + a * b / 2 ^ k :=
    add_nonneg (Int.emod_nonneg _ hR.ne') (Int.ediv_nonneg hab hR.le)
  unfold foldZ
  rw [cW_mask hk, andZ_mask hab, andZ_mask hr, fold_cast, fold_cast]
  push_cast
  ring

/-- The side condition of the fold block: the mask fits `2 w` bits, and the bounds check
from `[0, B]` to `[0, out]`. -/
def foldOk (w k B out : ℕ) : Bool :=
  decide (2 ^ k - 1 < 2 ^ (2 * w)) && boundsOk false (ivs2 w B) (foldBlk w k) (0, out)

/-- **The fold block.** On words representing `u`, `v` with bound `B`, the output
represents `u · v` with bound `out`. -/
theorem mulFold_rep {w k B out : ℕ} (h : foldOk w k B out = true) {x y : BitVec w}
    {u v : ZMod (2 ^ k - 1)} (hx : Rep (2 ^ k - 1) B x u) (hy : Rep (2 ^ k - 1) B y v) :
    Rep (2 ^ k - 1) out (run2 (foldBlk w k) x y) (u * v) := by
  simp only [foldOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, hb⟩ := h
  obtain ⟨e, hle⟩ := run2_eq_denoteZ hb x y hx.1 hy.1
  refine ⟨hle, ?_⟩
  rw [← hx.2, ← hy.2]
  rw [foldBlk_denoteZ] at e
  have := foldZ_cast w k h1 (Int.natCast_nonneg x.toNat) (Int.natCast_nonneg y.toNat)
  rw [← e] at this
  exact_mod_cast this

theorem mersenne31_foldOk : foldOk 32 31 2147483648 2147483648 = true := by decide +kernel

end CatCrypt.Crypto.SecureCompilation.VIR.NarrowField
