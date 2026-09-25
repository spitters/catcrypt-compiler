/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.TileBackend.TileS16HighMul
public import CatCrypt.Crypto.SecureCompilation.TileBackend.TileS16HighMul
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Arithmetic correctness of the tile word specifications

The tile backend proves that its tile programs compute `TileModel.bbMulWord` and
`TileS16HighMul.montMulS16Spec` lane for lane. This module proves what those two
word functions compute.

## Main results

- `bbMulWord_toNat`: for `a, b < p = 2013265921`, the BabyBear Barrett multiply
  `bbMulWord a b` is `a · b mod p`.
- `montMulS16Spec_exact`: the signed 16-bit Montgomery multiply satisfies
  `r · 2^16 = a · b - U · 3329` for some `U ∈ [-2^15, 2^15)`.
- `montMulS16Spec_mul_R_modEq`: `r · 2^16 ≡ a · b (mod 3329)`, for all inputs.
- `montMulS16Spec_abs_lt`: `|r| < 3329` when `|a · b| < 3329 · 2^15`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.TileArithCorrect

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
open CatCrypt.Crypto.SecureCompilation.TileBackend.TileS16HighMul

/-! ## BabyBear Barrett multiply -/

/-- The Barrett quotient estimate `⌊⌊X / 2^30⌋ · μ / 2^32⌋` with `μ = 2290649223`
    undershoots `⌊X / p⌋` by at most one for `X ≤ (p - 1)^2`, so `X` minus the
    estimate times `p` lies in `[0, 2p)`. -/
theorem bbMulQuot_bounds (X : Nat) (hX : X ≤ 2013265920 * 2013265920) :
    X / 2 ^ 30 * 2290649223 / 2 ^ 32 * 2013265921 ≤ X ∧
    X < X / 2 ^ 30 * 2290649223 / 2 ^ 32 * 2013265921 + 2 * 2013265921 := by
  omega

/-- The branchless conditional subtract of `bbMulWord` (subtract `p`, add `p`
    back under the sign mask) maps `y < 2p` to `y mod p`. -/
theorem bbCondSub_toNat (y : BitVec 64) (hy : y.toNat < 2 * 2013265921) :
    (let o := y - BitVec.ofNat 64 2013265921
     let m := BitVec.ofNat 64 0 - (o >>> 63)
     let m := m &&& BitVec.ofNat 64 2013265921
     o + m).toNat = y.toNat % 2013265921 := by
  by_cases h : 2013265921 ≤ y.toNat
  · have ho : (y - BitVec.ofNat 64 2013265921).toNat = y.toNat - 2013265921 := by
      rw [BitVec.toNat_sub]; simp; omega
    have hs : (y - BitVec.ofNat 64 2013265921) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ho]; simp; omega
    simp only [hs]
    simp [ho]
    omega
  · have ho : (y - BitVec.ofNat 64 2013265921).toNat = 2 ^ 64 - 2013265921 + y.toNat := by
      rw [BitVec.toNat_sub]; simp; omega
    have hs : (y - BitVec.ofNat 64 2013265921) >>> 63 = 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ho]; simp; omega
    simp only [hs]
    have hm : BitVec.ofNat 64 0 - 1 = BitVec.allOnes 64 := by decide
    rw [hm, BitVec.allOnes_and, BitVec.toNat_add, ho]
    simp
    omega

/-- **The BabyBear Barrett word multiply is the field multiply.** For
    `a, b < p = 2013265921`, `(bbMulWord a b).toNat = a · b mod p`. -/
theorem bbMulWord_toNat (a b : BitVec 64) (ha : a.toNat < 2013265921)
    (hb : b.toNat < 2013265921) :
    (bbMulWord a b).toNat = a.toNat * b.toNat % 2013265921 := by
  have hX : a.toNat * b.toNat ≤ 2013265920 * 2013265920 :=
    Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨hlo, hhi⟩ := bbMulQuot_bounds _ hX
  generalize hXd : a.toNat * b.toNat = X at hX hlo hhi
  have hx : (a * b).toNat = X := by
    rw [BitVec.toNat_mul, hXd]; exact Nat.mod_eq_of_lt (by omega)
  have h1 : ((a * b) >>> 30).toNat = X / 2 ^ 30 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx]
  have h2 : ((a * b) >>> 30 * BitVec.ofNat 64 2290649223).toNat
      = X / 2 ^ 30 * 2290649223 := by
    rw [BitVec.toNat_mul, h1]; simp; omega
  have h3 : (((a * b) >>> 30 * BitVec.ofNat 64 2290649223) >>> 32).toNat
      = X / 2 ^ 30 * 2290649223 / 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h2]
  have h4 : (((a * b) >>> 30 * BitVec.ofNat 64 2290649223) >>> 32
      * BitVec.ofNat 64 2013265921).toNat
      = X / 2 ^ 30 * 2290649223 / 2 ^ 32 * 2013265921 := by
    rw [BitVec.toNat_mul, h3]; simp; omega
  have h5 : (a * b - ((a * b) >>> 30 * BitVec.ofNat 64 2290649223) >>> 32
      * BitVec.ofNat 64 2013265921).toNat
      = X - X / 2 ^ 30 * 2290649223 / 2 ^ 32 * 2013265921 := by
    rw [BitVec.toNat_sub, h4, hx]; omega
  have hr := bbCondSub_toNat (a * b - ((a * b) >>> 30 * BitVec.ofNat 64 2290649223) >>> 32
      * BitVec.ofNat 64 2013265921) (by rw [h5]; omega)
  simp only [bbMulWord]
  rw [hr, h5]
  omega

/-! ## ML-KEM signed 16-bit Montgomery multiply -/

/-- Truncating a 32-bit vector to 16 bits takes its signed value to the balanced
    residue modulo `2^16`. -/
theorem toInt_setWidth_32_16 (x : BitVec 32) :
    (x.setWidth 16).toInt = x.toInt.bmod (2 ^ 16) := by
  rw [BitVec.toInt_setWidth, BitVec.toInt_eq_toNat_bmod x, Int.bmod_bmod_of_dvd]
  norm_num

/-- **Exact form of the signed Montgomery multiply.** For all `a b : BitVec 16`,
    `montMulS16Spec a b = (a·b - U·3329) / 2^16` exactly, where
    `U ∈ [-2^15, 2^15)` is the balanced residue of `a·b·62209` modulo `2^16`. -/
theorem montMulS16Spec_exact (a b : BitVec 16) :
    ∃ U : Int, -2 ^ 15 ≤ U ∧ U < 2 ^ 15 ∧
      (montMulS16Spec a b).toInt * 2 ^ 16 = a.toInt * b.toInt - U * 3329 := by
  have ha1 := BitVec.le_toInt a
  have ha2 := @BitVec.toInt_lt 16 a
  have hb1 := BitVec.le_toInt b
  have hb2 := @BitVec.toInt_lt 16 b
  norm_num at ha1 ha2 hb1 hb2
  have hAB1 : -(2 ^ 30) ≤ a.toInt * b.toInt := by nlinarith
  have hAB2 : a.toInt * b.toInt ≤ 2 ^ 30 := by nlinarith
  have ht : (a.signExtend 32 * b.signExtend 32).toInt = a.toInt * b.toInt := by
    rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by norm_num),
      BitVec.toInt_signExtend_of_le (by norm_num)]
    apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> omega
  have h62 : (62209 : BitVec 32).toInt = 62209 := by decide
  have h33 : (3329 : BitVec 32).toInt = 3329 := by decide
  simp only [montMulS16Spec]
  generalize a.signExtend 32 * b.signExtend 32 = t at ht
  generalize hT : a.toInt * b.toInt = T at ht hAB1 hAB2
  have hU : ((t * 62209).setWidth 16).toInt = (T * 62209).bmod (2 ^ 16) := by
    rw [toInt_setWidth_32_16, BitVec.toInt_mul, ht, Int.bmod_bmod_of_dvd (by norm_num), h62]
  have hU1 := @Int.le_bmod (T * 62209) (2 ^ 16) (by norm_num)
  have hU2 := @Int.bmod_lt (T * 62209) (2 ^ 16) (by norm_num)
  have hUe := @Int.bmod_eq_self_sub_mul_bdiv (T * 62209) (2 ^ 16)
  generalize (T * 62209).bmod (2 ^ 16) = U at hU hU1 hU2 hUe
  generalize (T * 62209).bdiv (2 ^ 16) = k at hUe
  norm_num at hU1 hU2 hUe
  refine ⟨U, by omega, by omega, ?_⟩
  have hsub : (t - (BitVec.truncate 16 (t * 62209)).signExtend 32 * 3329).toInt
      = T - U * 3329 := by
    rw [BitVec.toInt_sub, BitVec.toInt_mul, BitVec.truncate_eq_setWidth,
      BitVec.toInt_signExtend_of_le (by norm_num), hU, ht, h33,
      Int.bmod_eq_of_le_mul_two (x := U * 3329) (by push_cast; omega) (by push_cast; omega),
      Int.bmod_eq_of_le_mul_two (by push_cast; omega) (by push_cast; omega)]
  have hS : T - U * 3329 = 65536 * (3329 * k - 3160 * T) := by rw [hUe]; ring
  generalize 3329 * k - 3160 * T = W at hS
  rw [BitVec.truncate_eq_setWidth, toInt_setWidth_32_16, BitVec.toInt_sshiftRight, hsub,
    Int.shiftRight_eq_div_pow, hS]
  norm_num
  rw [Int.bmod_eq_of_le_mul_two (by push_cast; omega) (by push_cast; omega)]
  ring

/-- **Montgomery congruence.** For all `a b : BitVec 16`,
    `montMulS16Spec a b · 2^16 ≡ a · b (mod 3329)`. -/
theorem montMulS16Spec_mul_R_modEq (a b : BitVec 16) :
    (montMulS16Spec a b).toInt * 2 ^ 16 ≡ a.toInt * b.toInt [ZMOD 3329] := by
  obtain ⟨U, -, -, h⟩ := montMulS16Spec_exact a b
  rw [h]
  exact Int.modEq_iff_dvd.mpr ⟨U, by ring⟩

/-- **Montgomery range bound.** If `|a · b| < 3329 · 2^15` then
    `|montMulS16Spec a b| < 3329`. -/
theorem montMulS16Spec_abs_lt (a b : BitVec 16)
    (h : |a.toInt * b.toInt| < 3329 * 2 ^ 15) :
    |(montMulS16Spec a b).toInt| < 3329 := by
  obtain ⟨U, hU1, hU2, he⟩ := montMulS16Spec_exact a b
  rw [abs_lt] at h ⊢
  omega

end CatCrypt.Crypto.SecureCompilation.TileBackend.TileArithCorrect

end
