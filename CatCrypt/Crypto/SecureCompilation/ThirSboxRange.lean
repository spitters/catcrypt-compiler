/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ThirToComFront

/-!
# Range conditions for the width-64 BabyBear REDC and the Poseidon2 S-box

`ThirToComFront` defines the width-64 lazy Montgomery REDC `montMulSpec64` and the
S-box `sboxSpec64 x = montmul(montmul(montmul(montmul(x,x),x), ·), x)`, whose
programs denote these functions. Both compute in wrapping 64-bit arithmetic. This
module states when the arithmetic does not wrap and what the results are then.

## Main results

* `montMulSpec64_exact`: if `a·b + (2^32 − 1)·p < 2^64`, then
  `montMulSpec64 a b · 2^32 = a·b + k·p` for some `k < 2^32`; the REDC is an exact
  division.
* `montMulSpec64_step`: under bounds `a ≤ A`, `b ≤ B` with
  `A·B + (2^32 − 1)·p < 2^64`, the result satisfies
  `montMulSpec64 a b · 2^32 ≤ A·B + (2^32 − 1)·p` and
  `montMulSpec64 a b · 2^32 = a·b` in `ZMod p`.
* `sboxSpec64_modEq`: for `x ≤ 1756563332`, every step satisfies the no-wrap
  condition and `sboxSpec64 x · 2^(32·6) ≡ x^7 (mod p)`. With `x = x̃·R` for
  `R = 2^32`, the output is congruent to `x̃^7·R`, the Montgomery representative of
  `x̃^7`.

The range condition is needed: for `x = 2012966596 < p` the sum `t + m·p` of the
third step exceeds `2^64` and the congruence fails.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ThirSboxRange

open CatCrypt.Crypto.SecureCompilation.ThirToComFront

/-- The REDC low-word cancellation for the BabyBear constants:
    `T + ((T mod 2^32)·minv mod 2^32)·p ≡ 0 (mod 2^32)`. -/
theorem redc_low32_cancel (T : ℕ) :
    (T + ((T % 2 ^ 32) * babyBearMInv % 2 ^ 32) * babyBearP) % 2 ^ 32 = 0 := by
  have hp : babyBearP = 0x78000001 := rfl
  have hm : babyBearMInv = 0x77ffffff := rfl
  rw [hp, hm]
  omega

/-- **Exact REDC.** If `a·b + (2^32 − 1)·p < 2^64`, no step of `montMulSpec64 a b`
    wraps, and `montMulSpec64 a b · 2^32 = a·b + k·p` for the REDC multiplier
    `k < 2^32`. -/
theorem montMulSpec64_exact (a b : BitVec 64)
    (h : a.toNat * b.toNat + (2 ^ 32 - 1) * babyBearP < 2 ^ 64) :
    ∃ k < 2 ^ 32,
      (montMulSpec64 a b).toNat * 2 ^ 32 = a.toNat * b.toNat + k * babyBearP := by
  have hp : babyBearP = 0x78000001 := rfl
  have hprod : (a * b).toNat = a.toNat * b.toNat := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
  have hmask : (BitVec.ofNat 64 0xffffffff).toNat = 2 ^ 32 - 1 := by decide
  have hminv : (BitVec.ofNat 64 babyBearMInv).toNat = babyBearMInv := by decide
  have hpv : (BitVec.ofNat 64 babyBearP).toNat = babyBearP := by decide
  unfold montMulSpec64
  simp only
  set t := a * b with ht
  set m := ((t &&& BitVec.ofNat 64 0xffffffff) * BitVec.ofNat 64 babyBearMInv)
      &&& BitVec.ofNat 64 0xffffffff with hmdef
  have hm : m.toNat = ((t.toNat % 2 ^ 32) * babyBearMInv) % 2 ^ 32 := by
    rw [hmdef, BitVec.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_mul,
      BitVec.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod, hminv,
      Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]
  have hmlt : m.toNat < 2 ^ 32 := by rw [hm]; exact Nat.mod_lt _ (by norm_num)
  have hmle : m.toNat ≤ 2 ^ 32 - 1 := by omega
  have hmp_le : m.toNat * babyBearP ≤ (2 ^ 32 - 1) * babyBearP := Nat.mul_le_mul_right _ hmle
  have hmp : (m * BitVec.ofNat 64 babyBearP).toNat = m.toNat * babyBearP := by
    rw [BitVec.toNat_mul, hpv]; exact Nat.mod_eq_of_lt (by omega)
  have hadd : (t + m * BitVec.ofNat 64 babyBearP).toNat = t.toNat + m.toNat * babyBearP := by
    rw [BitVec.toNat_add, hmp]; exact Nat.mod_eq_of_lt (by rw [ht, hprod]; omega)
  have hcancel := redc_low32_cancel t.toNat
  rw [← hm] at hcancel
  refine ⟨m.toNat, hmlt, ?_⟩
  rw [BitVec.toNat_ushiftRight, hadd, Nat.shiftRight_eq_div_pow,
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hcancel), ht, hprod]

/-- **One REDC step under operand bounds.** If `a ≤ A`, `b ≤ B` and
    `A·B + (2^32 − 1)·p < 2^64`, then `montMulSpec64 a b · 2^32` is at most
    `A·B + (2^32 − 1)·p` and equals `a·b` in `ZMod p`. -/
theorem montMulSpec64_step (a b : BitVec 64) (A B : ℕ) (ha : a.toNat ≤ A) (hb : b.toNat ≤ B)
    (h : A * B + (2 ^ 32 - 1) * babyBearP < 2 ^ 64) :
    (montMulSpec64 a b).toNat * 2 ^ 32 ≤ A * B + (2 ^ 32 - 1) * babyBearP ∧
    ((montMulSpec64 a b).toNat * 2 ^ 32 : ZMod babyBearP)
      = (a.toNat : ZMod babyBearP) * b.toNat := by
  have hab : a.toNat * b.toNat ≤ A * B := Nat.mul_le_mul ha hb
  obtain ⟨k, hk, he⟩ := montMulSpec64_exact a b (by omega)
  have hkp : k * babyBearP ≤ (2 ^ 32 - 1) * babyBearP := Nat.mul_le_mul_right _ (by omega)
  refine ⟨by omega, ?_⟩
  have := congrArg (fun n : ℕ => (n : ZMod babyBearP)) he
  simp only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self, mul_zero, add_zero,
    Nat.cast_pow, Nat.cast_ofNat] at this
  exact this

/-- The S-box congruence in `ZMod p`: for `x ≤ 1756563332`,
    `sboxSpec64 x · (2^32)^6 = x^7`. The step bounds are
    `x2 ≤ 2731668303`, `x3 ≤ 3130468461`, `x6 ≤ 2^32 − 1`. -/
theorem sboxSpec64_congr (x : BitVec 64) (hx : x.toNat ≤ 1756563332) :
    ((sboxSpec64 x).toNat * 2 ^ (32 * 6) : ZMod babyBearP) = (x.toNat : ZMod babyBearP) ^ 7 := by
  have hp : babyBearP = 0x78000001 := rfl
  unfold sboxSpec64
  simp only
  obtain ⟨b2, e2⟩ := montMulSpec64_step x x 1756563332 1756563332 hx hx (by rw [hp]; norm_num)
  have hx2 : (montMulSpec64 x x).toNat ≤ 2731668303 := by rw [hp] at b2; omega
  obtain ⟨b3, e3⟩ := montMulSpec64_step (montMulSpec64 x x) x 2731668303 1756563332 hx2 hx
    (by rw [hp]; norm_num)
  have hx3 : (montMulSpec64 (montMulSpec64 x x) x).toNat ≤ 3130468461 := by rw [hp] at b3; omega
  obtain ⟨b6, e6⟩ := montMulSpec64_step _ _ 3130468461 3130468461 hx3 hx3 (by rw [hp]; norm_num)
  have hx6 : (montMulSpec64 (montMulSpec64 (montMulSpec64 x x) x)
      (montMulSpec64 (montMulSpec64 x x) x)).toNat ≤ 4294967295 := by rw [hp] at b6; omega
  obtain ⟨-, e7⟩ := montMulSpec64_step _ x 4294967295 1756563332 hx6 hx (by rw [hp]; norm_num)
  generalize ((montMulSpec64 (montMulSpec64 (montMulSpec64 (montMulSpec64 x x) x)
    (montMulSpec64 (montMulSpec64 x x) x)) x).toNat : ZMod babyBearP) = y7 at *
  generalize ((montMulSpec64 (montMulSpec64 (montMulSpec64 x x) x)
    (montMulSpec64 (montMulSpec64 x x) x)).toNat : ZMod babyBearP) = y6 at *
  generalize ((montMulSpec64 (montMulSpec64 x x) x).toNat : ZMod babyBearP) = y3 at *
  generalize ((montMulSpec64 x x).toNat : ZMod babyBearP) = y2 at *
  generalize (x.toNat : ZMod babyBearP) = a at *
  linear_combination (2 ^ 32 : ZMod babyBearP) ^ 5 * e7 + a * (2 ^ 32) ^ 4 * e6
    + a * (2 ^ 32) ^ 2 * (y3 * 2 ^ 32 + y2 * a) * e3 + a ^ 3 * (y2 * 2 ^ 32 + a ^ 2) * e2

/-- **S-box congruence.** For `x ≤ 1756563332`,
    `sboxSpec64 x · 2^(32·6) ≡ x^7 (mod p)`. -/
theorem sboxSpec64_modEq (x : BitVec 64) (hx : x.toNat ≤ 1756563332) :
    (sboxSpec64 x).toNat * 2 ^ (32 * 6) ≡ x.toNat ^ 7 [MOD babyBearP] := by
  have h := sboxSpec64_congr x hx
  rw [← (ZMod.natCast_eq_natCast_iff _ _ _), Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_ofNat]
  exact h

end CatCrypt.Crypto.SecureCompilation.ThirSboxRange
