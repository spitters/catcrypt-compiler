/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.SplitIfs

/-!
# FIPS 204 rounding functions (Section 7.4)

The ML-DSA rounding, decomposition and hint algorithms over the integers:
`Power2Round` (Algorithm 35), `Decompose` (Algorithm 36), `HighBits` and
`LowBits` (Algorithms 37 and 38), `MakeHint` (Algorithm 39) and `UseHint`
(Algorithm 40), with their range properties and the hint round-trip identity.

The modulus is `q = 8380417` and the dropped-bit count is `d = 13`.
The two parameter sets use `gamma2 = (q-1)/88` and `gamma2 = (q-1)/32`;
`IsGamma2` names that pair, and every statement below about `gamma2` is
stated for it.

## Main definitions

* `modPm`: the centred remainder `r mod± m` in `(-m/2, m/2]`
* `power2Round`, `decompose`, `highBits`, `lowBits`, `makeHint`, `useHint`:
  Algorithms 35 to 40

## Main results

* `power2Round_spec`: `r = r1 * 2^13 + r0` with `-4096 < r0 ≤ 4096` and `0 ≤ r1 ≤ 1023`
* `decompose_spec`: `r1 * 2γ2 + r0 ≡ r (mod q)`, `0 ≤ r1 < (q-1)/(2γ2)`, `-γ2 ≤ r0 ≤ γ2`
* `decompose_eq`: `r = r1 * 2γ2 + r0`, or `r1 = 0` and `r = q + r0`
* `decompose_snd_neg`: `r0 = -γ2` only where `r1 = 0`
* `useHint_makeHint`: `useHint (makeHint z r) r = highBits ((r + z) mod q)` for `|z| ≤ γ2`

## References
* NIST FIPS 204 (2024), Section 7.4, Algorithms 35-40
* CRYSTALS-Dilithium specification v3.1, Lemma 1.1
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLDSA.Spec

/-! ## Parameters -/

/-- The ML-DSA modulus. -/
def q : ℤ := 8380417

/-- The number of bits dropped by `power2Round`. -/
def d : ℤ := 13

/-- `2 ^ d`, the `power2Round` scaling factor. -/
def twoPowD : ℤ := 8192

/-- `gamma2` for ML-DSA-44: `(q - 1) / 88`. -/
def gamma2_88 : ℤ := 95232

/-- `gamma2` for ML-DSA-65 and ML-DSA-87: `(q - 1) / 32`. -/
def gamma2_32 : ℤ := 261888

/-- The two `gamma2` values used by the ML-DSA parameter sets. -/
def IsGamma2 (γ2 : ℤ) : Prop := γ2 = gamma2_88 ∨ γ2 = gamma2_32

/-! ## Centred remainder -/

/-- `modPm x α` is the representative of `x` modulo `α` in `(-α/2, α/2]`,
for even `α`. -/
def modPm (x α : ℤ) : ℤ :=
  let r := x % α
  if r > α / 2 then r - α else r

/-! ## Rounding -/

/-- `Power2Round` (FIPS 204, Algorithm 35): splits `r mod q` into a high part
scaled by `2 ^ d` and a centred low part. -/
def power2Round (r : ℤ) : ℤ × ℤ :=
  let rp := r % q
  let r0 := modPm rp twoPowD
  ((rp - r0) / twoPowD, r0)

/-- `Decompose` (FIPS 204, Algorithm 36): splits `r mod q` into a high part
scaled by `2 * γ2` and a centred low part, with the high part wrapped to `0`
at the top of the range. -/
def decompose (γ2 r : ℤ) : ℤ × ℤ :=
  let rp := r % q
  let r0 := modPm rp (2 * γ2)
  if rp - r0 = q - 1 then (0, r0 - 1) else ((rp - r0) / (2 * γ2), r0)

/-- `HighBits` (FIPS 204, Algorithm 37). -/
def highBits (γ2 r : ℤ) : ℤ := (decompose γ2 r).1

/-- `LowBits` (FIPS 204, Algorithm 38). -/
def lowBits (γ2 r : ℤ) : ℤ := (decompose γ2 r).2

/-- `MakeHint` (FIPS 204, Algorithm 39): whether adding `z` changes the high
bits of `r`. -/
def makeHint (γ2 z r : ℤ) : Bool := decide (highBits γ2 r ≠ highBits γ2 (r + z))

/-- `UseHint` (FIPS 204, Algorithm 40): recovers the high bits of `r + z` from
the high bits of `r` and the hint bit. -/
def useHint (γ2 : ℤ) (h : Bool) (r : ℤ) : ℤ :=
  let m := (q - 1) / (2 * γ2)
  let r1 := (decompose γ2 r).1
  let r0 := (decompose γ2 r).2
  if h = true ∧ 0 < r0 then (r1 + 1) % m
  else if h = true then (r1 - 1) % m
  else r1

/-! ## Range properties -/

/-- The high part of `decompose` as a single conditional. -/
theorem decompose_fst_eq (γ2 r : ℤ) :
    (decompose γ2 r).1 =
      (if r % q - modPm (r % q) (2 * γ2) = q - 1 then 0
       else (r % q - modPm (r % q) (2 * γ2)) / (2 * γ2)) := by
  simp only [decompose]
  split <;> rfl

/-- `decompose` depends on its argument only modulo `q`. -/
theorem decompose_emod (γ2 r : ℤ) : decompose γ2 (r % q) = decompose γ2 r := by
  simp only [decompose, Int.emod_emod_of_dvd r (Int.dvd_refl q)]

/-- The low part of `decompose` as a single conditional. -/
theorem decompose_snd_eq (γ2 r : ℤ) :
    (decompose γ2 r).2 =
      (if r % q - modPm (r % q) (2 * γ2) = q - 1 then modPm (r % q) (2 * γ2) - 1
       else modPm (r % q) (2 * γ2)) := by
  simp only [decompose]
  split <;> rfl

/-- `Power2Round` reconstructs its argument, with the low part centred in
`(-2 ^ 12, 2 ^ 12]` and the high part in `[0, 1023]`. -/
theorem power2Round_spec {r : ℤ} (h0 : 0 ≤ r) (h1 : r < q) :
    r = (power2Round r).1 * twoPowD + (power2Round r).2 ∧
      -4096 < (power2Round r).2 ∧ (power2Round r).2 ≤ 4096 ∧
      0 ≤ (power2Round r).1 ∧ (power2Round r).1 ≤ 1023 := by
  simp only [power2Round, modPm, twoPowD, q] at *
  split_ifs <;> omega

/-- `Decompose` reconstructs its argument modulo `q`, with the high part in
`[0, (q-1)/(2*γ2))` and the low part in `[-γ2, γ2]`. -/
theorem decompose_spec {γ2 r : ℤ} (hγ : IsGamma2 γ2) (h0 : 0 ≤ r) (h1 : r < q) :
    ((decompose γ2 r).1 * (2 * γ2) + (decompose γ2 r).2) % q = r % q ∧
      0 ≤ (decompose γ2 r).1 ∧ (decompose γ2 r).1 < (q - 1) / (2 * γ2) ∧
      -γ2 ≤ (decompose γ2 r).2 ∧ (decompose γ2 r).2 ≤ γ2 := by
  rcases hγ with rfl | rfl <;>
    simp only [decompose_fst_eq, decompose_snd_eq, modPm, gamma2_88, gamma2_32, q] at * <;>
    split_ifs <;> omega

/-- `Decompose` reconstructs its argument exactly, except in the wrap case, where
the high part is `0` and the argument exceeds the reconstruction by `q`. -/
theorem decompose_eq {γ2 r : ℤ} (hγ : IsGamma2 γ2) (h0 : 0 ≤ r) (h1 : r < q) :
    r = (decompose γ2 r).1 * (2 * γ2) + (decompose γ2 r).2 ∨
      ((decompose γ2 r).1 = 0 ∧ r = q + (decompose γ2 r).2) := by
  rcases hγ with rfl | rfl <;>
    simp only [decompose_fst_eq, decompose_snd_eq, modPm, gamma2_88, gamma2_32, q] at * <;>
    split_ifs <;> omega

/-- The low part of `decompose` reaches `-γ2` only where the high part is `0`. -/
theorem decompose_snd_neg {γ2 r : ℤ} (hγ : IsGamma2 γ2) :
    -γ2 < (decompose γ2 r).2 ∨ (decompose γ2 r).1 = 0 := by
  rcases hγ with rfl | rfl <;>
    simp only [decompose_fst_eq, decompose_snd_eq, modPm, gamma2_88, gamma2_32, q] at * <;>
    split_ifs <;> omega

/-- The high part produced by `decompose` is below `(q-1)/(2*γ2)`. -/
theorem highBits_lt {γ2 r : ℤ} (hγ : IsGamma2 γ2) (h0 : 0 ≤ r) (h1 : r < q) :
    0 ≤ highBits γ2 r ∧ highBits γ2 r < (q - 1) / (2 * γ2) :=
  ⟨(decompose_spec hγ h0 h1).2.1, (decompose_spec hγ h0 h1).2.2.1⟩

/-- The low part produced by `decompose` lies in `[-γ2, γ2]`. -/
theorem lowBits_abs_le {γ2 r : ℤ} (hγ : IsGamma2 γ2) (h0 : 0 ≤ r) (h1 : r < q) :
    -γ2 ≤ lowBits γ2 r ∧ lowBits γ2 r ≤ γ2 := by
  have h := decompose_spec hγ h0 h1
  simp only [lowBits]
  omega

/-! ## Hints -/

/-- With the hint bit clear, `useHint` returns the high bits unchanged. -/
theorem useHint_false (γ2 r : ℤ) : useHint γ2 false r = highBits γ2 r := by
  simp [useHint, highBits]

/-- `useHint` lands in `[0, (q-1)/(2*γ2))`. -/
theorem useHint_range {γ2 : ℤ} (hγ : IsGamma2 γ2) {r : ℤ} (h0 : 0 ≤ r) (h1 : r < q)
    (h : Bool) :
    0 ≤ useHint γ2 h r ∧ useHint γ2 h r < (q - 1) / (2 * γ2) := by
  have hs := decompose_spec hγ h0 h1
  rcases hγ with rfl | rfl <;>
    simp only [useHint, gamma2_88, gamma2_32, q] at hs ⊢ <;>
    split_ifs <;> omega

/-- The hint round-trip (CRYSTALS-Dilithium specification v3.1, Lemma 1.1):
for `0 ≤ r < q` and `-γ2 ≤ z ≤ γ2`, `useHint` applied to the hint produced by
`makeHint` recovers the high bits of `r + z`. -/
theorem useHint_makeHint {γ2 z r : ℤ} (hγ : IsGamma2 γ2) (h0 : 0 ≤ r) (h1 : r < q)
    (hz0 : -γ2 ≤ z) (hz1 : z ≤ γ2) :
    useHint γ2 (makeHint γ2 z r) r = highBits γ2 ((r + z) % q) := by
  have hmk : makeHint γ2 z r =
      decide ((decompose γ2 r).1 ≠ (decompose γ2 ((r + z) % q)).1) := by
    unfold makeHint highBits
    rw [decompose_emod]
  have hs0 : 0 ≤ (r + z) % q := Int.emod_nonneg _ (by decide)
  have hs1 : (r + z) % q < q := Int.emod_lt_of_pos _ (by decide)
  have hzb : -8380417 < r + z ∧ r + z < 2 * 8380417 := by
    rcases hγ with rfl | rfl <;>
      simp only [gamma2_88, gamma2_32, q] at hz0 hz1 h1 ⊢ <;> omega
  have hq3 : (r + z) % q = r + z ∨ (r + z) % q = r + z - q ∨ (r + z) % q = r + z + q := by
    simp only [q]
    omega
  have her := decompose_eq hγ h0 h1
  have hes := decompose_eq hγ hs0 hs1
  obtain ⟨-, hA0, hA1, hb0, hb1⟩ := decompose_spec hγ h0 h1
  obtain ⟨-, hf0, hf1, hg0, hg1⟩ := decompose_spec hγ hs0 hs1
  have hnr := decompose_snd_neg (r := r) hγ
  have hns := decompose_snd_neg (r := (r + z) % q) hγ
  simp only [useHint, highBits, hmk, decide_eq_true_eq, ne_eq]
  rcases hγ with rfl | rfl <;>
    simp only [gamma2_88, gamma2_32, q] at * <;>
    split_ifs <;> omega

/-! ## Pinned values

Static checks pinning the two boundary cases of the definitions: the `decompose`
wrap-around at `q - 1` and the `power2Round` carry at `2 ^ 13 - 1`. -/

/-- `decompose` at the top of the range wraps the high part to `0`. -/
theorem decompose_top : decompose gamma2_88 (q - 1) = (0, -1) := by decide

/-- `power2Round` at `2 ^ 13 - 1` carries into the high part. -/
theorem power2Round_carry : power2Round 8191 = (1, -1) := by decide

end CatCrypt.Crypto.MLDSA.Spec
