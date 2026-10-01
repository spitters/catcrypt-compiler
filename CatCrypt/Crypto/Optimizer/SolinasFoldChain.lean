/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.ModReduceSelect


@[expose] public section
set_option autoImplicit false

/-!
# Four Solinas folds and one conditional subtract

`ModReduceSelect.solinasReduce` composes two `solinasFold` applications with one
conditional subtract, and `solinasReduce_eq_mod` proves that composition exact
under `SolinasOK`. A generator that emits **four** folds needs its own magnitude
chain: the two-fold bound stops at `< 2 · p`, while a four-fold chain lands the
value below `2 ^ k` itself, which is what a generator whose trial subtract reads
only `k` bits of the fold result requires.

The chain over a double-width product `A · B` with `A, B < 2 ^ k`:

| value | bound | from |
|---|---|---|
| `V₀ = A · B` | `< 2 ^ k · 2 ^ k` | the operands |
| `V₁` | `< 2 ^ k · (c + 1)` | `solinasFold_lt` at `M = 2 ^ k` |
| `V₂` | `< 2 ^ k · 2` | `solinasFold_lt` at `M = c + 1`, then `(c+1)·c + 2^k < 2^(k+1)` |
| `V₃` | `< 2 ^ k + 2 · c` | `solinasFold_lt` at `M = 2` |
| `V₄` | `< 2 ^ k` | `solinasFold_lt_of_near` |

The last step is not an instance of `solinasFold_lt`: at `M = 2` that lemma only
gives `V₄ < 2 · c + 2 ^ k`. It is a case split on the single top bit of `V₃` —
either `V₃ < 2 ^ k` and the fold is the identity, or `V₃ - 2 ^ k < 2 · c` and the
fold yields `c + (V₃ - 2 ^ k) < 3 · c`.

## Main results

* `solinasFold_lt_of_near` — a fold of a value below `2 ^ k + 2 · c` lands below
  `2 ^ k`, under `3 · c < 2 ^ k`.
* `fourFold_lt` — four folds of a product of two values below `2 ^ k` land below
  `2 ^ k`.
* `fourFold_mod` — four folds preserve the residue mod `p`.
* `solinasSelect` — the branch-free select after a trial subtract of `p`: from
  the borrow balance `D + p = V + 2 ^ k · b` with `V, D < 2 ^ k` and `b ≤ 1`, the
  selected value is the canonical residue of `V`.
* `secpFourFold_lt`, `secpFourFold_mod`, `secpSelect` — the three at
  `solinasParamsSecp256k1`.
-/

namespace CatCrypt.Crypto.Optimizer.SolinasFoldChain

open CatCrypt.Crypto.Optimizer.ModReduceSelect

/-! ## 1. The fourth fold -/

/-- A fold of a value already within `2 · c` of the radix lands below the radix.
    The case split is on the single top bit the value can carry. -/
theorem solinasFold_lt_of_near (P : SolinasPrime) (h3 : 3 * P.c < 2 ^ P.k) {v : Nat}
    (hv : v < 2 ^ P.k + 2 * P.c) : solinasFold P v < 2 ^ P.k := by
  have hp : 0 < 2 ^ P.k := Nat.two_pow_pos P.k
  have hr : v % 2 ^ P.k < 2 ^ P.k := Nat.mod_lt _ hp
  have hdm : v % 2 ^ P.k + 2 ^ P.k * (v / 2 ^ P.k) = v := Nat.mod_add_div v (2 ^ P.k)
  have hd2 : v / 2 ^ P.k < 2 := by
    rw [Nat.div_lt_iff_lt_mul hp]
    omega
  simp only [solinasFold]
  -- `omega` treats `v / 2 ^ P.k` as opaque (the divisor is a symbolic power), so
  -- name the quotient before splitting on it.
  obtain ⟨q, hq⟩ : ∃ q, v / 2 ^ P.k = q := ⟨_, rfl⟩
  rw [hq] at hdm ⊢
  rw [hq] at hd2
  -- `q` is now a plain variable, so `omega` can split it; it could not split
  -- `v / 2 ^ P.k`, whose divisor is a symbolic power.
  have hq2 : q = 0 ∨ q = 1 := by omega
  rcases hq2 with rfl | rfl <;> omega

/-! ## 2. The four-fold magnitude chain -/

/-- **Four folds of a double-width product land below the radix.** `hcc` is the
    small-`c` regime that lets the second fold reach `2 ^ (k+1)`, `h3` the one
    that lets the fourth fold reach `2 ^ k`. -/
theorem fourFold_lt (P : SolinasPrime)
    (hcc : (P.c + 1) * P.c + 2 ^ P.k < 2 ^ P.k * 2)
    (h3 : 3 * P.c < 2 ^ P.k) {A B : Nat} (hA : A < 2 ^ P.k) (hB : B < 2 ^ P.k) :
    solinasFold P (solinasFold P (solinasFold P (solinasFold P (A * B)))) < 2 ^ P.k := by
  have hp : 0 < 2 ^ P.k := Nat.two_pow_pos P.k
  have h0 : A * B < 2 ^ P.k * 2 ^ P.k :=
    lt_of_le_of_lt (Nat.mul_le_mul (le_refl A) (le_of_lt hB))
      (mul_lt_mul_of_pos_right hA hp)
  have h1 : solinasFold P (A * B) < 2 ^ P.k * (P.c + 1) := by
    have hx := solinasFold_lt P h0
    calc solinasFold P (A * B) < 2 ^ P.k * P.c + 2 ^ P.k := hx
      _ = 2 ^ P.k * (P.c + 1) := by ring
  have h2 : solinasFold P (solinasFold P (A * B)) < 2 ^ P.k * 2 :=
    lt_trans (solinasFold_lt P h1) hcc
  have h3' : solinasFold P (solinasFold P (solinasFold P (A * B))) < 2 ^ P.k + 2 * P.c := by
    have hx := solinasFold_lt P h2
    omega
  exact solinasFold_lt_of_near P h3 h3'

/-- **Four folds preserve the residue.** -/
theorem fourFold_mod (P : SolinasPrime) (hc : P.c ≤ 2 ^ P.k) (v : Nat) :
    solinasFold P (solinasFold P (solinasFold P (solinasFold P v))) % P.modulus
      = v % P.modulus := by
  rw [solinasFold_mod P hc, solinasFold_mod P hc, solinasFold_mod P hc,
    solinasFold_mod P hc]

/-! ## 3. The trial subtract and the branch-free select -/

/-- **The conditional subtract canonicalises a value already below the radix.**
    `hbal` is the borrow balance a ripple subtract of `p` leaves: the difference
    limbs `D` plus `p` equal the minuend `V` plus `2 ^ k` times the outgoing
    borrow `b`, where `b = 1` says `V < p`. Selecting `V` at `b = 1` and `D` at
    `b = 0` gives the canonical residue of `V`. -/
theorem solinasSelect (P : SolinasPrime) (h2c : 2 * P.c < 2 ^ P.k) {V D b R : Nat}
    (hV : V < 2 ^ P.k) (hD : D < 2 ^ P.k) (hb : b ≤ 1)
    (hbal : D + P.modulus = V + 2 ^ P.k * b)
    (h1 : b = 1 → R = V) (h0 : b = 0 → R = D) :
    R < P.modulus ∧ R % P.modulus = V % P.modulus := by
  have hmod : P.modulus = 2 ^ P.k - P.c := rfl
  rcases (by omega : b = 0 ∨ b = 1) with hb0 | hb1
  · subst hb0
    rw [h0 rfl]
    have hle : P.modulus ≤ V := by omega
    have hDv : D = V - P.modulus := by omega
    have hlt : D < P.modulus := by omega
    refine ⟨hlt, ?_⟩
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_sub_mod hle, ← hDv, Nat.mod_eq_of_lt hlt]
  · subst hb1
    rw [h1 rfl]
    have hlt : V < P.modulus := by omega
    exact ⟨hlt, rfl⟩

/-! ## 4. The chain at secp256k1 -/

theorem secpCC :
    (solinasParamsSecp256k1.c + 1) * solinasParamsSecp256k1.c
      + 2 ^ solinasParamsSecp256k1.k < 2 ^ solinasParamsSecp256k1.k * 2 := by
  show (2 ^ 32 + 977 + 1) * (2 ^ 32 + 977) + 2 ^ 256 < 2 ^ 256 * 2
  norm_num

theorem secp3C : 3 * solinasParamsSecp256k1.c < 2 ^ solinasParamsSecp256k1.k := by
  show 3 * (2 ^ 32 + 977) < 2 ^ 256
  norm_num

theorem secp2C : 2 * solinasParamsSecp256k1.c < 2 ^ solinasParamsSecp256k1.k := by
  show 2 * (2 ^ 32 + 977) < 2 ^ 256
  norm_num

theorem secpCle : solinasParamsSecp256k1.c ≤ 2 ^ solinasParamsSecp256k1.k := by
  show (2 ^ 32 + 977 : Nat) ≤ 2 ^ 256
  norm_num

/-- **The secp256k1 four-fold chain lands below `2 ^ 256`.** -/
theorem secpFourFold_lt {A B : Nat} (hA : A < 2 ^ 256) (hB : B < 2 ^ 256) :
    solinasFold solinasParamsSecp256k1
        (solinasFold solinasParamsSecp256k1
          (solinasFold solinasParamsSecp256k1
            (solinasFold solinasParamsSecp256k1 (A * B)))) < 2 ^ 256 :=
  fourFold_lt solinasParamsSecp256k1 secpCC secp3C hA hB

/-- **The secp256k1 four-fold chain preserves the residue.** -/
theorem secpFourFold_mod (v : Nat) :
    solinasFold solinasParamsSecp256k1
        (solinasFold solinasParamsSecp256k1
          (solinasFold solinasParamsSecp256k1
            (solinasFold solinasParamsSecp256k1 v))) % solinasParamsSecp256k1.modulus
      = v % solinasParamsSecp256k1.modulus :=
  fourFold_mod solinasParamsSecp256k1 secpCle v

/-- **The secp256k1 conditional subtract and select.** -/
theorem secpSelect {V D b R : Nat} (hV : V < 2 ^ 256) (hD : D < 2 ^ 256) (hb : b ≤ 1)
    (hbal : D + solinasParamsSecp256k1.modulus = V + 2 ^ 256 * b)
    (h1 : b = 1 → R = V) (h0 : b = 0 → R = D) :
    R < solinasParamsSecp256k1.modulus
      ∧ R % solinasParamsSecp256k1.modulus = V % solinasParamsSecp256k1.modulus :=
  solinasSelect solinasParamsSecp256k1 secp2C hV hD hb hbal h1 h0

end CatCrypt.Crypto.Optimizer.SolinasFoldChain
