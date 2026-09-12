/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Bls377FinalExp

/-!
# Algebraic correctness of the BLS12-377 final-exponentiation schedule

The concrete schedule `Bls377FinalExp.finalExp377 ξ₂ ξ₆` is the composition of the
easy part `f ↦ m · Frob²(m)` (with `m = conj12 f · inv12 f`) and the hard part
`f ↦ f ^ hardExp377` with `hardExp377 = (q⁴ − q² + 1)/r`.  This module reduces the
schedule to the Tate final-exponent power map `f ↦ f ^ ((q¹² − 1)/r)` by exponent
arithmetic over the cyclotomic factorisation of the degree-12 exponent.

## The cyclotomic exponent factorisation (proved)

`cyclotomic_deg12_factor` : for every `q ≥ 1`,

    (q⁶ − 1)·(q² + 1)·(q⁴ − q² + 1) = q¹² − 1

proved symbolically over `ℤ` — `(q²+1)(q⁴−q²+1) = q⁶+1` (sum of cubes) and
`(q⁶−1)(q⁶+1) = q¹²−1` — then transferred to `ℕ` with the non-underflow bounds.
`bls377_cyclotomic_factor` instantiates it at `q = bls377Q`, the `1 ≤ q` bound
coming from `Fact (Nat.Prime bls377Q)`.

## The schedule reduction (proved from three hypotheses)

`finalExp377_eq_powMap` : under

* `hFrob` : `conj12 f = f ^ (q⁶)` — the cyclotomic conjugation is the `p⁶`-power
  Frobenius on `Fp12_377` (see the remaining sub-lemma below);
* `hInv`  : `f · inv12 ξ₂ ξ₆ f = 1` — `f` is a unit with inverse `inv12 f`
  (the `Fp12_377` field cancellation `mul_inv12` for `f` with nonzero norm);
* `hRdvd` : `r ∣ (q⁴ − q² + 1)` — `r` divides `Φ₁₂(q)`, so the hard-part Nat
  division composes with the outer factors,

the schedule equals the power map:

    finalExp377 ξ₂ ξ₆ f = f ^ ((q¹² − 1)/r).

The easy part contributes `m = f^(q⁶)·f⁻¹` raised to `q²+1`, the hard part raises
to `hardExp377`, and `npow_mul_inv_pow` collapses `(f^(q⁶)·f⁻¹)^k` to
`f^((q⁶−1)·k)`; the outer exponent then equals `(q¹²−1)/r` by the factorisation.

## Remaining sub-lemma

`hFrob` — `Fp12_377.conj12 f = f ^ (bls377Q ^ 6)` — is not derived here.  `conj12`
is defined structurally as `⟨c0, c1⟩ ↦ ⟨c0, −c1⟩`; identifying it with the
`q⁶`-power map is the Frobenius characterisation on the `Fp12_377` tower over
`F_q`, resting on the base field having characteristic `q`.  It is taken as an
explicit hypothesis and is the one piece left to close for an unconditional
`finalExp377 = (·)^((q¹²−1)/r)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Bls377FinalExpCorrect

open CatCrypt.Crypto.SecureCompilation.RelationalFront
open CatCrypt.Crypto.SecureCompilation.VIR.Bls377FinalExp

/-! ## 1. The degree-12 cyclotomic exponent factorisation -/

/-- **The degree-12 cyclotomic factorisation of `qⁿ − 1`.**  For `q ≥ 1`,
    `(q⁶ − 1)(q² + 1)(q⁴ − q² + 1) = q¹² − 1`.  Proved over `ℤ`
    (`(q²+1)(q⁴−q²+1) = q⁶+1`, then `(q⁶−1)(q⁶+1) = q¹²−1`) and cast to `ℕ` with
    the non-underflow bounds `1 ≤ q⁶`, `q² ≤ q⁴`, `1 ≤ q¹²`. -/
theorem cyclotomic_deg12_factor {q : ℕ} (hq : 1 ≤ q) :
    (q ^ 6 - 1) * (q ^ 2 + 1) * (q ^ 4 - q ^ 2 + 1) = q ^ 12 - 1 := by
  have h1 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h12]
  ring

/-- **The cyclotomic factorisation at `q = bls377Q`.**
    `(q⁶ − 1)(q² + 1)(q⁴ − q² + 1) = q¹² − 1` for the BLS12-377 base prime; the
    `1 ≤ q` bound comes from `Fact (Nat.Prime bls377Q)`. -/
theorem bls377_cyclotomic_factor [Fact (Nat.Prime bls377Q)] :
    (bls377Q ^ 6 - 1) * (bls377Q ^ 2 + 1) * (bls377Q ^ 4 - bls377Q ^ 2 + 1)
      = bls377Q ^ 12 - 1 :=
  cyclotomic_deg12_factor (Fact.out : Nat.Prime bls377Q).one_lt.le

/-! ## 2. A commutative-monoid collapse for `(xⁿ · x⁻¹)ᵏ` -/

/-- **`(xⁿ · fi)ᵏ = x^((n−1)·k)` when `fi` inverts `x`.**  In a commutative monoid,
    if `x · fi = 1` and `1 ≤ n`, then `xⁿ · fi` is `x^(n−1)` and its `k`-th power is
    `x^((n−1)·k)`.  Proved by right-cancelling the unit `xᵏ`:
    `(xⁿ·fi)ᵏ · xᵏ = x^(n·k) = x^((n−1)·k) · xᵏ`. -/
theorem npow_mul_inv_pow {M : Type*} [CommMonoid M] {x fi : M} (hfi : x * fi = 1)
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (x ^ n * fi) ^ k = x ^ ((n - 1) * k) := by
  have hfix : fi * x = 1 := by rw [mul_comm]; exact hfi
  have hu : IsUnit (x ^ k) :=
    IsUnit.of_mul_eq_one (fi ^ k) (by rw [← mul_pow, hfi, one_pow])
  have hnk : (n - 1) * k + k = n * k := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [Nat.succ_sub_one, Nat.succ_mul]
  have hL : (x ^ n * fi) ^ k * x ^ k = x ^ (n * k) := by
    rw [mul_pow, ← pow_mul, mul_assoc, ← mul_pow, hfix, one_pow, mul_one]
  have hR : x ^ ((n - 1) * k) * x ^ k = x ^ (n * k) := by
    rw [← pow_add, hnk]
  exact (IsUnit.mul_left_inj hu).mp (hL.trans hR.symm)

/-! ## 3. The schedule equals the Tate final-exponent power map -/

/-- **The concrete BLS12-377 final-exponentiation schedule equals the power map
    `f ↦ f ^ ((q¹² − 1)/r)`.**  Under `hFrob` (`conj12 f = f^(q⁶)`, the `p⁶`-power
    Frobenius), `hInv` (`f · inv12 f = 1`, `f` a unit), and `hRdvd`
    (`r ∣ q⁴ − q² + 1`), the schedule `finalExp377 ξ₂ ξ₆ f` — easy part
    `m · Frob²(m)` with `m = conj12 f · inv12 f`, then the hard part
    `(·)^hardExp377` — collapses to `f ^ ((bls377Q¹² − 1)/bls377R)`.  The exponent
    `(q⁶ − 1)·(q² + 1)·hardExp377` equals `(q¹² − 1)/r` by
    `bls377_cyclotomic_factor` and `hRdvd`. -/
theorem finalExp377_eq_powMap [Fact (Nat.Prime bls377Q)]
    (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (f : Fp12_377)
    (hFrob : letI := Fp12_377.commRing ξ₂ ξ₆
             Fp12_377.conj12 f = f ^ (bls377Q ^ 6))
    (hInv : letI := Fp12_377.commRing ξ₂ ξ₆
            f * Fp12_377.inv12 ξ₂ ξ₆ f = 1)
    (hRdvd : bls377R ∣ (bls377Q ^ 4 - bls377Q ^ 2 + 1)) :
    letI := Fp12_377.commRing ξ₂ ξ₆
    finalExp377 ξ₂ ξ₆ f = f ^ ((bls377Q ^ 12 - 1) / bls377R) := by
  letI := Fp12_377.commRing ξ₂ ξ₆
  -- The Nat exponent identity `(q⁶−1)·((q²+1)·hardExp377) = (q¹²−1)/r`.
  have hexp : (bls377Q ^ 6 - 1) * ((bls377Q ^ 2 + 1) * hardExp377)
      = (bls377Q ^ 12 - 1) / bls377R := by
    unfold hardExp377
    rw [← mul_assoc, ← Nat.mul_div_assoc _ hRdvd, bls377_cyclotomic_factor]
  -- Easy part collapses to `m ^ (q²+1)`, `m = conj12 f · inv12 f`.
  have hmulpow : ∀ a : Fp12_377, a * a ^ (bls377Q ^ 2) = a ^ (bls377Q ^ 2 + 1) := by
    intro a; rw [← pow_succ']
  have heasy : finalExpEasy377 ξ₂ ξ₆ f
      = (Fp12_377.conj12 f * Fp12_377.inv12 ξ₂ ξ₆ f) ^ (bls377Q ^ 2 + 1) := by
    show (Fp12_377.conj12 f * Fp12_377.inv12 ξ₂ ξ₆ f)
          * frobP2_377 ξ₂ ξ₆ (Fp12_377.conj12 f * Fp12_377.inv12 ξ₂ ξ₆ f)
        = (Fp12_377.conj12 f * Fp12_377.inv12 ξ₂ ξ₆ f) ^ (bls377Q ^ 2 + 1)
    unfold frobP2_377
    exact hmulpow _
  -- Full schedule as a single power of `f^(q⁶) · inv12 f`.
  have key : finalExp377 ξ₂ ξ₆ f
      = (f ^ (bls377Q ^ 6) * Fp12_377.inv12 ξ₂ ξ₆ f)
          ^ ((bls377Q ^ 2 + 1) * hardExp377) := by
    unfold finalExp377 finalExpHard377
    rw [heasy, hFrob, ← pow_mul]
  rw [key, npow_mul_inv_pow hInv
        (Nat.one_le_pow _ _ (Fact.out : Nat.Prime bls377Q).pos) _, hexp]

end CatCrypt.Crypto.SecureCompilation.VIR.Bls377FinalExpCorrect
