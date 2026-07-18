/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Montgomery reduction — the prime-parametric correctness law

This file ports the *reduction-correctness core* of fiat-crypto's
`WordByWordMontgomery` (the result the in-tree CIOS kernels —
`Bn254/Bls12381/Pasta/BignumMontMulKernel`, and the `mpnMontMul` reference in
`Jasmin/Examples/MpnMontgomeryPrototype.lean` — only validate by KAT) into a
single **prime-parametric** Lean theorem over `Nat`.

For an odd modulus `N`, a Montgomery radix `R` coprime to `N`, and the
Montgomery constant `Nprime` with `N · Nprime ≡ -1 (mod R)`, the reduction of
an input `T < R · N` is

```
redc T = (T + ((T · Nprime) mod R) · N) / R
```

and `montgomeryReduce_correct` establishes the three facts every Montgomery
multiplier rests on:

1. **Exactness** — `R ∣ (T + m · N)`, so the right-shift `/ R` is exact.
2. **Range** — `redc T < 2 · N`, so a single conditional subtract finishes.
3. **Congruence** — `(redc T) · R ≡ T (mod N)`, i.e. `redc T ≡ T · R⁻¹ (mod N)`.

A front-emitted (or owned-backend) Montgomery multiply discharges its
field-correctness by exhibiting that its limb output equals `redc (a · b)` for
the right `R`, then this law supplies `≡ a · b · R⁻¹ (mod N)` for *every* prime
at once — no per-prime BitVec REDC congruence.
-/

namespace CatCrypt.Crypto.Number

/-- The abstract Montgomery reduction step: `redc T = (T + m·N)/R` where
    `m = (T · Nprime) mod R` is the Montgomery digit. -/
def montgomeryReduce (N R Nprime T : Nat) : Nat :=
  (T + ((T * Nprime) % R) * N) / R

/-- The Montgomery digit `m = (T · Nprime) mod R` makes `T + m·N` divisible by
    `R`. This is the exactness fact that justifies the limb right-shift. -/
theorem montgomeryReduce_dvd
    (N R Nprime T : Nat) (hR : 0 < R)
    (hNprime : (N * Nprime) % R = R - 1) :
    R ∣ (T + ((T * Nprime) % R) * N) := by
  -- Work modulo R. m·N ≡ T·Nprime·N, and N·Nprime ≡ -1, so T + m·N ≡ 0.
  have hmod : (T + ((T * Nprime) % R) * N) % R = 0 := by
    have hm : ((T * Nprime) % R) * N % R = (T * Nprime * N) % R :=
      (Nat.mod_modEq (T * Nprime) R).mul_right N
    -- (T + m·N) % R = (T % R + (T·Nprime·N) % R) % R
    have h1 : (T + ((T * Nprime) % R) * N) % R = (T + T * Nprime * N) % R := by
      rw [Nat.add_mod, hm, ← Nat.add_mod]
    rw [h1]
    -- T + T·Nprime·N = T·(1 + Nprime·N). And N·Nprime ≡ R-1 ≡ -1, so 1+Nprime·N ≡ 0.
    have hfac : T + T * Nprime * N = T * (1 + N * Nprime) := by ring
    rw [hfac, Nat.mul_mod, Nat.add_mod 1 (N * Nprime), hNprime]
    -- 1 + (R-1) ≡ R ≡ 0 (mod R), so the whole product is 0 mod R.
    have hX : (1 % R + (R - 1)) % R = 0 := by
      rcases Nat.lt_or_ge R 2 with hR1 | hR2
      · interval_cases R <;> simp
      · rw [Nat.one_mod_eq_one.mpr (by omega)]
        have h1 : 1 + (R - 1) = R := by omega
        rw [h1, Nat.mod_self]
    rw [hX]; simp
  exact Nat.dvd_of_mod_eq_zero hmod

/-- **Montgomery reduction correctness (prime-parametric).**

    For an odd modulus `N`, radix `R` coprime to `N`, Montgomery constant
    `Nprime` (with `N·Nprime ≡ -1 mod R`), and input `T < R·N`:

    * the reduction `redc T` lies in `[0, 2N)` (one conditional subtract away
      from canonical), and
    * `(redc T) · R ≡ T (mod N)` — i.e. `redc T ≡ T · R⁻¹ (mod N)`.

    This is the reduction-correctness core of fiat-crypto's
    `WordByWordMontgomery`, stated once for all primes. -/
theorem montgomeryReduce_correct
    (N R Nprime T : Nat) (hN : 0 < N) (hR : 0 < R)
    (hNprime : (N * Nprime) % R = R - 1) (hT : T < R * N) :
    montgomeryReduce N R Nprime T < 2 * N ∧
    (montgomeryReduce N R Nprime T) * R ≡ T [MOD N] := by
  set m := (T * Nprime) % R with hm
  have hdvd : R ∣ (T + m * N) := montgomeryReduce_dvd N R Nprime T hR hNprime
  -- u·R = T + m·N  (exact division)
  have hexact : montgomeryReduce N R Nprime T * R = T + m * N := by
    unfold montgomeryReduce
    rw [← hm, Nat.div_mul_cancel hdvd]
  refine ⟨?_, ?_⟩
  · -- range: u < 2N.  T < R·N and m < R ⇒ m·N < R·N ⇒ T+m·N < 2RN ⇒ u < 2N.
    have hmR : m < R := Nat.mod_lt _ hR
    have hbound : T + m * N < 2 * N * R := by
      have h1 : m * N ≤ (R - 1) * N := Nat.mul_le_mul_right N (by omega)
      nlinarith [Nat.mul_le_mul_right N (show m ≤ R - 1 by omega)]
    -- u·R = T+m·N < 2N·R ⇒ u < 2N
    have : montgomeryReduce N R Nprime T * R < (2 * N) * R := by
      rw [hexact]; rw [Nat.mul_comm (2 * N) R] at *; linarith [hbound]
    exact Nat.lt_of_mul_lt_mul_right this
  · -- congruence: u·R = T + m·N ≡ T (mod N), since m·N ≡ 0 (mod N).
    rw [hexact]
    have hzero : m * N ≡ 0 [MOD N] := (Nat.modEq_zero_iff_dvd).mpr ⟨m, by ring⟩
    have := hzero.add_left T
    simpa using this

/-- **Montgomery reduction composes.** Reducing by radix `R1` then by `R2` is a
    reduction by `R1·R2`: the two-step result is in `[0, 2N)` and congruent to
    `T · (R1·R2)⁻¹ (mod N)`. This is what turns a per-limb word-reduction loop
    (each step a `montgomeryReduce` at `R = 2^64`) into a full-width reduction at
    `R = 2^(64·k)` — the bridge from the limb-level CIOS reference to the abstract
    law, proved modularly from `montgomeryReduce_correct` instead of a bespoke
    `k`-limb invariant. -/
theorem montgomeryReduce_comp
    (N R1 R2 Nprime1 Nprime2 T : Nat) (hN : 0 < N) (hR1 : 0 < R1) (hR2 : 2 ≤ R2)
    (hNp1 : (N * Nprime1) % R1 = R1 - 1) (hNp2 : (N * Nprime2) % R2 = R2 - 1)
    (hT : T < R1 * N) :
    montgomeryReduce N R2 Nprime2 (montgomeryReduce N R1 Nprime1 T) < 2 * N ∧
    (montgomeryReduce N R2 Nprime2 (montgomeryReduce N R1 Nprime1 T)) * (R1 * R2)
      ≡ T [MOD N] := by
  obtain ⟨hr1_range, hr1_cong⟩ :=
    montgomeryReduce_correct N R1 Nprime1 T hN hR1 hNp1 hT
  -- the inner result is < 2N ≤ R2·N, so the outer reduction's bound applies
  have hinner : montgomeryReduce N R1 Nprime1 T < R2 * N := by
    have : (2 : Nat) * N ≤ R2 * N := by gcongr
    omega
  obtain ⟨hr2_range, hr2_cong⟩ :=
    montgomeryReduce_correct N R2 Nprime2 _ hN (by omega) hNp2 hinner
  refine ⟨hr2_range, ?_⟩
  -- (redc_R2 (redc_R1 T)) · (R1·R2) = ((redc_R2 _) · R2) · R1 ≡ (redc_R1 T) · R1 ≡ T
  have step :
      (montgomeryReduce N R2 Nprime2 (montgomeryReduce N R1 Nprime1 T)) * (R1 * R2)
        = ((montgomeryReduce N R2 Nprime2 (montgomeryReduce N R1 Nprime1 T)) * R2)
            * R1 := by ring
  rw [step]
  exact (hr2_cong.mul_right R1).trans hr1_cong

/-- **Montgomery multiplication** of two residues `a, b ∈ [0, N)`: reduce the
    product `a·b` at the full radix `R` (= `2^(64·k)` for a `k`-limb modulus). -/
def montgomeryMul (N R Nprime a b : Nat) : Nat :=
  montgomeryReduce N R Nprime (a * b)

/-- **Montgomery multiplication correctness (prime-parametric, multi-limb).**

    For an odd modulus `N`, radix `R ≥ N` coprime to `N`, Montgomery constant
    `Nprime` (`N·Nprime ≡ -1 mod R`), and residues `a, b < N`:
    `montgomeryMul N R Nprime a b` lies in `[0, 2N)` and
    `(montgomeryMul …) · R ≡ a · b (mod N)`, i.e. `= a·b·R⁻¹ (mod N)`.

    This is the result the in-tree multi-limb Montgomery kernels
    (`Bn254/Bls12381/Pasta/BignumMontMulKernel`, the `mpnMontMul` CIOS
    reference) only validate by KAT — here for every prime at once, with
    `R = 2^(64·k)` and no per-prime BitVec REDC congruence. The product
    `a·b < N² ≤ N·R` satisfies the input bound directly, so no per-word
    decomposition is needed for *correctness* (the per-word loop merely
    *computes* this value — see `montgomeryReduce_comp` for that bridge). -/
theorem montgomeryMul_correct
    (N R Nprime a b : Nat) (hN : 0 < N) (hR : 0 < R) (hNleR : N ≤ R)
    (hNprime : (N * Nprime) % R = R - 1) (ha : a < N) (hb : b < N) :
    montgomeryMul N R Nprime a b < 2 * N ∧
    (montgomeryMul N R Nprime a b) * R ≡ a * b [MOD N] := by
  have hT : a * b < R * N := by
    have h1 : a * b < N * N := mul_lt_mul'' ha hb (Nat.zero_le a) (Nat.zero_le b)
    calc a * b < N * N := h1
      _ ≤ R * N := by gcongr
  exact montgomeryReduce_correct N R Nprime (a * b) hN hR hNprime hT

end CatCrypt.Crypto.Number
