/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

/-!
# Generic Montgomery reduction (REDC) — the ℤ congruence core

This file develops the **Montgomery reduction** (REDC) generically, over an
arbitrary modulus `N` and Montgomery radix `R`, working in `ℤ` (where the
`Int.ModEq` algebra is cleanest — no `Nat` truncated-subtraction or
division-rounding bookkeeping interleaved with the congruence reasoning).

For a modulus `N`, a Montgomery radix `R` coprime to `N`, and the precomputed
Montgomery constant `N'` with `N * N' ≡ -1 (mod R)`, the reduction of an input
`T` is

```
redc T = (T + m * N) / R   where   m = (T * N') mod R
```

and the main theorem `redc_mul_R_modEq` establishes the **defining Montgomery
property**

```
redc T * R ≡ T (mod N)        i.e.   redc T ≡ T * R⁻¹ (mod N).
```

The proof assembles two halves:

1. **Divisibility** (`R ∣ (T + m*N)`): by the choice `m = T*N' mod R`, we have
   `T + m*N ≡ 0 (mod R)` (here `m*N ≡ T*N'*N ≡ -T (mod R)` using
   `N*N' ≡ -1`), so the right-shift `/R` is exact.  This is `R_dvd_T_add_mN`.
2. **Congruence on the dividend** (`(T + m*N) ≡ T (mod N)`): since `m*N ≡ 0
   (mod N)`.  Combined with exactness `redc T * R = T + m*N`, this gives
   `redc T * R ≡ T (mod N)`.

This is the prime/modulus-parametric correctness core every Montgomery
multiplier rests on; the per-curve `MontMul` kernels instantiate it (at the
`ℕ` level the same statement is `CatCrypt.Crypto.Number.montgomeryReduce_correct`,
which additionally tracks the `[0, 2N)` range bound for the conditional
subtract — see the cross-reference below).

The subtractive form, with `μ = N⁻¹ mod R` and the reduction `T / R − m·N / R`, is
`redcSub_digit_mul_add`, `redcSub_mul_R_modEq` and `redcSub_lt`.
-/

namespace CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric

open Int

/-- The Montgomery digit `m = (T * N') mod R`: the multiple of `1` that, added
    as `m*N`, cancels `T` modulo `R`. -/
def montDigit (R N' T : ℤ) : ℤ := (T * N') % R

/-- The abstract Montgomery reduction step over `ℤ`:
    `redc T = (T + m*N) / R` with `m = (T * N') mod R`. -/
def redc (N R N' T : ℤ) : ℤ :=
  (T + montDigit R N' T * N) / R

/-- **Half 1 (divisibility / exactness).** With `m = T*N' mod R` and the
    Montgomery constant `N'` satisfying `N*N' ≡ -1 (mod R)`, the dividend
    `T + m*N` is divisible by `R`. This is what makes the right-shift exact. -/
theorem R_dvd_T_add_mN
    (N R N' T : ℤ) (hN' : N * N' ≡ -1 [ZMOD R]) :
    R ∣ (T + montDigit R N' T * N) := by
  -- It suffices to show T + m*N ≡ 0 (mod R).
  rw [← Int.modEq_zero_iff_dvd]
  -- m = (T*N') mod R ≡ T*N' (mod R).
  have hm : montDigit R N' T ≡ T * N' [ZMOD R] := Int.mod_modEq _ _
  have key : T + montDigit R N' T * N ≡ T + (T * N') * N [ZMOD R] :=
    (Int.ModEq.refl T).add (hm.mul_right N)
  refine key.trans ?_
  -- T + (T*N')*N = T*(1 + N*N') ≡ T*(1 + (-1)) = 0 (mod R).
  have hfac : T + (T * N') * N = T * (1 + N * N') := by ring
  rw [hfac]
  have hz : (1 : ℤ) + N * N' ≡ 0 [ZMOD R] := by
    have : (1 : ℤ) + N * N' ≡ 1 + (-1) [ZMOD R] := (Int.ModEq.refl 1).add hN'
    simpa using this
  calc T * (1 + N * N') ≡ T * 0 [ZMOD R] := hz.mul_left T
    _ = 0 := by ring

/-- **Exactness as an equation.** Given divisibility, `redc T * R = T + m*N`.
    (Exact `ediv` needs no `R ≠ 0` side condition: when `R = 0`, divisibility
    forces the dividend to be `0` and both sides vanish.) -/
theorem redc_mul_R_eq
    (N R N' T : ℤ) (hN' : N * N' ≡ -1 [ZMOD R]) :
    redc N R N' T * R = T + montDigit R N' T * N := by
  have hdvd : R ∣ (T + montDigit R N' T * N) := R_dvd_T_add_mN N R N' T hN'
  unfold redc
  exact Int.ediv_mul_cancel hdvd

/-- **Main theorem — the defining Montgomery property.**

    `redc T * R ≡ T (mod N)`, i.e. `redc T ≡ T * R⁻¹ (mod N)`.

    Assembled from the two halves: exactness `redc T * R = T + m*N`
    (`redc_mul_R_eq`, via `R_dvd_T_add_mN`) and the congruence on the dividend
    `T + m*N ≡ T (mod N)` (since `m*N ≡ 0 (mod N)`). -/
theorem redc_mul_R_modEq
    (N R N' T : ℤ) (hN' : N * N' ≡ -1 [ZMOD R]) :
    redc N R N' T * R ≡ T [ZMOD N] := by
  rw [redc_mul_R_eq N R N' T hN']
  -- T + m*N ≡ T (mod N), since m*N ≡ 0 (mod N).
  have hzero : montDigit R N' T * N ≡ 0 [ZMOD N] :=
    (Int.modEq_zero_iff_dvd).mpr ⟨montDigit R N' T, by ring⟩
  have hstep := (Int.ModEq.refl T).add hzero
  rw [add_zero] at hstep
  exact hstep

/-- **Montgomery multiplication** over `ℤ`: reduce the product `a*b` at radix
    `R`. -/
def montMul (N R N' a b : ℤ) : ℤ := redc N R N' (a * b)

/-- **Montgomery multiplication correctness (modulus-parametric).**
    `montMul a b * R ≡ a*b (mod N)`, i.e. `montMul a b ≡ a*b*R⁻¹ (mod N)`. -/
theorem montMul_mul_R_modEq
    (N R N' a b : ℤ) (hN' : N * N' ≡ -1 [ZMOD R]) :
    montMul N R N' a b * R ≡ a * b [ZMOD N] :=
  redc_mul_R_modEq N R N' (a * b) hN'

/-! ## The subtractive form

With `μ = N⁻¹ mod R` (`μ·N ≡ 1 (mod R)`) in place of `N' = −N⁻¹`, the reduction of
`T` is `T / R − u` with `m = ((T mod R)·μ) mod R` and `u = m·N / R`: the low word of
`m·N` equals the low word of `T`, so the difference of the two high words is
`(T − m·N) / R` exactly. A word implementation computes `T / R` and `u` as the high
halves of `a·b` and `m·N` and corrects a negative difference by adding `N`. -/

/-- **Subtractive digit relation.** For `μ·N ≡ 1 (mod R)` and
    `m = ((T mod R)·μ) mod R`, the high word `u = m·N / R` satisfies
    `u·R + T mod R = m·N`. -/
theorem redcSub_digit_mul_add (N R μ T : ℕ) (hμ : μ * N ≡ 1 [MOD R]) :
    (T % R * μ % R) * N / R * R + T % R = (T % R * μ % R) * N := by
  have hmN : (T % R * μ % R) * N % R = T % R := by
    have h : (T % R * μ % R) * N ≡ T % R * 1 [MOD R] := by
      calc (T % R * μ % R) * N ≡ (T % R * μ) * N [MOD R] := (Nat.mod_modEq _ R).mul_right N
        _ = T % R * (μ * N) := by ring
        _ ≡ T % R * 1 [MOD R] := hμ.mul_left _
    rw [Nat.mul_one] at h
    rw [h, Nat.mod_mod]
  conv_rhs => rw [← Nat.div_add_mod ((T % R * μ % R) * N) R]
  rw [hmN, Nat.mul_comm R]

/-- **Subtractive Montgomery property.** For `μ·N ≡ 1 (mod R)`,
    `(T / R − u)·R ≡ T (mod N)` with `u = (((T mod R)·μ) mod R)·N / R`, i.e. the
    signed difference of the two high words is `T·R⁻¹ (mod N)`. -/
theorem redcSub_mul_R_modEq (N R μ T : ℕ) (hμ : μ * N ≡ 1 [MOD R]) :
    (((T / R : ℕ) : ℤ) - (((T % R * μ % R) * N / R : ℕ) : ℤ)) * R ≡ T [ZMOD N] := by
  have e1 : ((T / R : ℕ) : ℤ) * R + ((T % R : ℕ) : ℤ) = T := by
    have := Nat.div_add_mod' T R; exact_mod_cast this
  have e2 : (((T % R * μ % R) * N / R : ℕ) : ℤ) * R + ((T % R : ℕ) : ℤ)
      = (((T % R * μ % R) : ℕ) : ℤ) * N := by
    exact_mod_cast redcSub_digit_mul_add N R μ T hμ
  have h : (((T / R : ℕ) : ℤ) - (((T % R * μ % R) * N / R : ℕ) : ℤ)) * R
      = T - (((T % R * μ % R) : ℕ) : ℤ) * N := by
    rw [← e1, ← e2]; ring
  rw [h]
  have hz : (((T % R * μ % R) : ℕ) : ℤ) * N ≡ 0 [ZMOD N] :=
    (Int.modEq_zero_iff_dvd).mpr ⟨_, by ring⟩
  simpa using (Int.ModEq.refl (T : ℤ)).sub hz

/-- **Subtractive range.** For `T < N·R` both high words lie below `N`:
    `T / R < N` and `(((T mod R)·μ) mod R)·N / R < N`. -/
theorem redcSub_lt (N R μ T : ℕ) (hR : 0 < R) (hN : 0 < N) (hT : T < N * R) :
    T / R < N ∧ (T % R * μ % R) * N / R < N :=
  ⟨Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hT),
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hR) hN)⟩

end CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric
