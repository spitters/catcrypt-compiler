/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

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

and the keystone `redc_mul_R_modEq` establishes the **defining Montgomery
property**

```
redc T * R ≡ T (mod N)        i.e.   redc T ≡ T * R⁻¹ (mod N).
```

The proof is the two-halves assembly the task description calls for:

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

/-- **Keystone — the defining Montgomery property.**

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

end CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric
