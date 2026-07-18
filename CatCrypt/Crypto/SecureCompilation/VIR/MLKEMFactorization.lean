/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.MLKEMNegacyclicSound
import CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Basic

set_option autoImplicit false
set_option maxRecDepth 4000

/-!
# Concrete ML-KEM cyclotomic factorization (incomplete-NTT discharge)

`MLKEMNegacyclicSound.lean` proves `mlkem_incompleteNTT_map_mul` modulo two
**explicit hypotheses** about a twiddle family `ζ : Fin 128 → ZMod 3329`:

* `hcop` — the quadratic factors `X^2 - ζ_i` are pairwise coprime as ideals;
* `hfact` — their ideal intersection is the principal ideal `(X^256 + 1)`.

This file **discharges both** for the concrete ML-KEM-768 twiddle family

  `ζ_i = (17 : ZMod 3329) ^ (2 * i + 1)`,   `i < 128`,

and instantiates `mlkem_incompleteNTT_map_mul` to obtain an **unconditional**
incomplete-NTT `map_mul` over `(ZMod 3329)[X] / (X^256 + 1)` — no hypotheses.

## The arithmetic backbone (kernel-checked `decide +kernel`)

`17` is a primitive `256`-th root of unity in `ZMod 3329`:
`17^256 = 1` and `17^128 = 3328 = -1 ≠ 1` (both by kernel `decide`, so no
`Lean.ofReduceBool` axiom). Since `256 = 2^8`, this pins
`orderOf (17 : ZMod 3329) = 256` (`mlkemRoot_orderOf`), hence
`IsPrimitiveRoot (17 : ZMod 3329) 256` (`mlkemRoot_isPrimitiveRoot`).

## The factorization (Kummer-style splitting + `X ↦ X^2` substitution)

Mathlib's `Polynomial.X_pow_sub_C_eq_prod` splits `X^128 - C(-1) = X^128 + 1`
into the `128` linear factors `X - C(ζ_i)` over the primitive-`128`-th root
`17^2` with `(17)^128 = -1`. Composing with `X ↦ X^2`
(`Polynomial.prod_comp`, `sub_comp`, `pow_comp`) lifts this to

  `X^256 + 1 = ∏_{i<128} (X^2 - C ζ_i) = ∏_{i<128} quadPoly (ζ i)`.

`Ideal.iInf_span_singleton` (over the field `ZMod 3329`) then turns the
polynomial product into the ideal intersection `hfact`, given pairwise
**polynomial** coprimality `IsCoprime (X^2 - ζ_i) (X^2 - ζ_j)` (`i ≠ j`),
which holds because `ζ_i ≠ ζ_j` makes their difference a unit constant — an
explicit Bézout witness. `Ideal.isCoprime_span_singleton_iff` then gives `hcop`.

## What is proved (all goals closed; no `sorry`, no extra hypotheses)

* `mlkemZeta` — the concrete twiddle family.
* `mlkemRoot_isPrimitiveRoot` — `17` is a primitive `256`-th root of unity.
* `mlkemZeta_quadPoly_pairwise_coprime` — pairwise polynomial coprimality.
* `mlkemZeta_hcop` / `mlkemZeta_hfact` — the two hypotheses of
  `mlkem_incompleteNTT_map_mul`, fully discharged.
* `mlkem_incompleteNTT` — the unconditional incomplete-NTT ring isomorphism
  `(ZMod 3329)[X] / (X^256 + 1) ≅ ∏_{i<128} (ZMod 3329)[X] / (X^2 - ζ_i)`.
* `mlkem_incompleteNTT_map_mul_concrete` — its `map_mul`, with no hypotheses.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Polynomial
open scoped Function
open CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic (negaPoly quadPoly quadPoly_monic
  incompleteNTTOfModulus incompleteNTTOfModulus_map_mul)

/-! ## 1. The concrete twiddle family and the primitive-root backbone -/

/-- The ML-KEM-768 twiddle family: the `128` odd powers of the primitive
    `256`-th root `17` over `ZMod 3329`. These are exactly the roots of
    `X^128 + 1`, i.e. the `256`-th roots of unity that are not `128`-th roots. -/
def mlkemZeta : Fin 128 → MLKEMField := fun i => (17 : MLKEMField) ^ (2 * (i : ℕ) + 1)

/-- `17^256 = 1` in `ZMod 3329`. -/
theorem mlkemRoot_pow_256 : (17 : MLKEMField) ^ 256 = 1 := by
  decide +kernel

/-- `17^128 = -1` in `ZMod 3329` — the load-bearing 2-adicity fact: `17` is a
    primitive `256`-th root with `(17^128)^2 = 1` but `17^128 ≠ 1`. -/
theorem mlkemRoot_pow_128 : (17 : MLKEMField) ^ 128 = -1 := by
  decide +kernel

/-- `17^128 ≠ 1` (consequence of `mlkemRoot_pow_128`, since `-1 ≠ 1` in
    `ZMod 3329`). -/
theorem mlkemRoot_pow_128_ne_one : (17 : MLKEMField) ^ 128 ≠ 1 := by
  rw [mlkemRoot_pow_128]; decide +kernel

/-- `orderOf (17 : ZMod 3329) = 256`. Since `17^256 = 1`, the order divides
    `256 = 2^8`, so it is `2^k` for some `k ≤ 8`. It cannot divide `128 = 2^7`
    (that would force `17^128 = 1`), so `k = 8` and the order is `256`. -/
theorem mlkemRoot_orderOf : orderOf (17 : MLKEMField) = 256 := by
  have hdvd : orderOf (17 : MLKEMField) ∣ 256 :=
    orderOf_dvd_of_pow_eq_one mlkemRoot_pow_256
  have hnot : ¬ orderOf (17 : MLKEMField) ∣ 128 := by
    intro h
    exact mlkemRoot_pow_128_ne_one (orderOf_dvd_iff_pow_eq_one.mp h)
  -- `orderOf 17 ∣ 2^8`, so `orderOf 17 = 2^k` with `k ≤ 8`.
  have hp : Nat.Prime 2 := Nat.prime_two
  rw [show (256 : ℕ) = 2 ^ 8 from by norm_num] at hdvd
  obtain ⟨k, hk, hke⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  -- `¬ 2^k ∣ 128 = 2^7`: if `k ≤ 7` then `2^k ∣ 2^7` (`pow_dvd_pow`), so `k = 8`.
  rw [hke, show (128 : ℕ) = 2 ^ 7 from by norm_num] at hnot
  have hk8 : k = 8 := by
    by_contra hk8
    exact hnot (pow_dvd_pow 2 (by omega))
  rw [hke, hk8]; norm_num

/-- **`17` is a primitive `256`-th root of unity in `ZMod 3329`.** This is the
    cyclotomic fact underlying the incomplete NTT: `ZMod 3329` contains a
    primitive `256`-th but no primitive `512`-th root of unity (its 2-adicity is
    `8`, since `3328 = 2^8 · 13`). -/
theorem mlkemRoot_isPrimitiveRoot : IsPrimitiveRoot (17 : MLKEMField) 256 :=
  IsPrimitiveRoot.iff_orderOf.mpr mlkemRoot_orderOf

/-- `17^2 = 289` is a primitive `128`-th root of unity in `ZMod 3329`. The roots
    `ζ_i = (17^2)^i · 17 = 17^(2i+1)` of `X^128 + 1` are generated by it. -/
theorem mlkemRootSq_isPrimitiveRoot :
    IsPrimitiveRoot ((17 : MLKEMField) ^ 2) 128 := by
  have h := mlkemRoot_isPrimitiveRoot.pow_of_dvd (p := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-! ## 2. The concrete factorization `X^256 + 1 = ∏ (X^2 - ζ_i)` -/

/-- The `128` twiddles `17^(2i+1)` are pairwise distinct (for `i < 128`):
    the exponents `2i+1` are distinct and lie below `256 = orderOf 17`, so the
    primitive root distinguishes them. -/
theorem mlkemZeta_injective : Function.Injective mlkemZeta := by
  intro i j h
  unfold mlkemZeta at h
  have hi : 2 * (i : ℕ) + 1 < 256 := by omega
  have hj : 2 * (j : ℕ) + 1 < 256 := by omega
  have := mlkemRoot_isPrimitiveRoot.pow_inj hi hj h
  exact Fin.ext (by omega)

/-- **Linear splitting of `X^128 + 1` over `ZMod 3329`.**
    `X^128 + 1 = ∏_{i<128} (X - C (17^(2i+1)))`. The roots are exactly the
    `128` odd powers of `17`. -/
theorem mlkem_X128_add_one_eq_prod :
    (X ^ 128 + 1 : MLKEMField[X])
      = ∏ i ∈ Finset.range 128, (X - C ((17 : MLKEMField) ^ (2 * i + 1))) := by
  have key :=
    X_pow_sub_C_eq_prod (R := MLKEMField) (n := 128) (ζ := (17 : MLKEMField) ^ 2)
      (α := (17 : MLKEMField)) (a := -1) mlkemRootSq_isPrimitiveRoot (by norm_num)
      (by rw [mlkemRoot_pow_128])
  -- `X^128 - C(-1) = X^128 + 1`, and `(17^2)^i * 17 = 17^(2i+1)`.
  rw [map_neg, C_1, sub_neg_eq_add] at key
  rw [key]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hexp : ((17 : MLKEMField) ^ 2) ^ i * (17 : MLKEMField) = (17 : MLKEMField) ^ (2 * i + 1) := by
    rw [← pow_mul, ← pow_succ, Nat.mul_comm]
  rw [hexp]

/-- **The concrete ML-KEM negacyclic factorization.**
    `X^256 + 1 = ∏_{i<128} (X^2 - C (17^(2i+1)))`. Obtained from the linear
    splitting of `X^128 + 1` by the substitution `X ↦ X^2`
    (`Polynomial.comp`): products and differences commute with composition, and
    `(X - C c).comp (X^2) = X^2 - C c`, `(X^128 + 1).comp (X^2) = X^256 + 1`. -/
theorem mlkem_X256_add_one_eq_prod :
    (X ^ 256 + 1 : MLKEMField[X])
      = ∏ i ∈ Finset.range 128, (X ^ 2 - C ((17 : MLKEMField) ^ (2 * i + 1))) := by
  -- Substitute `X ↦ X^2` into the linear splitting of `X^128 + 1`.
  have hcomp := congrArg (Polynomial.comp · (X ^ 2 : MLKEMField[X]))
    mlkem_X128_add_one_eq_prod
  dsimp only at hcomp
  -- LHS: `(X^128 + 1).comp (X^2) = X^256 + 1`.
  rw [add_comp, pow_comp, X_comp, one_comp, ← pow_mul,
    show (128 * 2 : ℕ) = 256 from rfl] at hcomp
  -- RHS: distribute comp through the product and simplify each factor.
  rw [Polynomial.prod_comp] at hcomp
  rw [hcomp]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [sub_comp, X_comp, C_comp]

/-- The factorization, phrased with the `Fin 128` twiddle family `mlkemZeta`
    and CompPoly's `quadPoly`: `X^256 + 1 = ∏_{i : Fin 128} quadPoly (ζ i)`. -/
theorem mlkem_negaPoly_eq_prod :
    (mlkemNegaPoly)
      = ∏ i : Fin 128, quadPoly (mlkemZeta i) := by
  have hnega : (mlkemNegaPoly : MLKEMField[X]) = X ^ (256 : ℕ) + 1 := rfl
  rw [hnega, mlkem_X256_add_one_eq_prod,
    Finset.prod_range (fun i => (X ^ 2 - C ((17 : MLKEMField) ^ (2 * i + 1))))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rfl

/-! ## 3. Pairwise coprimality of the quadratic factors -/

/-- **Pairwise polynomial coprimality.** For `i ≠ j`, `X^2 - ζ_i` and
    `X^2 - ζ_j` are coprime: their difference `C (ζ_j - ζ_i)` is a nonzero
    constant (a unit, since `ζ_i ≠ ζ_j` over the field `ZMod 3329`), which gives
    a direct Bézout witness. -/
theorem mlkemZeta_quadPoly_pairwise_coprime :
    Pairwise (IsCoprime on (fun i => quadPoly (mlkemZeta i))) := by
  intro i j hij
  simp only [Function.onFun]
  unfold quadPoly
  -- `c = ζ_j - ζ_i ≠ 0`, with inverse `c⁻¹`.
  set ci : MLKEMField := mlkemZeta i
  set cj : MLKEMField := mlkemZeta j
  have hne : ci ≠ cj := fun h => hij (mlkemZeta_injective h)
  set c : MLKEMField := cj - ci with hc
  have hcne : c ≠ 0 := by rw [hc]; exact sub_ne_zero.mpr (Ne.symm hne)
  -- Bézout: `C c⁻¹ · (X^2 - C ci) + (- C c⁻¹) · (X^2 - C cj) = 1`.
  refine ⟨C c⁻¹, - C c⁻¹, ?_⟩
  have hcc : c⁻¹ * c = 1 := inv_mul_cancel₀ hcne
  have hstep : C c⁻¹ * (X ^ 2 - C ci) + (- C c⁻¹) * (X ^ 2 - C cj)
      = C (c⁻¹ * c) := by
    rw [hc]
    rw [show (cj - ci : MLKEMField) = cj - ci from rfl]
    rw [C_mul, C_sub]
    ring
  rw [hstep, hcc, C_1]

/-! ## 4. Discharging `hcop` / `hfact` and the unconditional `map_mul` -/

/-- **`hcop` discharged.** Pairwise coprimality of the ideals `(X^2 - ζ_i)`,
    transported from the polynomial coprimality via
    `Ideal.isCoprime_span_singleton_iff`. -/
theorem mlkemZeta_hcop :
    Pairwise (IsCoprime on (fun i => Ideal.span {quadPoly (mlkemZeta i)})) := by
  intro i j hij
  simp only [Function.onFun]
  rw [Ideal.isCoprime_span_singleton_iff]
  exact mlkemZeta_quadPoly_pairwise_coprime hij

/-- **`hfact` discharged.** The ideal intersection of the quadratic factors is
    the principal ideal `(X^256 + 1) = (mlkemNegaPoly)`. Combines
    `Ideal.iInf_span_singleton` (product of pairwise-coprime factors) with the
    concrete factorization `mlkem_negaPoly_eq_prod`. -/
theorem mlkemZeta_hfact :
    (⨅ i, Ideal.span {quadPoly (mlkemZeta i)})
      = Ideal.span {mlkemNegaPoly} := by
  rw [Ideal.iInf_span_singleton (I := fun i => quadPoly (mlkemZeta i))
    (fun i j h => mlkemZeta_quadPoly_pairwise_coprime h)]
  rw [← mlkem_negaPoly_eq_prod]

/-- **The unconditional ML-KEM incomplete-NTT ring isomorphism.**

    `(ZMod 3329)[X] / (X^256 + 1) ≅ ∏_{i<128} (ZMod 3329)[X] / (X^2 - ζ_i)`,

    the genuine Chinese-Remainder decomposition of the ML-KEM negacyclic ring
    into its `128` degree-`2` incomplete-NTT components, with the concrete
    twiddles `ζ_i = 17^(2i+1)`. No hypotheses: the factorization `hcop`/`hfact`
    is fully discharged by `mlkemZeta_hcop` / `mlkemZeta_hfact`. -/
noncomputable def mlkem_incompleteNTT :
    (MLKEMField[X] ⧸ Ideal.span {mlkemNegaPoly})
      ≃+* ∀ i : Fin 128, MLKEMField[X] ⧸ Ideal.span {quadPoly (mlkemZeta i)} :=
  incompleteNTTOfModulus (fun i => quadPoly (mlkemZeta i)) mlkemNegaPoly
    mlkemZeta_hcop mlkemZeta_hfact

/-- **Unconditional ML-KEM incomplete-NTT multiplication soundness.**

    The incomplete NTT of two ML-KEM polynomials equals the pointwise product of
    their incomplete NTTs over the `128` quadratic components — i.e. NTT turns
    negacyclic convolution mod `X^256 + 1` into pointwise `basemul`. This is the
    concrete, hypothesis-free instance of `mlkem_incompleteNTT_map_mul` at the
    discharged twiddle family `ζ_i = 17^(2i+1)`. -/
theorem mlkem_incompleteNTT_map_mul_concrete
    (a b : MLKEMField[X] ⧸ Ideal.span {mlkemNegaPoly}) :
    mlkem_incompleteNTT (a * b)
      = mlkem_incompleteNTT a * mlkem_incompleteNTT b :=
  incompleteNTTOfModulus_map_mul (fun i => quadPoly (mlkemZeta i)) mlkemNegaPoly
    mlkemZeta_hcop mlkemZeta_hfact a b

end CatCrypt.Crypto.SecureCompilation.VIR
