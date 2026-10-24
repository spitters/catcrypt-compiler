/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.MLDSA.ConcreteParams
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Coefficient maps for the ML-DSA ring `Rq_dsa`

The maps between the ML-DSA ring `Rq_dsa = (ZMod 8380417)[X]/(X^256 + 1)` and the
coefficient representation `Fin 256 → ZMod q_dsa`, their round trips, their
additive properties, and the `Array Int` marshalling used by the extracted code.

## Main definitions

* `coeffsToRqDsa` — the ring element with the given 256 coefficients
* `rqDsaToCoeffs` — the 256 coefficients of a ring element
* `arrayIntToRqDsa` / `rqDsaToArrayInt` — `Array Int` marshalling

## Main statements

* `rqDsa_roundtrip` / `coeffs_roundtrip` — the two round trips
* `coeffsToRqDsa_add` / `coeffsToRqDsa_sub` — additivity

## References

* NIST FIPS 204 §2.3
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLDSA.Spec.Coeffs

open Polynomial AdjoinRoot
open CatCrypt.Crypto.MLDSA.ConcreteParams

/-! ## Degree of the ML-DSA modulus -/

/-- `X^n + 1` has natural degree `n`. -/
private lemma natDegree_X_pow_add_one {R : Type*} [Ring R] [Nontrivial R] (n : ℕ) :
    (X ^ n + 1 : R[X]).natDegree = n := by
  rw [← Polynomial.C_1]; exact Polynomial.natDegree_X_pow_add_C

/-- `X^256 + 1` has natural degree `256`. -/
lemma mldsa_poly_natDegree : mldsa_poly.natDegree = 256 :=
  natDegree_X_pow_add_one 256

/-- `X^256 + 1` has degree `256`. -/
lemma mldsa_poly_degree : mldsa_poly.degree = (256 : ℕ) :=
  (Polynomial.degree_eq_natDegree mldsa_poly_monic.ne_zero).trans
    (congrArg _ mldsa_poly_natDegree)

/-! ## Coefficient maps -/

/-- The `i`-th coefficient of an element of `Rq_dsa`: the `i`-th coefficient of its
unique representative of degree `< 256`. -/
noncomputable def rqDsaToCoeffs (a : Rq_dsa) : Fin 256 → ZMod q_dsa :=
  fun i => (modByMonicHom mldsa_poly_monic a).coeff i.val

/-- The element of `Rq_dsa` with coefficients `cs`:
`coeffsToRqDsa cs = mk mldsa_poly (∑ i, monomial i (cs i))`. -/
noncomputable def coeffsToRqDsa (cs : Fin 256 → ZMod q_dsa) : Rq_dsa :=
  mk mldsa_poly (∑ i : Fin 256, Polynomial.monomial i.val (cs i))

/-! ## Round trips -/

/-- A sum of monomials of index `< 256` has degree `< 256`. -/
lemma degree_coeffs_poly_lt (cs : Fin 256 → ZMod q_dsa) :
    (∑ j : Fin 256, Polynomial.monomial j.val (cs j)).degree < (256 : ℕ) := by
  refine (Polynomial.degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro j _
  exact (Polynomial.degree_monomial_le j.val (cs j)).trans_lt
    (WithBot.coe_lt_coe.mpr j.isLt)

/-- Building a ring element from coefficients and reading them back is the identity. -/
theorem rqDsa_roundtrip (cs : Fin 256 → ZMod q_dsa) :
    rqDsaToCoeffs (coeffsToRqDsa cs) = cs := by
  ext ⟨i, hi⟩
  simp only [rqDsaToCoeffs, coeffsToRqDsa, modByMonicHom_mk]
  have hlt : (∑ j : Fin 256, Polynomial.monomial j.val (cs j)).degree
      < mldsa_poly.degree := by
    rw [mldsa_poly_degree]; exact degree_coeffs_poly_lt cs
  rw [(modByMonic_eq_self_iff mldsa_poly_monic).mpr hlt,
      Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · simp
  · intro j _ hj; rw [ite_eq_right (Fin.val_ne_of_ne hj)]
  · exact absurd (Finset.mem_univ _)

/-- Reading the coefficients of a ring element and rebuilding it is the identity. -/
theorem coeffs_roundtrip (a : Rq_dsa) : coeffsToRqDsa (rqDsaToCoeffs a) = a := by
  induction a using AdjoinRoot.induction_on with
  | _ p =>
    simp only [coeffsToRqDsa, rqDsaToCoeffs, modByMonicHom_mk]
    have h := sum_modByMonic_coeff mldsa_poly_monic (p := p)
      (n := 256) (le_of_eq mldsa_poly_degree)
    rw [h]
    exact mk_leftInverse mldsa_poly_monic (mk mldsa_poly p)

/-- `coeffsToRqDsa` is injective, by the round trip. -/
theorem coeffsToRqDsa_injective : Function.Injective coeffsToRqDsa := by
  intro a b h
  rw [← rqDsa_roundtrip a, ← rqDsa_roundtrip b, h]

/-! ## `Array Int` marshalling

The extracted ML-DSA code represents a polynomial as an `Array Int` of length 256. -/

/-- The coefficient function of an `Array Int`, each entry reduced modulo `q_dsa`. -/
def arrayIntToCoeffs (arr : Array Int) : Fin 256 → ZMod q_dsa :=
  fun i => Int.cast (arr.getD i.val 0)

/-- The `Array Int` of the canonical representatives of a coefficient function. -/
def coeffsToArrayInt (cs : Fin 256 → ZMod q_dsa) : Array Int :=
  Array.ofFn (fun i : Fin 256 => ((cs i).val : Int))

/-- The element of `Rq_dsa` an `Array Int` represents. -/
noncomputable def arrayIntToRqDsa (arr : Array Int) : Rq_dsa :=
  coeffsToRqDsa (arrayIntToCoeffs arr)

/-- The `Array Int` representing an element of `Rq_dsa`. -/
noncomputable def rqDsaToArrayInt (a : Rq_dsa) : Array Int :=
  coeffsToArrayInt (rqDsaToCoeffs a)

/-- `arrayIntToCoeffs` is a left inverse of `coeffsToArrayInt`. -/
theorem arrayIntToCoeffs_coeffsToArrayInt (cs : Fin 256 → ZMod q_dsa) :
    arrayIntToCoeffs (coeffsToArrayInt cs) = cs := by
  funext i
  simp only [arrayIntToCoeffs, coeffsToArrayInt, Array.getD, Array.size_ofFn,
    i.isLt]
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- `arrayIntToRqDsa` inverts `rqDsaToArrayInt`. -/
theorem arrayIntToRqDsa_rqDsaToArrayInt (a : Rq_dsa) :
    arrayIntToRqDsa (rqDsaToArrayInt a) = a := by
  simp only [arrayIntToRqDsa, rqDsaToArrayInt, arrayIntToCoeffs_coeffsToArrayInt,
    coeffs_roundtrip]

/-! ## Vector marshalling -/

/-- The `k`-vector over `Rq_dsa` an `Array (Array Int)` represents. -/
noncomputable def arrayIntToDsaVec (k : ℕ) (arr : Array (Array Int)) : DsaVec k :=
  fun i => arrayIntToRqDsa (arr.getD i.val #[])

/-- The `Array (Array Int)` representing a `k`-vector over `Rq_dsa`. -/
noncomputable def dsaVecToArrayInt (k : ℕ) (v : DsaVec k) : Array (Array Int) :=
  Array.ofFn (fun i : Fin k => rqDsaToArrayInt (v i))

/-! ## Additivity -/

/-- `coeffsToRqDsa` carries pointwise addition to ring addition. -/
theorem coeffsToRqDsa_add (f g : Fin 256 → ZMod q_dsa) :
    coeffsToRqDsa (f + g) = coeffsToRqDsa f + coeffsToRqDsa g := by
  unfold coeffsToRqDsa; simp only [Pi.add_apply]
  simp_rw [map_add (Polynomial.monomial _)]
  rw [Finset.sum_add_distrib, map_add]

/-- `coeffsToRqDsa` carries pointwise subtraction to ring subtraction. -/
theorem coeffsToRqDsa_sub (f g : Fin 256 → ZMod q_dsa) :
    coeffsToRqDsa (f - g) = coeffsToRqDsa f - coeffsToRqDsa g := by
  unfold coeffsToRqDsa; simp only [Pi.sub_apply]
  simp_rw [map_sub (Polynomial.monomial _)]
  rw [Finset.sum_sub_distrib, map_sub]

/-- `coeffsToRqDsa` carries pointwise scaling by a constant to multiplication by the
image of that constant in `Rq_dsa`. -/
theorem coeffsToRqDsa_const_mul (c : ZMod q_dsa) (f : Fin 256 → ZMod q_dsa) :
    coeffsToRqDsa (fun i => c * f i) = of mldsa_poly c * coeffsToRqDsa f := by
  unfold coeffsToRqDsa
  rw [AdjoinRoot.of, RingHom.comp_apply, ← map_mul, Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl (fun i _ => ?_))
  rw [Polynomial.C_mul_monomial]

/-- `rqDsaToCoeffs` carries ring addition to pointwise addition. -/
theorem rqDsaToCoeffs_add (a b : Rq_dsa) :
    rqDsaToCoeffs (a + b) = rqDsaToCoeffs a + rqDsaToCoeffs b := by
  funext i
  simp [rqDsaToCoeffs, map_add]

/-- `rqDsaToCoeffs` carries ring subtraction to pointwise subtraction. -/
theorem rqDsaToCoeffs_sub (a b : Rq_dsa) :
    rqDsaToCoeffs (a - b) = rqDsaToCoeffs a - rqDsaToCoeffs b := by
  funext i
  simp [rqDsaToCoeffs, map_sub]

/-- The element of `Rq_dsa` with all coefficients zero is `0`. -/
theorem coeffsToRqDsa_zero : coeffsToRqDsa 0 = 0 := by
  simp [coeffsToRqDsa]

end CatCrypt.Crypto.MLDSA.Spec.Coeffs
