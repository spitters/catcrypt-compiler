/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Generic verified linear-combination / inner-product evaluation

The abstract core of a multi-scalar multiplication (MSM) and of a dot product is
the same operation: a coefficient-weighted sum `Σ kᵢ • Pᵢ` over a module.  This
file develops that operation generically, over an arbitrary
`[CommRing R] [AddCommMonoid M] [Module R M]`, as a list fold:

  `linComb coeffs pts = Σ kᵢ • Pᵢ`

and proves the structural laws a rewrite/optimizer pass needs:

* the fold/`cons` recursion (`linComb_nil`, `linComb_cons`);
* equality with the list-`sum` of the term map (`linComb_eq_sum`), the
  Horner/fold = explicit-sum bridge;
* the **append / recombination** law (`linComb_append`), the bucket-partition
  identity at the heart of Pippenger/Straus MSM scheduling — here at the
  generic module level.

## Specializations

* At `M = R` (with `R` acting on itself), `k • p = k * p`, so `linComb` is the
  **dot product** `Σ kᵢ * pᵢ` of two coefficient lists.
* At `M` an elliptic-curve point group — an `AddCommGroup`, hence a `ℤ`-module —
  `linComb` is the **MSM** `Σ kᵢ · Pᵢ`.  The concrete EC instance of the
  recombination law `linComb_append` is
  `CatCrypt.Crypto.Pairing.BLS12381MsmEmit.msm_append` (Pippenger sub-MSM
  recombination over a curve point list); this file is its module-generic core.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.LinearCombGeneric

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [Module R M]

/-- The coefficient-weighted sum `Σ kᵢ • Pᵢ`, as a fold over the zipped
    coefficient/point lists.  Excess coefficients or points (when the lists have
    unequal lengths) are dropped by `List.zip`. -/
def linComb (coeffs : List R) (pts : List M) : M :=
  (coeffs.zip pts).foldr (fun kp acc => kp.1 • kp.2 + acc) 0

@[simp]
theorem linComb_nil_left (pts : List M) : linComb ([] : List R) pts = 0 := by
  simp [linComb]

@[simp]
theorem linComb_nil_right (coeffs : List R) : linComb coeffs ([] : List M) = 0 := by
  simp [linComb]

/-- The `cons` recursion: the head term `k • p` is group-added to the tail
    combination.  This is the fold step made explicit. -/
@[simp]
theorem linComb_cons (k : R) (ks : List R) (p : M) (ps : List M) :
    linComb (k :: ks) (p :: ps) = k • p + linComb ks ps := by
  simp [linComb]

/-- **Fold = explicit sum.**  The fold-form linear combination equals the
    list-`sum` of the per-term scalar multiples — the bridge between the
    Horner/accumulator evaluation and the `Σ` notation. -/
theorem linComb_eq_sum (coeffs : List R) (pts : List M) :
    linComb coeffs pts = ((coeffs.zip pts).map (fun kp => kp.1 • kp.2)).sum := by
  unfold linComb
  induction coeffs.zip pts with
  | nil => simp
  | cons kp rest ih => simp [ih]

/-- **The recombination / bucket-partition law.**  When the coefficient and
    point lists split at the same boundary, the linear combination of the
    concatenation is the group sum of the two sub-combinations.  This is the
    generic-module form of the Pippenger sub-MSM recombination (and, at
    `M = R`, of dot-product splitting).

    The length hypothesis `ks₁.length = ps₁.length` ensures `zip` does not
    straddle the split point. -/
theorem linComb_append (ks₁ ks₂ : List R) (ps₁ ps₂ : List M)
    (h : ks₁.length = ps₁.length) :
    linComb (ks₁ ++ ks₂) (ps₁ ++ ps₂) = linComb ks₁ ps₁ + linComb ks₂ ps₂ := by
  rw [linComb_eq_sum, linComb_eq_sum, linComb_eq_sum, ← List.sum_append,
    ← List.map_append, List.zip_append h]

/-! ## Dot-product specialization (`M = R`)

At `M = R`, scalar multiplication is ring multiplication, so `linComb` is the
inner product of two coefficient lists.  The structural laws above transfer
verbatim. -/

/-- The inner / dot product `Σ aᵢ * bᵢ` is the `linComb` instance at `M = R`. -/
def dotProduct (a b : List R) : R := linComb a b

theorem dotProduct_eq_linComb (a b : List R) : dotProduct a b = linComb a b := rfl

/-- The dot product splits over a common-boundary append — the `M = R` instance
    of `linComb_append`. -/
theorem dotProduct_append (a₁ a₂ b₁ b₂ : List R) (h : a₁.length = b₁.length) :
    dotProduct (a₁ ++ a₂) (b₁ ++ b₂) = dotProduct a₁ b₁ + dotProduct a₂ b₂ :=
  linComb_append a₁ a₂ b₁ b₂ h

/-- A dot-product term is `aᵢ • bᵢ = aᵢ * bᵢ` at `M = R`; spelled out so the
    inner-product reading of `linComb` is checkable. -/
example (k : R) (ks : List R) (p : R) (ps : List R) :
    dotProduct (k :: ks) (p :: ps) = k * p + dotProduct ks ps := by
  simp [dotProduct, smul_eq_mul]

end CatCrypt.Crypto.Optimizer.Rewrite.LinearCombGeneric
