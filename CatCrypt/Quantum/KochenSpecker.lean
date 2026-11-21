/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

set_option autoImplicit false

/-!
# The Kochen–Specker theorem in dimension four

Cabello, Estebaranz and García-Alcaine gave eighteen vectors of `ℝ⁴` with entries in
`{-1, 0, 1}` that form nine orthogonal bases, each vector lying in exactly two of the
bases. A non-contextual `{0, 1}` valuation would give the value `1` to exactly one vector
of each basis; summing over the bases counts `9` ones, while counting by vectors gives an
even number. Hence no such valuation exists. The theorem of this module states it in `ℂ⁴`: no
function on vectors of `ℂ⁴` assigns `1` to exactly one vector of every orthogonal basis.

## Main definitions

* `cabelloVec` — the eighteen vectors, as integer vectors.
* `cabelloBasis` — the nine bases, as four indices each.

## Main results

* `cabelloBasis_orthogonal`, `cabelloVec_ne_zero` — each listed basis consists of
  pairwise orthogonal nonzero vectors.
* `card_cabelloBasis_fiber` — each vector lies in exactly two bases.
* `no_cabello_valuation` — no `{0, 1}` valuation of the eighteen vectors assigns `1` to
  exactly one vector of each of the nine bases.
* `kochenSpecker_complex` — the Kochen–Specker theorem in `ℂ⁴`: no function on vectors of
  `ℂ⁴` assigns `true` to exactly one member of every family of four pairwise orthogonal
  nonzero vectors.

## References

* Kochen, Specker, *The problem of hidden variables in quantum mechanics*, J. Math. Mech.
  17 (1967)
* Cabello, Estebaranz, García-Alcaine, *Bell–Kochen–Specker theorem: a proof with 18
  vectors*, Phys. Lett. A 212 (1996)
-/

open Matrix

namespace CatCrypt.Quantum.KochenSpecker

/-- The eighteen vectors of the Cabello–Estebaranz–García-Alcaine set. -/
def cabelloVec : Fin 18 → Fin 4 → ℤ :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![1, 1, 0, 0], ![1, -1, 0, 0], ![0, 1, 0, 0],
    ![1, 0, 1, 0], ![1, 0, -1, 0], ![1, -1, 1, -1], ![1, -1, -1, 1], ![0, 0, 1, 1],
    ![1, 1, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, 1], ![1, 0, 0, -1], ![0, 1, -1, 0],
    ![1, 1, -1, 1], ![1, 1, 1, -1], ![-1, 1, 1, 1]]

/-- The nine orthogonal bases, each given by the indices of its four vectors. -/
def cabelloBasis : Fin 9 → Fin 4 → Fin 18 :=
  ![![0, 1, 2, 3], ![0, 4, 5, 6], ![7, 8, 2, 9], ![7, 10, 6, 11], ![1, 4, 12, 13],
    ![8, 10, 13, 14], ![15, 16, 3, 9], ![15, 17, 5, 11], ![16, 17, 12, 14]]

/-- The eighteen vectors are pairwise distinct. -/
theorem cabelloVec_injective : Function.Injective cabelloVec := by
  decide

/-- Each vector is nonzero. -/
theorem cabelloVec_ne_zero (k : Fin 18) : cabelloVec k ≠ 0 := by
  revert k; decide

/-- The four vectors of each basis are pairwise orthogonal. -/
theorem cabelloBasis_orthogonal (b : Fin 9) (i j : Fin 4) (hij : i ≠ j) :
    cabelloVec (cabelloBasis b i) ⬝ᵥ cabelloVec (cabelloBasis b j) = 0 := by
  revert b i j; decide

/-- Each vector lies in exactly two of the nine bases. -/
theorem card_cabelloBasis_fiber (k : Fin 18) :
    (Finset.univ.filter fun p : Fin 9 × Fin 4 => cabelloBasis p.1 p.2 = k).card = 2 := by
  revert k; decide

/-- **Kochen–Specker for the eighteen vectors.** No `{0, 1}` valuation assigns `1` to
exactly one vector of each of the nine bases. -/
theorem no_cabello_valuation (f : Fin 18 → Bool) :
    ¬ ∀ b : Fin 9, ∃! i : Fin 4, f (cabelloBasis b i) = true := by
  intro h
  let g : Fin 18 → ℕ := fun k => if f k = true then 1 else 0
  have hrow : ∀ b, ∑ i, g (cabelloBasis b i) = 1 := by
    intro b
    obtain ⟨i, hi, huniq⟩ := h b
    rw [Finset.sum_eq_single i]
    · simp [g, hi]
    · intro j _ hji
      have : f (cabelloBasis b j) ≠ true := fun hj => hji (huniq j hj)
      simp [g, this]
    · simp
  have htotal : ∑ p : Fin 9 × Fin 4, g (cabelloBasis p.1 p.2) = 9 := by
    rw [Fintype.sum_prod_type]
    simp [hrow]
  have hfiber : ∑ p : Fin 9 × Fin 4, g (cabelloBasis p.1 p.2) = ∑ k, 2 * g k := by
    rw [← Finset.sum_fiberwise Finset.univ (fun p : Fin 9 × Fin 4 => cabelloBasis p.1 p.2)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => g k) (fun p hp => by
      rw [(Finset.mem_filter.mp hp).2]), Finset.sum_const, card_cabelloBasis_fiber,
      smul_eq_mul]
  rw [hfiber, ← Finset.mul_sum] at htotal
  omega

/-- The eighteen vectors as vectors of `ℂ⁴`. -/
def cabelloVecC (k : Fin 18) : Fin 4 → ℂ := fun i => (cabelloVec k i : ℂ)

theorem cabelloVecC_ne_zero (k : Fin 18) : cabelloVecC k ≠ 0 := by
  intro h
  apply cabelloVec_ne_zero k
  funext i
  have := congrFun h i
  simpa [cabelloVecC] using this

theorem cabelloVecC_orthogonal (b : Fin 9) (i j : Fin 4) (hij : i ≠ j) :
    star (cabelloVecC (cabelloBasis b i)) ⬝ᵥ cabelloVecC (cabelloBasis b j) = 0 := by
  have h := cabelloBasis_orthogonal b i j hij
  have hc : ((cabelloVec (cabelloBasis b i) ⬝ᵥ cabelloVec (cabelloBasis b j) : ℤ) : ℂ) = 0 := by
    rw [h, Int.cast_zero]
  rw [← hc]
  simp [dotProduct, cabelloVecC, Pi.star_apply]

/-- **The Kochen–Specker theorem in `ℂ⁴`.** No function on vectors of `ℂ⁴` assigns
`true` to exactly one member of every family of four pairwise orthogonal nonzero
vectors. -/
theorem kochenSpecker_complex (f : (Fin 4 → ℂ) → Bool) :
    ¬ ∀ v : Fin 4 → Fin 4 → ℂ, (∀ i, v i ≠ 0) →
      (∀ i j, i ≠ j → star (v i) ⬝ᵥ v j = 0) → ∃! i, f (v i) = true := by
  intro h
  apply no_cabello_valuation (fun k => f (cabelloVecC k))
  intro b
  exact h (fun i => cabelloVecC (cabelloBasis b i)) (fun i => cabelloVecC_ne_zero _)
    (fun i j hij => cabelloVecC_orthogonal b i j hij)

end CatCrypt.Quantum.KochenSpecker
