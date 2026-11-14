/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.Matrix.Schmidt
public import CatCrypt.Quantum.NoCommunication
public import CatCryptCore.Quantum.Stinespring

@[expose] public section

set_option autoImplicit false

/-!
# Schmidt decomposition of bipartite vectors and the unitary freedom of purifications

A vector `ψ` on `Fin (dA * dB)` has the coefficient matrix `coeff ψ i j = ψ (i, j)`; its
reduced state on the first factor is `tr_B |ψ⟩⟨ψ| = coeff ψ (coeff ψ)ᴴ`, and
`(1 ⊗ V) ψ` has coefficient matrix `coeff ψ Vᵀ`. The Schmidt decomposition and the
unitary freedom of `Matrix.exists_unitary_eq_mul_of_mul_conjTranspose_eq` then give the
Schrödinger–HJW theorem: two purifications of the same state on the same ancilla differ by a
unitary on the ancilla.

## Main definitions

* `coeff ψ` — the `dA × dB` coefficient matrix of a bipartite vector.

## Main results

* `schmidt` — every `ψ` on `Fin (dA * dB)` is `∑ₖ sₖ aₖ ⊗ bₖ` with `sₖ > 0` and orthonormal
  families `(aₖ)`, `(bₖ)`.
* `partialTrace₂_vecMulVec` — `tr_B |ψ⟩⟨ψ| = coeff ψ (coeff ψ)ᴴ`.
* `purification_unitary_freedom` — if `tr_B |φ⟩⟨φ| = tr_B |ψ⟩⟨ψ|`, then `φ = (1 ⊗ V) ψ`
  for a unitary `V` on the second factor.
* `exists_purification_unique` — a density matrix on `Fin d` has a unit-norm purification
  `ψ` on `Fin (d * d)`, and every vector with the same reduced state is `(1 ⊗ V) ψ` for a
  unitary `V`.

## References

* Hughston, Jozsa, Wootters, *A complete classification of quantum ensembles having a given
  density matrix*, Phys. Lett. A 183 (1993)
* Nielsen, Chuang, *Quantum Computation and Quantum Information*, Theorem 2.7, Exercise 2.81
-/

open scoped Matrix ComplexOrder
open Matrix CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.PartialTrace

noncomputable section

namespace CatCrypt.Quantum.PurificationFreedom

variable {dA dB : ℕ}

/-- The coefficient matrix `coeff ψ i j = ψ (i, j)` of a bipartite vector. -/
def coeff (ψ : Fin (dA * dB) → ℂ) : Matrix (Fin dA) (Fin dB) ℂ :=
  Matrix.of fun i j => ψ (finProdEquiv dA dB (i, j))

theorem coeff_injective : Function.Injective (coeff : (Fin (dA * dB) → ℂ) → _) := by
  intro ψ φ h
  funext x
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdEquiv dA dB).surjective x
  exact congrFun (congrFun h i) j

/-- **Schmidt decomposition** of a bipartite vector. -/
theorem schmidt (ψ : Fin (dA * dB) → ℂ) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (a : Fin r → Fin dA → ℂ) (b : Fin r → Fin dB → ℂ),
      (∀ k, 0 < s k) ∧
      (∀ k l, star (a k) ⬝ᵥ a l = if k = l then 1 else 0) ∧
      (∀ k l, star (b k) ⬝ᵥ b l = if k = l then 1 else 0) ∧
      ∀ i j, ψ (finProdEquiv dA dB (i, j)) = ∑ k, (s k : ℂ) * a k i * b k j :=
  Matrix.exists_schmidt (coeff ψ)

/-- The reduced state of a pure state: `tr_B |ψ⟩⟨ψ| = coeff ψ (coeff ψ)ᴴ`. -/
theorem partialTrace₂_vecMulVec (ψ : Fin (dA * dB) → ℂ) :
    partialTrace₂ (vecMulVec ψ (star ψ)) = coeff ψ * (coeff ψ)ᴴ := by
  ext i i'
  simp [partialTrace₂_apply, vecMulVec_apply, coeff, mul_apply, conjTranspose_apply]

/-- `(1 ⊗ V) ψ` has coefficient matrix `coeff ψ Vᵀ`. -/
theorem coeff_one_kronecker_mulVec (V : Matrix (Fin dB) (Fin dB) ℂ) (ψ : Fin (dA * dB) → ℂ) :
    coeff (((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ V) *ᵥ ψ) = coeff ψ * Vᵀ := by
  ext i j
  simp only [coeff, Matrix.of_apply, mulVec, dotProduct, mul_apply, transpose_apply]
  rw [NoCommunication.sum_finProd]
  simp [TensorProduct.kronecker_apply, Matrix.one_apply, mul_comm]

/-- **Unitary freedom of purifications (Schrödinger–HJW).** If two vectors on
`Fin (dA * dB)` have the same reduced state on the first factor, they differ by a unitary on
the second factor: `φ = (1 ⊗ V) ψ`. -/
theorem purification_unitary_freedom (ψ φ : Fin (dA * dB) → ℂ)
    (h : partialTrace₂ (vecMulVec φ (star φ)) = partialTrace₂ (vecMulVec ψ (star ψ))) :
    ∃ V ∈ unitaryGroup (Fin dB) ℂ, φ = ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ V) *ᵥ ψ := by
  rw [partialTrace₂_vecMulVec, partialTrace₂_vecMulVec] at h
  obtain ⟨W, hW, hφ⟩ := Matrix.exists_unitary_eq_mul_of_mul_conjTranspose_eq _ _ h
  have hWW : W * star W = 1 := mem_unitaryGroup_iff.mp hW
  refine ⟨Wᵀ, mem_unitaryGroup_iff'.mpr ?_, coeff_injective ?_⟩
  · rw [star_eq_conjTranspose, conjTranspose_transpose_eq_transpose_conjTranspose,
      ← transpose_mul, ← star_eq_conjTranspose, hWW, transpose_one]
  · rw [coeff_one_kronecker_mulVec, transpose_transpose, hφ]

/-- **Purification, existence and uniqueness up to a unitary.** A density matrix `ρ` on
`Fin d` has a unit-norm purification `ψ` on `Fin (d * d)`, and every vector `φ` with
`tr_B |φ⟩⟨φ| = ρ` is `(1 ⊗ V) ψ` for a unitary `V` on the ancilla. -/
theorem exists_purification_unique {d : ℕ} {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ ψ : Fin (d * d) → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ partialTrace₂ (vecMulVec ψ (star ψ)) = ρ ∧
      ∀ φ : Fin (d * d) → ℂ, partialTrace₂ (vecMulVec φ (star φ)) = ρ →
        ∃ V ∈ unitaryGroup (Fin d) ℂ, φ = ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ V) *ᵥ ψ := by
  obtain ⟨ψ, hnorm, hψ⟩ := Stinespring.exists_purification (Equiv.refl _) hρ htr
  have hψ' : partialTrace₂ (vecMulVec ψ (star ψ)) = ρ := by
    rw [hψ, Stinespring.trAnc]
    rfl
  exact ⟨ψ, hnorm, hψ', fun φ hφ => purification_unitary_freedom ψ φ (hφ.trans hψ'.symm)⟩

end CatCrypt.Quantum.PurificationFreedom
