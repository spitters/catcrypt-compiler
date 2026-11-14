/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.PartialTrace
public import CatCryptCore.Quantum.ChoiKraus

@[expose] public section

set_option autoImplicit false

/-!
# The no-communication theorem

A bipartite state `ρ` on `ℂ^{dA} ⊗ ℂ^{dB}` is a matrix on `Fin (dA * dB)`. A linear map
`Φ` on Alice's matrices acts on the bipartite system as `Φ ⊗ id`, which applies `Φ` to
every `dA × dA` block of `ρ`. Whatever trace-preserving operation Alice performs, Bob's
reduced state `tr_A ρ` does not change, so no measurement of Bob depends on Alice's
choice of operation.

## Main definitions

* `aliceLocal Φ` — the map `Φ ⊗ id` on bipartite matrices.

## Main results

* `aliceLocal_kronecker` — `(Φ ⊗ id)(A ⊗ B) = Φ A ⊗ B`.
* `aliceLocal_kraus` — for a Kraus sum `Φ ρ = ∑ K ρ Kᴴ`, `Φ ⊗ id` is the Kraus sum of
  the operators `K ⊗ 1`.
* `partialTrace₁_aliceLocal` — the no-communication theorem: for every trace-preserving
  linear map `Φ` on Alice's factor (in particular every CPTP map, `no_communication`),
  `tr_A ((Φ ⊗ id) ρ) = tr_A ρ`.
* `no_communication_kraus` — the same for a complete Kraus family `∑ Kᴴ K = 1`.
* `trace_bob_aliceLocal` — Bob's expectation values `tr((1 ⊗ M) ρ)` are unchanged.

## References

* Peres, Terno, *Quantum information and relativity theory*, Rev. Mod. Phys. 76 (2004)
* Nielsen, Chuang, *Quantum Computation and Quantum Information*, Box 2.5
-/

open scoped Matrix
open Matrix CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.PartialTrace

noncomputable section

namespace CatCrypt.Quantum.NoCommunication

variable {dA dA' dB : ℕ}

/-- The extension `Φ ⊗ id` of a linear map `Φ` on Alice's factor to bipartite matrices:
the `(i₂, j₂)` block of the output is `Φ` of the `(i₂, j₂)` block of the input. -/
def aliceLocal (Φ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin dA') (Fin dA') ℂ) :
    Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ →ₗ[ℂ]
      Matrix (Fin (dA' * dB)) (Fin (dA' * dB)) ℂ where
  toFun ρ := Matrix.of fun i j =>
    Φ (extractBlock ρ ((finProdEquiv dA' dB).symm i).2 ((finProdEquiv dA' dB).symm j).2)
      ((finProdEquiv dA' dB).symm i).1 ((finProdEquiv dA' dB).symm j).1
  map_add' ρ₁ ρ₂ := by
    ext i j
    simp [extractBlock_add, map_add]
  map_smul' c ρ := by
    ext i j
    simp [extractBlock_smul, map_smul]

theorem aliceLocal_apply
    (Φ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin dA') (Fin dA') ℂ)
    (ρ : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) (i j : Fin (dA' * dB)) :
    aliceLocal Φ ρ i j =
      Φ (extractBlock ρ ((finProdEquiv dA' dB).symm i).2 ((finProdEquiv dA' dB).symm j).2)
        ((finProdEquiv dA' dB).symm i).1 ((finProdEquiv dA' dB).symm j).1 :=
  rfl

/-- The blocks of `(Φ ⊗ id) ρ` are the images of the blocks of `ρ`. -/
theorem extractBlock_aliceLocal
    (Φ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin dA') (Fin dA') ℂ)
    (ρ : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) (i₂ j₂ : Fin dB) :
    extractBlock (aliceLocal Φ ρ) i₂ j₂ = Φ (extractBlock ρ i₂ j₂) := by
  ext i₁ j₁
  simp [extractBlock_apply, aliceLocal_apply]

/-- `Φ ⊗ id` sends a product `A ⊗ B` to `Φ A ⊗ B`. -/
theorem aliceLocal_kronecker
    (Φ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin dA') (Fin dA') ℂ)
    (A : Matrix (Fin dA) (Fin dA) ℂ) (B : Matrix (Fin dB) (Fin dB) ℂ) :
    aliceLocal Φ (A ⊗ₖ B) = Φ A ⊗ₖ B := by
  ext i j
  simp [aliceLocal_apply, extractBlock_kronecker, TensorProduct.kronecker_apply, mul_comm]

/-- **No-communication theorem.** For every trace-preserving linear map `Φ` on Alice's
factor, Bob's reduced state is unchanged: `tr_A ((Φ ⊗ id) ρ) = tr_A ρ`. -/
theorem partialTrace₁_aliceLocal
    (Φ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin dA') (Fin dA') ℂ)
    (hTP : ∀ X, (Φ X).trace = X.trace)
    (ρ : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    partialTrace₁ (aliceLocal Φ ρ) = partialTrace₁ ρ := by
  ext i₂ j₂
  have h := hTP (extractBlock ρ i₂ j₂)
  simp only [Matrix.trace, Matrix.diag, extractBlock_apply] at h
  simpa [partialTrace₁_apply, aliceLocal_apply] using h

/-- **No-communication theorem for channels**: for every CPTP map `Φ` on Alice's factor
and every bipartite state `ρ`, Bob's reduced state of `(Φ ⊗ id) ρ` is that of `ρ`. -/
theorem no_communication
    (Φ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin dA) (Fin dA) ℂ)
    (_hCP : IsCPMap Φ) (hTP : IsTP Φ)
    (ρ : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    partialTrace₁ (aliceLocal Φ ρ) = partialTrace₁ ρ :=
  partialTrace₁_aliceLocal Φ hTP ρ

/-- Bob's expectation values do not depend on Alice's trace-preserving operation:
`tr((1 ⊗ M) (Φ ⊗ id) ρ) = tr((1 ⊗ M) ρ)` for every matrix `M` on Bob's factor. -/
theorem trace_bob_aliceLocal
    (Φ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin dA') (Fin dA') ℂ)
    (hTP : ∀ X, (Φ X).trace = X.trace)
    (ρ : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) (M : Matrix (Fin dB) (Fin dB) ℂ) :
    (((1 : Matrix (Fin dA') (Fin dA') ℂ) ⊗ₖ M) * aliceLocal Φ ρ).trace =
      (((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ M) * ρ).trace := by
  rw [trace_one_kronecker_mul, trace_one_kronecker_mul]
  have key : ∀ X : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ,
      ∑ k : Fin dA, (M * extractBlock₁ X k k).trace = (M * partialTrace₁ X).trace := by
    intro X
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, extractBlock₁_apply,
      partialTrace₁_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.sum_comm]
  have key' : ∀ X : Matrix (Fin (dA' * dB)) (Fin (dA' * dB)) ℂ,
      ∑ k : Fin dA', (M * extractBlock₁ X k k).trace = (M * partialTrace₁ X).trace := by
    intro X
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, extractBlock₁_apply,
      partialTrace₁_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.sum_comm]
  rw [key, key', partialTrace₁_aliceLocal Φ hTP]

/-- Two bipartite matrices with the same blocks are equal. -/
theorem eq_of_extractBlock_eq {X Y : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ}
    (h : ∀ i₂ j₂, extractBlock X i₂ j₂ = extractBlock Y i₂ j₂) : X = Y := by
  ext i j
  have := congrFun (congrFun (h ((finProdEquiv dA dB).symm i).2
    ((finProdEquiv dA dB).symm j).2) ((finProdEquiv dA dB).symm i).1)
    ((finProdEquiv dA dB).symm j).1
  simpa [extractBlock_apply] using this

/-- A sum over the composite index is a sum over pairs. -/
theorem sum_finProd {M : Type*} [AddCommMonoid M] (f : Fin (dA * dB) → M) :
    ∑ k, f k = ∑ k₁ : Fin dA, ∑ k₂ : Fin dB, f (finProdEquiv dA dB (k₁, k₂)) := by
  rw [← Fintype.sum_prod_type', ← (finProdEquiv dA dB).sum_comp]

/-- The blocks of `(A ⊗ 1) Y` are `A Yᵢⱼ`. -/
theorem extractBlock_kronecker_one_mul (A : Matrix (Fin dA) (Fin dA) ℂ)
    (Y : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) (i₂ j₂ : Fin dB) :
    extractBlock ((A ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) * Y) i₂ j₂ =
      A * extractBlock Y i₂ j₂ := by
  ext i₁ j₁
  simp only [extractBlock_apply, Matrix.mul_apply]
  rw [sum_finProd]
  simp [TensorProduct.kronecker_apply, Matrix.one_apply]

/-- The blocks of `Y (A ⊗ 1)ᴴ` are `Yᵢⱼ Aᴴ`. -/
theorem extractBlock_mul_kronecker_one (A : Matrix (Fin dA) (Fin dA) ℂ)
    (Y : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) (i₂ j₂ : Fin dB) :
    extractBlock (Y * (A ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ))ᴴ) i₂ j₂ =
      extractBlock Y i₂ j₂ * Aᴴ := by
  ext i₁ j₁
  simp only [extractBlock_apply, Matrix.mul_apply]
  rw [sum_finProd]
  simp [TensorProduct.kronecker_apply, Matrix.one_apply, conjTranspose_apply, apply_ite,
    Finset.sum_ite_eq]

/-- The blocks of `(A ⊗ 1) X (A ⊗ 1)ᴴ` are `A Xᵢⱼ Aᴴ`. -/
theorem extractBlock_kronecker_one_conj (A : Matrix (Fin dA) (Fin dA) ℂ)
    (X : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) (i₂ j₂ : Fin dB) :
    extractBlock ((A ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) * X *
      (A ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ))ᴴ) i₂ j₂ = A * extractBlock X i₂ j₂ * Aᴴ := by
  rw [extractBlock_mul_kronecker_one, extractBlock_kronecker_one_mul]

/-- `Φ ⊗ id` of a Kraus sum is the Kraus sum of the operators `K ⊗ 1`. -/
theorem aliceLocal_kraus {ι : Type} [Fintype ι]
    (Φ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin dA) (Fin dA) ℂ)
    (K : ι → Matrix (Fin dA) (Fin dA) ℂ) (hK : ∀ X, Φ X = ∑ x, K x * X * (K x)ᴴ)
    (ρ : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    aliceLocal Φ ρ = ∑ x, (K x ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) * ρ *
      (K x ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ))ᴴ := by
  refine eq_of_extractBlock_eq fun i₂ j₂ => ?_
  rw [extractBlock_aliceLocal, hK]
  have hsum : ∀ (f : ι → Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ),
      extractBlock (∑ x, f x) i₂ j₂ = ∑ x, extractBlock (f x) i₂ j₂ := by
    intro f
    ext a b
    simp [extractBlock_apply, Matrix.sum_apply]
  rw [hsum]
  exact Finset.sum_congr rfl fun x _ => (extractBlock_kronecker_one_conj (K x) ρ i₂ j₂).symm

/-- **No-communication theorem, Kraus form**: for a complete Kraus family on Alice's
factor (`∑ Kᴴ K = 1`), `tr_A (∑ (K ⊗ 1) ρ (K ⊗ 1)ᴴ) = tr_A ρ`. -/
theorem no_communication_kraus {ι : Type} [Fintype ι]
    (K : ι → Matrix (Fin dA) (Fin dA) ℂ) (hK : ∑ x, (K x)ᴴ * K x = 1)
    (ρ : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    partialTrace₁ (∑ x, (K x ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) * ρ *
      (K x ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ))ᴴ) = partialTrace₁ ρ := by
  rw [map_sum]
  simpa using sum_partialTrace₁_kronecker_conj K 1 1 hK ρ

end CatCrypt.Quantum.NoCommunication
