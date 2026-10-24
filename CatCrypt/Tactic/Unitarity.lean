/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


@[expose] public section
set_option autoImplicit false

/-!
# Unitarity for Hermitian Involutory Exponentials

If `H` is Hermitian (`H† = H`) and involutory (`H * H = I`), then
`cos(θ) • I + (-I * sin(θ)) • H` is unitary.

This pattern covers Pauli exponentials, signal rotations, and cost unitaries.
-/

open scoped Matrix
open Matrix Complex

noncomputable section

namespace CatCrypt.Tactic.Unitarity

variable {d : ℕ}

/-- `cos(θ)·I - i·sin(θ)·H` is unitary when H† = H and H² = I. -/
theorem cos_sub_isin_mul_unitary
    (H : Matrix (Fin d) (Fin d) ℂ)
    (hHerm : Hᴴ = H)
    (hInvol : H * H = 1)
    (θ : ℝ) :
    let U := (↑(Real.cos θ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
             (-I * ↑(Real.sin θ)) • H
    U * Uᴴ = 1 := by
  simp only
  -- Expand Uᴴ
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul,
      conjTranspose_one, hHerm]
  -- star(cos θ) = cos θ (real), star(-I * sin θ) = I * sin θ
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_I, map_neg, map_mul, neg_neg]
  -- Goal: (cos θ • I + (-I * sin θ) • H)(cos θ • I + (I * sin θ) • H) = I
  -- Expand using distributivity
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    Matrix.one_mul, Matrix.mul_one, hInvol]
  -- Collect terms: cos²·I + cos·sin·(I - I)·H + sin²·I = I
  simp only [smul_smul, smul_add, ← add_smul]
  -- Use I² = -1 and cos² + sin² = 1
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  ring_nf
  simp only [Complex.I_sq, Complex.ofReal_cos, Complex.ofReal_sin]
  split_ifs <;> simp [Complex.cos_sq_add_sin_sq]

/-- Product of two unitaries is unitary. -/
theorem mul_unitary {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A * Aᴴ = 1) (hB : B * Bᴴ = 1) :
    (A * B) * (A * B)ᴴ = 1 := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB, Matrix.one_mul, hA]

/-- Product of a list of unitaries is unitary. -/
theorem list_prod_unitary {d : ℕ} (l : List (Matrix (Fin d) (Fin d) ℂ))
    (h : ∀ U ∈ l, U * Uᴴ = 1) :
    l.prod * l.prodᴴ = 1 := by
  induction l with
  | nil => simp
  | cons U l ih =>
    simp only [List.prod_cons]
    exact mul_unitary U l.prod (h U (.head l))
      (ih (fun V hV => h V (.tail U hV)))

/-- A diagonal matrix with unit-norm entries is unitary. -/
theorem diagonal_unit_unitary {d : ℕ} (f : Fin d → ℂ)
    (hf : ∀ i, ‖f i‖ = 1) :
    Matrix.diagonal f * (Matrix.diagonal f)ᴴ = 1 := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal, Matrix.one_apply]
  split_ifs with h
  · subst h
    simp only [Matrix.of_apply, ite_true]
    change f i * starRingEnd ℂ (f i) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp [hf i]
  · simp [Matrix.of_apply, h]

/-- Negation of a unitary is unitary. -/
theorem neg_unitary {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A * Aᴴ = 1) :
    (-A) * (-A)ᴴ = 1 := by
  rw [conjTranspose_neg, neg_mul_neg]
  exact hA

end CatCrypt.Tactic.Unitarity
