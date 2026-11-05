/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.GateUnitarity
public import CatCrypt.Quantum.Optimization.MixedCommute

/-!
# Projectors and controlled Paulis

The one-qubit projectors `proj0 = |0⟩⟨0|` and `proj1 = |1⟩⟨1|`, their products and sum, and
the matrix `ctrlMatrix c M = |0⟩⟨0|_c ⊗ I + |1⟩⟨1|_c ⊗ M` of `M` controlled on qubit `c`.
A two-qubit embedding whose `4 × 4` matrix is `A ⊗ B + C ⊗ D` is the sum of products of
one-qubit embeddings (`embedGate2_eq_add_mul`); in particular `CNOT c t` is
`P0_c ⊗ I + P1_c ⊗ X_t` and `CZ c t` is `P0_c ⊗ I + P1_c ⊗ Z_t`.

## Main results

* `embedGate2_eq_add_mul` — `embedGate2` of `A ⊗ B + C ⊗ D`.
* `gateEmbedding_CNOT`, `gateEmbedding_CZ` — `CNOT` and `CZ` as controlled Paulis.
* `czGate_mul_self` — `CZ` is an involution.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.Optimization.DisjointCommute
open CatCrypt.Quantum.Optimization.MixedCommute

noncomputable section

namespace CatCrypt.Quantum.ControlledGates

variable {n : ℕ}

/-! ## Projectors and the controlled matrix -/

/-- The projector `|0⟩⟨0|`. -/
def proj0 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![1, 0], ![0, 0]]

/-- The projector `|1⟩⟨1|`. -/
def proj1 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, 0], ![0, 1]]

/-- The matrix `M` controlled on qubit `c`: `|0⟩⟨0|_c ⊗ I + |1⟩⟨1|_c ⊗ M`. -/
def ctrlMatrix (c : Fin n) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  embedGate1 n c proj0 + embedGate1 n c proj1 * M

theorem proj0_mul_proj0 : proj0 * proj0 = proj0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.mul_apply, Fin.sum_univ_two]

theorem proj1_mul_proj1 : proj1 * proj1 = proj1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.mul_apply, Fin.sum_univ_two]

theorem proj0_mul_proj1 : proj0 * proj1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.mul_apply, Fin.sum_univ_two]

theorem proj1_mul_proj0 : proj1 * proj0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.mul_apply, Fin.sum_univ_two]

theorem proj0_add_proj1 : proj0 + proj1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, proj1]

theorem pauliX_proj0_pauliX : pauliX * proj0 * pauliX = proj1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliX_proj1_pauliX : pauliX * proj1 * pauliX = proj0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem embedGate1_proj0_add_proj1 (c : Fin n) :
    embedGate1 n c proj0 + embedGate1 n c proj1 = 1 := by
  rw [← embedGate1_map_add, proj0_add_proj1, embedGate1_one]

theorem isDiagonal_proj0 : IsDiagonal proj0 := by
  intro r c hrc; fin_cases r <;> fin_cases c <;> simp_all [proj0]

theorem isDiagonal_proj1 : IsDiagonal proj1 := by
  intro r c hrc; fin_cases r <;> fin_cases c <;> simp_all [proj1]

/-! ## `CNOT` and `CZ` are controlled Paulis -/

/-- A two-qubit embedding whose `4 × 4` matrix is `A ⊗ B + C ⊗ D` is the corresponding sum
    of products of single-qubit embeddings. -/
theorem embedGate2_eq_add_mul {i j : Fin n} (hij : i ≠ j) (G : Matrix (Fin 4) (Fin 4) ℂ)
    (A B C D : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ a b a' b' : Fin 2,
      G ⟨a.val * 2 + b.val, by omega⟩ ⟨a'.val * 2 + b'.val, by omega⟩
        = A a a' * B b b' + C a a' * D b b') :
    embedGate2 n i j G hij = embedGate1 n i A * embedGate1 n j B
      + embedGate1 n i C * embedGate1 n j D := by
  ext r c
  rw [Matrix.add_apply, embedGate1_mul_apply hij, embedGate1_mul_apply hij,
    CatCrypt.Quantum.Optimization.MixedCommute.embedGate2_apply hij]
  split_ifs
  · exact h _ _ _ _
  · simp

/-- `CNOT` with control `i` and target `j` is `X_j` controlled on `i`. -/
theorem embedGate2_cnot {i j : Fin n} (hij : i ≠ j) :
    embedGate2 n i j cnot hij = ctrlMatrix i (embedGate1 n j pauliX) := by
  rw [ctrlMatrix, ← mul_one (embedGate1 n i proj0), ← embedGate1_one n j]
  refine embedGate2_eq_add_mul hij _ _ _ _ _ fun a b a' b' => ?_
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [cnot, proj0, proj1, pauliX]

/-- `CZ` on `i`, `j` is `Z_j` controlled on `i`. -/
theorem embedGate2_czGate {i j : Fin n} (hij : i ≠ j) :
    embedGate2 n i j czGate hij = ctrlMatrix i (embedGate1 n j pauliZ) := by
  rw [ctrlMatrix, ← mul_one (embedGate1 n i proj0), ← embedGate1_one n j]
  refine embedGate2_eq_add_mul hij _ _ _ _ _ fun a b a' b' => ?_
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [czGate, proj0, proj1, pauliZ]

/-- `CNOT c t` is `X_t` controlled on `c`. -/
theorem gateEmbedding_CNOT {c t : Fin n} (hct : c ≠ t) :
    gateEmbedding (Gate.CNOT c t) = ctrlMatrix c (embedGate1 n t pauliX) := by
  rw [gateEmbedding, dite_eq_right hct, embedGate2_cnot]

/-- `CZ c t` is `Z_t` controlled on `c`. -/
theorem gateEmbedding_CZ {c t : Fin n} (hct : c ≠ t) :
    gateEmbedding (Gate.CZ c t) = ctrlMatrix c (embedGate1 n t pauliZ) := by
  rw [gateEmbedding, dite_eq_right hct, embedGate2_czGate]

end CatCrypt.Quantum.ControlledGates

namespace CatCrypt.Quantum.ZXGraph

/-- The `CZ` matrix is an involution. -/
theorem czGate_mul_self : czGate * czGate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [czGate, Matrix.mul_apply, Fin.sum_univ_four]

end CatCrypt.Quantum.ZXGraph

end
