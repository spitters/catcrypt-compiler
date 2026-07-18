/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Quantum.Instrument
import CatCrypt.Quantum.UnitaryChannel
import CatCrypt.Quantum.TensorProduct
import CatCrypt.Tactic.MatrixDecide
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

/-!
# Qubit Infrastructure

Standard qubit definitions: basis states, Pauli gates, Hadamard, CNOT, and Bell states.
All quantum programs in `CatCrypt.Quantum.Programs` build on these primitives.

## Main Definitions

* `Ket`, `ketbra`, `densityOf` — pure state infrastructure
* `pauliX`, `pauliY`, `pauliZ` — Pauli matrices
* `hadamard` — Hadamard gate
* `cnot` — CNOT gate on 2-qubit system
* `bellPhiPlusKet` etc. — Bell basis states
* `maxMixed` — maximally mixed state I/d

## References

* Nielsen & Chuang — Quantum Computation and Quantum Information, Chapter 1
-/

open scoped Matrix ComplexOrder
open Matrix Complex

noncomputable section

namespace CatCrypt.Quantum.Programs.Qubit

/-! ## Kets and Pure State Infrastructure -/

/-- A ket vector in d-dimensional Hilbert space. -/
abbrev Ket (d : ℕ) := Fin d → ℂ

/-- Outer product |ψ⟩⟨φ| as a d×d matrix. -/
def ketbra {d : ℕ} (ψ φ : Ket d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => ψ i * starRingEnd ℂ (φ j)

/-- Density matrix |ψ⟩⟨ψ| from a pure state. -/
def densityOf {d : ℕ} (ψ : Ket d) : Matrix (Fin d) (Fin d) ℂ :=
  ketbra ψ ψ

/-- Inner product ⟨φ|ψ⟩. -/
def braket {d : ℕ} (φ ψ : Ket d) : ℂ :=
  ∑ i : Fin d, starRingEnd ℂ (φ i) * ψ i

/-- A ket is normalized if ⟨ψ|ψ⟩ = 1. -/
def IsNormalized {d : ℕ} (ψ : Ket d) : Prop := braket ψ ψ = 1

/-- Two kets are orthogonal if ⟨φ|ψ⟩ = 0. -/
def AreOrthogonal {d : ℕ} (φ ψ : Ket d) : Prop := braket φ ψ = 0

/-! ## Computational Basis -/

/-- |0⟩ basis state. -/
def ket0 : Ket 2 := ![1, 0]

/-- |1⟩ basis state. -/
def ket1 : Ket 2 := ![0, 1]

/-- |+⟩ = (|0⟩ + |1⟩)/√2. -/
def ketPlus : Ket 2 :=
  let s : ℂ := ↑(1 / Real.sqrt 2)
  ![s, s]

/-- |−⟩ = (|0⟩ − |1⟩)/√2. -/
def ketMinus : Ket 2 :=
  let s : ℂ := ↑(1 / Real.sqrt 2)
  ![s, -s]

/-! ## Single-Qubit Gates -/

/-- Pauli X (NOT gate): |0⟩↦|1⟩, |1⟩↦|0⟩. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![0, 1], ![1, 0]]

/-- Pauli Y: |0⟩↦i|1⟩, |1⟩↦−i|0⟩. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![0, -Complex.I], ![Complex.I, 0]]

/-- Pauli Z: |0⟩↦|0⟩, |1⟩↦−|1⟩. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![1, 0], ![0, -1]]

/-- Hadamard gate: |0⟩↦|+⟩, |1⟩↦|−⟩. -/
def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  let s : ℂ := ↑(1 / Real.sqrt 2)
  Matrix.of ![![s, s], ![s, -s]]

/-- Phase gate S: |0⟩↦|0⟩, |1⟩↦i|1⟩. -/
def phaseS : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![1, 0], ![0, Complex.I]]

/-- T gate: |0⟩↦|0⟩, |1⟩↦e^{iπ/4}|1⟩. -/
def tGate : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![1, 0], ![0, Complex.exp (Complex.I * ↑(Real.pi / 4))]]

/-! ## Two-Qubit Gates -/

/-- CNOT gate on 4-dimensional space (2 qubits, control ⊗ target).
    |00⟩↦|00⟩, |01⟩↦|01⟩, |10⟩↦|11⟩, |11⟩↦|10⟩. -/
def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![1,0,0,0], ![0,1,0,0], ![0,0,0,1], ![0,0,1,0]]

/-- SWAP gate: |ij⟩ ↦ |ji⟩. -/
def swap : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![1,0,0,0], ![0,0,1,0], ![0,1,0,0], ![0,0,0,1]]

/-! ## Bell States -/

/-- Bell state |Φ⁺⟩ = (|00⟩ + |11⟩)/√2 as a ket on ℂ⁴. -/
def bellPhiPlusKet : Ket 4 :=
  let s : ℂ := ↑(1 / Real.sqrt 2)
  ![s, 0, 0, s]

/-- Bell state |Φ⁻⟩ = (|00⟩ − |11⟩)/√2. -/
def bellPhiMinusKet : Ket 4 :=
  let s : ℂ := ↑(1 / Real.sqrt 2)
  ![s, 0, 0, -s]

/-- Bell state |Ψ⁺⟩ = (|01⟩ + |10⟩)/√2. -/
def bellPsiPlusKet : Ket 4 :=
  let s : ℂ := ↑(1 / Real.sqrt 2)
  ![0, s, s, 0]

/-- Bell state |Ψ⁻⟩ = (|01⟩ − |10⟩)/√2. -/
def bellPsiMinusKet : Ket 4 :=
  let s : ℂ := ↑(1 / Real.sqrt 2)
  ![0, s, -s, 0]

/-- Bell state |Φ⁺⟩⟨Φ⁺| as density matrix. -/
def bellPhiPlus : Matrix (Fin 4) (Fin 4) ℂ := densityOf bellPhiPlusKet

/-- Bell state |Ψ⁺⟩⟨Ψ⁺| as density matrix. -/
def bellPsiPlus : Matrix (Fin 4) (Fin 4) ℂ := densityOf bellPsiPlusKet

/-! ## Maximally Mixed State -/

/-- Maximally mixed state I/d. -/
def maxMixed (d : ℕ) [NeZero d] : Matrix (Fin d) (Fin d) ℂ :=
  (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)

/-! ## Two-Qubit Kets from Single-Qubit Kets -/

/-- Tensor product of two single-qubit kets: |ψ⟩ ⊗ |φ⟩ as a ket on ℂ⁴. -/
def tensorKet (ψ : Ket 2) (φ : Ket 2) : Ket 4 :=
  fun k =>
    let ⟨i, j⟩ := (TensorProduct.finProdEquiv 2 2).symm k
    ψ i * φ j

/-! ## Basic Properties -/

@[grind =]
theorem ketbra_conjTranspose {d : ℕ} (ψ φ : Ket d) :
    (ketbra ψ φ)ᴴ = ketbra φ ψ := by
  ext i j; simp [ketbra, conjTranspose_apply, of_apply, mul_comm]

theorem densityOf_hermitian {d : ℕ} (ψ : Ket d) :
    (densityOf ψ).IsHermitian := by
  rw [Matrix.IsHermitian]; exact ketbra_conjTranspose ψ ψ

@[grind =]
theorem densityOf_trace {d : ℕ} (ψ : Ket d) :
    (densityOf ψ).trace = braket ψ ψ := by
  simp [densityOf, ketbra, Matrix.trace, Matrix.diag, braket, of_apply, mul_comm]

/-- Pure state density matrix from normalized ket has trace 1. -/
theorem densityOf_trace_one {d : ℕ} (ψ : Ket d) (hψ : IsNormalized ψ) :
    (densityOf ψ).trace = 1 := by
  rw [densityOf_trace, hψ]

/-- Pauli X is self-inverse: X² = I. -/
@[grind =]
theorem pauliX_sq : pauliX * pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, of_apply, Fin.sum_univ_two]

/-- Pauli Z is self-inverse: Z² = I. -/
@[grind =]
theorem pauliZ_sq : pauliZ * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, of_apply, Fin.sum_univ_two]

/-- Pauli X is self-adjoint: X† = X. -/
@[grind =]
theorem pauliX_hermitian : pauliXᴴ = pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, conjTranspose_apply, of_apply]

/-- Pauli Z is self-adjoint: Z† = Z. -/
@[grind =]
theorem pauliZ_hermitian : pauliZᴴ = pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, conjTranspose_apply, of_apply]

/-- XZ = −ZX (anticommutation). -/
@[grind =]
theorem pauliX_pauliZ_anticommute :
    pauliX * pauliZ = -(pauliZ * pauliX) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ, Matrix.mul_apply, of_apply, Fin.sum_univ_two, neg_apply]

set_option maxHeartbeats 1600000 in
private theorem bell_ket_aux (k : Fin 4) : (∑ i : Fin 4, cnot k i *
    (TensorProduct.kronecker hadamard 1) i
      ((TensorProduct.finProdEquiv 2 2) (0, 0))) = bellPhiPlusKet k := by
  fin_cases k <;>
    simp only [cnot, hadamard, bellPhiPlusKet, TensorProduct.kronecker,
      TensorProduct.finProdEquiv, finProdFinEquiv,
      Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_four, Fin.isValue,
      Fin.divNat, Fin.modNat,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.vecHead, Matrix.vecTail, Matrix.empty_val',
      Fin.val_mk, Fin.mk_zero, Fin.mk_one] <;>
    norm_num <;> rfl

/-- Bell state |Φ⁺⟩ is created from |00⟩ by (H ⊗ I) then CNOT. -/
theorem bellPhiPlus_eq_cnot_hadamard :
    bellPhiPlus =
      let ψ₀ := tensorKet ket0 ket0
      densityOf (fun k => ∑ i : Fin 4, cnot k i *
        (TensorProduct.kronecker hadamard 1) i
          ((TensorProduct.finProdEquiv 2 2) (0, 0))) := by
  show bellPhiPlus = densityOf _
  have h : (fun k => ∑ i : Fin 4, cnot k i *
    (TensorProduct.kronecker hadamard 1) i
      ((TensorProduct.finProdEquiv 2 2) (0, 0))) = bellPhiPlusKet :=
    funext bell_ket_aux
  rw [h]; rfl

end CatCrypt.Quantum.Programs.Qubit
