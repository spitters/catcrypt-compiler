/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Programs.Qubit
public import CatCrypt.Quantum.Programs.Teleportation
public import CatCrypt.Quantum.Measurement

/-!
# Superdense Coding

Formalizes the superdense coding protocol (Bennett & Wiesner, 1992): two
classical bits are transmitted using one qubit and a shared Bell pair.

## Protocol

Given a shared Bell pair |Φ⁺⟩ between Alice and Bob, and 2 classical bits (i, j):

1. **Encoding**: Alice applies the Pauli σᵢⱼ to her qubit:
   - (0,0) → I,  (0,1) → X,  (1,0) → Z,  (1,1) → XZ
2. **Sending**: Alice sends her qubit to Bob.
3. **Decoding**: Bob performs a Bell measurement on both qubits, recovering (i, j).

## Main results

* `encode` — Alice's encoding operation as a unitary channel
* `decode` — Bob's Bell measurement
* `superdense_correctness` — decoding recovers the encoded bits with certainty
* `superdense_capacity` — exactly one outcome has nonzero probability

## References

* Bennett & Wiesner — *Communication via One- and Two-Particle Operators on
  Einstein-Podolsky-Rosen States*, PRL 69(20), 1992
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix
open CatCrypt.Quantum
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.Programs.Teleportation
open CatCrypt.Quantum.TensorProduct

noncomputable section

namespace CatCrypt.Quantum.Programs.SuperdenseCoding

/-- (↑√2)⁻¹ * (↑√2)⁻¹ = (2 : ℂ)⁻¹. Used to close Bell state arithmetic. -/
private theorem sqrt2_inv_sq :
    (↑(Real.sqrt 2) : ℂ)⁻¹ * (↑(Real.sqrt 2))⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast; ring

/-! ## Encoding -/

/-- Alice's encoding: apply Pauli σᵢⱼ to her qubit of the shared Bell pair.
    Defined as σᵢⱼ ⊗ I on the 2-qubit space, given by explicit 4×4 matrices. -/
def encode : Fin 2 → Fin 2 → Matrix (Fin 4) (Fin 4) ℂ
  | 0, 0 => 1  -- I ⊗ I
  | 0, 1 => Matrix.of ![![0,0,1,0], ![0,0,0,1], ![1,0,0,0], ![0,1,0,0]]  -- X ⊗ I
  | 1, 0 => Matrix.of ![![1,0,0,0], ![0,1,0,0], ![0,0,-1,0], ![0,0,0,-1]] -- Z ⊗ I
  | 1, 1 => Matrix.of ![![0,0,-1,0], ![0,0,0,-1], ![1,0,0,0], ![0,1,0,0]] -- XZ ⊗ I

/-- Encoding is unitary: U * U† = I. -/
theorem encode_unitary (i j : Fin 2) :
    encode i j * (encode i j)ᴴ = 1 := by
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [encode, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

/-- Encoding is unitary: U† * U = I. -/
theorem encode_unitary' (i j : Fin 2) :
    (encode i j)ᴴ * encode i j = 1 := by
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [encode, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

/-- After encoding (i,j), the shared Bell pair becomes the (i,j)-th Bell state. -/
theorem encode_bell (i j : Fin 2) :
    encode i j * bellPhiPlus * (encode i j)ᴴ =
      bellMeasOp (i, j) := by
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [encode, bellMeasOp, bellPhiPlus, densityOf, ketbra, bellPhiPlusKet,
      bellPsiPlusKet, bellPhiMinusKet, bellPsiMinusKet, Matrix.mul_apply,
      Fin.sum_univ_four, sqrt2_inv_sq, vecHead, vecTail]

/-! ## Decoding -/

/-- Bob's decoding: Bell measurement on 2 qubits, returning (i,j).

    Constructed as a `measureOps` instrument using the Bell measurement operators.
    The `branch_stp` property follows from `bellMeas_completeness`. -/
def decode : QComp 4 (Fin 2 × Fin 2) :=
  Measurement.measureOps {
    op := fun ⟨i, j⟩ => bellMeasOp (i, j)
    completeness := bellMeas_completeness
  }

/-! ## Full Protocol -/

/-- Superdense coding protocol: encode 2 bits, then decode via Bell measurement.

    Input: classical bits (i, j) and shared Bell pair |Φ⁺⟩
    Output: measured bits (i', j') -/
def superdenseCoding (i j : Fin 2) : QComp 4 (Fin 2 × Fin 2) :=
  QComp.qbind
    (UnitaryChannel.unitaryChannel ⟨encode i j, by
      rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
      exact encode_unitary' i j⟩)
    (fun () => decode)

/-! ## Correctness -/

/-- Bell measurement operators are Hermitian: P† = P. -/
private theorem bellMeasOp_hermitian' (ij : Fin 2 × Fin 2) :
    (bellMeasOp ij)ᴴ = bellMeasOp ij := by
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;>
    simp only [bellMeasOp] <;> exact densityOf_hermitian _

/-- **Superdense coding correctness**: decoding recovers the encoded bits
    with probability 1.

    When the input state is |Φ⁺⟩⟨Φ⁺| and Alice encodes (i, j), Bob's Bell
    measurement returns (i, j) with certainty.

    `tr(P_{i',j'} · (σ_{i,j} |Φ⁺⟩⟨Φ⁺| σ_{i,j}†) · P_{i',j'}†) = δ_{(i,j),(i',j')}`
-/
theorem superdense_correctness (i j : Fin 2) :
    ∀ (i' j' : Fin 2),
      let encodedState := encode i j * bellPhiPlus * (encode i j)ᴴ
      let decodedBranch := decode.branch (i', j') encodedState
      decodedBranch.trace = if i = i' ∧ j = j' then 1 else 0 := by
  intro i' j'
  change (bellMeasOp (i', j') *
    (encode i j * bellPhiPlus * (encode i j)ᴴ) *
    (bellMeasOp (i', j'))ᴴ).trace =
    if i = i' ∧ j = j' then 1 else 0
  rw [encode_bell, bellMeasOp_hermitian']
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp only [bellMeasOp, ite_true, and_self, and_true, true_and] <;>
    simp [densityOf, ketbra, bellPhiPlusKet, bellPsiPlusKet, bellPhiMinusKet, bellPsiMinusKet,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, of_apply, Fin.sum_univ_four,
      sqrt2_inv_sq] <;>
    norm_num

/-- Unique decoding: after encoding `(i, j)`, the only Bell outcome with nonzero
    probability is `(i, j)` itself. -/
theorem superdense_capacity :
    ∀ (i j : Fin 2), ∃! (ij' : Fin 2 × Fin 2),
      (decode.branch ij' (encode i j * bellPhiPlus * (encode i j)ᴴ)).trace ≠ 0
      ∧ ij'.1 = i ∧ ij'.2 = j := by
  intro i j
  refine ⟨⟨i, j⟩, ?_, ?_⟩
  · constructor
    · have := superdense_correctness i j i j
      simp only [ite_true, and_self] at this
      rw [this]; norm_num
    · exact ⟨rfl, rfl⟩
  · intro ⟨i', j'⟩ ⟨_, hi', hj'⟩
    exact Prod.ext hi' hj'

end CatCrypt.Quantum.Programs.SuperdenseCoding
