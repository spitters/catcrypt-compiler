/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QFT.Circuit

/-!
# The inverse quantum Fourier transform circuit

The inverse of a gate list is the reversed list of the inverses of its gates.
`H`, `X`, `Y`, `Z`, `CNOT`, `CZ` and measurement are their own inverses, `T`
and `T†` are inverse to each other, a `Z` rotation is inverted by negating its
angle, and `S` is inverted by the rotation by `-π / 2`. The inverse transform
circuit is the inverse of `qftGates n`; every angle stays a rational multiple
of `π`.

## Main definitions

* `invGate g` — the inverse of a gate.
* `invGates l` — the inverse of a gate list.
* `qftInvGates n` — the inverse transform circuit on `n` qubits.

## Main results

* `gateEmbedding_invGate` — the matrix of `invGate g` is the conjugate
  transpose of the matrix of `g`.
* `listMatrix_invGates` — the matrix of `invGates l` is the conjugate
  transpose of the matrix of `l`.
* `qftInvGates_matrix` — the matrix of `qftInvGates n` is `(qftMatrix n)ᴴ`.
* `unitaryDenote_qftInvGates` — `qftInvGates n` denotes the channel of
  `(qftUnitary n)⁻¹`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.UnitaryChannel
open CatCrypt.Quantum.Programs.Qubit

noncomputable section

namespace CatCrypt.Quantum.QFT

variable {n : ℕ}

/-! ## Conjugate transposes of the gate matrices -/

theorem hadamard_conjTranspose : hadamardᴴ = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.conjTranspose_apply, Complex.conj_ofReal]

theorem pauliX_conjTranspose : pauliXᴴ = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]

theorem pauliY_conjTranspose : pauliYᴴ = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.conjTranspose_apply, Complex.conj_I]

theorem pauliZ_conjTranspose : pauliZᴴ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose_apply]

theorem cnot_conjTranspose : cnotᴴ = cnot := by
  simp [cnot, Matrix.conjTranspose, ← Matrix.ext_iff, Fin.forall_fin_succ]

theorem czGate_conjTranspose : czGateᴴ = czGate := by
  simp [czGate, Matrix.conjTranspose, ← Matrix.ext_iff, Fin.forall_fin_succ]

private theorem star_exp_I_mul (θ : ℝ) :
    star (Complex.exp (Complex.I * θ)) = Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I, Complex.conj_ofReal]

theorem rzGate_conjTranspose (θ : ℝ) : (rzGate θ)ᴴ = rzGate (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rzGate, Matrix.conjTranspose_apply, -Complex.ofReal_neg, star_exp_I_mul]

theorem tGate_conjTranspose : tGateᴴ = tDaggerGate := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tGate, tDaggerGate, Matrix.conjTranspose_apply]
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I, Complex.conj_ofReal, map_ofNat]

theorem tDaggerGate_conjTranspose : tDaggerGateᴴ = tGate := by
  rw [← tGate_conjTranspose, Matrix.conjTranspose_conjTranspose]

theorem phaseS_conjTranspose : phaseSᴴ = rzGate (PiLin.toReal (-(1 / 2))) := by
  have h : Complex.exp (Complex.I * ((PiLin.toReal (-(1 / 2)) : ℝ) : ℂ)) = -Complex.I := by
    have e : Complex.I * ((PiLin.toReal (-(1 / 2)) : ℝ) : ℂ)
        = -(((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
      simp only [PiLin.one_eq_ofPi, PiLin.ofNat_eq_ofPi, PiLin.ofPi_div_ofPi, PiLin.neg_ofPi,
        PiLin.toReal_ofPi]
      push_cast
      ring
    rw [e, Complex.exp_neg, Complex.exp_mul_I]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseS, rzGate, Matrix.conjTranspose_apply, Complex.conj_I]
  simpa using h.symm

/-! ## The inverse of a gate list -/

/-- The inverse of a gate: `T` and `T†` are exchanged, a `Z` rotation has its
    angle negated, `S` becomes the rotation by `-π / 2`, and every other gate
    is its own inverse. -/
def invGate : Gate n → Gate n
  | .H i      => .H i
  | .X i      => .X i
  | .Y i      => .Y i
  | .Z i      => .Z i
  | .T i      => .Tdg i
  | .Tdg i    => .T i
  | .S i      => .RzQ i (-(1 / 2))
  | .CNOT c t => .CNOT c t
  | .CZ c t   => .CZ c t
  | .Rz i θ   => .Rz i (-θ)
  | .RzQ i q  => .RzQ i (-q)

/-- The matrix of the inverse of a gate is the conjugate transpose of its
    matrix. -/
theorem gateEmbedding_invGate (g : Gate n) :
    gateEmbedding (invGate g) = (gateEmbedding g)ᴴ := by
  cases g with
  | H i => simp only [invGate, gateEmbedding, embedGate1_conjTranspose, hadamard_conjTranspose]
  | X i => simp only [invGate, gateEmbedding, embedGate1_conjTranspose, pauliX_conjTranspose]
  | Y i => simp only [invGate, gateEmbedding, embedGate1_conjTranspose, pauliY_conjTranspose]
  | Z i => simp only [invGate, gateEmbedding, embedGate1_conjTranspose, pauliZ_conjTranspose]
  | T i => simp only [invGate, gateEmbedding, embedGate1_conjTranspose, tGate_conjTranspose]
  | Tdg i =>
    simp only [invGate, gateEmbedding, embedGate1_conjTranspose, tDaggerGate_conjTranspose]
  | S i => simp only [invGate, gateEmbedding, embedGate1_conjTranspose, phaseS_conjTranspose]
  | Rz i θ => simp only [invGate, gateEmbedding, embedGate1_conjTranspose, rzGate_conjTranspose]
  | RzQ i q =>
    simp only [invGate, gateEmbedding, embedGate1_conjTranspose, rzGate_conjTranspose,
      PiLin.toReal_neg]
  | CNOT c t =>
    by_cases h : c = t
    · simp only [invGate, gateEmbedding, dite_eq_left h, Matrix.conjTranspose_one]
    · simp only [invGate, gateEmbedding, dite_eq_right h, embedGate2_conjTranspose, cnot_conjTranspose]
  | CZ c t =>
    by_cases h : c = t
    · simp only [invGate, gateEmbedding, dite_eq_left h, Matrix.conjTranspose_one]
    · simp only [invGate, gateEmbedding, dite_eq_right h, embedGate2_conjTranspose,
        czGate_conjTranspose]
/-- The inverse of a gate list: the inverses of its gates in reverse order. -/
def invGates (l : List (Gate n)) : List (Gate n) := (l.map invGate).reverse

theorem invGates_nil : invGates ([] : List (Gate n)) = [] := rfl

theorem invGates_cons (g : Gate n) (l : List (Gate n)) :
    invGates (g :: l) = invGates l ++ [invGate g] := by
  simp only [invGates, List.map_cons, List.reverse_cons]

theorem length_invGates (l : List (Gate n)) : (invGates l).length = l.length := by
  simp only [invGates, List.length_reverse, List.length_map]

/-- The matrix of the inverse of a gate list is the conjugate transpose of the
    matrix of the list. -/
theorem listMatrix_invGates (l : List (Gate n)) :
    listMatrix (invGates l) = (listMatrix l)ᴴ := by
  induction l with
  | nil => rw [invGates_nil, listMatrix_nil, Matrix.conjTranspose_one]
  | cons g l ih =>
    rw [invGates_cons, listMatrix_append, listMatrix_cons, listMatrix_nil, Matrix.one_mul,
      gateEmbedding_invGate, ih, listMatrix_cons, Matrix.conjTranspose_mul]

/-! ## The inverse transform circuit -/

/-- The inverse quantum Fourier transform circuit on `n` qubits: the
    bit-reversal swaps, then for each qubit from the last to the first the
    phases with negated angles and a Hadamard. -/
def qftInvGates (n : ℕ) : List (Gate n) := invGates (qftGates n)

/-- The matrix of the inverse transform circuit is the conjugate transpose of
    `qftMatrix n`. -/
theorem qftInvGates_matrix (n : ℕ) : listMatrix (qftInvGates n) = (qftMatrix n)ᴴ := by
  rw [qftInvGates, listMatrix_invGates, qftGates_matrix]

/-- The inverse transform circuit denotes the channel of the inverse of the
    quantum Fourier transform. -/
theorem unitaryDenote_qftInvGates (n : ℕ) :
    unitaryDenote (Circuit.ofList (qftInvGates n)) = unitaryChannel (qftUnitary n)⁻¹ := by
  rw [unitaryDenote_ofList]
  congr 1
  exact Subtype.ext ((qftInvGates_matrix n).trans (qftUnitary_inv_val n).symm)

end CatCrypt.Quantum.QFT
