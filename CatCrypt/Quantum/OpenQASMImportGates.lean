/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QFT.Circuit

/-!
# The matrices of the imported OpenQASM gates

`OpenQASMImport.parseOps` lowers `swap`, `sx`, `sxdg`, `rx`, `ry`, `U`, `u3` and `u2`
to lists of `Gate` constructors. This file states the matrix each list realises
(`QFT.listMatrix`, whose channel is `unitaryDenote` by `QFT.unitaryDenote_ofList`)
against the matrix OpenQASM gives the gate.

The OpenQASM matrices, with `c = cos (θ/2)` and `s = sin (θ/2)`:

* `sx = ½ [[1+i, 1−i], [1−i, 1+i]]`, `sxdg = ½ [[1−i, 1+i], [1+i, 1−i]]`;
* `rx(θ) = [[c, −i s], [−i s, c]]`;
* `ry(θ) = [[c, −s], [s, c]]`;
* `U(θ,φ,λ) = [[c, −e^{iλ} s], [e^{iφ} s, e^{i(φ+λ)} c]]`, which is OpenQASM
  2.0's `u3`; `u2(φ,λ) = U(π/2,φ,λ)`.

`sx`, `sxdg` and `swap` are realised exactly. The lists for `rx(θ)`, `ry(θ)`
and `U(θ,φ,λ)` realise the OpenQASM matrix times the global phase `e^{iθ/2}`.

## Main results

* `listMatrix_swapCnotGates` — `swap` is the permutation matrix exchanging the
  two qubits' bits.
* `listMatrix_sxGates`, `listMatrix_sxdgGates` — `sx` and `sxdg`, exactly.
* `listMatrix_rxGates` — `rx(θ)` times `e^{iθ/2}`.
* `listMatrix_ryGates` — `ry(θ)` times `e^{iθ/2}`.
* `listMatrix_uGates` — `U(θ,φ,λ)` times `e^{iθ/2}`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.OpenQASMImport
open CatCrypt.Quantum.QFT (listMatrix listMatrix_cons listMatrix_nil listMatrix_append)
open CatCrypt.Quantum.Optimization.SwapConj
open CatCrypt.Quantum.Optimization.RoutingPerm

noncomputable section

namespace CatCrypt.Quantum.OpenQASMImportGates

/-! ## The OpenQASM matrices -/

/-- `S† = diag(1, −i)`. -/
def sdgMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![1, 0], ![0, -Complex.I]]

/-- OpenQASM's `sx`, the square root of `X`. -/
def sxMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![(1 + Complex.I) / 2, (1 - Complex.I) / 2],
    ![(1 - Complex.I) / 2, (1 + Complex.I) / 2]]

/-- OpenQASM's `sxdg`, the inverse of `sx`. -/
def sxdgMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![(1 - Complex.I) / 2, (1 + Complex.I) / 2],
    ![(1 + Complex.I) / 2, (1 - Complex.I) / 2]]

/-- OpenQASM's `rx(θ)`, the rotation `exp(−i θ X / 2)`. -/
def rxMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![(Real.cos (θ / 2) : ℂ), -Complex.I * (Real.sin (θ / 2) : ℂ)],
    ![-Complex.I * (Real.sin (θ / 2) : ℂ), (Real.cos (θ / 2) : ℂ)]]

/-- OpenQASM's `ry(θ)`, the rotation `exp(−i θ Y / 2)`. -/
def ryMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ)],
    ![(Real.sin (θ / 2) : ℂ), (Real.cos (θ / 2) : ℂ)]]

/-- OpenQASM's `U(θ, φ, λ)`. -/
def uMatrix (θ φ l : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![(Real.cos (θ / 2) : ℂ), -Complex.exp (Complex.I * l) * (Real.sin (θ / 2) : ℂ)],
    ![Complex.exp (Complex.I * φ) * (Real.sin (θ / 2) : ℂ),
      Complex.exp (Complex.I * (φ + l)) * (Real.cos (θ / 2) : ℂ)]]

/-! ## Two-by-two identities -/

/-- `T†·T† = S†`. -/
theorem tDaggerGate_mul_self : tDaggerGate * tDaggerGate = sdgMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tDaggerGate, sdgMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  rw [← Complex.exp_add, show -(Complex.I * (↑Real.pi / 4)) + -(Complex.I * (↑Real.pi / 4))
    = -(↑Real.pi / 2 * Complex.I) by ring, Complex.exp_neg, Complex.exp_pi_div_two_mul_I,
    Complex.inv_I]

/-- `H·S·H = sx`. -/
theorem hadamard_phaseS_hadamard : hadamard * phaseS * hadamard = sxMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, phaseS, sxMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [ofReal_sqrt_two_sq] <;> ring

/-- `H·S†·H = sxdg`. -/
theorem hadamard_sdg_hadamard : hadamard * sdgMatrix * hadamard = sxdgMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, sdgMatrix, sxdgMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [ofReal_sqrt_two_sq] <;> ring

/-- `S·H·P(θ)·H·S† = e^{iθ/2}·Ry(θ)`. -/
theorem phaseS_hadamard_rz_hadamard_sdg (θ : ℝ) :
    phaseS * hadamard * rzGate θ * hadamard * sdgMatrix
      = Complex.exp (Complex.I * (θ / 2 : ℝ)) • ryMatrix θ := by
  set w := Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) with hw
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := ofReal_sqrt2_ne_zero
  have hc : Complex.cos ((θ : ℂ) / 2) = (w + w⁻¹) / 2 := by
    rw [Complex.cos, hw, ← Complex.exp_neg]; push_cast; ring_nf
  have hsn : Complex.sin ((θ : ℂ) / 2) = (w⁻¹ - w) * Complex.I / 2 := by
    rw [Complex.sin, hw, ← Complex.exp_neg]; push_cast; ring_nf
  have he : Complex.exp (Complex.I * (θ : ℂ)) = w * w := by
    rw [hw, ← Complex.exp_add]; push_cast; ring_nf
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, phaseS, rzGate, sdgMatrix, ryMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      he, hc, hsn] <;> field_simp <;> ring_nf <;> simp [ofReal_sqrt_two_sq, Complex.I_sq] <;> ring

/-- `S†·S = 1`. -/
theorem sdgMatrix_mul_phaseS : sdgMatrix * phaseS = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sdgMatrix, phaseS, Matrix.mul_apply, Fin.sum_univ_two]

/-- `S†·Ry(θ)·S = Rx(θ)`. -/
theorem sdgMatrix_ryMatrix_phaseS (θ : ℝ) :
    sdgMatrix * ryMatrix θ * phaseS = rxMatrix θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sdgMatrix, ryMatrix, rxMatrix, phaseS, Matrix.mul_apply, Fin.sum_univ_two]
  · ring
  · linear_combination -(Complex.cos ((θ : ℂ) / 2)) * Complex.I_sq

/-- `H·P(θ)·H = e^{iθ/2}·Rx(θ)`: conjugate `phaseS_hadamard_rz_hadamard_sdg` by `S`. -/
theorem hadamard_rz_hadamard (θ : ℝ) :
    hadamard * rzGate θ * hadamard = Complex.exp (Complex.I * (θ / 2 : ℝ)) • rxMatrix θ := by
  have e : sdgMatrix * (phaseS * hadamard * rzGate θ * hadamard * sdgMatrix) * phaseS =
      hadamard * rzGate θ * hadamard := by
    simp only [← Matrix.mul_assoc, sdgMatrix_mul_phaseS, Matrix.one_mul]
    simp only [Matrix.mul_assoc, sdgMatrix_mul_phaseS, Matrix.mul_one]
  rw [← e, phaseS_hadamard_rz_hadamard_sdg, Matrix.mul_smul, Matrix.smul_mul,
    sdgMatrix_ryMatrix_phaseS]

/-- `P(φ)·Ry(θ)·P(λ) = U(θ, φ, λ)`. -/
theorem rz_ry_rz (θ φ l : ℝ) : rzGate φ * ryMatrix θ * rzGate l = uMatrix θ φ l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rzGate, ryMatrix, uMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_add,
      Complex.exp_add] <;> ring

/-! ## The gate lists -/

variable {n : ℕ}

/-- `swap` is the basis permutation exchanging the bits of the two qubits. -/
theorem listMatrix_swapCnotGates (a b : Fin n) :
    listMatrix (swapCnotGates a b) = (qubitPermUnitary (swapBitPerm a b)).val :=
  QFT.swapGates_matrix a b

/-- `sx` exactly. -/
theorem listMatrix_sxGates (q : Fin n) : listMatrix (sxGates q) = embedGate1 n q sxMatrix := by
  simp only [sxGates, listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, embedGate1_mul,
    hadamard_phaseS_hadamard]

/-- `sxdg` exactly. -/
theorem listMatrix_sxdgGates (q : Fin n) :
    listMatrix (sxdgGates q) = embedGate1 n q sxdgMatrix := by
  simp only [sxdgGates, sdgGates, List.cons_append, List.nil_append, listMatrix_cons,
    listMatrix_nil, one_mul, gateEmbedding, embedGate1_mul]
  rw [mul_assoc hadamard, tDaggerGate_mul_self, hadamard_sdg_hadamard]

/-- `rx(a)` times the global phase `e^{i a / 2}`. -/
theorem listMatrix_rxGates (q : Fin n) (a : PiLin) :
    listMatrix (rxGates q a)
      = Complex.exp (Complex.I * (a.toReal / 2 : ℝ)) • embedGate1 n q (rxMatrix a.toReal) := by
  simp only [rxGates, listMatrix_cons, listMatrix_nil, one_mul, gateEmbedding, embedGate1_mul]
  rw [hadamard_rz_hadamard, embedGate1_smul]

/-- `ry(a)` times the global phase `e^{i a / 2}`. -/
theorem listMatrix_ryGates (q : Fin n) (a : PiLin) :
    listMatrix (ryGates q a)
      = Complex.exp (Complex.I * (a.toReal / 2 : ℝ)) • embedGate1 n q (ryMatrix a.toReal) := by
  simp only [ryGates, sdgGates, List.cons_append, List.nil_append, listMatrix_cons,
    listMatrix_nil, one_mul, gateEmbedding, embedGate1_mul]
  rw [mul_assoc (phaseS * hadamard * rzGate a.toReal * hadamard), tDaggerGate_mul_self,
    phaseS_hadamard_rz_hadamard_sdg, embedGate1_smul]

/-- `U(θ, φ, λ)` times the global phase `e^{i θ / 2}`. -/
theorem listMatrix_uGates (q : Fin n) (θ φ l : PiLin) :
    listMatrix (uGates q θ φ l)
      = Complex.exp (Complex.I * (θ.toReal / 2 : ℝ)) •
          embedGate1 n q (uMatrix θ.toReal φ.toReal l.toReal) := by
  simp only [uGates, ryGates, sdgGates, List.cons_append, List.nil_append, listMatrix_cons,
    listMatrix_nil, one_mul, gateEmbedding, embedGate1_mul]
  rw [mul_assoc (rzGate φ.toReal * phaseS * hadamard * rzGate θ.toReal * hadamard),
    tDaggerGate_mul_self,
    show rzGate φ.toReal * phaseS * hadamard * rzGate θ.toReal * hadamard * sdgMatrix
        = rzGate φ.toReal * (phaseS * hadamard * rzGate θ.toReal * hadamard * sdgMatrix) by
      simp only [mul_assoc],
    phaseS_hadamard_rz_hadamard_sdg, Matrix.mul_smul, Matrix.smul_mul, rz_ry_rz,
    embedGate1_smul]

end CatCrypt.Quantum.OpenQASMImportGates
