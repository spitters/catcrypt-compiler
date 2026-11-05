/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.OpenQASMImportGates

/-!
# ZYZ Euler decomposition of a single-qubit unitary

Every `2 × 2` unitary `U` is a global phase times a product of a Z-rotation, a
Y-rotation and a Z-rotation:
`U = e^{iα} · Rz(β) · Ry(γ) · Rz(δ)`, with `Rz = rzGate` and `Ry = ryMatrix`.

With `p = U 0 0`, `q = U 1 0` and `d = det U`, the angles are
`α = arg p`, `β = arg q − arg p`, `γ = 2 arccos ‖p‖` and `δ = arg d − arg q − arg p`.
The proof uses that the adjugate of a unitary `U` is `det U • star U`, so that
`U 1 1 = d · conj p` and `U 0 1 = −d · conj q`, together with `‖p‖² + ‖q‖² = 1`.

## Main results

* `zyz_exists` — the decomposition of a `2 × 2` unitary.
* `zyz_exists_embedGate1` — the same decomposition of the gate on qubit `q` of `n`.
-/

set_option autoImplicit false

@[expose] public section

open Matrix Complex
open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.OpenQASMImportGates

namespace CatCrypt.Quantum.Synthesis.ZYZ

variable {U : Matrix (Fin 2) (Fin 2) ℂ}

/-- The adjugate of a unitary matrix is its determinant times its conjugate transpose. -/
theorem adjugate_eq_det_smul_star_of_mem_unitaryGroup
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : adjugate U = U.det • star U := by
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc adjugate U = (star U * U) * adjugate U := by rw [h1, Matrix.one_mul]
    _ = star U * (U * adjugate U) := by rw [Matrix.mul_assoc]
    _ = U.det • star U := by rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]

/-- The lower-right entry of a `2 × 2` unitary. -/
theorem entry_one_one_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    U 1 1 = U.det * (starRingEnd ℂ) (U 0 0) := by
  have h := congrFun (congrFun (adjugate_eq_det_smul_star_of_mem_unitaryGroup hU) 0) 0
  simpa [Matrix.adjugate_fin_two] using h

/-- The upper-right entry of a `2 × 2` unitary. -/
theorem entry_zero_one_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    U 0 1 = -(U.det * (starRingEnd ℂ) (U 1 0)) := by
  have h := congrFun (congrFun (adjugate_eq_det_smul_star_of_mem_unitaryGroup hU) 0) 1
  simp [Matrix.adjugate_fin_two] at h
  grind

/-- The first column of a `2 × 2` unitary has norm one. -/
theorem norm_sq_add_norm_sq_of_mem_unitaryGroup
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : ‖U 0 0‖ ^ 2 + ‖U 1 0‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) 0) 0
  have h' : ((‖U 0 0‖ ^ 2 + ‖U 1 0‖ ^ 2 : ℝ) : ℂ) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Complex.conj_mul'] using h
  exact_mod_cast h'

/-- The determinant of a unitary matrix has norm one. -/
theorem norm_det_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖U.det‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)

/-- **ZYZ Euler decomposition.** Every `2 × 2` unitary is a global phase times
`Rz(β) · Ry(γ) · Rz(δ)`. -/
theorem zyz_exists (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ,
      U = Complex.exp (α * I) • (rzGate β * ryMatrix γ * rzGate δ) := by
  set p := U 0 0 with hpdef
  set q := U 1 0 with hqdef
  set d := U.det with hddef
  have hpq : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1 := norm_sq_add_norm_sq_of_mem_unitaryGroup hU
  have hp1 : ‖p‖ ≤ 1 := by nlinarith [norm_nonneg p, norm_nonneg q]
  have hcos : Real.cos (2 * Real.arccos ‖p‖ / 2) = ‖p‖ := by
    rw [mul_div_cancel_left₀ _ two_ne_zero, Real.cos_arccos (by linarith [norm_nonneg p]) hp1]
  have hsin : Real.sin (2 * Real.arccos ‖p‖ / 2) = ‖q‖ := by
    rw [mul_div_cancel_left₀ _ two_ne_zero, Real.sin_arccos,
      show 1 - ‖p‖ ^ 2 = ‖q‖ ^ 2 by linarith, Real.sqrt_sq (norm_nonneg q)]
  have hp : p = ‖p‖ * Complex.exp (arg p * I) := (Complex.norm_mul_exp_arg_mul_I p).symm
  have hq : q = ‖q‖ * Complex.exp (arg q * I) := (Complex.norm_mul_exp_arg_mul_I q).symm
  have hd : d = Complex.exp (arg d * I) := by
    have := (Complex.norm_mul_exp_arg_mul_I d).symm
    rwa [norm_det_of_mem_unitaryGroup hU, Complex.ofReal_one, one_mul] at this
  have hpc : (starRingEnd ℂ) p = ‖p‖ / Complex.exp (arg p * I) := by
    conv_lhs => rw [hp]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I, mul_neg, Complex.exp_neg, div_eq_mul_inv]
  have hqc : (starRingEnd ℂ) q = ‖q‖ / Complex.exp (arg q * I) := by
    conv_lhs => rw [hq]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I, mul_neg, Complex.exp_neg, div_eq_mul_inv]
  have h11 : U 1 1 = Complex.exp (arg d * I) * (‖p‖ / Complex.exp (arg p * I)) := by
    rw [entry_one_one_of_mem_unitaryGroup hU, ← hpdef, hpc, ← hd]
  have h01 : U 0 1 = -(Complex.exp (arg d * I) * (‖q‖ / Complex.exp (arg q * I))) := by
    rw [entry_zero_one_of_mem_unitaryGroup hU, ← hqdef, hqc, ← hd]
  refine ⟨arg p, arg q - arg p, 2 * Real.arccos ‖p‖, arg d - arg q - arg p, ?_⟩
  rw [rz_ry_rz, uMatrix, hcos, hsin]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, ← hpdef, ← hqdef, h11, h01]
  · linear_combination hp
  · push_cast
    simp only [mul_comm I, sub_mul, Complex.exp_sub]
    field_simp
  · conv_lhs => rw [hq]
    push_cast
    simp only [mul_comm I, sub_mul, Complex.exp_sub]
    field_simp
  · push_cast
    simp only [mul_comm I, add_mul, sub_mul, Complex.exp_sub, Complex.exp_add]
    field_simp

/-- **ZYZ Euler decomposition in circuit form.** The gate of a `2 × 2` unitary on
qubit `q` of `n` is a global phase times the product of the embedded
`Rz(β)`, `Ry(γ)` and `Rz(δ)` gates. -/
theorem zyz_exists_embedGate1 (n : ℕ) (q : Fin n)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α β γ δ : ℝ, embedGate1 n q U = Complex.exp (α * I) •
      (embedGate1 n q (rzGate β) * embedGate1 n q (ryMatrix γ) *
        embedGate1 n q (rzGate δ)) := by
  obtain ⟨α, β, γ, δ, h⟩ := zyz_exists hU
  exact ⟨α, β, γ, δ, by rw [embedGate1_mul, embedGate1_mul, ← embedGate1_smul, ← h]⟩

end CatCrypt.Quantum.Synthesis.ZYZ
