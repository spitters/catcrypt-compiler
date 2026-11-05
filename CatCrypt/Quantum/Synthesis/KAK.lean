/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.ZYZ
public import CatCrypt.Quantum.HQPL.ConcreteLowering
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Matrix.Spectrum
public import CatCryptCore.ForMathlib.Matrix.SimultaneousDiag

/-!
# KAK decomposition of a two-qubit unitary

Every `4 × 4` unitary is, up to a global phase, the universal three-CNOT circuit of
Vatan and Williams (Phys. Rev. A 69, 032315 (2004), Fig. 6): a layer of single-qubit
ZYZ rotations on both qubits, the canonical two-qubit part realised by three CNOTs and
three rotations, and a second layer of single-qubit ZYZ rotations.

The proof follows the magic-basis route. With the magic basis `magic`, conjugation
`W ↦ magic * W * star magic` sends a real orthogonal matrix of determinant one to a
tensor product of single-qubit unitaries (`localReal_of_det_eq_one`), and sends a
diagonal matrix to a member of the canonical family (`vwCore_eq`). For a unitary `U`,
`U' = star magic * U * magic` gives the symmetric unitary `U'ᵀ * U'`, which a real
orthogonal matrix diagonalises (`Matrix.exists_orthogonal_diagonal_of_symm_unitary`, in
`CatCryptCore.ForMathlib.Matrix.SimultaneousDiag`); this writes `U'` as orthogonal times
diagonal times orthogonal.

## Main results

* `localReal_of_det_eq_one` — `SO(4)` is the magic-basis image of local unitaries.
* `vwCore_eq` — the three-CNOT canonical circuit is diagonal in the magic basis.
* `kak3_exists` — every two-qubit unitary is a global phase times `kak3 θ`.
* `kak3_exists_listMatrix` — the same decomposition as a gate list on qubits `i ≠ j`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix Complex
open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.GateUnitarity CatCrypt.Quantum.TensorProduct
open CatCrypt.Quantum.OpenQASMImportGates CatCrypt.Quantum.Synthesis.ZYZ

namespace CatCrypt.Quantum.Synthesis.KAK

/-! ## Two-qubit tensor products -/

/-- The Kronecker product of two `2 × 2` matrices, entry by entry. -/
theorem kronecker_two_eq (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (A ⊗ₖ B : Matrix (Fin 4) (Fin 4) ℂ) =
      !![A 0 0 * B 0 0, A 0 0 * B 0 1, A 0 1 * B 0 0, A 0 1 * B 0 1;
        A 0 0 * B 1 0, A 0 0 * B 1 1, A 0 1 * B 1 0, A 0 1 * B 1 1;
        A 1 0 * B 0 0, A 1 0 * B 0 1, A 1 1 * B 0 0, A 1 1 * B 0 1;
        A 1 0 * B 1 0, A 1 0 * B 1 1, A 1 1 * B 1 0, A 1 1 * B 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- A scalar multiple of a unitary by a unit-norm scalar is unitary. -/
theorem smul_mem_unitaryGroup {k : Type} [Fintype k] [DecidableEq k] {c : ℂ}
    {A : Matrix k k ℂ} (hc : ‖c‖ = 1) (hA : A ∈ Matrix.unitaryGroup k ℂ) :
    c • A ∈ Matrix.unitaryGroup k ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA ⊢
  rw [star_smul, smul_mul_smul_comm, hA]
  have : star c * c = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hc]
    simp
  rw [this, one_smul]

/-! ## The magic basis -/

/-- The magic basis up to the factor `1/√2`; its columns are `|00⟩ + |11⟩`,
`i(|00⟩ − |11⟩)`, `i(|01⟩ + |10⟩)` and `|01⟩ − |10⟩`. -/
def magic0 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, I, 0, 0; 0, 0, I, 1; 0, 0, I, -1; 1, -I, 0, 0]

/-- The magic basis, a unitary whose conjugation sends local unitaries to real
orthogonal matrices. -/
def magic : Matrix (Fin 4) (Fin 4) ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • magic0

theorem star_magic0_mul_magic0 : star magic0 * magic0 = (2 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [magic0, Matrix.mul_apply, Fin.sum_univ_four] <;> ring_nf

theorem magic0_mul_star_magic0 : magic0 * star magic0 = (2 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [magic0, Matrix.mul_apply, Fin.sum_univ_four] <;> ring_nf

theorem magic_scalar_sq : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2 = 1 := by
  rw [← ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast
  norm_num

theorem star_magic : star magic = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • star magic0 := by
  rw [magic, star_smul, Complex.star_def, Complex.conj_ofReal]

theorem star_magic_mul_magic : star magic * magic = 1 := by
  rw [star_magic, magic, smul_mul_smul_comm, star_magic0_mul_magic0, smul_smul, magic_scalar_sq,
    one_smul]

theorem magic_mul_star_magic : magic * star magic = 1 := by
  rw [star_magic, magic, smul_mul_smul_comm, magic0_mul_star_magic0, smul_smul, magic_scalar_sq,
    one_smul]

/-- A matrix identity `magic0 * R = W * magic0` holds for `magic`. -/
theorem magic_mul_eq_of_magic0 {R W : Matrix (Fin 4) (Fin 4) ℂ} (h : magic0 * R = W * magic0) :
    magic * R * star magic = W := by
  have h' : magic * R = W * magic := by rw [magic, Matrix.smul_mul, h, Matrix.mul_smul]
  rw [h', Matrix.mul_assoc, magic_mul_star_magic, Matrix.mul_one]

/-! ## Local unitaries and their magic-basis images -/

/-- A two-qubit matrix is local when it is a tensor product of two single-qubit unitaries. -/
def IsLocal (W : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    B ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ W = A ⊗ₖ B

theorem IsLocal.mul {W W' : Matrix (Fin 4) (Fin 4) ℂ} (h : IsLocal W) (h' : IsLocal W') :
    IsLocal (W * W') := by
  obtain ⟨A, B, hA, hB, rfl⟩ := h
  obtain ⟨A', B', hA', hB', rfl⟩ := h'
  exact ⟨A * A', B * B', mul_mem hA hA', mul_mem hB hB', kronecker_mul_kronecker A A' B B'⟩

/-- A real matrix whose magic-basis image is local. -/
def LocalReal (R : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  IsLocal (magic * R.map ofReal * star magic)

theorem map_ofReal_mul (R R' : Matrix (Fin 4) (Fin 4) ℝ) :
    (R * R').map ofReal = R.map ofReal * R'.map ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

theorem LocalReal.mul {R R' : Matrix (Fin 4) (Fin 4) ℝ} (h : LocalReal R) (h' : LocalReal R') :
    LocalReal (R * R') := by
  have := IsLocal.mul h h'
  rw [LocalReal, map_ofReal_mul]
  convert this using 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star magic) magic, star_magic_mul_magic, Matrix.one_mul]

/-! ## Plane rotations -/

/-- Rotation by `t` in the plane of the basis vectors `0` and `1`. -/
def rotA (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![Real.cos t, -Real.sin t, 0, 0; Real.sin t, Real.cos t, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- Rotation by `t` in the plane of the basis vectors `1` and `2`. -/
def rotB (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, Real.cos t, -Real.sin t, 0; 0, Real.sin t, Real.cos t, 0; 0, 0, 0, 1]

/-- Rotation by `t` in the plane of the basis vectors `2` and `3`. -/
def rotC (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, Real.cos t, -Real.sin t; 0, 0, Real.sin t, Real.cos t]

theorem exp_I_mul_ofReal (t : ℝ) : exp (I * t) = Real.cos t + Real.sin t * I := by
  rw [mul_comm, exp_mul_I, ← ofReal_cos, ← ofReal_sin]

theorem exp_neg_I_mul_ofReal (t : ℝ) : exp (-(I * t)) = Real.cos t - Real.sin t * I := by
  rw [← mul_neg, ← ofReal_neg, exp_I_mul_ofReal, Real.cos_neg, Real.sin_neg, ofReal_neg]
  ring

theorem rotA_orth (t : ℝ) : (rotA t)ᵀ * rotA t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotA, Matrix.mul_apply, Fin.sum_univ_four] <;> nlinarith [Real.cos_sq_add_sin_sq t]

theorem rotB_orth (t : ℝ) : (rotB t)ᵀ * rotB t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotB, Matrix.mul_apply, Fin.sum_univ_four] <;> nlinarith [Real.cos_sq_add_sin_sq t]

theorem rotC_orth (t : ℝ) : (rotC t)ᵀ * rotC t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotC, Matrix.mul_apply, Fin.sum_univ_four] <;> nlinarith [Real.cos_sq_add_sin_sq t]

theorem det_rotA (t : ℝ) : (rotA t).det = 1 := by
  simp [rotA, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  nlinarith [Real.cos_sq_add_sin_sq t]

theorem det_rotB (t : ℝ) : (rotB t).det = 1 := by
  simp [rotB, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  nlinarith [Real.cos_sq_add_sin_sq t]

theorem det_rotC (t : ℝ) : (rotC t).det = 1 := by
  simp [rotC, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  nlinarith [Real.cos_sq_add_sin_sq t]

theorem magic0_mul_rotA (t : ℝ) :
    magic0 * (rotA t).map ofReal = ((exp (I * t) • rzGate (-t)) ⊗ₖ rzGate (-t)) * magic0 := by
  rw [kronecker_two_eq]
  ext i j
  have h := Real.cos_sq_add_sin_sq t
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [magic0, rotA, rzGate, Matrix.mul_apply, Fin.sum_univ_four, exp_I_mul_ofReal,
      exp_neg_I_mul_ofReal, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    nlinarith [h, congrArg (· * Real.cos t) h, congrArg (· * Real.sin t) h]

theorem magic0_mul_rotB (t : ℝ) :
    magic0 * (rotB t).map ofReal = (ryMatrix t ⊗ₖ ryMatrix t) * magic0 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = 2 * s := ⟨t / 2, by ring⟩
  have h := Real.cos_sq_add_sin_sq s
  rw [kronecker_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [magic0, rotB, ryMatrix, Matrix.mul_apply, Fin.sum_univ_four, Real.cos_two_mul,
      Real.sin_two_mul, -Complex.ofReal_cos, -Complex.ofReal_sin, -Complex.ofReal_pow] <;>
    nlinarith [h]

theorem magic0_mul_rotC (t : ℝ) :
    magic0 * (rotC t).map ofReal = (rzGate t ⊗ₖ rzGate (-t)) * magic0 := by
  rw [kronecker_two_eq]
  ext i j
  have h := Real.cos_sq_add_sin_sq t
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [magic0, rotC, rzGate, Matrix.mul_apply, Fin.sum_univ_four, exp_I_mul_ofReal,
      exp_neg_I_mul_ofReal, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    nlinarith [h, congrArg (· * Real.cos t) h, congrArg (· * Real.sin t) h]

theorem rzGate_mem_unitaryGroup (t : ℝ) : rzGate t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact rzGate_unitary t

theorem ryMatrix_mem_unitaryGroup (t : ℝ) : ryMatrix t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h := Real.cos_sq_add_sin_sq (t / 2)
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [ryMatrix, Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_cos,
      -Complex.ofReal_sin] <;>
    nlinarith [h]

theorem norm_exp_I_mul_ofReal (t : ℝ) : ‖exp (I * t)‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I t

theorem localReal_rotA (t : ℝ) : LocalReal (rotA t) :=
  ⟨_, _, smul_mem_unitaryGroup (norm_exp_I_mul_ofReal t) (rzGate_mem_unitaryGroup (-t)),
    rzGate_mem_unitaryGroup (-t), magic_mul_eq_of_magic0 (magic0_mul_rotA t)⟩

theorem localReal_rotB (t : ℝ) : LocalReal (rotB t) :=
  ⟨_, _, ryMatrix_mem_unitaryGroup t, ryMatrix_mem_unitaryGroup t,
    magic_mul_eq_of_magic0 (magic0_mul_rotB t)⟩

theorem localReal_rotC (t : ℝ) : LocalReal (rotC t) :=
  ⟨_, _, rzGate_mem_unitaryGroup t, rzGate_mem_unitaryGroup (-t),
    magic_mul_eq_of_magic0 (magic0_mul_rotC t)⟩

/-! ## `SO(4)` is the magic-basis image of the local unitaries -/

theorem orth_mul {Q R : Matrix (Fin 4) (Fin 4) ℝ} (hQ : Qᵀ * Q = 1) (hR : Rᵀ * R = 1) :
    (Q * R)ᵀ * (Q * R) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul, hR]

theorem orth_transpose {Q : Matrix (Fin 4) (Fin 4) ℝ} (hQ : Qᵀ * Q = 1) : Qᵀᵀ * Qᵀ = 1 := by
  rw [Matrix.transpose_transpose]
  exact mul_eq_one_comm.mp hQ

theorem mul_transpose_mul_cancel {Q : Matrix (Fin 4) (Fin 4) ℝ} (hQ : Qᵀ * Q = 1)
    (X : Matrix (Fin 4) (Fin 4) ℝ) : Q * (Qᵀ * X) = X := by
  rw [← Matrix.mul_assoc, mul_eq_one_comm.mp hQ, Matrix.one_mul]

/-- If the columns `j` of `O` and of an orthogonal `Q` agree, column `j` of `Qᵀ * O` is the
basis vector `j`. -/
theorem transpose_mul_apply_of_col {Q O : Matrix (Fin 4) (Fin 4) ℝ} (hQ : Qᵀ * Q = 1)
    {j : Fin 4} (h : ∀ l, O l j = Q l j) (k : Fin 4) :
    (Qᵀ * O) k j = (1 : Matrix (Fin 4) (Fin 4) ℝ) k j := by
  rw [← hQ]
  simp only [Matrix.mul_apply, h]

/-- In an orthogonal matrix whose column `i` is the basis vector `i`, row `i` is that basis
vector too. -/
theorem apply_of_col_eq_one {O : Matrix (Fin 4) (Fin 4) ℝ} (hO : Oᵀ * O = 1) {i : Fin 4}
    (h : ∀ l, O l i = (1 : Matrix (Fin 4) (Fin 4) ℝ) l i) (j : Fin 4) :
    O i j = (1 : Matrix (Fin 4) (Fin 4) ℝ) i j := by
  have := congrFun (congrFun hO i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, h, Matrix.one_apply] at this
  simpa [Matrix.one_apply] using this

/-- The columns of an orthogonal matrix are unit vectors. -/
theorem col_norm {O : Matrix (Fin 4) (Fin 4) ℝ} (hO : Oᵀ * O = 1) (j : Fin 4) :
    O 0 j ^ 2 + O 1 j ^ 2 + O 2 j ^ 2 + O 3 j ^ 2 = 1 := by
  have := congrFun (congrFun hO j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, Matrix.one_apply_eq]
    at this
  linarith

theorem sq_sqrt_add_sq (x y : ℝ) : √(x ^ 2 + y ^ 2) ^ 2 = x ^ 2 + y ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem exists_rot_col0 {v : Fin 4 → ℝ} (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 1) :
    ∃ a b c : ℝ, ∀ l, v l = (rotC c * rotB b * rotA a) l 0 := by
  obtain ⟨c, hc2, hc3⟩ := Real.exists_polar (v 2) (v 3)
  obtain ⟨b, hb1, hb3⟩ := Real.exists_polar (v 1) √(v 2 ^ 2 + v 3 ^ 2)
  obtain ⟨a, ha0, ha2⟩ := Real.exists_polar (v 0) √(v 1 ^ 2 + √(v 2 ^ 2 + v 3 ^ 2) ^ 2)
  have h1 : √(v 0 ^ 2 + √(v 1 ^ 2 + √(v 2 ^ 2 + v 3 ^ 2) ^ 2) ^ 2) = 1 := by
    rw [sq_sqrt_add_sq, sq_sqrt_add_sq, ← Real.sqrt_one]
    congr 1
    linarith
  rw [h1, one_mul] at ha0 ha2
  rw [ha2] at hb1 hb3
  rw [hb3] at hc2 hc3
  refine ⟨a, b, c, fun l => ?_⟩
  fin_cases l <;>
    simp [rotA, rotB, rotC, Matrix.mul_apply, Fin.sum_univ_four, ha0, hb1, hc2, hc3] <;> ring

theorem exists_rot_col1 {v : Fin 4 → ℝ} (h0 : v 0 = 0)
    (hv : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 1) :
    ∃ b c : ℝ, ∀ l, v l = (rotC c * rotB b) l 1 := by
  obtain ⟨c, hc2, hc3⟩ := Real.exists_polar (v 2) (v 3)
  obtain ⟨b, hb1, hb3⟩ := Real.exists_polar (v 1) √(v 2 ^ 2 + v 3 ^ 2)
  have h1 : √(v 1 ^ 2 + √(v 2 ^ 2 + v 3 ^ 2) ^ 2) = 1 := by
    rw [sq_sqrt_add_sq, ← Real.sqrt_one]
    congr 1
    linarith
  rw [h1, one_mul] at hb1 hb3
  rw [hb3] at hc2 hc3
  refine ⟨b, c, fun l => ?_⟩
  fin_cases l <;> simp [rotB, rotC, Matrix.mul_apply, Fin.sum_univ_four, h0, hb1, hc2, hc3] <;>
    ring

theorem exists_rot_col2 {v : Fin 4 → ℝ} (h0 : v 0 = 0) (h1 : v 1 = 0)
    (hv : v 2 ^ 2 + v 3 ^ 2 = 1) : ∃ c : ℝ, ∀ l, v l = rotC c l 2 := by
  obtain ⟨c, hc2, hc3⟩ := Real.exists_polar (v 2) (v 3)
  rw [hv, Real.sqrt_one, one_mul] at hc2 hc3
  refine ⟨c, fun l => ?_⟩
  fin_cases l <;> simp [rotC, h0, h1, hc2, hc3]

/-- **`SO(4)` is local in the magic basis.** The magic-basis image of a real orthogonal
matrix of determinant one is a tensor product of two single-qubit unitaries. The proof
writes the matrix as a product of six plane rotations (Givens reduction, column by column). -/
theorem localReal_of_det_eq_one {O : Matrix (Fin 4) (Fin 4) ℝ} (hO : Oᵀ * O = 1)
    (hdet : O.det = 1) : LocalReal O := by
  obtain ⟨a, b, c, hv⟩ := exists_rot_col0 (v := fun l => O l 0) (col_norm hO 0)
  set Q₁ := rotC c * rotB b * rotA a with hQ₁
  have oQ₁ : Q₁ᵀ * Q₁ = 1 := orth_mul (orth_mul (rotC_orth c) (rotB_orth b)) (rotA_orth a)
  set O₁ := Q₁ᵀ * O with hO₁
  have oO₁ : O₁ᵀ * O₁ = 1 := orth_mul (orth_transpose oQ₁) hO
  have c₁0 : ∀ l, O₁ l 0 = (1 : Matrix (Fin 4) (Fin 4) ℝ) l 0 :=
    transpose_mul_apply_of_col oQ₁ hv
  have e₁ : O₁ 0 1 = 0 := by simpa using apply_of_col_eq_one oO₁ c₁0 1
  obtain ⟨b', c', hw⟩ := exists_rot_col1 (v := fun l => O₁ l 1) e₁
    (by have := col_norm oO₁ 1; rw [e₁] at this; linarith)
  set Q₂ := rotC c' * rotB b' with hQ₂
  have oQ₂ : Q₂ᵀ * Q₂ = 1 := orth_mul (rotC_orth c') (rotB_orth b')
  set O₂ := Q₂ᵀ * O₁ with hO₂
  have oO₂ : O₂ᵀ * O₂ = 1 := orth_mul (orth_transpose oQ₂) oO₁
  have c₂0 : ∀ l, O₂ l 0 = (1 : Matrix (Fin 4) (Fin 4) ℝ) l 0 :=
    transpose_mul_apply_of_col oQ₂ (fun l => by
      fin_cases l <;> simp [c₁0, Q₂, rotB, rotC])
  have c₂1 : ∀ l, O₂ l 1 = (1 : Matrix (Fin 4) (Fin 4) ℝ) l 1 :=
    transpose_mul_apply_of_col oQ₂ hw
  have e₂0 : O₂ 0 2 = 0 := by simpa using apply_of_col_eq_one oO₂ c₂0 2
  have e₂1 : O₂ 1 2 = 0 := by simpa using apply_of_col_eq_one oO₂ c₂1 2
  obtain ⟨c'', hu⟩ := exists_rot_col2 (v := fun l => O₂ l 2) e₂0 e₂1
    (by have := col_norm oO₂ 2; rw [e₂0, e₂1] at this; linarith)
  set O₃ := (rotC c'')ᵀ * O₂ with hO₃
  have oO₃ : O₃ᵀ * O₃ = 1 := orth_mul (orth_transpose (rotC_orth c'')) oO₂
  have c₃0 : ∀ l, O₃ l 0 = (1 : Matrix (Fin 4) (Fin 4) ℝ) l 0 :=
    transpose_mul_apply_of_col (rotC_orth c'') (fun l => by
      fin_cases l <;> simp [c₂0, rotC])
  have c₃1 : ∀ l, O₃ l 1 = (1 : Matrix (Fin 4) (Fin 4) ℝ) l 1 :=
    transpose_mul_apply_of_col (rotC_orth c'') (fun l => by
      fin_cases l <;> simp [c₂1, rotC])
  have c₃2 : ∀ l, O₃ l 2 = (1 : Matrix (Fin 4) (Fin 4) ℝ) l 2 :=
    transpose_mul_apply_of_col (rotC_orth c'') hu
  have e₃0 : O₃ 0 3 = 0 := by simpa using apply_of_col_eq_one oO₃ c₃0 3
  have e₃1 : O₃ 1 3 = 0 := by simpa using apply_of_col_eq_one oO₃ c₃1 3
  have e₃2 : O₃ 2 3 = 0 := by simpa using apply_of_col_eq_one oO₃ c₃2 3
  have hd : O₃ = diagonal ![1, 1, 1, O₃ 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [c₃0, c₃1, c₃2, e₃0, e₃1, e₃2]
  have hdet₃ : O₃.det = 1 := by
    simp only [hO₃, hO₂, hO₁, hQ₁, hQ₂, Matrix.det_mul, Matrix.det_transpose, det_rotA, det_rotB,
      det_rotC, hdet, mul_one]
  have h33 : O₃ 3 3 = 1 := by
    rw [hd] at hdet₃
    simpa [Matrix.det_diagonal, Fin.prod_univ_four] using hdet₃
  have hO₃1 : O₃ = 1 := by
    rw [hd, h33]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hOeq : O = Q₁ * (Q₂ * rotC c'') := by
    have h1 : O = Q₁ * O₁ := (mul_transpose_mul_cancel oQ₁ O).symm
    have h2 : O₁ = Q₂ * O₂ := (mul_transpose_mul_cancel oQ₂ O₁).symm
    have h3 : O₂ = rotC c'' * O₃ := (mul_transpose_mul_cancel (rotC_orth c'') O₂).symm
    rw [h1, h2, h3, hO₃1, Matrix.mul_one]
  rw [hOeq]
  exact (((localReal_rotC c).mul (localReal_rotB b)).mul (localReal_rotA a)).mul
    (((localReal_rotC c').mul (localReal_rotB b')).mul (localReal_rotC c''))

/-! ## The three-CNOT canonical circuit -/

/-- CNOT with the low qubit as control and the high qubit as target. -/
def cnotRev : Matrix (Fin 4) (Fin 4) ℂ :=
  Programs.Qubit.swap * Programs.Qubit.cnot * Programs.Qubit.swap

theorem cnotRev_eq : cnotRev = !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnotRev, Programs.Qubit.swap, Programs.Qubit.cnot, Matrix.mul_apply, Fin.sum_univ_four]

theorem cnotRev_mul_self : cnotRev * cnotRev = 1 := by
  rw [cnotRev_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem rzGate_pi_div_two : rzGate (Real.pi / 2) = !![1, 0; 0, I] := by
  rw [rzGate, exp_I_mul_ofReal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rzGate_neg_mul_rzGate (t : ℝ) : rzGate (-t) * rzGate t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rzGate, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]

/-- The three-CNOT circuit for the canonical two-qubit part (Vatan and Williams, Fig. 6). The
matrix product lists the gates in reverse time order: `Rz(π/2)` on the low qubit, CNOT from
the low to the high qubit, `Rz(a)` on the high and `Ry(b)` on the low qubit, CNOT from the
high to the low qubit, `Ry(c)` on the low qubit, CNOT from the low to the high qubit, and
`Rz(−π/2)` on the high qubit. -/
def vwCore (a b c : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (rzGate (-(Real.pi / 2)) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * cnotRev *
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ryMatrix c) * Programs.Qubit.cnot *
    (rzGate a ⊗ₖ ryMatrix b) * cnotRev *
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ rzGate (Real.pi / 2))

/-- The eigenvalues of `vwCore a b c` in the magic basis. -/
def vwPhase (a b c : ℝ) : Fin 4 → ℂ :=
  ![exp (I * ((-(b / 2) : ℝ) : ℂ)) * exp (I * ((-(c / 2) : ℝ) : ℂ)),
    exp (I * ((b / 2 : ℝ) : ℂ)) * exp (I * ((c / 2 : ℝ) : ℂ)),
    exp (I * a) * exp (I * ((-(b / 2) : ℝ) : ℂ)) * exp (I * ((c / 2 : ℝ) : ℂ)),
    -(exp (I * a) * exp (I * ((b / 2 : ℝ) : ℂ)) * exp (I * ((-(c / 2) : ℝ) : ℂ)))]

theorem vwCore_right :
    cnotRev * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ rzGate (Real.pi / 2)) * magic0 =
      !![1, I, 0, 0; I, 1, 0, 0; 0, 0, I, -1; 0, 0, -1, I] := by
  rw [cnotRev_eq, rzGate_pi_div_two, kronecker_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [magic0, Matrix.mul_apply, Fin.sum_univ_four]

theorem vwCore_left :
    cnotRev * (rzGate (Real.pi / 2) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * magic0 =
      !![1, I, 0, 0; I, 1, 0, 0; 0, 0, -1, -I; 0, 0, I, 1] := by
  rw [cnotRev_eq, rzGate_pi_div_two, kronecker_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [magic0, Matrix.mul_apply, Fin.sum_univ_four]

theorem vwCore_middle (a b c : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ryMatrix c) * Programs.Qubit.cnot *
        (rzGate a ⊗ₖ ryMatrix b) *
        !![1, I, 0, 0; I, 1, 0, 0; 0, 0, I, -1; 0, 0, -1, I] =
      !![1, I, 0, 0; I, 1, 0, 0; 0, 0, -1, -I; 0, 0, I, 1] * diagonal (vwPhase a b c) := by
  rw [kronecker_two_eq, kronecker_two_eq]
  simp only [vwPhase, rzGate, exp_I_mul_ofReal, Real.cos_neg, Real.sin_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Programs.Qubit.cnot, ryMatrix, Matrix.mul_apply, Fin.sum_univ_four,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    ring

theorem vwCore_mul_magic0 (a b c : ℝ) :
    vwCore a b c * magic0 = magic0 * diagonal (vwPhase a b c) := by
  have h : vwCore a b c * magic0 =
      (rzGate (-(Real.pi / 2)) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * cnotRev *
        (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ryMatrix c) * Programs.Qubit.cnot *
          (rzGate a ⊗ₖ ryMatrix b) *
          (cnotRev * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ rzGate (Real.pi / 2)) * magic0)) := by
    simp only [vwCore, Matrix.mul_assoc]
  rw [h, vwCore_right, vwCore_middle, ← vwCore_left]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ cnotRev cnotRev, cnotRev_mul_self, Matrix.mul_one,
    kronecker_mul_kronecker, rzGate_neg_mul_rzGate, Matrix.one_mul, kronecker_one_one]
  simp

/-- The canonical circuit is diagonal in the magic basis. -/
theorem vwCore_eq (a b c : ℝ) :
    vwCore a b c = magic * diagonal (vwPhase a b c) * star magic :=
  (magic_mul_eq_of_magic0 (vwCore_mul_magic0 a b c).symm).symm

/-! ## Orthogonal, diagonal, orthogonal -/

theorem transpose_map_ofReal (R : Matrix (Fin 4) (Fin 4) ℝ) :
    (R.map ofReal)ᵀ = Rᵀ.map ofReal :=
  (Matrix.transpose_map).symm

theorem star_map_ofReal (R : Matrix (Fin 4) (Fin 4) ℝ) :
    star (R.map ofReal) = Rᵀ.map ofReal := by
  ext i j
  simp [Matrix.star_apply]

theorem map_ofReal_one : (1 : Matrix (Fin 4) (Fin 4) ℝ).map ofReal = 1 :=
  Matrix.map_one _ ofReal_zero ofReal_one

theorem map_ofReal_mem_unitaryGroup {R : Matrix (Fin 4) (Fin 4) ℝ} (hR : Rᵀ * R = 1) :
    R.map ofReal ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_map_ofReal, ← map_ofReal_mul, hR, map_ofReal_one]

theorem diagonal_mem_unitaryGroup {g : Fin 4 → ℂ} (hg : ∀ k, ‖g k‖ = 1) :
    diagonal g ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  simp [Complex.conj_mul', hg k]

/-- A unitary matrix is real orthogonal times diagonal unitary times real orthogonal. -/
theorem exists_orth_diagonal_orth {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ V O : Matrix (Fin 4) (Fin 4) ℝ, Vᵀ * V = 1 ∧ Oᵀ * O = 1 ∧ ∃ f : Fin 4 → ℂ,
      (∀ k, ‖f k‖ = 1) ∧ U = V.map ofReal * diagonal f * O.map ofReal := by
  have hUt : Uᵀ ∈ Matrix.unitaryGroup (Fin 4) ℂ := Matrix.transpose_mem_unitaryGroup_iff.mpr hU
  have hS : (Uᵀ * U)ᵀ = Uᵀ * U := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  obtain ⟨O, hO, d, hd⟩ := exists_orthogonal_diagonal_of_symm_unitary hS (mul_mem hUt hU)
  set Oc := O.map ofReal with hOc
  have hOct : Ocᵀ * Oc = 1 := by
    rw [transpose_map_ofReal, ← map_ofReal_mul, hO, map_ofReal_one]
  have hOct' : Oc * Ocᵀ = 1 := mul_eq_one_comm.mp hOct
  have hD : diagonal d = Ocᵀ * (Uᵀ * U) * Oc := by
    rw [Matrix.mul_assoc, hd, ← Matrix.mul_assoc, hOct, Matrix.one_mul]
  have hOtU : Ocᵀ ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    rw [transpose_map_ofReal]
    exact map_ofReal_mem_unitaryGroup (orth_transpose hO)
  have hDU : diagonal d ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    rw [hD]
    exact mul_mem (mul_mem hOtU (mul_mem hUt hU)) (map_ofReal_mem_unitaryGroup hO)
  have hdn : ∀ k, ‖d k‖ = 1 := by
    intro k
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hDU) k) k
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply, Complex.star_def,
      Complex.conj_mul'] at h
    have h' : ‖d k‖ ^ 2 = 1 := by exact_mod_cast h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h'
  set f : Fin 4 → ℂ := fun k => exp (I * ((arg (d k) / 2 : ℝ) : ℂ)) with hfdef
  have hf : ∀ k, ‖f k‖ = 1 := fun k => norm_exp_I_mul_ofReal _
  have hff : ∀ k, f k * f k = d k := by
    intro k
    rw [hfdef, ← Complex.exp_add, ← mul_add, ← ofReal_add, add_halves]
    have h := Complex.norm_mul_exp_arg_mul_I (d k)
    rw [hdn k, ofReal_one, one_mul, mul_comm] at h
    exact h
  set g : Fin 4 → ℂ := fun k => star (f k) with hgdef
  have hg : ∀ k, g k * f k = 1 := by
    intro k
    rw [hgdef, Complex.star_def, Complex.conj_mul', hf k]
    simp
  have hgf : diagonal g * diagonal f = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact hg k
  have hgU : diagonal g ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
    diagonal_mem_unitaryGroup fun k => by rw [hgdef, norm_star, hf k]
  set V := U * Oc * diagonal g with hVdef
  have hV : V ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
    mul_mem (mul_mem hU (map_ofReal_mem_unitaryGroup hO)) hgU
  have hVt : Vᵀ * V = 1 := by
    have h : Vᵀ * V = diagonal g * (Ocᵀ * (Uᵀ * U) * Oc) * diagonal g := by
      simp only [hVdef, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [h, ← hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext k
    rw [← hff k]
    linear_combination (g k * f k + 1) * hg k
  have hVstar : Vᵀ = star V := by
    have h1 : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hV
    calc Vᵀ = Vᵀ * (V * star V) := by rw [h1, Matrix.mul_one]
      _ = star V := by rw [← Matrix.mul_assoc, hVt, Matrix.one_mul]
  have hreal : ∀ i j, (V i j).im = 0 := by
    intro i j
    have h := congrFun (congrFun hVstar j) i
    rw [Matrix.transpose_apply, Matrix.star_apply, Complex.star_def] at h
    exact Complex.conj_eq_iff_im.mp h.symm
  have hVr : (V.map re).map ofReal = V := by
    ext i j
    apply Complex.ext <;> simp [hreal i j]
  have hVrt : (V.map re)ᵀ * V.map re = 1 := by
    apply Matrix.map_injective Complex.ofReal_injective
    dsimp only
    rw [map_ofReal_mul, ← transpose_map_ofReal, hVr, hVt, map_ofReal_one]
  refine ⟨V.map re, Oᵀ, hVrt, orth_transpose hO, f, hf, ?_⟩
  rw [hVr, ← transpose_map_ofReal, ← hOc, hVdef]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonal g), hgf, Matrix.one_mul, hOct', Matrix.mul_one]

/-- An orthogonal matrix is a determinant-one orthogonal matrix times a diagonal sign matrix. -/
theorem exists_det_eq_one_mul_sign {V : Matrix (Fin 4) (Fin 4) ℝ} (hV : Vᵀ * V = 1) :
    ∃ V' : Matrix (Fin 4) (Fin 4) ℝ, V'ᵀ * V' = 1 ∧ V'.det = 1 ∧ ∃ g : Fin 4 → ℝ,
      (∀ k, g k * g k = 1) ∧ V = V' * diagonal g := by
  have hs : V.det * V.det = 1 := by
    have h := congrArg Matrix.det hV
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  set g : Fin 4 → ℝ := ![V.det, 1, 1, 1] with hgdef
  have hg : ∀ k, g k * g k = 1 := by
    intro k
    fin_cases k <;> simp [hgdef, hs]
  have hgg : diagonal g * diagonal g = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact hg k
  refine ⟨V * diagonal g, ?_, ?_, g, hg, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul, hgg]
  · rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_four]
    simp [hgdef, hs]
  · rw [Matrix.mul_assoc, hgg, Matrix.mul_one]

theorem magic_conj_mul3 (A B C : Matrix (Fin 4) (Fin 4) ℂ) :
    magic * (A * B * C) * star magic =
      (magic * A * star magic) * (magic * B * star magic) * (magic * C * star magic) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star magic) magic, star_magic_mul_magic, Matrix.one_mul,
    ← Matrix.mul_assoc (star magic) magic, star_magic_mul_magic, Matrix.one_mul]

/-- A unitary matrix is a local unitary, a magic-basis diagonal unitary and a local unitary. -/
theorem exists_local_diagonal_local {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ W₁ W₂ : Matrix (Fin 4) (Fin 4) ℂ, IsLocal W₁ ∧ IsLocal W₂ ∧ ∃ f : Fin 4 → ℂ,
      (∀ k, ‖f k‖ = 1) ∧ U = W₁ * (magic * diagonal f * star magic) * W₂ := by
  have hM : magic ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
    Matrix.mem_unitaryGroup_iff'.mpr star_magic_mul_magic
  have hU' : star magic * U * magic ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
    mul_mem (mul_mem (Matrix.mem_unitaryGroup_iff'.mpr (by rw [star_star]; exact
      magic_mul_star_magic)) hU) hM
  obtain ⟨V, O, hV, hO, f, hf, hVO⟩ := exists_orth_diagonal_orth hU'
  obtain ⟨V', hV', hdV', g, hg, rfl⟩ := exists_det_eq_one_mul_sign hV
  obtain ⟨O', hO', hdO', g', hg', hOt⟩ := exists_det_eq_one_mul_sign (orth_transpose hO)
  have hOeq : O = diagonal g' * O'ᵀ := by
    rw [← Matrix.transpose_transpose O, hOt, Matrix.transpose_mul, Matrix.diagonal_transpose]
  have hgn : ∀ {h : Fin 4 → ℝ}, (∀ k, h k * h k = 1) → ∀ k, ‖((h k : ℝ) : ℂ)‖ = 1 := by
    intro h hh k
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 : |h k| * |h k| = 1 := by rw [← abs_mul, hh k, abs_one]
    nlinarith [abs_nonneg (h k)]
  refine ⟨magic * V'.map ofReal * star magic, magic * O'ᵀ.map ofReal * star magic,
    localReal_of_det_eq_one hV' hdV', localReal_of_det_eq_one (orth_transpose hO')
      (by rw [Matrix.det_transpose, hdO']),
    fun k => (g k : ℂ) * f k * (g' k : ℂ), ?_, ?_⟩
  · intro k
    rw [norm_mul, norm_mul, hf k, hgn hg k, hgn hg' k]
    norm_num
  · have hU2 : U = magic * (star magic * U * magic) * star magic := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, magic_mul_star_magic, Matrix.one_mul,
        Matrix.mul_assoc, magic_mul_star_magic, Matrix.mul_one]
    rw [hU2, hVO, hOeq, map_ofReal_mul, map_ofReal_mul, Matrix.diagonal_map ofReal_zero,
      Matrix.diagonal_map ofReal_zero]
    rw [← magic_conj_mul3]
    congr 2
    simp only [Matrix.mul_assoc]
    congr 1
    simp only [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2
    funext k
    ring

/-! ## The canonical part and the universal circuit -/

theorem exp_I_mul_eq_neg (x : ℝ) : exp (I * x) = -exp (I * ((x - Real.pi : ℝ) : ℂ)) := by
  rw [ofReal_sub, mul_sub, Complex.exp_sub, mul_comm I (Real.pi : ℂ), Complex.exp_pi_mul_I,
    div_neg, div_one, neg_neg]

/-- A diagonal unitary in the magic basis is a global phase times the canonical circuit. -/
theorem exists_vwCore {f : Fin 4 → ℂ} (hf : ∀ k, ‖f k‖ = 1) :
    ∃ φ a b c : ℝ, magic * diagonal f * star magic = exp (φ * I) • vwCore a b c := by
  have hfk : ∀ k, f k = exp (I * (arg (f k) : ℂ)) := by
    intro k
    have h := Complex.norm_mul_exp_arg_mul_I (f k)
    rw [hf k, ofReal_one, one_mul, mul_comm] at h
    exact h.symm
  refine ⟨(arg (f 0) + arg (f 1)) / 2,
    (arg (f 2) + (arg (f 3) - Real.pi)) / 2 - (arg (f 0) + arg (f 1)) / 2,
    ((arg (f 1) - arg (f 0)) + (arg (f 3) - Real.pi - arg (f 2))) / 2,
    ((arg (f 1) - arg (f 0)) - (arg (f 3) - Real.pi - arg (f 2))) / 2, ?_⟩
  rw [vwCore_eq, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
  congr 3
  funext k
  fin_cases k <;>
    simp only [Fin.isValue, Pi.smul_apply, smul_eq_mul, vwPhase, Fin.zero_eta, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk]
  · conv_lhs => rw [hfk]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · conv_lhs => rw [hfk]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · conv_lhs => rw [hfk]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · conv_lhs => rw [hfk, exp_I_mul_eq_neg]
    simp only [mul_neg, neg_inj, ← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- The ZYZ product `Rz(β) · Ry(γ) · Rz(δ)`. -/
def zyz (β γ δ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := rzGate β * ryMatrix γ * rzGate δ

/-- The universal three-CNOT two-qubit circuit of Vatan and Williams (Phys. Rev. A 69,
032315 (2004), Fig. 6): ZYZ layers on both qubits around the canonical part `vwCore`.
Angles `0`–`5` parametrise the last layer (high qubit, then low qubit), `6`–`11` the first
layer and `12`–`14` the canonical part. -/
def kak3 (θ : Fin 15 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (zyz (θ 0) (θ 1) (θ 2) ⊗ₖ zyz (θ 3) (θ 4) (θ 5)) * vwCore (θ 12) (θ 13) (θ 14) *
    (zyz (θ 6) (θ 7) (θ 8) ⊗ₖ zyz (θ 9) (θ 10) (θ 11))

theorem smul_kronecker_smul (c d : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (c • A) ⊗ₖ (d • B) = (c * d) • (A ⊗ₖ B) := by
  ext i j
  simp only [kronecker_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- A local unitary is a global phase times a tensor product of ZYZ products. -/
theorem IsLocal.exists_zyz {W : Matrix (Fin 4) (Fin 4) ℂ} (h : IsLocal W) :
    ∃ α : ℝ, ∃ x : Fin 6 → ℝ, W = exp (α * I) •
      (zyz (x 0) (x 1) (x 2) ⊗ₖ zyz (x 3) (x 4) (x 5)) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := h
  obtain ⟨α, β, γ, δ, hA'⟩ := zyz_exists hA
  obtain ⟨α', β', γ', δ', hB'⟩ := zyz_exists hB
  refine ⟨α + α', ![β, γ, δ, β', γ', δ'], ?_⟩
  rw [hA', hB', smul_kronecker_smul, ← Complex.exp_add, ofReal_add, add_mul]
  rfl

/-- **KAK decomposition.** Every two-qubit unitary is a global phase times the universal
three-CNOT circuit `kak3 θ` of Vatan and Williams. -/
theorem kak3_exists {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ (φ : ℝ) (θ : Fin 15 → ℝ), U = Complex.exp (φ * I) • kak3 θ := by
  obtain ⟨W₁, W₂, h₁, h₂, f, hf, hU'⟩ := exists_local_diagonal_local hU
  obtain ⟨φ, a, b, c, hc⟩ := exists_vwCore hf
  obtain ⟨α₁, x, hx⟩ := h₁.exists_zyz
  obtain ⟨α₂, y, hy⟩ := h₂.exists_zyz
  refine ⟨α₁ + φ + α₂,
    ![x 0, x 1, x 2, x 3, x 4, x 5, y 0, y 1, y 2, y 3, y 4, y 5, a, b, c], ?_⟩
  rw [hU', hc, hx, hy, kak3]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ## The universal circuit as a gate list on qubits `i ≠ j` -/

section Circuit

open CatCrypt.Quantum.QFT (listMatrix listMatrix_cons listMatrix_nil listMatrix_append)
open CatCrypt.Quantum.HQPL.ConcreteLowering (embedGate1_mul_embedGate1_eq_embedGate2)

variable {n : ℕ}

theorem embedGate1_eq_embedGate2_left {i j : Fin n} (hij : i ≠ j) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n i A = embedGate2 n i j (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) hij := by
  rw [← embedGate1_mul_embedGate1_eq_embedGate2, embedGate1_one, Matrix.mul_one]

theorem embedGate1_eq_embedGate2_right {i j : Fin n} (hij : i ≠ j)
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n j B = embedGate2 n i j ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B) hij := by
  rw [← embedGate1_mul_embedGate1_eq_embedGate2, embedGate1_one, Matrix.one_mul]

theorem embedGate2_cnot_rev {i j : Fin n} (hij : i ≠ j) :
    embedGate2 n j i Programs.Qubit.cnot (Ne.symm hij) = embedGate2 n i j cnotRev hij :=
  Optimization.SwapConj.embedGate2_swap_pair hij _

theorem rzGate_neg_pi_div_two : rzGate (-(Real.pi / 2)) = sdgMatrix := by
  rw [rzGate, exp_I_mul_ofReal, sdgMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `Ry(γ)` as the gates `Rz(−π/2)`, `H`, `Rz(γ)`, `H`, `S` on qubit `q`, over an angle
carrier `α`: `rz q a` rotates qubit `q` by `a`, and `nhp` is the angle `−π/2`. -/
@[simp] def ryGatesA {α : Type*} (rz : Fin n → α → Gate n) (nhp : α) (q : Fin n) (γ : α) :
    List (Gate n) :=
  [rz q nhp, Gate.H q, rz q γ, Gate.H q, Gate.S q]

/-- `Ry(γ)` as the gates `Rz(−π/2)`, `H`, `Rz(γ)`, `H`, `S` on qubit `q`. -/
def ryGatesR (q : Fin n) (γ : ℝ) : List (Gate n) := ryGatesA Gate.Rz (-(Real.pi / 2)) q γ

theorem listMatrix_ryGatesR (q : Fin n) (γ : ℝ) :
    listMatrix (ryGatesR q γ) = exp (I * ((γ / 2 : ℝ) : ℂ)) • embedGate1 n q (ryMatrix γ) := by
  simp only [ryGatesR, ryGatesA, listMatrix_cons, listMatrix_nil, Matrix.one_mul, gateEmbedding,
    embedGate1_mul]
  rw [rzGate_neg_pi_div_two, phaseS_hadamard_rz_hadamard_sdg, embedGate1_smul]

/-- The ZYZ product `Rz(β) · Ry(γ) · Rz(δ)` as gates on qubit `q`, over an angle carrier `α`
with the rotation `rz` and the angle `nhp` for `−π/2`. -/
@[simp] def zyzGatesA {α : Type*} (rz : Fin n → α → Gate n) (nhp : α) (q : Fin n)
    (β γ δ : α) : List (Gate n) :=
  rz q δ :: (ryGatesA rz nhp q γ ++ [rz q β])

/-- The ZYZ product `Rz(β) · Ry(γ) · Rz(δ)` as gates on qubit `q`. -/
def zyzGates (q : Fin n) (β γ δ : ℝ) : List (Gate n) :=
  zyzGatesA Gate.Rz (-(Real.pi / 2)) q β γ δ

theorem listMatrix_zyzGates (q : Fin n) (β γ δ : ℝ) :
    listMatrix (zyzGates q β γ δ) = exp (I * ((γ / 2 : ℝ) : ℂ)) • embedGate1 n q (zyz β γ δ) := by
  rw [zyzGates, zyzGatesA, listMatrix_cons, listMatrix_append, ← ryGatesR, listMatrix_ryGatesR,
    listMatrix_cons, listMatrix_nil, Matrix.one_mul]
  simp only [gateEmbedding, Matrix.mul_smul, Matrix.smul_mul, embedGate1_mul, zyz]

/-- The canonical part `vwCore a b c` as gates on qubits `i` (high) and `j` (low), over an
angle carrier `α` with the rotation `rz` and the angles `hp`, `nhp` for `π/2`, `−π/2`. -/
@[simp] def vwCoreGatesA {α : Type*} (rz : Fin n → α → Gate n) (hp nhp : α) (i j : Fin n)
    (a b c : α) : List (Gate n) :=
  [rz j hp, Gate.CNOT j i, rz i a] ++ ryGatesA rz nhp j b ++ [Gate.CNOT i j] ++
    ryGatesA rz nhp j c ++ [Gate.CNOT j i, rz i nhp]

/-- The canonical part `vwCore a b c` as gates on qubits `i` (high) and `j` (low). -/
def vwCoreGates (i j : Fin n) (a b c : ℝ) : List (Gate n) :=
  vwCoreGatesA Gate.Rz (Real.pi / 2) (-(Real.pi / 2)) i j a b c

theorem listMatrix_vwCoreGates {i j : Fin n} (hij : i ≠ j) (a b c : ℝ) :
    listMatrix (vwCoreGates i j a b c) =
      exp (I * (((b + c) / 2 : ℝ) : ℂ)) • embedGate2 n i j (vwCore a b c) hij := by
  have hab : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ryMatrix b) *
      (rzGate a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) = rzGate a ⊗ₖ ryMatrix b := by
    rw [kronecker_mul_kronecker, Matrix.one_mul, Matrix.mul_one]
  rw [vwCoreGates, vwCoreGatesA, ← ryGatesR, ← ryGatesR]
  simp only [listMatrix_append, listMatrix_cons, listMatrix_nil, Matrix.one_mul,
    listMatrix_ryGatesR, gateEmbedding, dite_eq_right hij, dite_eq_right (Ne.symm hij),
    embedGate2_cnot_rev hij, embedGate1_eq_embedGate2_left hij,
    embedGate1_eq_embedGate2_right hij, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    embedGate2_mul]
  rw [← Complex.exp_add, ← mul_add, ← ofReal_add, add_div]
  congr 2
  simp only [vwCore, ← hab, Matrix.mul_assoc]

/-- The universal circuit `kak3 θ` as gates on qubits `i` (high) and `j` (low), over an angle
carrier `α` with the rotation `rz` and the angles `hp`, `nhp` for `π/2`, `−π/2`. -/
@[simp] def kak3GatesA {α : Type*} (rz : Fin n → α → Gate n) (hp nhp : α) (i j : Fin n)
    (θ : Fin 15 → α) : List (Gate n) :=
  zyzGatesA rz nhp j (θ 9) (θ 10) (θ 11) ++ zyzGatesA rz nhp i (θ 6) (θ 7) (θ 8) ++
    vwCoreGatesA rz hp nhp i j (θ 12) (θ 13) (θ 14) ++ zyzGatesA rz nhp j (θ 3) (θ 4) (θ 5) ++
    zyzGatesA rz nhp i (θ 0) (θ 1) (θ 2)

/-- The universal circuit `kak3 θ` as gates on qubits `i` (high) and `j` (low). -/
def kak3Gates (i j : Fin n) (θ : Fin 15 → ℝ) : List (Gate n) :=
  kak3GatesA Gate.Rz (Real.pi / 2) (-(Real.pi / 2)) i j θ

/-- The universal circuit `kak3` as gates on qubits `i` (high) and `j` (low), with the exact
angles `θ` carried by `Gate.RzQ`; `ofPi (1 / 2)` and `ofPi (-(1 / 2))` are `π/2` and `−π/2`. -/
def kak3GatesQ (i j : Fin n) (θ : Fin 15 → PiLin) : List (Gate n) :=
  kak3GatesA Gate.RzQ (PiLin.ofPi (1 / 2)) (PiLin.ofPi (-(1 / 2))) i j θ

/-- The ZYZ template `Rz(β) · Ry(γ) · Rz(δ)` on qubit `q` with the exact angles
`(β, γ, δ) = (θ 0, θ 1, θ 2)` carried by `Gate.RzQ`; `ofPi (-(1 / 2))` is `−π/2`. -/
def zyzGatesQ (q : Fin n) (θ : Fin 3 → PiLin) : List (Gate n) :=
  zyzGatesA Gate.RzQ (PiLin.ofPi (-(1 / 2))) q (θ 0) (θ 1) (θ 2)

/-- The exact ZYZ template has seven gates. -/
theorem length_zyzGatesQ (q : Fin n) (θ : Fin 3 → PiLin) : (zyzGatesQ q θ).length = 7 := by
  simp [zyzGatesQ]

theorem listMatrix_kak3Gates {i j : Fin n} (hij : i ≠ j) (θ : Fin 15 → ℝ) :
    listMatrix (kak3Gates i j θ) =
      exp (I * (((θ 1 + θ 4 + θ 7 + θ 10 + θ 13 + θ 14) / 2 : ℝ) : ℂ)) •
        embedGate2 n i j (kak3 θ) hij := by
  have hL : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B) = A ⊗ₖ B := fun A B => by
    rw [kronecker_mul_kronecker, Matrix.one_mul, Matrix.mul_one]
  rw [kak3Gates, kak3GatesA, ← zyzGates, ← zyzGates, ← zyzGates, ← zyzGates, ← vwCoreGates]
  simp only [listMatrix_append, listMatrix_zyzGates, listMatrix_vwCoreGates hij,
    embedGate1_eq_embedGate2_left hij, embedGate1_eq_embedGate2_right hij,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, embedGate2_mul, ← Complex.exp_add]
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    rw [kak3, ← hL (zyz (θ 0) (θ 1) (θ 2)) (zyz (θ 3) (θ 4) (θ 5)),
      ← hL (zyz (θ 6) (θ 7) (θ 8)) (zyz (θ 9) (θ 10) (θ 11))]
    simp only [Matrix.mul_assoc]

/-- **KAK decomposition in circuit form.** On qubits `i ≠ j` of `n`, the embedded two-qubit
unitary `U` is, up to a global phase, the matrix of the gate list `kak3Gates i j θ` of `Rz`,
`H`, `S` and `CNOT` gates. -/
theorem kak3_exists_listMatrix {i j : Fin n} (hij : i ≠ j) {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ (φ : ℝ) (θ : Fin 15 → ℝ),
      listMatrix (kak3Gates i j θ) = Complex.exp (φ * I) • embedGate2 n i j U hij := by
  obtain ⟨ψ, θ, hθ⟩ := kak3_exists hU
  refine ⟨(θ 1 + θ 4 + θ 7 + θ 10 + θ 13 + θ 14) / 2 - ψ, θ, ?_⟩
  rw [listMatrix_kak3Gates hij, hθ, embedGate2_smul, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ### Exact angles read as real angles -/

/-- The gate with an exact rotation `RzQ q p` read as the real rotation `Rz q (toReal p)`;
every other gate is unchanged. -/
def rzQToRz : Gate n → Gate n
  | .RzQ q p => .Rz q (PiLin.toReal p)
  | g => g

/-- `rzQToRz` preserves the matrix of a gate. -/
theorem gateEmbedding_rzQToRz (g : Gate n) : gateEmbedding (rzQToRz g) = gateEmbedding g := by
  cases g <;> rfl

/-- `rzQToRz` preserves the matrix of a gate list. -/
theorem listMatrix_map_rzQToRz (l : List (Gate n)) :
    listMatrix (l.map rzQToRz) = listMatrix l := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [List.map_cons, listMatrix_cons, listMatrix_cons, ih, gateEmbedding_rzQToRz]

section Naturality

variable {α β : Type*} {rz : Fin n → α → Gate n} {rz' : Fin n → β → Gate n} {t : α → β}

/-! Naturality of the parametric templates: if `rzQToRz` sends each rotation `rz q a` to
`rz' q (t a)`, it sends a template over `rz` to the template over `rz'` at the angles mapped
by `t`. -/

/-- Naturality of `ryGatesA` along `rzQToRz`. -/
theorem map_rzQToRz_ryGatesA (hrz : ∀ q a, rzQToRz (rz q a) = rz' q (t a)) (nhp : α)
    (q : Fin n) (γ : α) :
    (ryGatesA rz nhp q γ).map rzQToRz = ryGatesA rz' (t nhp) q (t γ) := by
  simp only [ryGatesA, List.map_cons, List.map_nil, hrz]
  rfl

/-- Naturality of `zyzGatesA` along `rzQToRz`. -/
theorem map_rzQToRz_zyzGatesA (hrz : ∀ q a, rzQToRz (rz q a) = rz' q (t a)) (nhp : α)
    (q : Fin n) (β γ δ : α) :
    (zyzGatesA rz nhp q β γ δ).map rzQToRz = zyzGatesA rz' (t nhp) q (t β) (t γ) (t δ) := by
  simp only [zyzGatesA, List.map_cons, List.map_append, List.map_nil, hrz,
    map_rzQToRz_ryGatesA hrz]

/-- Naturality of `vwCoreGatesA` along `rzQToRz`. -/
theorem map_rzQToRz_vwCoreGatesA (hrz : ∀ q a, rzQToRz (rz q a) = rz' q (t a)) (hp nhp : α)
    (i j : Fin n) (a b c : α) :
    (vwCoreGatesA rz hp nhp i j a b c).map rzQToRz =
      vwCoreGatesA rz' (t hp) (t nhp) i j (t a) (t b) (t c) := by
  simp only [vwCoreGatesA, List.map_cons, List.map_nil, List.map_append, hrz,
    map_rzQToRz_ryGatesA hrz]
  rfl

/-- Naturality of `kak3GatesA` along `rzQToRz`. -/
theorem map_rzQToRz_kak3GatesA (hrz : ∀ q a, rzQToRz (rz q a) = rz' q (t a)) (hp nhp : α)
    (i j : Fin n) (θ : Fin 15 → α) :
    (kak3GatesA rz hp nhp i j θ).map rzQToRz = kak3GatesA rz' (t hp) (t nhp) i j (t ∘ θ) := by
  simp only [kak3GatesA, List.map_append, map_rzQToRz_zyzGatesA hrz,
    map_rzQToRz_vwCoreGatesA hrz, Function.comp_apply]

end Naturality

/-- The exact angle `ofPi (1 / 2)` is `π/2`. -/
theorem toReal_ofPi_half : PiLin.toReal (PiLin.ofPi (1 / 2)) = Real.pi / 2 := by
  simp only [PiLin.toReal_ofPi]
  push_cast
  ring

/-- The exact angle `ofPi (-(1 / 2))` is `−π/2`. -/
theorem toReal_ofPi_neg_half : PiLin.toReal (PiLin.ofPi (-(1 / 2))) = -(Real.pi / 2) := by
  simp only [PiLin.toReal_ofPi]
  push_cast
  ring

/-- The exact template `kak3GatesQ`, read through `rzQToRz`, is the real template `kak3Gates`
at the real angles. -/
theorem map_rzQToRz_kak3GatesQ (i j : Fin n) (θ : Fin 15 → PiLin) :
    (kak3GatesQ i j θ).map rzQToRz = kak3Gates i j (PiLin.toReal ∘ θ) := by
  rw [kak3GatesQ, map_rzQToRz_kak3GatesA (rz' := Gate.Rz) (fun _ _ => rfl),
    toReal_ofPi_half, toReal_ofPi_neg_half, kak3Gates]

/-- The exact template `kak3GatesQ` has the matrix of `kak3Gates` at the real angles. -/
theorem listMatrix_kak3GatesQ (i j : Fin n) (θ : Fin 15 → PiLin) :
    listMatrix (kak3GatesQ i j θ) = listMatrix (kak3Gates i j (PiLin.toReal ∘ θ)) := by
  rw [← map_rzQToRz_kak3GatesQ, listMatrix_map_rzQToRz]

/-- The exact template `zyzGatesQ`, read through `rzQToRz`, is the real template `zyzGates`
at the real angles. -/
theorem map_rzQToRz_zyzGatesQ (q : Fin n) (θ : Fin 3 → PiLin) :
    (zyzGatesQ q θ).map rzQToRz =
      zyzGates q (PiLin.toReal (θ 0)) (PiLin.toReal (θ 1)) (PiLin.toReal (θ 2)) := by
  rw [zyzGatesQ, map_rzQToRz_zyzGatesA (rz' := Gate.Rz) (fun _ _ => rfl),
    toReal_ofPi_neg_half, zyzGates]

/-- The exact template `zyzGatesQ` has the matrix of `zyzGates` at the real angles. -/
theorem listMatrix_zyzGatesQ (q : Fin n) (θ : Fin 3 → PiLin) :
    listMatrix (zyzGatesQ q θ) =
      listMatrix (zyzGates q (PiLin.toReal (θ 0)) (PiLin.toReal (θ 1)) (PiLin.toReal (θ 2))) := by
  rw [← map_rzQToRz_zyzGatesQ, listMatrix_map_rzQToRz]

end Circuit

end CatCrypt.Quantum.Synthesis.KAK
