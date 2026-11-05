/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.KAK

/-!
# Two-qubit templates with zero, one and two CNOTs

`KAK.lean` writes every two-qubit unitary as `W₁ · (M · diag f · M†) · W₂` with `M` the magic
basis, `W₁`, `W₂` local and `f` a vector of unit phases (`exists_local_diagonal_local`). The
phases `f` decide how many CNOTs a circuit for the unitary needs. This file fixes, for each
CNOT count `k ≤ 2`, a condition `classPhase k f` on the phases and a template circuit, and
proves that every unitary of class `k` is a global phase times its template.

* Class `0`: all four phases are equal, so the canonical part is a scalar and the unitary is
  local. Template `kak0`: a ZYZ layer on both qubits.
* Class `1`: `f` is proportional to `(1, 1, i, i)`, the magic-basis phases of
  `exp(−i π/4 · Z⊗Z)`, which is the local class of CNOT. Template `kak1`: local, CNOT, local.
* Class `2`: `f 0 · f 3 = f 1 · f 2`. In the Cartan coordinates of
  `exp(i(x X⊗X + y Y⊗Y + z Z⊗Z))`, whose magic-basis phases are `x − y + z`, `−x + y + z`,
  `x + y − z`, `−x − y − z`, the condition says `y ≡ 0 (mod π/2)`: the class of
  `exp(i(x X⊗X + z Z⊗Z))`, which the Weyl group maps to the class of `exp(i(x X⊗X + y Y⊗Y))`.
  Template `kak2`: local, CNOT, `Rx(s)` on the control and `Rz(t)` on the target, CNOT,
  local. Conjugation by CNOT sends `X⊗1` to `X⊗X` and `1⊗Z` to `Z⊗Z`, so the middle part is
  `exp(−i s/2 · X⊗X) · exp(−i t/2 · Z⊗Z)` up to phase, diagonal in the magic basis
  (`core2_eq`); its two angles reach every phase vector of class `2`.
* Class `3`: no condition; `KAK.kak3_exists`.

## Main results

* `kak0_exists`, `kak1_exists`, `kak2_exists` — a unitary of class `k` is a global phase
  times the template `k`.
* `kak0_exists_listMatrix`, `kak1_exists_listMatrix`, `kak2_exists_listMatrix` — the same as
  gate lists on qubits `i ≠ j` with `0`, `1` and `2` CNOTs.
* `inClass_three` — every two-qubit unitary is of class `3`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix Complex
open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.GateUnitarity CatCrypt.Quantum.TensorProduct
open CatCrypt.Quantum.OpenQASMImportGates CatCrypt.Quantum.Synthesis.ZYZ
open CatCrypt.Quantum.Synthesis.KAK

namespace CatCrypt.Quantum.Synthesis.KAKSmall

/-! ## The classes -/

/-- The condition on the magic-basis phases `f` of the canonical part for class `k`: all
phases equal (`0`), proportional to `(1, 1, i, i)` (`1`), `f 0 · f 3 = f 1 · f 2` (`2`), none
(`3`). -/
def classPhase : Fin 4 → (Fin 4 → ℂ) → Prop :=
  ![fun f => f 1 = f 0 ∧ f 2 = f 0 ∧ f 3 = f 0,
    fun f => f 1 = f 0 ∧ f 2 = I * f 0 ∧ f 3 = I * f 0,
    fun f => f 0 * f 3 = f 1 * f 2,
    fun _ => True]

/-- `U` is of class `k`: it has the form `W₁ · (M · diag f · M†) · W₂` of
`KAK.exists_local_diagonal_local` with phases `f` satisfying `classPhase k`. -/
def InClass (k : Fin 4) (U : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ W₁ W₂ : Matrix (Fin 4) (Fin 4) ℂ, IsLocal W₁ ∧ IsLocal W₂ ∧ ∃ f : Fin 4 → ℂ,
    (∀ l, ‖f l‖ = 1) ∧ classPhase k f ∧ U = W₁ * (magic * diagonal f * star magic) * W₂

/-- Every two-qubit unitary is of class `3`. -/
theorem inClass_three {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    InClass 3 U := by
  obtain ⟨W₁, W₂, h₁, h₂, f, hf, hU'⟩ := exists_local_diagonal_local hU
  exact ⟨W₁, W₂, h₁, h₂, f, hf, trivial, hU'⟩

/-! ## Local facts -/

theorem isLocal_kronecker {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    IsLocal (A ⊗ₖ B) :=
  ⟨A, B, hA, hB, rfl⟩

theorem smul_kronecker_left (c : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (c • A) ⊗ₖ B = c • (A ⊗ₖ B) := by
  simpa using smul_kronecker_smul c 1 A B

theorem hadamard_mem_unitaryGroup :
    Programs.Qubit.hadamard ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr hadamard_unitary

theorem phaseS_mem_unitaryGroup :
    Programs.Qubit.phaseS ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr phaseS_unitary

/-- A unit complex number is `exp (arg z · i)`. -/
theorem eq_exp_arg_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z = exp ((arg z : ℂ) * I) := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  rw [hz, ofReal_one, one_mul] at h
  exact h.symm

/-- Two local layers around `c • K` give a global phase times ZYZ layers around `K`. -/
theorem exists_zyz_sandwich {W₁ W₂ K : Matrix (Fin 4) (Fin 4) ℂ} (h₁ : IsLocal W₁)
    (h₂ : IsLocal W₂) (φ : ℝ) :
    ∃ (ψ : ℝ) (x y : Fin 6 → ℝ), W₁ * (exp (φ * I) • K) * W₂ = exp (ψ * I) •
      ((zyz (x 0) (x 1) (x 2) ⊗ₖ zyz (x 3) (x 4) (x 5)) * K *
        (zyz (y 0) (y 1) (y 2) ⊗ₖ zyz (y 3) (y 4) (y 5))) := by
  obtain ⟨α₁, x, hx⟩ := h₁.exists_zyz
  obtain ⟨α₂, y, hy⟩ := h₂.exists_zyz
  refine ⟨α₁ + φ + α₂, x, y, ?_⟩
  rw [hx, hy]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ## Class `0`: local unitaries -/

/-- The zero-CNOT template: ZYZ products on both qubits. Angles `0`–`2` act on the high
qubit, `3`–`5` on the low qubit. -/
def kak0 (θ : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  zyz (θ 0) (θ 1) (θ 2) ⊗ₖ zyz (θ 3) (θ 4) (θ 5)

/-- **Class `0`.** A unitary of class `0` is a global phase times `kak0 θ`. -/
theorem kak0_exists {U : Matrix (Fin 4) (Fin 4) ℂ} (h : InClass 0 U) :
    ∃ (φ : ℝ) (θ : Fin 6 → ℝ), U = exp (φ * I) • kak0 θ := by
  obtain ⟨W₁, W₂, h₁, h₂, f, hf, hc, rfl⟩ := h
  obtain ⟨h1, h2, h3⟩ := hc
  have hd : diagonal f = f 0 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    rw [Matrix.smul_one_eq_diagonal]
    congr 1
    funext l
    fin_cases l <;> simp [h1, h2, h3]
  have hm : magic * diagonal f * star magic = f 0 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, magic_mul_star_magic]
  obtain ⟨α, x, hx⟩ := (h₁.mul h₂).exists_zyz
  refine ⟨arg (f 0) + α, x, ?_⟩
  rw [hm, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hx, smul_smul]
  conv_lhs => rw [eq_exp_arg_of_norm_eq_one (hf 0)]
  rw [← Complex.exp_add, kak0]
  congr 2
  push_cast
  ring

/-! ## Class `1`: the CNOT class -/

/-- The one-CNOT template: ZYZ layers around a CNOT from the high to the low qubit. Angles
`0`–`5` parametrise the last layer (high qubit, then low qubit), `6`–`11` the first. -/
def kak1 (θ : Fin 12 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (zyz (θ 0) (θ 1) (θ 2) ⊗ₖ zyz (θ 3) (θ 4) (θ 5)) * Programs.Qubit.cnot *
    (zyz (θ 6) (θ 7) (θ 8) ⊗ₖ zyz (θ 9) (θ 10) (θ 11))

/-- The projector `|0⟩⟨0|`. -/
def proj0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- The projector `|1⟩⟨1|`. -/
def proj1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

theorem cnot_eq_ctrl :
    Programs.Qubit.cnot = proj0 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      proj1 ⊗ₖ Programs.Qubit.pauliX := by
  rw [kronecker_two_eq, kronecker_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Programs.Qubit.cnot, Programs.Qubit.pauliX, proj0, proj1]

theorem czGate_eq_ctrl :
    czGate = proj0 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + proj1 ⊗ₖ Programs.Qubit.pauliZ := by
  rw [kronecker_two_eq, kronecker_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [czGate, Programs.Qubit.pauliZ, proj0, proj1]

/-- `CZ = (1 ⊗ H) · CNOT · (1 ⊗ H)`. -/
theorem hadamard_cnot_hadamard :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Programs.Qubit.hadamard) * Programs.Qubit.cnot *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Programs.Qubit.hadamard) = czGate := by
  rw [cnot_eq_ctrl, czGate_eq_ctrl, Matrix.mul_add, Matrix.add_mul, kronecker_mul_kronecker,
    kronecker_mul_kronecker, kronecker_mul_kronecker, kronecker_mul_kronecker, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, Matrix.mul_one, hadamard_sq,
    hadamard_pauliX_hadamard]

/-- `diag(1, i, i, 1) = CZ · (S ⊗ S)`. -/
theorem czGate_mul_phaseS_phaseS :
    czGate * (Programs.Qubit.phaseS ⊗ₖ Programs.Qubit.phaseS) = diagonal ![1, I, I, 1] := by
  rw [kronecker_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [czGate, Programs.Qubit.phaseS, Matrix.mul_apply, Fin.sum_univ_four]

/-- `diag(1, i, i, 1)` has the magic-basis phases `(1, 1, i, i)`. -/
theorem magic_diagonal_cnotClass :
    magic * diagonal ![1, 1, I, I] * star magic = diagonal ![1, I, I, 1] := by
  apply magic_mul_eq_of_magic0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [magic0, Matrix.mul_apply, Fin.sum_univ_four]

/-- **Class `1`.** A unitary of class `1` is a global phase times `kak1 θ`. -/
theorem kak1_exists {U : Matrix (Fin 4) (Fin 4) ℂ} (h : InClass 1 U) :
    ∃ (φ : ℝ) (θ : Fin 12 → ℝ), U = exp (φ * I) • kak1 θ := by
  obtain ⟨W₁, W₂, h₁, h₂, f, hf, hc, rfl⟩ := h
  obtain ⟨h1, h2, h3⟩ := hc
  have hd : diagonal f = f 0 • diagonal ![1, 1, I, I] := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext l
    fin_cases l <;> simp [h1, h2, h3, mul_comm]
  have hH : IsLocal ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Programs.Qubit.hadamard) :=
    isLocal_kronecker (one_mem _) hadamard_mem_unitaryGroup
  have hS : IsLocal (Programs.Qubit.phaseS ⊗ₖ Programs.Qubit.phaseS) :=
    isLocal_kronecker phaseS_mem_unitaryGroup phaseS_mem_unitaryGroup
  have hm : W₁ * (magic * diagonal f * star magic) * W₂ =
      (W₁ * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Programs.Qubit.hadamard)) *
        (exp ((arg (f 0) : ℂ) * I) • Programs.Qubit.cnot) *
        (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Programs.Qubit.hadamard) *
          (Programs.Qubit.phaseS ⊗ₖ Programs.Qubit.phaseS) * W₂) := by
    rw [hd, Matrix.mul_smul, Matrix.smul_mul, magic_diagonal_cnotClass,
      ← czGate_mul_phaseS_phaseS, ← hadamard_cnot_hadamard,
      ← eq_exp_arg_of_norm_eq_one (hf 0)]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  obtain ⟨ψ, x, y, hxy⟩ := exists_zyz_sandwich (h₁.mul hH) ((hH.mul hS).mul h₂) (arg (f 0))
    (K := Programs.Qubit.cnot)
  refine ⟨ψ, ![x 0, x 1, x 2, x 3, x 4, x 5, y 0, y 1, y 2, y 3, y 4, y 5], ?_⟩
  rw [hm, hxy, kak1]
  rfl

/-! ## Class `2` -/

/-- The two-CNOT canonical part: CNOT from the high to the low qubit, `Rx(s)` on the high and
`Rz(t)` on the low qubit, CNOT again. -/
def core2 (s t : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Programs.Qubit.cnot * (rxMatrix s ⊗ₖ rzGate t) * Programs.Qubit.cnot

/-- The magic-basis phases of `core2 s t`. -/
def core2Phase (s t : ℝ) : Fin 4 → ℂ :=
  ![exp (I * ((-(s / 2) : ℝ) : ℂ)), exp (I * ((s / 2 : ℝ) : ℂ)),
    exp (I * t) * exp (I * ((-(s / 2) : ℝ) : ℂ)), exp (I * t) * exp (I * ((s / 2 : ℝ) : ℂ))]

theorem rxMatrix_eq (s : ℝ) :
    rxMatrix s = ((Real.cos (s / 2) : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (-(I * ((Real.sin (s / 2) : ℝ) : ℂ))) • Programs.Qubit.pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rxMatrix, Programs.Qubit.pauliX]

theorem cnot_pauliX_cnot :
    Programs.Qubit.cnot * (Programs.Qubit.pauliX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      Programs.Qubit.cnot = Programs.Qubit.pauliX ⊗ₖ Programs.Qubit.pauliX := by
  rw [kronecker_two_eq, kronecker_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Programs.Qubit.cnot, Programs.Qubit.pauliX, Matrix.mul_apply, Fin.sum_univ_four]

/-- `X ⊗ X` is diagonal in the magic basis. -/
theorem pauliX_pauliX_mul_magic0 :
    (Programs.Qubit.pauliX ⊗ₖ Programs.Qubit.pauliX : Matrix (Fin 4) (Fin 4) ℂ) * magic0 =
      magic0 * diagonal ![1, -1, 1, -1] := by
  rw [kronecker_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Programs.Qubit.pauliX, magic0, Matrix.mul_apply, Fin.sum_univ_four]

/-- `CNOT · (Rx(s) ⊗ 1) · CNOT = exp(−i s/2 · X⊗X)` is diagonal in the magic basis. -/
theorem cnot_rx_cnot_mul_magic0 (s : ℝ) :
    Programs.Qubit.cnot * (rxMatrix s ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Programs.Qubit.cnot *
        magic0 =
      magic0 * diagonal ![exp (I * ((-(s / 2) : ℝ) : ℂ)), exp (I * ((s / 2 : ℝ) : ℂ)),
        exp (I * ((-(s / 2) : ℝ) : ℂ)), exp (I * ((s / 2 : ℝ) : ℂ))] := by
  have hd : diagonal ![exp (I * ((-(s / 2) : ℝ) : ℂ)), exp (I * ((s / 2 : ℝ) : ℂ)),
      exp (I * ((-(s / 2) : ℝ) : ℂ)), exp (I * ((s / 2 : ℝ) : ℂ))] =
        ((Real.cos (s / 2) : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
          (-(I * ((Real.sin (s / 2) : ℝ) : ℂ))) • diagonal ![1, -1, 1, -1] := by
    simp only [exp_I_mul_ofReal, Real.cos_neg, Real.sin_neg]
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_smul, Matrix.diagonal_add]
    congr 1
    funext l
    fin_cases l <;> simp <;> ring
  rw [hd, rxMatrix_eq, kronecker_add_left, smul_kronecker_left, smul_kronecker_left]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, kronecker_one_one,
    Matrix.mul_one, cnot_sq, Matrix.one_mul]
  rw [cnot_pauliX_cnot, pauliX_pauliX_mul_magic0]

theorem rzGate_eq (t : ℝ) :
    rzGate t = ((1 + exp (I * t)) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((1 - exp (I * t)) / 2) • Programs.Qubit.pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rzGate, Programs.Qubit.pauliZ] <;> ring

theorem kronecker_add_right (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    A ⊗ₖ (B + C) = A ⊗ₖ B + A ⊗ₖ C := by
  ext i j
  simp only [_root_.CatCrypt.Quantum.TensorProduct.kronecker_apply, Matrix.add_apply, mul_add]

theorem cnot_pauliZ_cnot :
    Programs.Qubit.cnot * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Programs.Qubit.pauliZ) *
      Programs.Qubit.cnot = Programs.Qubit.pauliZ ⊗ₖ Programs.Qubit.pauliZ := by
  rw [kronecker_two_eq, kronecker_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Programs.Qubit.cnot, Programs.Qubit.pauliZ, Matrix.mul_apply, Fin.sum_univ_four]

/-- `Z ⊗ Z` is diagonal in the magic basis. -/
theorem pauliZ_pauliZ_mul_magic0 :
    (Programs.Qubit.pauliZ ⊗ₖ Programs.Qubit.pauliZ : Matrix (Fin 4) (Fin 4) ℂ) * magic0 =
      magic0 * diagonal ![1, 1, -1, -1] := by
  rw [kronecker_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Programs.Qubit.pauliZ, magic0, Matrix.mul_apply, Fin.sum_univ_four]

/-- `CNOT · (1 ⊗ P(t)) · CNOT = diag(1, e^{it}, e^{it}, 1)` is diagonal in the magic basis. -/
theorem cnot_rz_cnot_mul_magic0 (t : ℝ) :
    Programs.Qubit.cnot * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ rzGate t) * Programs.Qubit.cnot *
        magic0 = magic0 * diagonal ![1, 1, exp (I * t), exp (I * t)] := by
  have hd : diagonal ![1, 1, exp (I * t), exp (I * t)] =
      ((1 + exp (I * t)) / 2) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
        ((1 - exp (I * t)) / 2) • diagonal ![1, 1, -1, -1] := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_smul, Matrix.diagonal_add]
    congr 1
    funext l
    fin_cases l <;> simp <;> ring
  rw [hd, rzGate_eq, kronecker_add_right, ← smul_kronecker_eq_kronecker_smul,
    ← smul_kronecker_eq_kronecker_smul, smul_kronecker_left, smul_kronecker_left]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, kronecker_one_one,
    Matrix.mul_one, cnot_sq, Matrix.one_mul]
  rw [cnot_pauliZ_cnot, pauliZ_pauliZ_mul_magic0]

theorem core2_eq_mul (s t : ℝ) :
    core2 s t = (Programs.Qubit.cnot * (rxMatrix s ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      Programs.Qubit.cnot) * (Programs.Qubit.cnot *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ rzGate t) * Programs.Qubit.cnot) := by
  have h : rxMatrix s ⊗ₖ rzGate t = (rxMatrix s ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ rzGate t) := by
    rw [kronecker_mul_kronecker, Matrix.mul_one, Matrix.one_mul]
  rw [core2, h]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Programs.Qubit.cnot Programs.Qubit.cnot, cnot_sq, Matrix.one_mul]

theorem core2_mul_magic0 (s t : ℝ) :
    core2 s t * magic0 = magic0 * diagonal (core2Phase s t) := by
  rw [core2_eq_mul, Matrix.mul_assoc, cnot_rz_cnot_mul_magic0, ← Matrix.mul_assoc,
    cnot_rx_cnot_mul_magic0, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  congr 2
  funext l
  fin_cases l <;> simp [core2Phase, mul_comm]

/-- The two-CNOT canonical part is diagonal in the magic basis. -/
theorem core2_eq (s t : ℝ) : core2 s t = magic * diagonal (core2Phase s t) * star magic :=
  (magic_mul_eq_of_magic0 (core2_mul_magic0 s t).symm).symm

/-- Unit phases of class `2` are a global phase times the phases of `core2 s t`. -/
theorem exists_core2Phase {f : Fin 4 → ℂ} (hf : ∀ l, ‖f l‖ = 1) (hc : f 0 * f 3 = f 1 * f 2) :
    ∃ ψ s t : ℝ, f = exp (ψ * I) • core2Phase s t := by
  obtain ⟨a, ha⟩ : ∃ a : Fin 4 → ℝ, ∀ l, f l = exp (I * a l) :=
    ⟨fun l => arg (f l), fun l => by rw [mul_comm]; exact eq_exp_arg_of_norm_eq_one (hf l)⟩
  have h3 : f 3 = f 1 * f 2 / f 0 := by
    rw [eq_div_iff (by rw [ha 0]; exact Complex.exp_ne_zero _), mul_comm, hc]
  refine ⟨(a 0 + a 1) / 2, a 1 - a 0, a 2 - a 0, ?_⟩
  funext l
  fin_cases l <;>
    simp only [Fin.isValue, Pi.smul_apply, smul_eq_mul, core2Phase, Fin.zero_eta, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk]
  · rw [ha 0]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [ha 1]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [ha 2]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [h3, ha 0, ha 1, ha 2, ← Complex.exp_add, ← Complex.exp_sub]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- The two-CNOT template: ZYZ layers around `core2`. Angles `0`–`5` parametrise the last
layer (high qubit, then low qubit), `6`–`11` the first layer, `12` the `Rx` angle on the high
qubit and `13` the `Rz` angle on the low qubit. -/
def kak2 (θ : Fin 14 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (zyz (θ 0) (θ 1) (θ 2) ⊗ₖ zyz (θ 3) (θ 4) (θ 5)) * core2 (θ 12) (θ 13) *
    (zyz (θ 6) (θ 7) (θ 8) ⊗ₖ zyz (θ 9) (θ 10) (θ 11))

/-- **Class `2`.** A unitary of class `2` is a global phase times `kak2 θ`. -/
theorem kak2_exists {U : Matrix (Fin 4) (Fin 4) ℂ} (h : InClass 2 U) :
    ∃ (φ : ℝ) (θ : Fin 14 → ℝ), U = exp (φ * I) • kak2 θ := by
  obtain ⟨W₁, W₂, h₁, h₂, f, hf, hc, rfl⟩ := h
  obtain ⟨ψ, s, t, hst⟩ := exists_core2Phase hf hc
  have hm : magic * diagonal f * star magic = exp (ψ * I) • core2 s t := by
    rw [hst, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
    rw [core2_eq]
  obtain ⟨φ, x, y, hxy⟩ := exists_zyz_sandwich h₁ h₂ ψ (K := core2 s t)
  refine ⟨φ, ![x 0, x 1, x 2, x 3, x 4, x 5, y 0, y 1, y 2, y 3, y 4, y 5, s, t], ?_⟩
  rw [hm, hxy, kak2]
  rfl

/-! ## The templates as gate lists on qubits `i ≠ j` -/

section Circuit

open CatCrypt.Quantum.QFT (listMatrix listMatrix_cons listMatrix_nil listMatrix_append)

variable {n : ℕ}

/-- The canonical part `core2 s t` as gates on qubits `i` (control) and `j` (target), over an
angle carrier `α` with the rotation `rz`. -/
@[simp] def core2GatesA {α : Type*} (rz : Fin n → α → Gate n) (i j : Fin n) (s t : α) :
    List (Gate n) :=
  [Gate.CNOT i j, Gate.H i, rz i s, Gate.H i, rz j t, Gate.CNOT i j]

/-- The canonical part `core2 s t` as gates on qubits `i` (control) and `j` (target). -/
def core2Gates (i j : Fin n) (s t : ℝ) : List (Gate n) := core2GatesA Gate.Rz i j s t

theorem listMatrix_core2Gates {i j : Fin n} (hij : i ≠ j) (s t : ℝ) :
    listMatrix (core2Gates i j s t) =
      exp (I * ((s / 2 : ℝ) : ℂ)) • embedGate2 n i j (core2 s t) hij := by
  simp only [core2Gates, core2GatesA, listMatrix_cons, listMatrix_nil, Matrix.one_mul,
    gateEmbedding, dite_eq_right hij, embedGate1_eq_embedGate2_left hij,
    embedGate1_eq_embedGate2_right hij, embedGate2_mul]
  rw [← embedGate2_smul]
  congr 1
  have hm : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ rzGate t) *
      (Programs.Qubit.hadamard ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      (rzGate s ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      (Programs.Qubit.hadamard ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        (Programs.Qubit.hadamard * rzGate s * Programs.Qubit.hadamard) ⊗ₖ rzGate t := by
    simp only [kronecker_mul_kronecker, Matrix.one_mul, Matrix.mul_one]
  have ha : Programs.Qubit.cnot * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ rzGate t) *
      (Programs.Qubit.hadamard ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      (rzGate s ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      (Programs.Qubit.hadamard ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Programs.Qubit.cnot =
        Programs.Qubit.cnot * (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ rzGate t) *
          (Programs.Qubit.hadamard ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (rzGate s ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (Programs.Qubit.hadamard ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) *
          Programs.Qubit.cnot := by
    simp only [Matrix.mul_assoc]
  rw [ha, hm, hadamard_rz_hadamard, smul_kronecker_left, Matrix.mul_smul, Matrix.smul_mul,
    core2]

theorem listMatrix_cnot {i j : Fin n} (hij : i ≠ j) :
    listMatrix [Gate.CNOT i j] = embedGate2 n i j Programs.Qubit.cnot hij := by
  simp only [listMatrix_cons, listMatrix_nil, Matrix.one_mul, gateEmbedding, dite_eq_right hij]

theorem kronecker_one_mul_one_kronecker (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B) = A ⊗ₖ B := by
  rw [kronecker_mul_kronecker, Matrix.one_mul, Matrix.mul_one]

/-- The template `kak0 θ` as gates on qubits `i` (high) and `j` (low), over an angle carrier
`α` with the rotation `rz` and the angle `nhp` for `−π/2`. -/
@[simp] def kak0GatesA {α : Type*} (rz : Fin n → α → Gate n) (nhp : α) (i j : Fin n)
    (θ : Fin 6 → α) : List (Gate n) :=
  zyzGatesA rz nhp j (θ 3) (θ 4) (θ 5) ++ zyzGatesA rz nhp i (θ 0) (θ 1) (θ 2)

/-- The template `kak0 θ` as gates on qubits `i` (high) and `j` (low). -/
def kak0Gates (i j : Fin n) (θ : Fin 6 → ℝ) : List (Gate n) :=
  kak0GatesA Gate.Rz (-(Real.pi / 2)) i j θ

/-- The template `kak0` with the exact angles `θ` carried by `Gate.RzQ`. -/
def kak0GatesQ (i j : Fin n) (θ : Fin 6 → PiLin) : List (Gate n) :=
  kak0GatesA Gate.RzQ (PiLin.ofPi (-(1 / 2))) i j θ

theorem listMatrix_kak0Gates {i j : Fin n} (hij : i ≠ j) (θ : Fin 6 → ℝ) :
    listMatrix (kak0Gates i j θ) =
      exp (I * (((θ 1 + θ 4) / 2 : ℝ) : ℂ)) • embedGate2 n i j (kak0 θ) hij := by
  rw [kak0Gates, kak0GatesA, ← zyzGates, ← zyzGates]
  simp only [listMatrix_append, listMatrix_zyzGates,
    embedGate1_eq_embedGate2_left hij, embedGate1_eq_embedGate2_right hij,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, embedGate2_mul, ← Complex.exp_add]
  congr 1
  · congr 1
    push_cast
    ring
  · rw [kak0, kronecker_one_mul_one_kronecker]

/-- The template `kak1 θ` as gates on qubits `i` (high, the control) and `j` (low), over an
angle carrier `α` with the rotation `rz` and the angle `nhp` for `−π/2`. -/
@[simp] def kak1GatesA {α : Type*} (rz : Fin n → α → Gate n) (nhp : α) (i j : Fin n)
    (θ : Fin 12 → α) : List (Gate n) :=
  zyzGatesA rz nhp j (θ 9) (θ 10) (θ 11) ++ zyzGatesA rz nhp i (θ 6) (θ 7) (θ 8) ++
    [Gate.CNOT i j] ++ zyzGatesA rz nhp j (θ 3) (θ 4) (θ 5) ++ zyzGatesA rz nhp i (θ 0) (θ 1) (θ 2)

/-- The template `kak1 θ` as gates on qubits `i` (high, the control) and `j` (low). -/
def kak1Gates (i j : Fin n) (θ : Fin 12 → ℝ) : List (Gate n) :=
  kak1GatesA Gate.Rz (-(Real.pi / 2)) i j θ

/-- The template `kak1` with the exact angles `θ` carried by `Gate.RzQ`. -/
def kak1GatesQ (i j : Fin n) (θ : Fin 12 → PiLin) : List (Gate n) :=
  kak1GatesA Gate.RzQ (PiLin.ofPi (-(1 / 2))) i j θ

theorem listMatrix_kak1Gates {i j : Fin n} (hij : i ≠ j) (θ : Fin 12 → ℝ) :
    listMatrix (kak1Gates i j θ) =
      exp (I * (((θ 1 + θ 4 + θ 7 + θ 10) / 2 : ℝ) : ℂ)) • embedGate2 n i j (kak1 θ) hij := by
  rw [kak1Gates, kak1GatesA, ← zyzGates, ← zyzGates, ← zyzGates, ← zyzGates]
  simp only [listMatrix_append, listMatrix_zyzGates, listMatrix_cnot hij,
    embedGate1_eq_embedGate2_left hij, embedGate1_eq_embedGate2_right hij,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, embedGate2_mul, ← Complex.exp_add]
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    rw [kak1, ← kronecker_one_mul_one_kronecker (zyz (θ 0) (θ 1) (θ 2)) (zyz (θ 3) (θ 4) (θ 5)),
      ← kronecker_one_mul_one_kronecker (zyz (θ 6) (θ 7) (θ 8)) (zyz (θ 9) (θ 10) (θ 11))]
    simp only [Matrix.mul_assoc]

/-- The template `kak2 θ` as gates on qubits `i` (high, the control) and `j` (low), over an
angle carrier `α` with the rotation `rz` and the angle `nhp` for `−π/2`. -/
@[simp] def kak2GatesA {α : Type*} (rz : Fin n → α → Gate n) (nhp : α) (i j : Fin n)
    (θ : Fin 14 → α) : List (Gate n) :=
  zyzGatesA rz nhp j (θ 9) (θ 10) (θ 11) ++ zyzGatesA rz nhp i (θ 6) (θ 7) (θ 8) ++
    core2GatesA rz i j (θ 12) (θ 13) ++ zyzGatesA rz nhp j (θ 3) (θ 4) (θ 5) ++
    zyzGatesA rz nhp i (θ 0) (θ 1) (θ 2)

/-- The template `kak2 θ` as gates on qubits `i` (high, the control) and `j` (low). -/
def kak2Gates (i j : Fin n) (θ : Fin 14 → ℝ) : List (Gate n) :=
  kak2GatesA Gate.Rz (-(Real.pi / 2)) i j θ

/-- The template `kak2` with the exact angles `θ` carried by `Gate.RzQ`. -/
def kak2GatesQ (i j : Fin n) (θ : Fin 14 → PiLin) : List (Gate n) :=
  kak2GatesA Gate.RzQ (PiLin.ofPi (-(1 / 2))) i j θ

theorem listMatrix_kak2Gates {i j : Fin n} (hij : i ≠ j) (θ : Fin 14 → ℝ) :
    listMatrix (kak2Gates i j θ) =
      exp (I * (((θ 1 + θ 4 + θ 7 + θ 10 + θ 12) / 2 : ℝ) : ℂ)) •
        embedGate2 n i j (kak2 θ) hij := by
  rw [kak2Gates, kak2GatesA, ← zyzGates, ← zyzGates, ← zyzGates, ← zyzGates, ← core2Gates]
  simp only [listMatrix_append, listMatrix_zyzGates, listMatrix_core2Gates hij,
    embedGate1_eq_embedGate2_left hij, embedGate1_eq_embedGate2_right hij,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, embedGate2_mul, ← Complex.exp_add]
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    rw [kak2, ← kronecker_one_mul_one_kronecker (zyz (θ 0) (θ 1) (θ 2)) (zyz (θ 3) (θ 4) (θ 5)),
      ← kronecker_one_mul_one_kronecker (zyz (θ 6) (θ 7) (θ 8)) (zyz (θ 9) (θ 10) (θ 11))]
    simp only [Matrix.mul_assoc]

/-- A gate list whose matrix is `c` times the embedding of a phase multiple of `U` realises `U`
up to a global phase. -/
theorem exists_phase_of_listMatrix {i j : Fin n} (hij : i ≠ j) {l : List (Gate n)}
    {U K : Matrix (Fin 4) (Fin 4) ℂ} {a ψ : ℝ}
    (hl : listMatrix l = exp (I * (a : ℂ)) • embedGate2 n i j K hij)
    (hU : U = exp (ψ * I) • K) :
    listMatrix l = exp (((a - ψ : ℝ) : ℂ) * I) • embedGate2 n i j U hij := by
  rw [hl, hU, embedGate2_smul, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Class `0` in circuit form.** On qubits `i ≠ j`, a unitary of class `0` is, up to a global
phase, the matrix of the CNOT-free gate list `kak0Gates i j θ`. -/
theorem kak0_exists_listMatrix {i j : Fin n} (hij : i ≠ j) {U : Matrix (Fin 4) (Fin 4) ℂ}
    (h : InClass 0 U) :
    ∃ (φ : ℝ) (θ : Fin 6 → ℝ),
      listMatrix (kak0Gates i j θ) = exp (φ * I) • embedGate2 n i j U hij := by
  obtain ⟨ψ, θ, hθ⟩ := kak0_exists h
  exact ⟨_, θ, exists_phase_of_listMatrix hij (listMatrix_kak0Gates hij θ) hθ⟩

/-- **Class `1` in circuit form.** On qubits `i ≠ j`, a unitary of class `1` is, up to a global
phase, the matrix of the one-CNOT gate list `kak1Gates i j θ`. -/
theorem kak1_exists_listMatrix {i j : Fin n} (hij : i ≠ j) {U : Matrix (Fin 4) (Fin 4) ℂ}
    (h : InClass 1 U) :
    ∃ (φ : ℝ) (θ : Fin 12 → ℝ),
      listMatrix (kak1Gates i j θ) = exp (φ * I) • embedGate2 n i j U hij := by
  obtain ⟨ψ, θ, hθ⟩ := kak1_exists h
  exact ⟨_, θ, exists_phase_of_listMatrix hij (listMatrix_kak1Gates hij θ) hθ⟩

/-- **Class `2` in circuit form.** On qubits `i ≠ j`, a unitary of class `2` is, up to a global
phase, the matrix of the two-CNOT gate list `kak2Gates i j θ`. -/
theorem kak2_exists_listMatrix {i j : Fin n} (hij : i ≠ j) {U : Matrix (Fin 4) (Fin 4) ℂ}
    (h : InClass 2 U) :
    ∃ (φ : ℝ) (θ : Fin 14 → ℝ),
      listMatrix (kak2Gates i j θ) = exp (φ * I) • embedGate2 n i j U hij := by
  obtain ⟨ψ, θ, hθ⟩ := kak2_exists h
  exact ⟨_, θ, exists_phase_of_listMatrix hij (listMatrix_kak2Gates hij θ) hθ⟩

/-! ### Exact angles read as real angles -/

section Naturality

variable {α β : Type*} {rz : Fin n → α → Gate n} {rz' : Fin n → β → Gate n} {t : α → β}

/-- Naturality of `core2GatesA` along `rzQToRz`. -/
theorem map_rzQToRz_core2GatesA (hrz : ∀ q a, rzQToRz (rz q a) = rz' q (t a))
    (i j : Fin n) (s u : α) :
    (core2GatesA rz i j s u).map rzQToRz = core2GatesA rz' i j (t s) (t u) := by
  simp only [core2GatesA, List.map_cons, List.map_nil, hrz]
  rfl

/-- Naturality of `kak0GatesA` along `rzQToRz`. -/
theorem map_rzQToRz_kak0GatesA (hrz : ∀ q a, rzQToRz (rz q a) = rz' q (t a)) (nhp : α)
    (i j : Fin n) (θ : Fin 6 → α) :
    (kak0GatesA rz nhp i j θ).map rzQToRz = kak0GatesA rz' (t nhp) i j (t ∘ θ) := by
  simp only [kak0GatesA, List.map_append, map_rzQToRz_zyzGatesA hrz, Function.comp_apply]

/-- Naturality of `kak1GatesA` along `rzQToRz`. -/
theorem map_rzQToRz_kak1GatesA (hrz : ∀ q a, rzQToRz (rz q a) = rz' q (t a)) (nhp : α)
    (i j : Fin n) (θ : Fin 12 → α) :
    (kak1GatesA rz nhp i j θ).map rzQToRz = kak1GatesA rz' (t nhp) i j (t ∘ θ) := by
  simp only [kak1GatesA, List.map_append, map_rzQToRz_zyzGatesA hrz, Function.comp_apply,
    List.map_cons, List.map_nil]
  rfl

/-- Naturality of `kak2GatesA` along `rzQToRz`. -/
theorem map_rzQToRz_kak2GatesA (hrz : ∀ q a, rzQToRz (rz q a) = rz' q (t a)) (nhp : α)
    (i j : Fin n) (θ : Fin 14 → α) :
    (kak2GatesA rz nhp i j θ).map rzQToRz = kak2GatesA rz' (t nhp) i j (t ∘ θ) := by
  simp only [kak2GatesA, List.map_append, map_rzQToRz_zyzGatesA hrz,
    map_rzQToRz_core2GatesA hrz, Function.comp_apply]

end Naturality

/-- The exact template `kak0GatesQ`, read through `rzQToRz`, is `kak0Gates` at the real
angles. -/
theorem map_rzQToRz_kak0GatesQ (i j : Fin n) (θ : Fin 6 → PiLin) :
    (kak0GatesQ i j θ).map rzQToRz = kak0Gates i j (PiLin.toReal ∘ θ) := by
  rw [kak0GatesQ, map_rzQToRz_kak0GatesA (rz' := Gate.Rz) (fun _ _ => rfl),
    toReal_ofPi_neg_half, kak0Gates]

/-- The exact template `kak1GatesQ`, read through `rzQToRz`, is `kak1Gates` at the real
angles. -/
theorem map_rzQToRz_kak1GatesQ (i j : Fin n) (θ : Fin 12 → PiLin) :
    (kak1GatesQ i j θ).map rzQToRz = kak1Gates i j (PiLin.toReal ∘ θ) := by
  rw [kak1GatesQ, map_rzQToRz_kak1GatesA (rz' := Gate.Rz) (fun _ _ => rfl),
    toReal_ofPi_neg_half, kak1Gates]

/-- The exact template `kak2GatesQ`, read through `rzQToRz`, is `kak2Gates` at the real
angles. -/
theorem map_rzQToRz_kak2GatesQ (i j : Fin n) (θ : Fin 14 → PiLin) :
    (kak2GatesQ i j θ).map rzQToRz = kak2Gates i j (PiLin.toReal ∘ θ) := by
  rw [kak2GatesQ, map_rzQToRz_kak2GatesA (rz' := Gate.Rz) (fun _ _ => rfl),
    toReal_ofPi_neg_half, kak2Gates]

end Circuit

end CatCrypt.Quantum.Synthesis.KAKSmall
