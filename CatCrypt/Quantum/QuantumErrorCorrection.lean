/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Instrument
public import CatCryptCore.Quantum.CPMap
public import CatCryptCore.Quantum.ChoiKraus
public import Mathlib.LinearAlgebra.Center
public import CatCrypt.Quantum.TensorProduct
public import CatCrypt.Quantum.Measurement

@[expose] public section

set_option autoImplicit false

/-!
# Quantum Error Correction

Defines quantum error-correcting codes, the Knill-Laflamme conditions,
and recovery channels. A [[n,k,d]] quantum code encodes k logical qubits
into n physical qubits, correcting up to floor((d-1)/2) errors.

## Main definitions

* `QuantumCode` -- a quantum error-correcting code (projector onto code subspace)
* `ErrorSet` -- a set of correctable errors (Kraus operators)
* `KnillLaflamme` -- the Knill-Laflamme correctability conditions
* `IsCorrectableBy` -- correctability by a completely positive trace-preserving recovery
* `OrthonormalKets` -- orthonormal system infrastructure for constructing codes
* `QuantumCode.ofOrthonormalKets` -- build a code from orthonormal codewords

## Main results

* `knill_laflamme_iff_correctable` -- KL conditions characterize correctability
  (Nielsen-Chuang, Theorem 10.1)
* `exists_recovery_of_orthogonal` -- the recovery channel built from an error family
  with orthogonal ranges on the code
* `basisPairCode` -- the code spanned by `|0…0⟩` and `|1…1⟩` on `n` qubits, with the
  instances `basisPairCode9`, `basisPairCode7`, `basisPairCode5`

## References

* Knill, E. & Laflamme, R. -- *Theory of Quantum Error-Correcting Codes*,
  PRA 55(2), 1997
* Nielsen & Chuang -- Chapter 10
* Gottesman, D. -- *Stabilizer Codes and Quantum Error Correction*, PhD thesis, 1997
-/

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical

noncomputable section

namespace CatCrypt.Quantum.QuantumErrorCorrection

open CatCrypt.Quantum

/-! ## Ket Infrastructure (self-contained for QEC) -/

/-- A ket vector in d-dimensional Hilbert space. -/
abbrev Ket' (d : ℕ) := Fin d → ℂ

/-- Outer product |psi><phi| as a d x d matrix. -/
def ketbra' {d : ℕ} (ψ φ : Ket' d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => ψ i * starRingEnd ℂ (φ j)

/-- Density matrix |psi><psi| from a pure state. -/
def densityOf' {d : ℕ} (ψ : Ket' d) : Matrix (Fin d) (Fin d) ℂ :=
  ketbra' ψ ψ

/-- Inner product <phi|psi>. -/
def braket' {d : ℕ} (φ ψ : Ket' d) : ℂ :=
  ∑ i : Fin d, starRingEnd ℂ (φ i) * ψ i

/-- A ket is normalized if <psi|psi> = 1. -/
def IsNormalized' {d : ℕ} (ψ : Ket' d) : Prop := braket' ψ ψ = 1

/-- Two kets are orthogonal if <phi|psi> = 0. -/
def AreOrthogonal' {d : ℕ} (φ ψ : Ket' d) : Prop := braket' φ ψ = 0

theorem ketbra'_conjTranspose {d : ℕ} (ψ φ : Ket' d) :
    (ketbra' ψ φ)ᴴ = ketbra' φ ψ := by
  ext i j; simp [ketbra', conjTranspose_apply, of_apply, mul_comm]

theorem densityOf'_hermitian {d : ℕ} (ψ : Ket' d) :
    (densityOf' ψ)ᴴ = densityOf' ψ :=
  ketbra'_conjTranspose ψ ψ

theorem densityOf'_trace {d : ℕ} (ψ : Ket' d) :
    (densityOf' ψ).trace = braket' ψ ψ := by
  simp [densityOf', ketbra', Matrix.trace, Matrix.diag, braket', of_apply, mul_comm]

theorem densityOf'_trace_one {d : ℕ} (ψ : Ket' d) (hψ : IsNormalized' ψ) :
    (densityOf' ψ).trace = 1 := by
  rw [densityOf'_trace, hψ]

/-- General ketbra multiplication: |psi1><psi2| * |psi3><psi4| = <psi2|psi3> . |psi1><psi4|. -/
theorem ketbra'_mul_ketbra' {d : ℕ} (ψ₁ ψ₂ ψ₃ ψ₄ : Ket' d) :
    ketbra' ψ₁ ψ₂ * ketbra' ψ₃ ψ₄ = braket' ψ₂ ψ₃ • ketbra' ψ₁ ψ₄ := by
  ext i j
  simp only [ketbra', braket', of_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    starRingEnd_apply]
  rw [Finset.sum_mul]
  congr 1; ext k; ring

/-- densityOf' psi1 * densityOf' psi2 = <psi1|psi2> . ketbra' psi1 psi2. -/
theorem densityOf'_mul_densityOf' {d : ℕ} (ψ₁ ψ₂ : Ket' d) :
    densityOf' ψ₁ * densityOf' ψ₂ = braket' ψ₁ ψ₂ • ketbra' ψ₁ ψ₂ :=
  ketbra'_mul_ketbra' ψ₁ ψ₁ ψ₂ ψ₂

/-! ## Orthonormal Projector Construction -/

/-- An **orthonormal system** of kets: pairwise orthogonal and each normalized. -/
structure OrthonormalKets (d m : ℕ) where
  /-- The ket vectors. -/
  kets : Fin m → Ket' d
  /-- Each ket is normalized. -/
  normalized : ∀ i, IsNormalized' (kets i)
  /-- Distinct kets are orthogonal. -/
  orthogonal : ∀ i j, i ≠ j → AreOrthogonal' (kets i) (kets j)

/-- Inner product of an orthonormal system satisfies <psi_i|psi_j> = delta_{ij}. -/
theorem OrthonormalKets.braket_eq {d m : ℕ} (sys : OrthonormalKets d m)
    (i j : Fin m) :
    braket' (sys.kets i) (sys.kets j) = if i = j then 1 else 0 := by
  split
  · case isTrue h => rw [h]; exact sys.normalized j
  · case isFalse h => exact sys.orthogonal i j h

/-- The projector onto the span of an orthonormal system:
    P = sum_i |psi_i><psi_i|. -/
def orthonormalProjector {d m : ℕ} (sys : OrthonormalKets d m) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ i : Fin m, densityOf' (sys.kets i)

/-- The orthonormal projector is self-adjoint. -/
theorem orthonormalProjector_self_adj {d m : ℕ} (sys : OrthonormalKets d m) :
    (orthonormalProjector sys)ᴴ = orthonormalProjector sys := by
  unfold orthonormalProjector
  simp only [conjTranspose_sum, densityOf'_hermitian]

/-- Helper: the sum over j of the product densityOf' (kets i) * densityOf' (kets j)
    telescopes to densityOf' (kets i). -/
private theorem orthonormal_sum_row {d m : ℕ} (sys : OrthonormalKets d m) (i : Fin m) :
    ∑ j : Fin m, densityOf' (sys.kets i) * densityOf' (sys.kets j) =
      densityOf' (sys.kets i) := by
  simp only [densityOf'_mul_densityOf', sys.braket_eq]
  -- Goal: sum j, (if i = j then 1 else 0) . ketbra' (kets i) (kets j) = densityOf' (kets i)
  have : ∀ j ∈ Finset.univ, (if i = j then (1 : ℂ) else 0) • ketbra' (sys.kets i) (sys.kets j) =
      if j = i then densityOf' (sys.kets i) else 0 := by
    intro j _
    by_cases h : i = j
    · subst h; simp [densityOf']
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  simp [Finset.mem_univ]

/-- The orthonormal projector is idempotent. -/
theorem orthonormalProjector_idempotent {d m : ℕ} (sys : OrthonormalKets d m) :
    orthonormalProjector sys * orthonormalProjector sys = orthonormalProjector sys := by
  unfold orthonormalProjector
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [orthonormal_sum_row sys]

/-- The orthonormal projector has trace equal to the number of kets. -/
theorem orthonormalProjector_trace {d m : ℕ} (sys : OrthonormalKets d m) :
    (orthonormalProjector sys).trace = (m : ℂ) := by
  unfold orthonormalProjector
  rw [trace_sum]
  have : ∀ i ∈ Finset.univ, (densityOf' (sys.kets i)).trace = (1 : ℂ) :=
    fun i _ => densityOf'_trace_one _ (sys.normalized i)
  rw [Finset.sum_congr rfl this]
  simp

/-! ## Quantum Code -/

/-- A **quantum error-correcting code** on n qubits encoding k logical qubits.

    The code is specified by a projector P onto the 2^k-dimensional code subspace
    of the 2^n-dimensional physical Hilbert space.

    The parameters [[n, k, d]] indicate:
    - n = number of physical qubits
    - k = number of logical qubits
    - d = code distance (corrects up to floor((d-1)/2) errors) -/
structure QuantumCode where
  /-- Number of physical qubits. -/
  n : ℕ
  /-- Number of logical qubits. -/
  k : ℕ
  /-- Code distance. -/
  distance : ℕ
  /-- Physical Hilbert space dimension. -/
  dim : ℕ := 2 ^ n
  /-- Code subspace dimension. -/
  codeDim : ℕ := 2 ^ k
  /-- Projector onto the code subspace. -/
  codeProj : Matrix (Fin dim) (Fin dim) ℂ
  /-- codeProj is a projector. -/
  proj_self_adj : codeProjᴴ = codeProj
  proj_idempotent : codeProj * codeProj = codeProj
  /-- The projector has rank 2^k (code subspace dimension). -/
  proj_rank : codeProj.trace = (codeDim : ℂ)

/-- Build a `QuantumCode` from an orthonormal system of 2^k codewords
    in 2^n-dimensional space. All three projector properties
    (self-adjointness, idempotence, trace) are proved generically. -/
def QuantumCode.ofOrthonormalKets (n k distance : ℕ)
    (sys : OrthonormalKets (2 ^ n) (2 ^ k)) : QuantumCode where
  n := n
  k := k
  distance := distance
  codeProj := orthonormalProjector sys
  proj_self_adj := orthonormalProjector_self_adj sys
  proj_idempotent := orthonormalProjector_idempotent sys
  proj_rank := orthonormalProjector_trace sys

/-! ## Error Model -/

/-- A set of **error operators** (Kraus operators) representing possible errors.
    The error channel is E(rho) = sum_i E_i rho E_i dagger. -/
structure ErrorSet (dim : ℕ) (numErrors : ℕ) where
  /-- The error operators. -/
  errors : Fin numErrors → Matrix (Fin dim) (Fin dim) ℂ
  /-- Trace-preserving: sum_i E_i dagger E_i = I (for the full error model). -/
  tp : ∑ i, (errors i)ᴴ * errors i = 1

/-- The error channel: E(rho) = sum_i E_i rho E_i dagger. -/
def errorChannel {dim numErrors : ℕ} (E : ErrorSet dim numErrors) :
    Matrix (Fin dim) (Fin dim) ℂ →ₗ[ℂ] Matrix (Fin dim) (Fin dim) ℂ where
  toFun ρ := ∑ i : Fin numErrors, E.errors i * ρ * (E.errors i)ᴴ
  map_add' ρ₁ ρ₂ := by simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c ρ := by
    simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Finset.smul_sum]

/-! ## Knill-Laflamme Conditions -/

/-- **Knill-Laflamme conditions** for error correction.

    A code with projector P corrects error set {E_i} iff:
    P E_i dagger E_j P = alpha_{ij} P for some Hermitian matrix alpha_{ij}.

    The matrix alpha captures the error syndromes. -/
def KnillLaflamme (code : QuantumCode) {numErrors : ℕ} (E : ErrorSet code.dim numErrors)
    (α : Matrix (Fin numErrors) (Fin numErrors) ℂ) : Prop :=
  ∀ i j : Fin numErrors,
    code.codeProj * (E.errors i)ᴴ * E.errors j * code.codeProj =
      α i j • code.codeProj

/-- Scalar cancellation for matrix smul: `a * P = b * P` and `P != 0` implies `a = b`. -/
private lemma smul_matrix_cancel {dim : ℕ} {a b : ℂ} {P : Matrix (Fin dim) (Fin dim) ℂ}
    (hP : P ≠ 0) (h : a • P = b • P) : a = b := by
  have ⟨i, j, hij⟩ : ∃ i j, P i j ≠ 0 := by
    by_contra h_all; push Not at h_all
    exact hP (Matrix.ext fun i j => by simpa using h_all i j)
  have : a * P i j = b * P i j := by
    have := congr_fun (congr_fun h i) j; simpa [Matrix.smul_apply] using this
  exact mul_right_cancel₀ hij this

/-- Conjugate transpose reverses the Knill-Laflamme product. -/
private lemma kl_conj_transpose {dim : ℕ}
    (P : Matrix (Fin dim) (Fin dim) ℂ) (hP_sa : Pᴴ = P)
    (Ei Ej : Matrix (Fin dim) (Fin dim) ℂ) :
    (P * Eiᴴ * Ej * P)ᴴ = P * Ejᴴ * Ei * P := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP_sa, mul_assoc]

/-- The Knill-Laflamme matrix alpha must be Hermitian.

    Requires the code projector to be nonzero (equivalently, codeDim > 0,
    which holds for all concrete codes since codeDim = 2^k >= 1).

    Proof: Taking the conjugate transpose of the KL equation at (i,j) gives
    `P E_j^H E_i P = star(alpha_{ij}) P`, which by KL at (j,i) equals
    `alpha_{ji} P`. Since P is nonzero, `star(alpha_{ij}) = alpha_{ji}`. -/
theorem knill_laflamme_hermitian {code : QuantumCode} {numErrors : ℕ}
    {E : ErrorSet code.dim numErrors}
    {α : Matrix (Fin numErrors) (Fin numErrors) ℂ}
    (hKL : KnillLaflamme code E α)
    (hP_ne : code.codeProj ≠ 0 := by
      intro h; simp [h, Matrix.trace_zero] at code.proj_rank) :
    α.IsHermitian := by
  show αᴴ = α; ext i j; simp only [conjTranspose_apply]; symm
  apply smul_matrix_cancel hP_ne
  calc α i j • code.codeProj
      = code.codeProj * (E.errors i)ᴴ * E.errors j * code.codeProj :=
        (hKL i j).symm
    _ = (code.codeProj * (E.errors j)ᴴ * E.errors i * code.codeProj)ᴴ :=
        (kl_conj_transpose _ code.proj_self_adj _ _).symm
    _ = (α j i • code.codeProj)ᴴ := by rw [hKL j i]
    _ = starRingEnd ℂ (α j i) • code.codeProjᴴ := conjTranspose_smul _ _
    _ = starRingEnd ℂ (α j i) • code.codeProj := by rw [code.proj_self_adj]

/-! ## Correctability -/

/-- A code **corrects** an error set if there exists a recovery channel `R`,
    completely positive and trace preserving, such that `R(E(ρ)) = ρ` for all
    positive semidefinite code states `ρ` (`P ρ P = ρ`). -/
def IsCorrectableBy (code : QuantumCode) {numErrors : ℕ} (E : ErrorSet code.dim numErrors) : Prop :=
  ∃ (R : Matrix (Fin code.dim) (Fin code.dim) ℂ →ₗ[ℂ]
         Matrix (Fin code.dim) (Fin code.dim) ℂ),
    IsCPMap R ∧ IsTP R ∧
    ∀ (ρ : Matrix (Fin code.dim) (Fin code.dim) ℂ),
      ρ.PosSemidef →
      code.codeProj * ρ * code.codeProj = ρ →
      R (errorChannel E ρ) = ρ

/-- The error channel as its Kraus sum. -/
theorem errorChannel_apply {dim numErrors : ℕ} (E : ErrorSet dim numErrors)
    (ρ : Matrix (Fin dim) (Fin dim) ℂ) :
    errorChannel E ρ = ∑ i, E.errors i * ρ * (E.errors i)ᴴ := rfl

/-! ### Vector lemmas -/

/-- If `∑ⱼ wⱼ wⱼ† = v v†`, then every vector orthogonal to `v` is orthogonal to
    each `wⱼ`. -/
theorem dotProduct_eq_zero_of_sum_vecMulVec_eq {ι : Type*} [Fintype ι] {d : ℕ}
    (w : ι → Fin d → ℂ) (v : Fin d → ℂ)
    (h : ∑ j, vecMulVec (w j) (star (w j)) = vecMulVec v (star v))
    (φ : Fin d → ℂ) (hφ : star φ ⬝ᵥ v = 0) (j : ι) : star φ ⬝ᵥ w j = 0 := by
  have key : ∀ x : Fin d → ℂ, star φ ⬝ᵥ (vecMulVec x (star x) *ᵥ φ) =
      (star φ ⬝ᵥ x) * star (star φ ⬝ᵥ x) := by
    intro x
    simp only [dotProduct, mulVec, vecMulVec_apply, Pi.star_apply, star_sum, star_mul',
      star_star, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have h2 := congrArg (fun M => star φ ⬝ᵥ (M *ᵥ φ)) h
  simp only [Matrix.sum_mulVec, dotProduct_sum, key, hφ, zero_mul] at h2
  have hnn : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ (star φ ⬝ᵥ w j) * star (star φ ⬝ᵥ w j) := fun j _ => mul_star_self_nonneg _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h2 j (Finset.mem_univ _)
  exact (mul_eq_zero.1 hz).elim id star_eq_zero.1

/-- A vector `w` orthogonal to every vector orthogonal to `v` is a multiple of `v`. -/
theorem exists_smul_of_forall_dotProduct {d : ℕ} (v w : Fin d → ℂ)
    (h : ∀ φ : Fin d → ℂ, star φ ⬝ᵥ v = 0 → star φ ⬝ᵥ w = 0) : ∃ c : ℂ, w = c • v := by
  by_cases hv : v = 0
  · refine ⟨0, ?_⟩
    have hw := h w (by simp [hv])
    rw [dotProduct_star_self_eq_zero] at hw
    simp [hw]
  · have ha : star v ⬝ᵥ v ≠ 0 := fun h0 => hv (dotProduct_star_self_eq_zero.1 h0)
    obtain ⟨φ, hφ⟩ : ∃ φ : Fin d → ℂ, φ = (star v ⬝ᵥ v) • w - (star v ⬝ᵥ w) • v := ⟨_, rfl⟩
    have hsa : star (star v ⬝ᵥ v) = star v ⬝ᵥ v := by
      rw [← star_dotProduct]
    have hsb : star (star v ⬝ᵥ w) = star w ⬝ᵥ v := by
      rw [← star_dotProduct]
    have hφv : star φ ⬝ᵥ v = 0 := by
      rw [hφ, star_sub, star_smul, star_smul, sub_dotProduct, smul_dotProduct, smul_dotProduct,
        hsa, hsb, smul_eq_mul, smul_eq_mul, mul_comm, sub_self]
    have hφw := h φ hφv
    have hφφ : star φ ⬝ᵥ φ = 0 := by
      have h1 : star φ ⬝ᵥ ((star v ⬝ᵥ v) • w - (star v ⬝ᵥ w) • v) = 0 := by
        rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, hφw, hφv]
        simp
      rwa [← hφ] at h1
    have h0 : (star v ⬝ᵥ v) • w = (star v ⬝ᵥ w) • v :=
      sub_eq_zero.1 (hφ ▸ dotProduct_star_self_eq_zero.1 hφφ)
    refine ⟨(star v ⬝ᵥ w) / (star v ⬝ᵥ v), ?_⟩
    calc w = (star v ⬝ᵥ v)⁻¹ • ((star v ⬝ᵥ v) • w) := by
          rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = _ := by rw [h0, smul_smul, div_eq_inv_mul]

/-- A matrix `M = M P` that maps every vector of the range of the projector `P`
    to a multiple of itself is a scalar multiple of `P`. -/
theorem exists_eq_smul_of_forall_mulVec {d : ℕ} {P M : Matrix (Fin d) (Fin d) ℂ}
    (hP : P * P = P) (hM : M * P = M)
    (h : ∀ v, P *ᵥ v = v → ∃ c : ℂ, M *ᵥ v = c • v) : ∃ c : ℂ, M = c • P := by
  let W := LinearMap.range (Matrix.toLin' P)
  have memW : ∀ x, x ∈ W ↔ P *ᵥ x = x := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      simp [Matrix.toLin'_apply, mulVec_mulVec, hP]
    · intro hx
      exact ⟨x, by simpa [Matrix.toLin'_apply] using hx⟩
  have hMW : ∀ x ∈ W, Matrix.toLin' M x ∈ W := by
    intro x hx
    obtain ⟨c, hc⟩ := h x ((memW x).1 hx)
    rw [Matrix.toLin'_apply, hc]
    exact W.smul_mem c hx
  let f : W →ₗ[ℂ] W := (Matrix.toLin' M).restrict hMW
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (f := f) (by
    intro x hx
    obtain ⟨c, hc⟩ := h x ((memW x).1 x.2)
    have hfx : f x = c • x := Subtype.ext (by
      simp [f, LinearMap.restrict_apply, Matrix.toLin'_apply, hc])
    rw [LinearIndependent.pair_iff] at hx
    have := hx c (-1) (by rw [hfx]; simp)
    exact absurd this.2 (by norm_num))
  refine ⟨a, ?_⟩
  have hv : ∀ y, M *ᵥ y = (a • P) *ᵥ y := by
    intro y
    have hy := congrArg Subtype.val
      (LinearMap.congr_fun ha ⟨P *ᵥ y, (memW _).2 (by rw [mulVec_mulVec, hP])⟩)
    simp [f, LinearMap.restrict_apply, Matrix.toLin'_apply] at hy
    rw [hM] at hy
    rw [hy, Matrix.smul_mulVec]
  exact Matrix.toLin'.injective (LinearMap.ext hv)

/-! ### Unitary mixing of operator families -/

/-- Mixing a family by the columns of a matrix `u` with `u uᴴ = 1` leaves the
    diagonal sum unchanged: `∑ₖ ∑ₐ ∑_b conj(u a k) u b k • B a b = ∑ₐ B a a`. -/
theorem sum_star_mul_smul_of_mul_conjTranspose_eq_one {M : Type*} [AddCommMonoid M]
    [Module ℂ M] {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u * uᴴ = 1)
    (B : Fin n → Fin n → M) :
    ∑ k, ∑ a, ∑ b, (star (u a k) * u b k) • B a b = ∑ a, B a a := by
  have hk : ∀ a b, ∑ k, star (u a k) * u b k = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hu b) a
    simp only [mul_apply, conjTranspose_apply, one_apply] at this
    rw [show (if a = b then (1 : ℂ) else 0) = if b = a then 1 else 0 from by
      by_cases hab : a = b
      · subst hab; rfl
      · rw [ite_eq_right hab, ite_eq_right (Ne.symm hab)]]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hk]
  simp

/-! ### The recovery channel -/

/-- Recovery from an orthogonal family: if `G k = G k P` and
    `(G k)ᴴ G l = δ_kl c_k P` with real `c_k` and `∑ₖ (G k)ᴴ G k = P`, then a
    completely positive trace-preserving map inverts `ρ ↦ ∑ₖ G k ρ (G k)ᴴ` on
    code states. Its Kraus operators are the normalised adjoints `(G k)ᴴ / √c_k`
    together with the projector onto the complement of their joint range. -/
theorem exists_recovery_of_orthogonal {d n : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    (hPsa : Pᴴ = P) (hP : P * P = P) (G : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (c : Fin n → ℝ) (hGP : ∀ k, G k * P = G k)
    (hGG : ∀ k l, (G k)ᴴ * G l = (if k = l then (c k : ℂ) else 0) • P)
    (hsum : ∑ k, (G k)ᴴ * G k = P) :
    ∃ R : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ, IsCPMap R ∧ IsTP R ∧
      ∀ ρ, P * ρ * P = ρ → R (∑ k, G k * ρ * (G k)ᴴ) = ρ := by
  have htrP : 0 ≤ P.trace := by
    have := (posSemidef_conjTranspose_mul_self P).trace_nonneg
    rwa [hPsa, hP] at this
  have hG0 : ∀ k, ¬ 0 < c k → G k = 0 := by
    intro k hk
    have h1 := congrArg Matrix.trace (hGG k k)
    rw [ite_eq_left rfl, trace_smul, smul_eq_mul] at h1
    have h2 := (posSemidef_conjTranspose_mul_self (G k)).trace_nonneg
    have h3 : (c k : ℂ) * P.trace ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast not_lt.1 hk) htrP
    exact trace_conjTranspose_mul_self_eq_zero_iff.1 (le_antisymm (h1 ▸ h3) h2)
  let s : Fin n → ℂ := fun k => if 0 < c k then (((Real.sqrt (c k))⁻¹ : ℝ) : ℂ) else 0
  let V : Fin n → Matrix (Fin d) (Fin d) ℂ := fun k => s k • G k
  have hV0 : ∀ k, ¬ 0 < c k → V k = 0 := fun k hk => by simp [V, s, hk]
  have hVP : ∀ k, V k * P = V k := fun k => by simp [V, hGP]
  have hVV : ∀ l k, (V l)ᴴ * V k = (if l = k ∧ 0 < c k then (1 : ℂ) else 0) • P := by
    intro l k
    simp only [V, conjTranspose_smul, smul_mul_smul_comm, hGG, smul_smul]
    congr 1
    by_cases hlk : l = k
    · subst hlk
      by_cases hc : 0 < c l
      · have hr : (Real.sqrt (c l))⁻¹ * (Real.sqrt (c l))⁻¹ * c l = 1 := by
          rw [← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']
        simp only [s, ite_eq_left hc, ↓reduceIte, true_and, Complex.star_def, Complex.conj_ofReal]
        exact_mod_cast hr
      · simp [s, hc]
    · simp [hlk]
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin d) (Fin d) ℂ, Q = ∑ k, V k * (V k)ᴴ := ⟨_, rfl⟩
  have hQV : ∀ l, Q * V l = V l := by
    intro l
    rw [hQ, Finset.sum_mul]
    simp only [Matrix.mul_assoc, hVV, Matrix.mul_smul, hVP]
    by_cases hc : 0 < c l
    · simp [hc]
    · simp [hc, hV0 l hc]
  have hQsa : Qᴴ = Q := by
    rw [hQ]; simp [conjTranspose_sum, conjTranspose_mul]
  have hQQ : Q * Q = Q := by
    calc Q * Q = Q * ∑ k, V k * (V k)ᴴ := by rw [← hQ]
      _ = ∑ k, (Q * V k) * (V k)ᴴ := by rw [Finset.mul_sum]; simp [Matrix.mul_assoc]
      _ = Q := by simp_rw [hQV]; exact hQ.symm
  let K : Option (Fin n) → Matrix (Fin d) (Fin d) ℂ := fun o => o.elim (1 - Q) (fun k => (V k)ᴴ)
  let R : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    ∑ o, UnitaryChannel.conjugate (K o)
  have hRK : ∀ ρ, R ρ = ∑ o, K o * ρ * (K o)ᴴ := fun ρ => by
    simp [R, LinearMap.sum_apply, UnitaryChannel.conjugate_apply]
  have hRapp : ∀ ρ, R ρ = (1 - Q) * ρ * (1 - Q)ᴴ + ∑ k, (V k)ᴴ * ρ * V k := fun ρ => by
    rw [hRK, Fintype.sum_option]
    simp [K]
  have hKK : (1 - Q)ᴴ * (1 - Q) + ∑ k, V k * (V k)ᴴ = 1 := by
    rw [conjTranspose_sub, conjTranspose_one, hQsa, ← hQ, sub_mul, mul_sub, mul_sub, one_mul,
      mul_one, one_mul, hQQ]
    abel
  refine ⟨R, isCPMap_of_kraus K hRK, fun ρ => ?_, fun ρ hρ => ?_⟩
  · rw [hRapp, trace_add, trace_sum, trace_mul_cycle]
    simp_rw [trace_mul_cycle ((V _)ᴴ)]
    rw [← trace_sum, ← trace_add, ← Finset.sum_mul, ← add_mul, hKK, Matrix.one_mul]
  · have hPρ : P * ρ = ρ := by
      calc P * ρ = P * (P * ρ * P) := by rw [hρ]
        _ = P * ρ * P := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP]
        _ = ρ := hρ
    let e : Fin n → ℂ := fun k => if 0 < c k then (c k : ℂ) else 0
    have he : ∀ k, G k * ρ * (G k)ᴴ = e k • (V k * ρ * (V k)ᴴ) := by
      intro k
      by_cases hc : 0 < c k
      · have hGV : G k = ((Real.sqrt (c k) : ℝ) : ℂ) • V k := by
          simp only [V, s, ite_eq_left hc, smul_smul]
          rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 hc).ne', Complex.ofReal_one,
            one_smul]
        rw [hGV]
        simp only [Matrix.smul_mul, Matrix.mul_smul, conjTranspose_smul, smul_smul, e, ite_eq_left hc,
          Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
          Real.mul_self_sqrt hc.le]
      · simp [hG0 k hc, e, hc]
    have hRV : ∀ k, R (V k * ρ * (V k)ᴴ) = (if 0 < c k then (1 : ℂ) else 0) • ρ := by
      intro k
      rw [hRapp]
      have h1 : (1 - Q) * (V k * ρ * (V k)ᴴ) * (1 - Q)ᴴ = 0 := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, sub_mul, Matrix.one_mul, hQV, sub_self]
        simp
      have h2 : ∀ l, (V l)ᴴ * (V k * ρ * (V k)ᴴ) * V l =
          ((V l)ᴴ * V k) * ρ * ((V l)ᴴ * V k)ᴴ := fun l => by
        simp [conjTranspose_mul, Matrix.mul_assoc]
      rw [h1, zero_add]
      simp_rw [h2, hVV]
      by_cases hc : 0 < c k
      · simp [hc, hPsa, hρ]
      · simp [hc]
    have hsumE : ∑ k, e k • P = P := by
      conv_rhs => rw [← hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hc : 0 < c k
      · rw [hGG k k, ite_eq_left rfl]; simp [e, hc]
      · simp [e, hc, hG0 k hc]
    simp_rw [he, map_sum, map_smul, hRV, smul_smul]
    calc ∑ k, (e k * if 0 < c k then (1 : ℂ) else 0) • ρ = ∑ k, e k • (P * ρ) := by
          rw [hPρ]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hc : 0 < c k <;> simp [e, hc]
      _ = ρ := by
          simp_rw [← Matrix.smul_mul]
          rw [← Finset.sum_mul, hsumE, hPρ]

/-! ### The Knill-Laflamme theorem -/

/-- Knill-Laflamme conditions can be taken with a Hermitian coefficient matrix. -/
theorem exists_knillLaflamme_hermitian {code : QuantumCode} {numErrors : ℕ}
    {E : ErrorSet code.dim numErrors} (h : ∃ α, KnillLaflamme code E α) :
    ∃ α, KnillLaflamme code E α ∧ α.IsHermitian := by
  obtain ⟨α, hα⟩ := h
  by_cases hP : code.codeProj = 0
  · exact ⟨0, fun i j => by simp [hP], isHermitian_zero⟩
  · exact ⟨α, hα, knill_laflamme_hermitian hα hP⟩

/-- Knill-Laflamme conditions imply correctability. -/
theorem isCorrectableBy_of_knillLaflamme (code : QuantumCode) {numErrors : ℕ}
    (E : ErrorSet code.dim numErrors) (h : ∃ α, KnillLaflamme code E α) :
    IsCorrectableBy code E := by
  obtain ⟨α, hKL, hα⟩ := exists_knillLaflamme_hermitian h
  have hPsa := code.proj_self_adj
  have hP := code.proj_idempotent
  obtain ⟨u, hu, hdiag⟩ : ∃ u : Matrix (Fin numErrors) (Fin numErrors) ℂ,
      u * uᴴ = 1 ∧ uᴴ * α * u = diagonal (Complex.ofReal ∘ hα.eigenvalues) := by
    refine ⟨(hα.eigenvectorUnitary : Matrix _ _ ℂ), ?_, ?_⟩
    · rw [← star_eq_conjTranspose]
      exact Unitary.mul_star_self_of_mem hα.eigenvectorUnitary.2
    · have := hα.conjStarAlgAut_star_eigenvectorUnitary
      rw [Unitary.conjStarAlgAut_star_apply] at this
      simpa [star_eq_conjTranspose] using this
  let F : Fin numErrors → Matrix (Fin code.dim) (Fin code.dim) ℂ :=
    fun k => ∑ a, u a k • E.errors a
  let G : Fin numErrors → Matrix (Fin code.dim) (Fin code.dim) ℂ :=
    fun k => F k * code.codeProj
  have hFF : ∀ k l, (F k)ᴴ * F l =
      ∑ a, ∑ b, (star (u a k) * u b l) • ((E.errors a)ᴴ * E.errors b) := by
    intro k l
    simp only [F, conjTranspose_sum, conjTranspose_smul, Finset.sum_mul, Finset.mul_sum,
      smul_mul_smul_comm]
    exact Finset.sum_comm
  have hGG' : ∀ k l, (G k)ᴴ * G l = code.codeProj * ((F k)ᴴ * F l) * code.codeProj := by
    intro k l
    simp only [G, conjTranspose_mul, hPsa, Matrix.mul_assoc]
  have hGG : ∀ k l, (G k)ᴴ * G l =
      (if k = l then (hα.eigenvalues k : ℂ) else 0) • code.codeProj := by
    intro k l
    rw [hGG', hFF]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.mul_assoc]
    have e3 : ∀ a b, (star (u a k) * u b l) •
        (code.codeProj * (E.errors a)ᴴ * E.errors b * code.codeProj) =
        (star (u a k) * u b l * α a b) • code.codeProj := fun a b => by
      rw [hKL a b, smul_smul]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e3 a b]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_smul.symm, ← Finset.sum_smul]
    congr 1
    have hkl := congrFun (congrFun hdiag k) l
    rw [diagonal_apply, mul_apply, Function.comp_apply] at hkl
    rw [← hkl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [conjTranspose_apply]
    ring
  have hsum : ∑ k, (G k)ᴴ * G k = code.codeProj := by
    simp_rw [hGG', hFF, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_star_mul_smul_of_mul_conjTranspose_eq_one u hu, E.tp, Matrix.mul_one, hP]
  obtain ⟨R, hcp, htp, hR⟩ := exists_recovery_of_orthogonal hPsa hP G hα.eigenvalues
    (fun k => by simp [G, Matrix.mul_assoc, hP]) hGG hsum
  refine ⟨R, hcp, htp, fun ρ _ hρ => ?_⟩
  have e2 : ∀ k, G k * ρ * (G k)ᴴ =
      ∑ a, ∑ b, (star (u a k) * u b k) • (E.errors b * ρ * (E.errors a)ᴴ) := by
    intro k
    calc G k * ρ * (G k)ᴴ = F k * (code.codeProj * ρ * code.codeProj) * (F k)ᴴ := by
          simp only [G, conjTranspose_mul, hPsa, Matrix.mul_assoc]
      _ = F k * ρ * (F k)ᴴ := by rw [hρ]
      _ = _ := by
          simp only [F, conjTranspose_sum, conjTranspose_smul, Finset.sum_mul, Finset.mul_sum,
            Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hE : errorChannel E ρ = ∑ k, G k * ρ * (G k)ᴴ := by
    rw [errorChannel_apply]
    simp_rw [e2]
    exact (sum_star_mul_smul_of_mul_conjTranspose_eq_one u hu
      (fun a b => E.errors b * ρ * (E.errors a)ᴴ)).symm
  rw [hE]
  exact hR ρ hρ

/-- Correctability implies the Knill-Laflamme conditions. -/
theorem knillLaflamme_of_isCorrectableBy (code : QuantumCode) {numErrors : ℕ}
    (E : ErrorSet code.dim numErrors) (h : IsCorrectableBy code E) :
    ∃ α, KnillLaflamme code E α := by
  obtain ⟨R, hcp, htp, hR⟩ := h
  obtain ⟨K, hK⟩ := exists_kraus hcp
  have hK1 := kraus_sum_conjTranspose_mul_self_eq_one hK htp
  have hPsa := code.proj_self_adj
  have hP := code.proj_idempotent
  have hcoll : ∀ x a, ∃ c : ℂ, K x * E.errors a * code.codeProj = c • code.codeProj := by
    intro x a
    refine exists_eq_smul_of_forall_mulVec hP (by rw [Matrix.mul_assoc, hP]) fun v hv => ?_
    let w : ((Fin code.dim × Fin code.dim) × Fin numErrors) → Fin code.dim → ℂ :=
      fun j => (K j.1 * E.errors j.2) *ᵥ v
    have hcode : code.codeProj * vecMulVec v (star v) * code.codeProj = vecMulVec v (star v) := by
      rw [mul_vecMulVec, hv, vecMulVec_mul]
      congr 1
      rw [← hPsa, ← star_mulVec, hv]
    have hρ := hR _ (posSemidef_vecMulVec_self_star v) hcode
    rw [hK, errorChannel_apply] at hρ
    have hsum : ∑ j, vecMulVec (w j) (star (w j)) = vecMulVec v (star v) := by
      rw [← hρ, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [w, star_mulVec, ← mul_vecMulVec, ← vecMulVec_mul, conjTranspose_mul,
        Matrix.mul_assoc]
    obtain ⟨c, hc⟩ := exists_smul_of_forall_dotProduct v (w (x, a))
      (fun φ hφ => dotProduct_eq_zero_of_sum_vecMulVec_eq w v hsum φ hφ (x, a))
    exact ⟨c, by rw [← mulVec_mulVec, hv]; exact hc⟩
  choose c hc using hcoll
  refine ⟨fun a b => ∑ x, star (c x a) * c x b, fun a b => ?_⟩
  calc code.codeProj * (E.errors a)ᴴ * E.errors b * code.codeProj
      = code.codeProj * (E.errors a)ᴴ * (∑ x, (K x)ᴴ * K x) * E.errors b * code.codeProj := by
        rw [hK1, Matrix.mul_one]
    _ = ∑ x, (K x * E.errors a * code.codeProj)ᴴ * (K x * E.errors b * code.codeProj) := by
        simp only [Finset.mul_sum, Finset.sum_mul, conjTranspose_mul, hPsa, Matrix.mul_assoc]
    _ = ∑ x, (star (c x a) * c x b) • code.codeProj := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hc, hc, conjTranspose_smul, hPsa, smul_mul_smul_comm, hP]
    _ = _ := by rw [Finset.sum_smul]

/-- **Knill-Laflamme theorem** (Nielsen-Chuang, Theorem 10.1): a code with
    projector `P` is correctable for the error set `{Eᵢ}` by a completely positive
    trace-preserving recovery map iff `P Eᵢ† Eⱼ P = αᵢⱼ P` for some matrix `α`.

    **Reference**: E. Knill, R. Laflamme, "Theory of quantum error-correcting
    codes", Phys. Rev. A 55 (1997), 900-911. -/
theorem knill_laflamme_iff_correctable (code : QuantumCode)
    {numErrors : ℕ} (E : ErrorSet code.dim numErrors) :
    (∃ α, KnillLaflamme code E α) ↔ IsCorrectableBy code E :=
  ⟨isCorrectableBy_of_knillLaflamme code E, knillLaflamme_of_isCorrectableBy code E⟩

/-! ## Standard Codes -/

/-- Standard basis ket: |i> in d-dimensional space, i.e. the function
    that is 1 at position i and 0 elsewhere. -/
def stdKet (d : ℕ) (i : Fin d) : Ket' d :=
  fun j => if j = i then 1 else 0

theorem stdKet_normalized (d : ℕ) (i : Fin d) : IsNormalized' (stdKet d i) := by
  unfold IsNormalized' braket' stdKet
  simp only [starRingEnd_apply]
  rw [show ∑ j : Fin d, star (if j = i then (1 : ℂ) else 0) * (if j = i then 1 else 0) =
    ∑ j : Fin d, if j = i then 1 else 0 from by
    congr 1; ext j; split <;> simp]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

theorem stdKet_orthogonal (d : ℕ) (i j : Fin d) (h : i ≠ j) :
    AreOrthogonal' (stdKet d i) (stdKet d j) := by
  unfold AreOrthogonal' braket' stdKet
  apply Finset.sum_eq_zero
  intro k _
  simp only [starRingEnd_apply]
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all

/-- Orthonormal system from standard basis vectors. -/
def stdBasisOrthonormal (d m : ℕ) (indices : Fin m → Fin d)
    (h_inj : Function.Injective indices) : OrthonormalKets d m where
  kets i := stdKet d (indices i)
  normalized i := stdKet_normalized d (indices i)
  orthogonal i j hij := stdKet_orthogonal d (indices i) (indices j) (h_inj.ne hij)

/-- The one-logical-qubit code on `n ≥ 1` physical qubits whose codewords are the
    computational basis states `|0…0⟩` and `|1…1⟩`, with the projector
    `|0…0⟩⟨0…0| + |1…1⟩⟨1…1|`. The stored distance is `1`: a single phase flip is
    undetectable on this code. -/
def basisPairCode (n : ℕ) (hn : n ≠ 0) : QuantumCode :=
  QuantumCode.ofOrthonormalKets n 1 1
    (stdBasisOrthonormal (2 ^ n) 2
      (fun i : Fin 2 =>
        if i = 0 then ⟨0, Nat.two_pow_pos n⟩
        else ⟨2 ^ n - 1, by have := Nat.two_pow_pos n; omega⟩)
      (by
        have h2 : 1 < 2 ^ n := Nat.one_lt_two_pow hn
        intro a b h
        fin_cases a <;> fin_cases b <;> first | rfl | (simp [Fin.ext_iff] at h; omega)))

/-- `basisPairCode` on 9 physical qubits. -/
def basisPairCode9 : QuantumCode := basisPairCode 9 (by norm_num)

/-- `basisPairCode` on 7 physical qubits. -/
def basisPairCode7 : QuantumCode := basisPairCode 7 (by norm_num)

/-- `basisPairCode` on 5 physical qubits. -/
def basisPairCode5 : QuantumCode := basisPairCode 5 (by norm_num)

end CatCrypt.Quantum.QuantumErrorCorrection
