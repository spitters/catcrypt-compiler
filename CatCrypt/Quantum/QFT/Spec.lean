/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The quantum Fourier transform as a unitary matrix

The `n`-qubit quantum Fourier transform in the convention of Nielsen and
Chuang, `QFT |j⟩ = (1/√N) ∑ k, ω ^ (j * k) |k⟩` with `N = 2 ^ n` and
`ω = exp (2πi / N)`, as a matrix over the computational basis `Fin (2 ^ n)`.

Mathlib's discrete Fourier transform `ZMod.dft` on functions `ZMod N → ℂ` uses
the character `exp (-2πi j k / N)` and no normalisation. Along the equivalence
`basisEquiv n : Fin (2 ^ n) ≃ ZMod (2 ^ n)` the matrix acts as `√N` times the
inverse transform, and its conjugate transpose as `1/√N` times the transform.
Unitarity is Fourier inversion (`ZMod.dft` is a linear equivalence).

## Main definitions

* `qftRoot n` — the root of unity `exp (2πi / 2 ^ n)`.
* `qftNorm n` — the normalisation `√(2 ^ n)`.
* `qftMatrix n` — the transform, with entries `qftRoot n ^ (j * k) / qftNorm n`.
* `basisEquiv n` — the equivalence `Fin (2 ^ n) ≃ ZMod (2 ^ n)`.
* `qftUnitary n` — `qftMatrix n` as an element of the unitary group.
* `negPerm n` — the negation permutation `|j⟩ ↦ |-j mod 2 ^ n⟩` of the basis.

## Main results

* `qftMatrix_mulVec` — `qftMatrix n` acts as `qftNorm n` times the inverse of
  `ZMod.dft`.
* `qftMatrix_conjTranspose_mulVec` — its conjugate transpose acts as
  `(qftNorm n)⁻¹` times `ZMod.dft`.
* `qftMatrix_mem_unitaryGroup` — the transform is unitary.
* `qftUnitary_inv_val` — the inverse is the conjugate transpose.
* `qftMatrix_mulVec_single` — the image of a computational basis state.
* `qftMatrix_mul_self` — the square of the transform is the permutation
  matrix of `negPerm n`.
* `qftMatrix_pow_four` — the fourth power of the transform is the identity.

## References

* Nielsen, Chuang — Quantum Computation and Quantum Information, §5.1
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open ZMod

noncomputable section

namespace CatCrypt.Quantum.QFT

/-! ## Root of unity and normalisation -/

/-- The root of unity `exp (2πi / 2 ^ n)`. -/
def qftRoot (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 ^ n : ℕ))

/-- The normalisation `√(2 ^ n)` of the `n`-qubit transform. -/
def qftNorm (n : ℕ) : ℂ := ((Real.sqrt (2 ^ n : ℕ) : ℝ) : ℂ)

theorem qftNorm_mul_self (n : ℕ) : qftNorm n * qftNorm n = ((2 ^ n : ℕ) : ℂ) := by
  rw [qftNorm, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp

theorem qftNorm_ne_zero (n : ℕ) : qftNorm n ≠ 0 := by
  intro h
  have := qftNorm_mul_self n
  rw [h] at this
  simp only [mul_zero, Nat.cast_pow, Nat.cast_ofNat] at this
  exact pow_ne_zero n two_ne_zero this.symm

theorem conj_qftNorm (n : ℕ) : (starRingEnd ℂ) (qftNorm n) = qftNorm n :=
  Complex.conj_ofReal _

/-- `qftRoot n` is a `2 ^ n`-th root of unity. -/
theorem qftRoot_pow_two_pow (n : ℕ) : qftRoot n ^ (2 ^ n) = 1 := by
  rw [qftRoot, ← Complex.exp_nat_mul,
    mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (pow_ne_zero n two_ne_zero))]
  exact Complex.exp_two_pi_mul_I

/-- The square of the root at width `n + 1` is the root at width `n`. -/
theorem qftRoot_succ_sq (n : ℕ) : qftRoot (n + 1) ^ 2 = qftRoot n := by
  rw [qftRoot, qftRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp
  ring

/-- The root at width `n + 1` raised to `2 ^ n` is `-1`. -/
theorem qftRoot_succ_pow_two_pow (n : ℕ) : qftRoot (n + 1) ^ (2 ^ n) = -1 := by
  rw [qftRoot, ← Complex.exp_nat_mul, ← Complex.exp_pi_mul_I]
  congr 1
  push_cast
  field_simp
  ring

/-- The exponent of `qftRoot n` is read modulo `2 ^ n`. -/
theorem qftRoot_pow_mod (n m : ℕ) : qftRoot n ^ (m % 2 ^ n) = qftRoot n ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m (2 ^ n), pow_add, pow_mul, qftRoot_pow_two_pow,
    one_pow, one_mul]

/-! ## The matrix -/

/-- The `n`-qubit quantum Fourier transform: the entry at row `k` and column
    `j` is `qftRoot n ^ (j * k) / qftNorm n`. -/
def qftMatrix (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.of fun k j => qftRoot n ^ (j.val * k.val) / qftNorm n

theorem qftMatrix_apply (n : ℕ) (k j : Fin (2 ^ n)) :
    qftMatrix n k j = qftRoot n ^ (j.val * k.val) / qftNorm n := rfl

/-- The transform is a symmetric matrix. -/
theorem qftMatrix_transpose (n : ℕ) : (qftMatrix n)ᵀ = qftMatrix n := by
  ext k j
  rw [Matrix.transpose_apply, qftMatrix_apply, qftMatrix_apply, mul_comm]

/-! ## The equivalence with `ZMod (2 ^ n)` -/

/-- `ZMod.finEquiv` sends an index to the cast of its value. -/
theorem finEquiv_apply (N : ℕ) [NeZero N] (j : Fin N) :
    ZMod.finEquiv N j = ((j.val : ℕ) : ZMod N) := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => exact (Fin.cast_val_eq_self j).symm

/-- The computational basis indices as residues modulo `2 ^ n`. -/
def basisEquiv (n : ℕ) : Fin (2 ^ n) ≃ ZMod (2 ^ n) := (ZMod.finEquiv (2 ^ n)).toEquiv

theorem basisEquiv_apply (n : ℕ) (j : Fin (2 ^ n)) :
    basisEquiv n j = ((j.val : ℕ) : ZMod (2 ^ n)) :=
  finEquiv_apply _ j

/-- A power of `qftRoot n` is a value of the standard additive character of
    `ZMod (2 ^ n)`. -/
theorem qftRoot_pow_eq_stdAddChar (n : ℕ) (j k : Fin (2 ^ n)) :
    qftRoot n ^ (j.val * k.val) = ZMod.stdAddChar (basisEquiv n j * basisEquiv n k) := by
  rw [basisEquiv_apply, basisEquiv_apply, ← Nat.cast_mul]
  have h := ZMod.stdAddChar_coe (N := 2 ^ n) ((j.val * k.val : ℕ) : ℤ)
  rw [Int.cast_natCast] at h
  rw [h, qftRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem qftMatrix_apply_stdAddChar (n : ℕ) (k j : Fin (2 ^ n)) :
    qftMatrix n k j = ZMod.stdAddChar (basisEquiv n j * basisEquiv n k) / qftNorm n := by
  rw [← qftRoot_pow_eq_stdAddChar]
  rfl

theorem qftMatrix_conjTranspose_apply (n : ℕ) (k j : Fin (2 ^ n)) :
    (qftMatrix n)ᴴ k j
      = ZMod.stdAddChar (-(basisEquiv n j * basisEquiv n k)) / qftNorm n := by
  rw [Matrix.conjTranspose_apply, qftMatrix_apply_stdAddChar, star_div₀,
    AddChar.map_neg_eq_conj, mul_comm]
  congr 1
  exact conj_qftNorm n

/-! ## The action as a discrete Fourier transform -/

/-- The conjugate transpose of `qftMatrix n` acts on an amplitude vector as
    `(qftNorm n)⁻¹` times `ZMod.dft`, along `basisEquiv n`. -/
theorem qftMatrix_conjTranspose_mulVec (n : ℕ) (v : Fin (2 ^ n) → ℂ) :
    (qftMatrix n)ᴴ *ᵥ v =
      fun k => (qftNorm n)⁻¹ * 𝓕 (v ∘ (basisEquiv n).symm) (basisEquiv n k) := by
  funext k
  rw [Matrix.mulVec, dotProduct, ZMod.dft_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (basisEquiv n) _ _ fun j => ?_
  rw [qftMatrix_conjTranspose_apply]
  simp only [div_eq_mul_inv, Function.comp_apply, Equiv.symm_apply_apply, smul_eq_mul]
  ring

/-- `qftMatrix n` acts on an amplitude vector as `qftNorm n` times the inverse
    of `ZMod.dft`, along `basisEquiv n`. -/
theorem qftMatrix_mulVec (n : ℕ) (v : Fin (2 ^ n) → ℂ) :
    qftMatrix n *ᵥ v =
      fun k => qftNorm n * 𝓕⁻ (v ∘ (basisEquiv n).symm) (basisEquiv n k) := by
  funext k
  rw [Matrix.mulVec, dotProduct, ZMod.invDFT_apply, smul_eq_mul, Finset.mul_sum,
    Finset.mul_sum]
  refine Fintype.sum_equiv (basisEquiv n) _ _ fun j => ?_
  rw [qftMatrix_apply_stdAddChar]
  have h := qftNorm_mul_self n
  have h0 := qftNorm_ne_zero n
  simp only [Function.comp_apply, Equiv.symm_apply_apply, smul_eq_mul]
  rw [← h]
  field_simp

/-! ## Unitarity -/

/-- `QFT† * QFT = 1`, from `𝓕 (𝓕⁻ Ψ) = Ψ`. -/
theorem qftMatrix_conjTranspose_mul_self (n : ℕ) : (qftMatrix n)ᴴ * qftMatrix n = 1 := by
  refine Matrix.mulVec_injective ?_
  funext v
  rw [← Matrix.mulVec_mulVec, qftMatrix_mulVec, qftMatrix_conjTranspose_mulVec,
    Matrix.one_mulVec]
  funext k
  have hcomp : ((fun k => qftNorm n * 𝓕⁻ (v ∘ (basisEquiv n).symm) (basisEquiv n k))
      ∘ (basisEquiv n).symm) = qftNorm n • 𝓕⁻ (v ∘ (basisEquiv n).symm) := by
    funext z
    simp
  rw [hcomp, _root_.map_smul, LinearEquiv.apply_symm_apply]
  simp [qftNorm_ne_zero n]

/-- `QFT * QFT† = 1`, from `𝓕⁻ (𝓕 Ψ) = Ψ`. -/
theorem qftMatrix_mul_conjTranspose_self (n : ℕ) : qftMatrix n * (qftMatrix n)ᴴ = 1 := by
  refine Matrix.mulVec_injective ?_
  funext v
  rw [← Matrix.mulVec_mulVec, qftMatrix_conjTranspose_mulVec, qftMatrix_mulVec,
    Matrix.one_mulVec]
  funext k
  have hcomp : ((fun k => (qftNorm n)⁻¹ * 𝓕 (v ∘ (basisEquiv n).symm) (basisEquiv n k))
      ∘ (basisEquiv n).symm) = (qftNorm n)⁻¹ • 𝓕 (v ∘ (basisEquiv n).symm) := by
    funext z
    simp
  rw [hcomp, _root_.map_smul, LinearEquiv.symm_apply_apply]
  simp [qftNorm_ne_zero n]

/-- The quantum Fourier transform is unitary. -/
theorem qftMatrix_mem_unitaryGroup (n : ℕ) :
    qftMatrix n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact qftMatrix_mul_conjTranspose_self n

/-- The quantum Fourier transform as an element of the unitary group. -/
def qftUnitary (n : ℕ) : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  ⟨qftMatrix n, qftMatrix_mem_unitaryGroup n⟩

@[simp]
theorem qftUnitary_val (n : ℕ) : (qftUnitary n).val = qftMatrix n := rfl

/-- The inverse transform is the conjugate transpose. -/
theorem qftUnitary_inv_val (n : ℕ) : ((qftUnitary n)⁻¹).val = (qftMatrix n)ᴴ := rfl

/-- The matrix inverse of the transform is its conjugate transpose. -/
theorem qftMatrix_inv (n : ℕ) : (qftMatrix n)⁻¹ = (qftMatrix n)ᴴ :=
  Matrix.inv_eq_left_inv (qftMatrix_conjTranspose_mul_self n)

/-! ## Action on the computational basis -/

/-- The transform sends the basis state `|j⟩` to the vector with amplitude
    `qftRoot n ^ (j * k) / qftNorm n` at `|k⟩`. -/
theorem qftMatrix_mulVec_single (n : ℕ) (j : Fin (2 ^ n)) :
    qftMatrix n *ᵥ Pi.single j 1 = fun k => qftRoot n ^ (j.val * k.val) / qftNorm n := by
  funext k
  rw [Matrix.mulVec_single_one]
  rfl

/-- The inverse transform sends `|j⟩` to the vector with the conjugate
    amplitudes. -/
theorem qftMatrix_conjTranspose_mulVec_single (n : ℕ) (j : Fin (2 ^ n)) :
    (qftMatrix n)ᴴ *ᵥ Pi.single j 1
      = fun k => (starRingEnd ℂ) (qftRoot n ^ (j.val * k.val)) / qftNorm n := by
  funext k
  rw [Matrix.mulVec_single_one]
  show star (qftMatrix n j k) = _
  rw [qftMatrix_apply, star_div₀, mul_comm]
  congr 1
  exact conj_qftNorm n

/-! ## The square and the fourth power -/

/-- Applying the inverse transform twice reflects the argument and divides
    by `N`. -/
theorem invDFT_invDFT {N : ℕ} [NeZero N] (Ψ : ZMod N → ℂ) :
    𝓕⁻ (𝓕⁻ Ψ) = fun j => (N : ℂ)⁻¹ * Ψ (-j) := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [LinearEquiv.apply_symm_apply,
    show (fun j => (N : ℂ)⁻¹ * Ψ (-j)) = (N : ℂ)⁻¹ • (fun j => Ψ (-j)) from rfl,
    ZMod.dft_const_smul, ZMod.dft_comp_neg, ZMod.invDFT_def']
  rfl

/-- The negation permutation of the computational basis, `|j⟩ ↦ |-j mod 2 ^ n⟩`,
    transported along `basisEquiv n`. -/
def negPerm (n : ℕ) : Equiv.Perm (Fin (2 ^ n)) :=
  ((basisEquiv n).trans (Equiv.neg (ZMod (2 ^ n)))).trans (basisEquiv n).symm

theorem basisEquiv_negPerm (n : ℕ) (k : Fin (2 ^ n)) :
    basisEquiv n (negPerm n k) = -basisEquiv n k := by
  simp [negPerm]

/-- The negation permutation is an involution. -/
theorem negPerm_mul_self (n : ℕ) : negPerm n * negPerm n = 1 := by
  ext k
  simp [negPerm, Equiv.Perm.mul_apply]

/-- The square of the transform sends an amplitude vector `v` to `v ∘ negPerm n`. -/
theorem qftMatrix_mul_self_mulVec (n : ℕ) (v : Fin (2 ^ n) → ℂ) :
    (qftMatrix n * qftMatrix n) *ᵥ v = v ∘ negPerm n := by
  rw [← Matrix.mulVec_mulVec, qftMatrix_mulVec, qftMatrix_mulVec]
  funext k
  have hcomp : ((fun k => qftNorm n * 𝓕⁻ (v ∘ (basisEquiv n).symm) (basisEquiv n k))
      ∘ (basisEquiv n).symm) = qftNorm n • 𝓕⁻ (v ∘ (basisEquiv n).symm) := by
    funext z
    simp
  rw [hcomp, _root_.map_smul, invDFT_invDFT]
  simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  rw [← mul_assoc, ← mul_assoc, qftNorm_mul_self, mul_inv_cancel₀ (by simp), one_mul]
  congr 1

/-- The square of the transform is the permutation matrix of the negation
    permutation. -/
theorem qftMatrix_mul_self (n : ℕ) :
    qftMatrix n * qftMatrix n = Equiv.Perm.permMatrix ℂ (negPerm n) := by
  refine Matrix.mulVec_injective ?_
  funext v
  rw [qftMatrix_mul_self_mulVec, Matrix.permMatrix_mulVec]

/-- The fourth power of the transform is the identity. -/
theorem qftMatrix_pow_four (n : ℕ) : qftMatrix n ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq (qftMatrix n), qftMatrix_mul_self, sq,
    ← Matrix.permMatrix_mul, negPerm_mul_self, Matrix.permMatrix_one]

end CatCrypt.Quantum.QFT
