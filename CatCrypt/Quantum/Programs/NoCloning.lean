/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Programs.Qubit
public import CatCrypt.Quantum.UnitaryChannel
public import CatCrypt.Quantum.TensorProduct
public import CatCryptCore.Quantum.PartialTrace

@[expose] public section

set_option autoImplicit false

/-!
# No-Cloning Theorem

The no-cloning theorem (Wootters & Zurek, 1982; Dieks, 1982): there is no
quantum operation that can copy an arbitrary unknown quantum state.

## Statement

There is no unitary U on ℂ² ⊗ ℂ² such that for all |ψ⟩:
  `U (|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩`

## Proof Sketch

Suppose such U exists. For two states |ψ⟩, |φ⟩:
- U(|ψ⟩|0⟩) = |ψ⟩|ψ⟩ and U(|φ⟩|0⟩) = |φ⟩|φ⟩
- Taking inner products: ⟨ψ|φ⟩ = ⟨ψ|φ⟩²
- Solutions: ⟨ψ|φ⟩ = 0 or ⟨ψ|φ⟩ = 1
- So U can only clone orthogonal or identical states, not arbitrary states.

## Main results

* `no_cloning` — the no-cloning theorem
* `no_broadcasting` — no positive linear map broadcasts all states
* `no_deleting` — no unitary maps `|ψ⟩|ψ⟩` to `|ψ⟩|0⟩` for all `|ψ⟩` (Pati–Braunstein,
  ancilla-free form)

## References

* Wootters, W.K. & Zurek, W.H. — *A Single Quantum Cannot Be Cloned*,
  Nature 299, 1982
* Dieks, D. — *Communication by EPR Devices*, Phys. Lett. A 92, 1982
* Barnum et al. — *Noncommuting Mixed States Cannot Be Broadcast*,
  PRL 76, 1996
-/

open scoped Matrix ComplexOrder
open Matrix Complex
open CatCrypt.Quantum
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.TensorProduct

noncomputable section

namespace CatCrypt.Quantum.Programs.NoCloning

/-! ## Cloning Map Specification -/

/-- Tensor product of two kets in arbitrary dimension. -/
def tensorKetGen {d : ℕ} (ψ φ : Ket d) : Ket (d * d) :=
  fun k =>
    let ⟨i, j⟩ := (TensorProduct.finProdEquiv d d).symm k
    ψ i * φ j

/-- A **cloning map** for dimension d is a unitary U on ℂ^d ⊗ ℂ^d such that
    U (|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩ for all normalized |ψ⟩. -/
def IsCloningMap {d : ℕ} (U : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (blank : Ket d) : Prop :=
  U * Uᴴ = 1 ∧
  ∀ (ψ : Ket d), IsNormalized ψ →
    ∀ k, (∑ j, U k j * tensorKetGen ψ blank j) = tensorKetGen ψ ψ k

/-! ## Tensor Product Inner Product -/

/-- Inner product of tensor products factors:
    ⟨ψ₁⊗ψ₂|φ₁⊗φ₂⟩ = ⟨ψ₁|φ₁⟩·⟨ψ₂|φ₂⟩. -/
private theorem braket_tensorKetGen {d : ℕ} (ψ₁ ψ₂ φ₁ φ₂ : Fin d → ℂ) :
    braket (tensorKetGen ψ₁ ψ₂) (tensorKetGen φ₁ φ₂) = braket ψ₁ φ₁ * braket ψ₂ φ₂ := by
  simp only [braket, tensorKetGen]
  set e := TensorProduct.finProdEquiv d d
  -- Reindex: ∑_{k : Fin(d*d)} f(e.symm k) = ∑_{(i,j) : Fin d × Fin d} f(i,j)
  rw [show (∑ k : Fin (d * d), starRingEnd ℂ
      (let ⟨i, j⟩ := e.symm k; ψ₁ i * ψ₂ j) *
      (let ⟨i, j⟩ := e.symm k; φ₁ i * φ₂ j)) =
    ∑ p : Fin d × Fin d, starRingEnd ℂ (ψ₁ p.1 * ψ₂ p.2) * (φ₁ p.1 * φ₂ p.2) from
    Fintype.sum_equiv e.symm _ _ (fun k => by simp)]
  rw [Fintype.sum_prod_type]
  simp_rw [map_mul (starRingEnd ℂ), mul_mul_mul_comm]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

/-- Unitarity: if U*U† = 1, then ⟨Uv|Uw⟩ = ⟨v|w⟩ where Uv means k ↦ ∑_j U_{kj} v_j. -/
private theorem unitary_preserves_braket {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) (v w : Fin n → ℂ) :
    braket (fun k => ∑ j, U k j * v j) (fun k => ∑ j, U k j * w j) = braket v w := by
  have hUadj : Uᴴ * U = 1 := mul_eq_one_comm.mpr hU
  -- Extract (U†U)_{ij} = δ_{ij}
  have hUU : ∀ i j : Fin n, ∑ k, star (U k i) * U k j = if i = j then 1 else 0 := by
    intro i j
    have := congr_fun (congr_fun hUadj i) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
    exact this
  simp only [braket]
  -- Use transitivity through the rearranged form
  -- Direct calculation: expand, rearrange sums, use U†U = I
  have step1 : ∀ k, (starRingEnd ℂ) (∑ j, U k j * v j) * ∑ j, U k j * w j =
      ∑ i, ∑ j, star (U k i) * star (v i) * (U k j * w j) := by
    intro k
    rw [map_sum (starRingEnd ℂ)]
    simp_rw [map_mul (starRingEnd ℂ), starRingEnd_apply,
      Finset.sum_mul, Finset.mul_sum]
  have step2 : ∀ i j, ∑ k, star (U k i) * star (v i) * (U k j * w j) =
      star (v i) * w j * ∑ k, star (U k i) * U k j := by
    intro i j
    have : ∀ k, star (U k i) * star (v i) * (U k j * w j) =
        star (v i) * w j * (star (U k i) * U k j) := fun k => by ring
    simp_rw [this, ← Finset.mul_sum]
  simp_rw [step1]
  rw [Finset.sum_comm]
  congr 1; ext i
  rw [Finset.sum_comm]
  simp_rw [step2, hUU]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    starRingEnd_apply]

/-! ## Inner Product Lemma -/

/-- If U is a cloning map, then for any two states |ψ⟩, |φ⟩:
    ⟨ψ|φ⟩ = ⟨ψ|φ⟩² (inner product is preserved as a square).

    This follows from unitarity: ⟨ψ⊗0|U†U|φ⊗0⟩ = ⟨ψ⊗0|φ⊗0⟩ = ⟨ψ|φ⟩
    and U|ψ⊗0⟩ = |ψ⊗ψ⟩, so ⟨ψ⊗ψ|φ⊗φ⟩ = ⟨ψ|φ⟩·⟨ψ|φ⟩ = ⟨ψ|φ⟩². -/
theorem cloning_inner_product_sq {d : ℕ} (U : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (blank : Ket d)
    (hU : IsCloningMap U blank)
    (ψ φ : Ket d) (hψ : IsNormalized ψ) (hφ : IsNormalized φ) :
    braket ψ φ = braket ψ φ * braket ψ φ := by
  obtain ⟨hUU, hclone⟩ := hU
  -- Define ket vectors: v = ψ⊗blank, w = φ⊗blank
  set v := tensorKetGen ψ blank
  set w := tensorKetGen φ blank
  -- Unitarity: ⟨Uv|Uw⟩ = ⟨v|w⟩
  have h_unit : braket (fun k => ∑ j, U k j * v j) (fun k => ∑ j, U k j * w j) =
      braket v w := unitary_preserves_braket U hUU v w
  -- Cloning: U·v = ψ⊗ψ, U·w = φ⊗φ
  have hUv : (fun k => ∑ j, U k j * v j) = tensorKetGen ψ ψ := funext (hclone ψ hψ)
  have hUw : (fun k => ∑ j, U k j * w j) = tensorKetGen φ φ := funext (hclone φ hφ)
  -- LHS: ⟨ψ⊗ψ|φ⊗φ⟩ = ⟨ψ|φ⟩²
  rw [hUv, hUw] at h_unit
  rw [braket_tensorKetGen] at h_unit
  -- RHS: ⟨ψ⊗blank|φ⊗blank⟩ = ⟨ψ|φ⟩·⟨blank|blank⟩
  rw [braket_tensorKetGen] at h_unit
  -- Derive blank normalization from ψ case
  have h_blank : braket blank blank = 1 := by
    -- Apply unitarity to ψ, ψ: ⟨ψ⊗ψ|ψ⊗ψ⟩ = ⟨ψ⊗blank|ψ⊗blank⟩
    have h_self : braket (fun k => ∑ j, U k j * v j) (fun k => ∑ j, U k j * v j) =
        braket v v := unitary_preserves_braket U hUU v v
    rw [hUv] at h_self
    rw [braket_tensorKetGen, braket_tensorKetGen] at h_self
    -- ⟨ψ|ψ⟩ · ⟨ψ|ψ⟩ = ⟨ψ|ψ⟩ · ⟨blank|blank⟩
    rw [hψ] at h_self
    simp at h_self
    exact h_self.symm
  -- Now: braket ψ φ * braket ψ φ = braket ψ φ * braket blank blank
  rw [h_blank, mul_one] at h_unit
  exact h_unit.symm

/-! ## The No-Cloning Theorem -/

/-- **No-cloning theorem** (Wootters-Zurek 1982, Dieks 1982).

    There is no unitary cloning map for d ≥ 2. More precisely, if U is a
    cloning map then only orthogonal or identical states can be cloned.

    Proof: from `⟨ψ|φ⟩ = ⟨ψ|φ⟩²` we get `⟨ψ|φ⟩(1 - ⟨ψ|φ⟩) = 0`, so
    `⟨ψ|φ⟩ = 0` (orthogonal) or `⟨ψ|φ⟩ = 1` (identical up to phase). -/
theorem no_cloning {d : ℕ} (hd : 2 ≤ d)
    (U : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) (blank : Ket d)
    (hU : IsCloningMap U blank)
    (ψ φ : Ket d) (hψ : IsNormalized ψ) (hφ : IsNormalized φ) :
    braket ψ φ = 0 ∨ braket ψ φ = 1 := by
  have hsq := cloning_inner_product_sq U blank hU ψ φ hψ hφ
  -- From z = z², we get z * (1 - z) = 0, so z = 0 or z = 1
  have h : braket ψ φ * (1 - braket ψ φ) = 0 := by grind
  rcases mul_eq_zero.mp h with h0 | h1
  · left; exact h0
  · right; grind

/-- |0⟩ is normalized. -/
private theorem ket0_normalized : IsNormalized ket0 := by
  simp only [IsNormalized, braket, ket0, Fin.sum_univ_two, starRingEnd_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- |+⟩ is normalized. -/
private theorem ketPlus_normalized : IsNormalized ketPlus := by
  simp only [IsNormalized, braket, ketPlus, Fin.sum_univ_two, starRingEnd_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Complex.star_def, Complex.conj_ofReal]
  ring_nf
  -- Goal: ↑(√2)⁻¹ ^ 2 * 2 = 1, where ↑ is ofReal and the arg is (√2)⁻¹
  rw [← ofReal_pow, ← ofReal_ofNat, ← ofReal_mul]
  rw [show ((Real.sqrt 2)⁻¹ ^ 2 * 2 : ℝ) = (1 : ℝ) from by
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)
    field_simp
    linarith]
  exact ofReal_one

/-- ⟨0|+⟩ = 1/√2 (used in no_cloning_qubit). -/
private theorem braket_ket0_ketPlus :
    braket ket0 ketPlus = ↑(1 / Real.sqrt 2) := by
  simp only [braket, ket0, ketPlus, Fin.sum_univ_two, starRingEnd_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **No-cloning for qubits**: no unitary on ℂ⁴ clones all qubit states.

    Specialized to d = 2, this says there exist non-orthogonal, non-identical
    qubit states (e.g., |0⟩ and |+⟩) that cannot both be cloned by any single U. -/
theorem no_cloning_qubit :
    ¬ ∃ (U : Matrix (Fin 4) (Fin 4) ℂ),
      IsCloningMap U ket0 := by
  intro ⟨U, hU⟩
  have h := no_cloning (by omega : 2 ≤ 2) U ket0 hU ket0 ketPlus ket0_normalized
    ketPlus_normalized
  rw [braket_ket0_ketPlus] at h
  rcases h with h0 | h1
  · -- braket = 0, but 1/√2 ≠ 0
    have : (1 / Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    exact this (ofReal_eq_zero.mp h0)
  · -- braket = 1, but 1/√2 ≠ 1
    have hsqrt : Real.sqrt 2 ≠ 1 := by
      intro h
      have := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
      rw [h, one_pow] at this; linarith
    have : (1 / Real.sqrt 2 : ℝ) ≠ 1 := by
      rw [one_div, ne_eq, inv_eq_one]
      exact hsqrt
    exact this (ofReal_eq_one.mp h1)

/-! ## No-Broadcasting Theorem -/

/-- A positive semidefinite matrix with a zero diagonal entry at `a` has zero
    entries in row `a`: the principal `2 × 2` minor at `(a, b)` has determinant
    `-|M a b|² ≥ 0`. -/
private theorem posSemidef_apply_eq_zero_of_diag {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) {a : n} (ha : M a a = 0) (b : n) :
    M a b = 0 := by
  have h := (hM.submatrix ![a, b]).det_nonneg
  have hba : M b a = star (M a b) := (hM.1.apply b a).symm
  simp only [Matrix.det_fin_two, submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    ha, zero_mul, zero_sub, hba] at h
  rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_neg, Complex.zero_le_real] at h
  exact Complex.normSq_eq_zero.1 (le_antisymm (by linarith) (Complex.normSq_nonneg _))

/-- A positive semidefinite `D` on `ℂ^d ⊗ ℂ^d` whose two marginals both equal the
    basis projector `|k⟩⟨k|` has zero diagonal entries at every product index
    `(i, j)` with `i ≠ j`. -/
private theorem diag_eq_zero_of_marginals_single {d : ℕ}
    {D : Matrix (Fin (d * d)) (Fin (d * d)) ℂ} (hD : D.PosSemidef) (k : Fin d)
    (h₂ : PartialTrace.partialTrace₂ D =
      vecMulVec (Pi.single k 1 : Fin d → ℂ) (star (Pi.single k 1)))
    (h₁ : PartialTrace.partialTrace₁ D =
      vecMulVec (Pi.single k 1 : Fin d → ℂ) (star (Pi.single k 1)))
    {i j : Fin d} (hij : i ≠ j) :
    D (finProdEquiv d d (i, j)) (finProdEquiv d d (i, j)) = 0 := by
  have hsum : ∀ f : Fin d → ℂ, (∀ l, 0 ≤ f l) → ∑ l, f l = 0 → ∀ l, f l = 0 :=
    fun f hf h l => (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hf l)).1 h l
      (Finset.mem_univ l)
  by_cases hik : i = k
  · subst hik
    have h := congr_fun (congr_fun h₁ j) j
    rw [PartialTrace.partialTrace₁_apply, vecMulVec_apply, Pi.single_eq_of_ne hij.symm,
      zero_mul] at h
    exact hsum _ (fun _ => hD.diag_nonneg) h i
  · have h := congr_fun (congr_fun h₂ i) i
    rw [PartialTrace.partialTrace₂_apply, vecMulVec_apply, Pi.single_eq_of_ne hik,
      zero_mul] at h
    exact hsum _ (fun _ => hD.diag_nonneg) h j

/-- **No-broadcasting theorem** (Barnum et al. 1996), stated for positive maps:
    for `d ≥ 2` no `ℂ`-linear map `Φ` from `d × d` matrices to `d² × d²` matrices
    that preserves positive semidefiniteness has both partial traces of `Φ ρ`
    equal to `ρ` for every positive semidefinite `ρ`.

    The marginal conditions force the diagonal of `Φ |k⟩⟨k|` to vanish off the
    index pairs `(k, k)`. Linearity gives `Φ |+⟩⟨+| + Φ |−⟩⟨−| = 2 (Φ |0⟩⟨0| + Φ |1⟩⟨1|)`
    (unnormalised `|±⟩ = |0⟩ ± |1⟩`), so `Φ |+⟩⟨+|` has zero diagonal at every
    pair `(i, j)` with `i ≠ j`, hence zero rows there, and its first partial trace
    has entry `0` at `(0, 1)`, where `|+⟩⟨+|` has entry `1`.

    **Reference**: H. Barnum et al., "Noncommuting mixed states cannot be
    broadcast", PRL 76 (1996), 2818-2821. -/
theorem no_broadcasting {d : ℕ} (hd : 2 ≤ d) :
    ¬ ∃ (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin (d * d)) (Fin (d * d)) ℂ),
      (∀ ρ, ρ.PosSemidef → (Φ ρ).PosSemidef) ∧
      (∀ ρ, ρ.PosSemidef → CatCrypt.Quantum.PartialTrace.partialTrace₂ (Φ ρ) = ρ) ∧
      (∀ ρ, ρ.PosSemidef → CatCrypt.Quantum.PartialTrace.partialTrace₁ (Φ ρ) = ρ) := by
  rintro ⟨Φ, hpos, h₂, h₁⟩
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin d := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  set P : (Fin d → ℂ) → Matrix (Fin d) (Fin d) ℂ := fun v => vecMulVec v (star v) with hPdef
  have hP : ∀ v, (P v).PosSemidef := fun v => posSemidef_vecMulVec_self_star v
  set u₀ : Fin d → ℂ := Pi.single i₀ 1 with hu₀
  set u₁ : Fin d → ℂ := Pi.single i₁ 1 with hu₁
  have hsum : P (u₀ + u₁) + P (u₀ - u₁) = (2 : ℂ) • (P u₀ + P u₁) := by
    ext a b
    simp only [hPdef, vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
      Pi.sub_apply, Pi.star_apply, star_add, star_sub, smul_eq_mul]
    ring
  set A := Φ (P (u₀ + u₁)) with hAdef
  have hApsd : A.PosSemidef := hpos _ (hP _)
  have hBpsd : (Φ (P (u₀ - u₁))).PosSemidef := hpos _ (hP _)
  have hAB : A + Φ (P (u₀ - u₁)) = (2 : ℂ) • (Φ (P u₀) + Φ (P u₁)) := by
    rw [hAdef, ← map_add, hsum, map_smul, map_add]
  have hd₀ : ∀ {i j : Fin d}, i ≠ j →
      Φ (P u₀) (finProdEquiv d d (i, j)) (finProdEquiv d d (i, j)) = 0 :=
    fun hij => diag_eq_zero_of_marginals_single (hpos _ (hP _)) i₀ (h₂ _ (hP _))
      (h₁ _ (hP _)) hij
  have hd₁ : ∀ {i j : Fin d}, i ≠ j →
      Φ (P u₁) (finProdEquiv d d (i, j)) (finProdEquiv d d (i, j)) = 0 :=
    fun hij => diag_eq_zero_of_marginals_single (hpos _ (hP _)) i₁ (h₂ _ (hP _))
      (h₁ _ (hP _)) hij
  have hA : ∀ {i j : Fin d}, i ≠ j →
      A (finProdEquiv d d (i, j)) (finProdEquiv d d (i, j)) = 0 := by
    intro i j hij
    have h := congr_fun (congr_fun hAB (finProdEquiv d d (i, j))) (finProdEquiv d d (i, j))
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.add_apply, hd₀ hij, hd₁ hij, add_zero,
      smul_zero] at h
    exact ((add_eq_zero_iff_of_nonneg hApsd.diag_nonneg hBpsd.diag_nonneg).1 h).1
  have hzero : ∀ l, A (finProdEquiv d d (i₀, l)) (finProdEquiv d d (i₁, l)) = 0 := by
    intro l
    by_cases hl : l = i₀
    · rw [hl, ← hApsd.1.apply,
        posSemidef_apply_eq_zero_of_diag hApsd (hA h01.symm), star_zero]
    · exact posSemidef_apply_eq_zero_of_diag hApsd (hA (Ne.symm hl)) _
  have hentry := congr_fun (congr_fun (h₂ _ (hP (u₀ + u₁))) i₀) i₁
  rw [PartialTrace.partialTrace₂_apply] at hentry
  rw [Finset.sum_eq_zero (fun l _ => hzero l)] at hentry
  simp [hPdef, hu₀, hu₁, vecMulVec_apply, h01, h01.symm] at hentry

/-! ## No-Deleting Theorem -/

/-- **No-deleting theorem** (Pati & Braunstein 2000).

    The dual of no-cloning: there is no unitary that maps |ψ⟩|ψ⟩ → |ψ⟩|0⟩
    for all |ψ⟩. (If cloning is impossible in one direction, so is
    un-cloning/deleting.) -/
theorem no_deleting {d : ℕ} (hd : 2 ≤ d)
    (U : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (blank : Ket d) :
    ¬ (U * Uᴴ = 1 ∧
       ∀ (ψ : Ket d), IsNormalized ψ →
         ∀ k, (∑ j, U k j * tensorKetGen ψ ψ j) = tensorKetGen ψ blank k) := by
  intro ⟨hUU, hdel⟩
  -- U† is a cloning map: U†|ψ,blank⟩ = |ψψ⟩
  have hUadj : Uᴴ * U = 1 := mul_eq_one_comm.mpr hUU
  -- U† is unitary: U†*(U†)† = U†*U = 1
  -- Note: (U†)† = U, so U†*(U†)† = U†*U = 1
  have hUdagUnit : Uᴴ * Uᴴᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact hUadj
  -- U† clones: from U|ψψ⟩ = |ψ,blank⟩ and U†U = 1, we get U†|ψ,blank⟩ = |ψψ⟩
  have hUdagClone : ∀ (ψ : Ket d), IsNormalized ψ →
      ∀ k, (∑ j, Uᴴ k j * tensorKetGen ψ blank j) = tensorKetGen ψ ψ k := by
    intro ψ hψ k
    -- U†(Uv) = v for v = ψ⊗ψ, and Uv = ψ⊗blank
    have hUv := hdel ψ hψ
    -- ∑_j U†_{kj} (ψ⊗blank)_j = ∑_j U†_{kj} (∑_l U_{jl} (ψ⊗ψ)_l)
    -- Substitute the cloning condition: (ψ⊗blank)_j = ∑_l U_{jl} (ψ⊗ψ)_l
    conv_lhs => arg 2; ext j; rw [← hUv j]
    -- Now: ∑_j U†_{kj} * (∑_l U_{jl} * (ψ⊗ψ)_l)
    -- Distribute and swap: = ∑_l (∑_j U†_{kj} * U_{jl}) * (ψ⊗ψ)_l
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    -- Use (U†U)_{kl} = δ_{kl}
    have hentry := congr_fun (congr_fun hUadj k)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hentry
    -- Reassociate: Uᴴ k j * (U j l * t_l) = (Uᴴ k j * U j l) * t_l
    simp_rw [show ∀ l, ∑ j, Uᴴ k j * (U j l * tensorKetGen ψ ψ l) =
        (∑ j, Uᴴ k j * U j l) * tensorKetGen ψ ψ l from
      fun l => by
        conv_lhs => arg 2; ext j; rw [← mul_assoc]
        exact (Finset.sum_mul (Finset.univ) (fun j => Uᴴ k j * U j l) (tensorKetGen ψ ψ l)).symm]
    -- Use hentry: ∑_j conj(U_{jk}) * U_{jl} = δ_{kl}
    -- Note: Uᴴ k j = star (U j k), so ∑_j Uᴴ k j * U j l = ∑_j star(U j k) * U j l = hentry l
    simp_rw [show ∀ l, ∑ j, Uᴴ k j * U j l = if k = l then 1 else 0 from by
      intro l
      simp only [Matrix.conjTranspose_apply]
      exact hentry l]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- U† is a cloning map
  have hClone : IsCloningMap Uᴴ blank := ⟨hUdagUnit, hUdagClone⟩
  -- For d ≥ 2, construct basis ket e₀ and superposition, derive contradiction
  -- Standard basis kets
  let i₀ : Fin d := ⟨0, by omega⟩
  let i₁ : Fin d := ⟨1, by omega⟩
  have hi01 : i₀ ≠ i₁ := by intro h; exact absurd (Fin.mk.inj h) (by omega)
  let e₀ : Ket d := fun i => if i = i₀ then 1 else 0
  let sr : ℝ := 1 / Real.sqrt 2
  have hsr_pos : (0 : ℝ) < sr := by positivity
  have hsr_ne1 : sr ≠ 1 := by
    simp only [sr, one_div, ne_eq, inv_eq_one]
    intro h; have := Real.sq_sqrt (show (2:ℝ) ≥ 0 by norm_num)
    rw [h, one_pow] at this; linarith
  have hsr2 : sr * sr * 2 = 1 := by
    simp only [sr, one_div]
    have : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)
    field_simp; linarith
  let sup : Ket d := fun i => if i = i₀ then ↑sr else if i = i₁ then ↑sr else 0
  -- Helper: sum of f over Fin d where f is nonzero only at i₀
  have sum_at_0 : ∀ (c : ℂ), ∑ i : Fin d, (if i = i₀ then c else 0) = c := by
    intro c; rw [Finset.sum_ite_eq']; simp
  -- Helper: sum of f over Fin d where f is nonzero only at i₀ and i₁
  have sum_at_01 : ∀ (c₀ c₁ : ℂ),
      ∑ i : Fin d, (if i = i₀ then c₀ else if i = i₁ then c₁ else 0) = c₀ + c₁ := by
    intro c₀ c₁
    have : ∀ i : Fin d, (if i = i₀ then c₀ else if i = i₁ then c₁ else 0) =
        (if i = i₀ then c₀ else 0) + (if i = i₁ then c₁ else 0) := by
      intro i; by_cases h0 : i = i₀
      · simp [h0, show i₀ ≠ i₁ from hi01]
      · by_cases h1 : i = i₁
        · simp [h1, show i₁ ≠ i₀ from hi01.symm]
        · simp [h0, h1]
    simp_rw [this, Finset.sum_add_distrib, sum_at_0, Finset.sum_ite_eq']; simp
  -- e₀ is normalized
  have he₀ : IsNormalized e₀ := by
    show braket e₀ e₀ = 1; unfold braket
    simp only [starRingEnd_apply, e₀]
    convert sum_at_0 1 using 1
    congr 1; ext i; split <;> simp
  -- sup is normalized
  have hsup : IsNormalized sup := by
    show braket sup sup = 1; unfold braket
    simp only [starRingEnd_apply, sup]
    have : ∀ i : Fin d, star (if i = i₀ then (↑sr:ℂ) else if i = i₁ then ↑sr else 0) *
        (if i = i₀ then (↑sr:ℂ) else if i = i₁ then ↑sr else 0) =
      if i = i₀ then star (↑sr:ℂ) * ↑sr else if i = i₁ then star (↑sr:ℂ) * ↑sr else 0 := by
      intro i; split <;> [rfl; split <;> simp]
    simp_rw [this, sum_at_01]
    rw [Complex.star_def, Complex.conj_ofReal]
    rw [show (↑sr : ℂ) * ↑sr + (↑sr : ℂ) * ↑sr = ↑(sr * sr * 2) from by push_cast; ring]
    rw [hsr2]; exact ofReal_one
  -- braket e₀ sup = sr
  have hbk : braket e₀ sup = ↑sr := by
    unfold braket; simp only [starRingEnd_apply, e₀, sup]
    convert sum_at_0 (↑sr : ℂ) using 1
    congr 1; ext i; split
    · subst_vars; simp
    · simp [*]
  -- Contradiction via no_cloning
  have h := no_cloning hd Uᴴ blank hClone e₀ sup he₀ hsup
  rw [hbk] at h
  rcases h with h0 | h1
  · exact hsr_pos.ne' (ofReal_eq_zero.mp h0)
  · exact hsr_ne1 (ofReal_eq_one.mp h1)

end CatCrypt.Quantum.Programs.NoCloning
