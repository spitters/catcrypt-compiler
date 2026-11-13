/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Programs.Qubit
public import CatCrypt.Quantum.TensorProduct

@[expose] public section

set_option autoImplicit false

/-!
# The CHSH inequality and the Tsirelson bound

A CHSH strategy is a shared state and two ±1 observables for each of Alice and Bob; its CHSH
value is `S = ⟨A₀B₀⟩ + ⟨A₀B₁⟩ + ⟨A₁B₀⟩ - ⟨A₁B₁⟩`. Product states give `S ≤ 2`; quantum
strategies give `S ≤ 2√2` (Tsirelson), and the optimal strategy on `|Φ⁺⟩` attains it.

## Main results

* `chshValue` — the CHSH value of a strategy
* `chsh_classical_bound` — a product state with real expectations in `[-1, 1]` gives `S ≤ 2`
* `tsirelson_bound` — a quantum strategy (density-matrix state, Hermitian involutive
  observables, `CHSHStrategy.IsQuantum`) gives `S ≤ 2√2`
* `optimalCHSH_value` — the optimal quantum strategy attains `S = 2√2`
* `optimalCHSH_beats_classical` — `S = 2√2 > 2`

## References

* Clauser, Horne, Shimony, Holt — *Proposed Experiment to Test Local Hidden-Variable
  Theories*, PRL 23, 1969
* Tsirelson — *Quantum Generalizations of Bell's Inequality*, Lett. Math. Phys. 4, 1980
-/

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical
open CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
open CatCrypt.Quantum.Programs.Qubit

noncomputable section

namespace CatCrypt.Quantum.Programs.CHSH

/-! ## CHSH Game -/

/-- A CHSH strategy consists of a shared quantum state and measurement operators
    for Alice and Bob. -/
structure CHSHStrategy where
  /-- Dimension of Alice's system. -/
  dA : ℕ
  /-- Dimension of Bob's system. -/
  dB : ℕ
  /-- The shared quantum state (density matrix on C^{dA * dB}). -/
  state : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ
  /-- Alice's measurement operators for inputs 0, 1 (binary outcome). -/
  aliceObs : Fin 2 → Matrix (Fin dA) (Fin dA) ℂ
  /-- Bob's measurement operators for inputs 0, 1 (binary outcome). -/
  bobObs : Fin 2 → Matrix (Fin dB) (Fin dB) ℂ

/-- The CHSH value for a given strategy.
    S = <A0 B0> + <A0 B1> + <A1 B0> - <A1 B1>
    where <Ax By> = tr(rho * (Ax tensor By)). -/
def chshValue (strat : CHSHStrategy) : ℝ :=
  -- S = <A0 B0> + <A0 B1> + <A1 B0> - <A1 B1>
  -- where <Ax By> = Tr(rho * (Ax kron By))
  let correlator (x y : Fin 2) : ℝ :=
    (strat.state * TensorProduct.kronecker (strat.aliceObs x) (strat.bobObs y)).trace.re
  correlator 0 0 + correlator 0 1 + correlator 1 0 - correlator 1 1

/-- **Algebraic CHSH bound**: for bounded correlator values, S ≤ 2.
    This is the core arithmetic fact underlying Bell's theorem. -/
theorem chsh_algebraic_bound (a₀ a₁ b₀ b₁ : ℝ)
    (ha₀ : |a₀| ≤ 1) (ha₁ : |a₁| ≤ 1) (hb₀ : |b₀| ≤ 1) (hb₁ : |b₁| ≤ 1) :
    a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁ ≤ 2 := by
  -- Proof: 2(2-S) = ∑ᵢ ½(1±aᵢ)(1±bⱼ) ≥ 0 since all factors are nonneg.
  have ha₀' := abs_le.mp ha₀
  have ha₁' := abs_le.mp ha₁
  have hb₀' := abs_le.mp hb₀
  have hb₁' := abs_le.mp hb₁
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a₀) (by linarith : (0 : ℝ) ≤ 1 + b₁),
             mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a₀) (by linarith : (0 : ℝ) ≤ 1 - b₁),
             mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a₁) (by linarith : (0 : ℝ) ≤ 1 - b₀),
             mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a₁) (by linarith : (0 : ℝ) ≤ 1 + b₀),
             mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a₀) (by linarith : (0 : ℝ) ≤ 1 + b₀),
             mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a₀) (by linarith : (0 : ℝ) ≤ 1 - b₀),
             mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a₁) (by linarith : (0 : ℝ) ≤ 1 - b₁),
             mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a₁) (by linarith : (0 : ℝ) ≤ 1 + b₁)]

/-- The classical bound: no classical (local hidden variable) strategy
    achieves S > 2. A classical strategy uses a separable (product) state,
    and the observables have real, bounded expectation values. -/
theorem chsh_classical_bound (strat : CHSHStrategy)
    (ρA : Matrix (Fin strat.dA) (Fin strat.dA) ℂ)
    (ρB : Matrix (Fin strat.dB) (Fin strat.dB) ℂ)
    (h_state : strat.state = ρA ⊗ₖ ρB)
    (h_real_A : ∀ x, ((ρA * strat.aliceObs x).trace).im = 0)
    (h_real_B : ∀ y, ((ρB * strat.bobObs y).trace).im = 0)
    (h_bound_A : ∀ x, |((ρA * strat.aliceObs x).trace).re| ≤ 1)
    (h_bound_B : ∀ y, |((ρB * strat.bobObs y).trace).re| ≤ 1) :
    chshValue strat ≤ 2 := by
  unfold chshValue
  simp only [h_state, kronecker_mul_kronecker, trace_kronecker,
    Complex.mul_re, h_real_A, h_real_B, mul_zero, sub_zero]
  exact chsh_algebraic_bound _ _ _ _
    (h_bound_A 0) (h_bound_A 1) (h_bound_B 0) (h_bound_B 1)

/-! ## Tsirelson's Bound -/

/-- A CHSH strategy is quantum when its state is a density matrix (positive
    semidefinite, trace one) and every observable is Hermitian and squares to
    the identity (a `±1`-valued observable). -/
structure CHSHStrategy.IsQuantum (strat : CHSHStrategy) : Prop where
  /-- The shared state is positive semidefinite. -/
  state_posSemidef : strat.state.PosSemidef
  /-- The shared state has trace one. -/
  trace_state : strat.state.trace = 1
  /-- Alice's observables are Hermitian. -/
  alice_hermitian : ∀ x, (strat.aliceObs x).IsHermitian
  /-- Alice's observables square to the identity. -/
  alice_sq : ∀ x, strat.aliceObs x * strat.aliceObs x = 1
  /-- Bob's observables are Hermitian. -/
  bob_hermitian : ∀ y, (strat.bobObs y).IsHermitian
  /-- Bob's observables square to the identity. -/
  bob_sq : ∀ y, strat.bobObs y * strat.bobObs y = 1

/-- Sum-of-squares identity behind Tsirelson's bound: in a `ℂ`-algebra, for
    involutions `x₀ x₁ y₀ y₁` with each `xᵢ` commuting with each `yⱼ` and a
    scalar `r` with `r² = 2`,
    `(r x₀ - (y₀ + y₁))² + (r x₁ - (y₀ - y₁))² = 8 - 2r·C` where
    `C = x₀y₀ + x₀y₁ + x₁y₀ - x₁y₁`. -/
theorem chsh_sos_identity {R : Type*} [Ring R] [Algebra ℂ R] (x₀ x₁ y₀ y₁ : R) (r : ℂ)
    (hr : r * r = 2) (hx₀ : x₀ * x₀ = 1) (hx₁ : x₁ * x₁ = 1)
    (hy₀ : y₀ * y₀ = 1) (hy₁ : y₁ * y₁ = 1)
    (c₀₀ : y₀ * x₀ = x₀ * y₀) (c₀₁ : y₁ * x₀ = x₀ * y₁)
    (c₁₀ : y₀ * x₁ = x₁ * y₀) (c₁₁ : y₁ * x₁ = x₁ * y₁) :
    (r • x₀ - (y₀ + y₁)) * (r • x₀ - (y₀ + y₁)) +
        (r • x₁ - (y₀ - y₁)) * (r • x₁ - (y₀ - y₁)) =
      (8 : ℂ) • (1 : R) - (2 * r) • (x₀ * y₀ + x₀ * y₁ + x₁ * y₀ - x₁ * y₁) := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc,
    mul_smul_comm, hx₀, hx₁, hy₀, hy₁, c₀₀, c₀₁, c₁₀, c₁₁]
  match_scalars <;>
    first | ring1 | linear_combination (-2 : ℂ) * hr | linear_combination (2 : ℂ) * hr

/-- For a positive semidefinite `ρ`, `Re tr(ρ PᴴP) ≥ 0`. -/
theorem re_trace_mul_conjTranspose_mul_self_nonneg {n : ℕ}
    (ρ P : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) :
    0 ≤ (ρ * (Pᴴ * P)).trace.re := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.mp (hρ.mul_mul_conjTranspose_same P).trace_nonneg).1

/-- **Tsirelson's bound**: every quantum CHSH strategy has `S ≤ 2√2`.
    The proof is the sum-of-squares certificate
    `2√2·1 - C = (P² + Q²)/(2√2)` with `P = √2 (A₀⊗1) - 1⊗(B₀+B₁)` and
    `Q = √2 (A₁⊗1) - 1⊗(B₀-B₁)` Hermitian, so `Re tr(ρ (2√2·1 - C)) ≥ 0`.

    **Reference**: B.S. Tsirelson, "Quantum generalizations of Bell's
    inequality", Lett. Math. Phys. 4 (1980), 93-100. -/
theorem tsirelson_bound (strat : CHSHStrategy) (hq : strat.IsQuantum) :
    chshValue strat ≤ 2 * Real.sqrt 2 := by
  set X : Fin 2 → Matrix (Fin (strat.dA * strat.dB)) (Fin (strat.dA * strat.dB)) ℂ :=
    fun x => strat.aliceObs x ⊗ₖ (1 : Matrix (Fin strat.dB) (Fin strat.dB) ℂ) with hX
  set Y : Fin 2 → Matrix (Fin (strat.dA * strat.dB)) (Fin (strat.dA * strat.dB)) ℂ :=
    fun y => (1 : Matrix (Fin strat.dA) (Fin strat.dA) ℂ) ⊗ₖ strat.bobObs y with hY
  have hXY : ∀ x y, strat.aliceObs x ⊗ₖ strat.bobObs y = X x * Y y := fun x y => by
    simp only [hX, hY, kronecker_mul_kronecker, Matrix.mul_one, Matrix.one_mul]
  have hYX : ∀ x y, Y y * X x = X x * Y y := fun x y => by
    simp only [hX, hY, kronecker_mul_kronecker, Matrix.mul_one, Matrix.one_mul]
  have hXX : ∀ x, X x * X x = 1 := fun x => by
    simp only [hX, kronecker_mul_kronecker, hq.alice_sq, Matrix.mul_one, kronecker_one_one]
  have hYY : ∀ y, Y y * Y y = 1 := fun y => by
    simp only [hY, kronecker_mul_kronecker, hq.bob_sq, Matrix.mul_one, kronecker_one_one]
  have hXh : ∀ x, (X x)ᴴ = X x := fun x => by
    simp only [hX, conjTranspose_kronecker, (hq.alice_hermitian x).eq, Matrix.conjTranspose_one]
  have hYh : ∀ y, (Y y)ᴴ = Y y := fun y => by
    simp only [hY, conjTranspose_kronecker, (hq.bob_hermitian y).eq, Matrix.conjTranspose_one]
  set r : ℂ := (Real.sqrt 2 : ℂ) with hr_def
  have hr : r * r = 2 := by
    rw [hr_def, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hrs : star r = r := by rw [hr_def]; exact Complex.conj_ofReal _
  set C := X 0 * Y 0 + X 0 * Y 1 + X 1 * Y 0 - X 1 * Y 1 with hC
  set P := r • X 0 - (Y 0 + Y 1) with hP
  set Q := r • X 1 - (Y 0 - Y 1) with hQ
  have hPh : Pᴴ = P := by
    simp only [hP, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, hrs, hXh, hYh]
  have hQh : Qᴴ = Q := by
    simp only [hQ, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hrs, hXh, hYh]
  have hsos : P * P + Q * Q = (8 : ℂ) • (1 : Matrix _ _ ℂ) - (2 * r) • C :=
    chsh_sos_identity (X 0) (X 1) (Y 0) (Y 1) r hr (hXX 0) (hXX 1) (hYY 0) (hYY 1)
      (hYX 0 0) (hYX 0 1) (hYX 1 0) (hYX 1 1)
  have hS : chshValue strat = (strat.state * C).trace.re := by
    simp only [chshValue, hXY, hC, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add,
      Matrix.trace_sub, Complex.add_re, Complex.sub_re]
  have hnn : 0 ≤ (strat.state * (P * P + Q * Q)).trace.re := by
    have h1 := re_trace_mul_conjTranspose_mul_self_nonneg strat.state P hq.state_posSemidef
    have h2 := re_trace_mul_conjTranspose_mul_self_nonneg strat.state Q hq.state_posSemidef
    rw [hPh] at h1
    rw [hQh] at h2
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    exact add_nonneg h1 h2
  rw [hsos, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, hq.trace_state, smul_eq_mul,
    smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.mul_re, hr_def] at hnn
  simp only [Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hnn
  rw [hS]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : 0 < Real.sqrt 2 := by positivity
  nlinarith

/-- The optimal quantum CHSH strategy achieves exactly S = 2*sqrt(2). -/
def optimalCHSH : CHSHStrategy where
  dA := 2
  dB := 2
  state := bellPhiPlus
  aliceObs := fun x => match x with
    | ⟨0, _⟩ => pauliZ     -- Z basis
    | ⟨1, _⟩ => pauliX     -- X basis
  bobObs := fun y => match y with
    | ⟨0, _⟩ =>  -- (Z + X) / sqrt(2) basis
      let s : ℂ := ↑(1 / Real.sqrt 2)
      s • (pauliZ + pauliX)
    | ⟨1, _⟩ =>  -- (Z - X) / sqrt(2) basis
      let s : ℂ := ↑(1 / Real.sqrt 2)
      s • (pauliZ - pauliX)

-- Compute the four correlator values for the optimal CHSH strategy.
-- Each correlator is Tr(bellPhiPlus * (Ax kron By)).re
-- where Ax and By are the Alice/Bob observables.
-- The computation is:
--   <Z, (Z+X)/√2> = 1/√2,  <Z, (Z-X)/√2> = 1/√2
--   <X, (Z+X)/√2> = 1/√2,  <X, (Z-X)/√2> = -1/√2
-- So S = 1/√2 + 1/√2 + 1/√2 - (-1/√2) = 4/√2 = 2√2

-- Macro for the big simp set needed to reduce correlator computations.
local macro "chsh_simp" : tactic => `(tactic|
  simp (config := { decide := true }) only [
    bellPhiPlus, densityOf, bellPhiPlusKet, ketbra, pauliZ, pauliX,
    Matrix.trace, Matrix.diag, Matrix.mul_apply,
    TensorProduct.kronecker_apply, TensorProduct.finProdEquiv,
    finProdFinEquiv, Equiv.coe_fn_symm_mk,
    Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.sum_univ_two, Fin.sum_univ_four,
    Fin.divNat, Fin.modNat, Fin.val_mk,
    Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.ext_iff,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.head_fin_const,
    Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    starRingEnd_self_apply, Complex.conj_ofReal,
    Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.neg_re,
    Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.neg_im,
    Complex.zero_re, Complex.one_re, Complex.zero_im, Complex.one_im,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    Complex.ofReal_inv,
    mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
    neg_zero, sub_zero, zero_sub, neg_neg, sub_self, smul_eq_mul,
    ite_true, ite_false, ite_true, ite_false,
    eq_self_iff_true, reduceCtorEq,
    mul_neg, neg_mul,
    map_neg, map_zero, map_one, map_inv₀,
    Matrix.vecHead, Matrix.vecTail])

/-- `(√2)⁻¹ * (√2)⁻¹ = 2⁻¹`. -/
theorem inv_sqrt_two_mul_self : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 2⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Correlator of the optimal strategy for Alice's `Z` and Bob's `(Z + X)/√2`. -/
theorem optimalCHSH_corr_00 :
    (bellPhiPlus * TensorProduct.kronecker pauliZ
      ((↑(1 / Real.sqrt 2) : ℂ) • (pauliZ + pauliX))).trace.re = 1 / Real.sqrt 2 := by
  simp only [bellPhiPlus, densityOf, bellPhiPlusKet, ketbra, pauliZ, pauliX]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    TensorProduct.kronecker_apply, TensorProduct.finProdEquiv]
  chsh_simp
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [inv_sqrt_two_mul_self]
  ring

/-- Correlator of the optimal strategy for Alice's `Z` and Bob's `(Z - X)/√2`. -/
theorem optimalCHSH_corr_01 :
    (bellPhiPlus * TensorProduct.kronecker pauliZ
      ((↑(1 / Real.sqrt 2) : ℂ) • (pauliZ - pauliX))).trace.re = 1 / Real.sqrt 2 := by
  simp only [bellPhiPlus, densityOf, bellPhiPlusKet, ketbra, pauliZ, pauliX]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    TensorProduct.kronecker_apply, TensorProduct.finProdEquiv]
  chsh_simp
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [inv_sqrt_two_mul_self]
  ring

/-- Correlator of the optimal strategy for Alice's `X` and Bob's `(Z + X)/√2`. -/
theorem optimalCHSH_corr_10 :
    (bellPhiPlus * TensorProduct.kronecker pauliX
      ((↑(1 / Real.sqrt 2) : ℂ) • (pauliZ + pauliX))).trace.re = 1 / Real.sqrt 2 := by
  simp only [bellPhiPlus, densityOf, bellPhiPlusKet, ketbra, pauliZ, pauliX]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    TensorProduct.kronecker_apply, TensorProduct.finProdEquiv]
  chsh_simp
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [inv_sqrt_two_mul_self]
  ring

/-- Correlator of the optimal strategy for Alice's `X` and Bob's `(Z - X)/√2`. -/
theorem optimalCHSH_corr_11 :
    (bellPhiPlus * TensorProduct.kronecker pauliX
      ((↑(1 / Real.sqrt 2) : ℂ) • (pauliZ - pauliX))).trace.re = -(1 / Real.sqrt 2) := by
  simp only [bellPhiPlus, densityOf, bellPhiPlusKet, ketbra, pauliZ, pauliX]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    TensorProduct.kronecker_apply, TensorProduct.finProdEquiv]
  chsh_simp
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [inv_sqrt_two_mul_self]
  ring

/-- The optimal strategy achieves the Tsirelson bound. -/
theorem optimalCHSH_value :
    chshValue optimalCHSH = 2 * Real.sqrt 2 := by
  unfold chshValue optimalCHSH
  dsimp only
  rw [optimalCHSH_corr_00, optimalCHSH_corr_01, optimalCHSH_corr_10, optimalCHSH_corr_11]
  have h0 : 0 < Real.sqrt 2 := by positivity
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith

/-- **Quantum violation of the classical bound** (certified nonlocality):
    the optimal quantum strategy strictly exceeds the classical CHSH bound `2`.

    The proof combines the computed value `optimalCHSH_value`
    (`chshValue optimalCHSH = 2√2`) with `√2 > 1`. -/
theorem optimalCHSH_beats_classical :
    chshValue optimalCHSH > 2 := by
  rw [optimalCHSH_value]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- The size of the quantum advantage over the classical bound, computed
    exactly: `chshValue optimalCHSH - 2 = 2√2 - 2`, and this gap is strictly
    positive. -/
theorem optimalCHSH_violation_gap :
    chshValue optimalCHSH - 2 = 2 * Real.sqrt 2 - 2 ∧
    chshValue optimalCHSH - 2 > 0 := by
  refine ⟨by rw [optimalCHSH_value], ?_⟩
  have := optimalCHSH_beats_classical
  linarith

end CatCrypt.Quantum.Programs.CHSH
