/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Programs.CHSH
public import CatCryptCore.ForMathlib.Matrix.TraceInequalities

/-!
# The tilted CHSH inequality and the trade-off `⟨A₀⟩² + (S/2)² ≤ 2`

The tilted CHSH operator is `α X₀ + C` with `C = X₀Y₀ + X₀Y₁ + X₁Y₀ − X₁Y₁`. For involutions
`Xₓ`, `Y_y` with each `Xₓ` commuting with each `Y_y`, and `β² = 8 + 2α²`, the operator
`β − α X₀ − C` is a sum of two squares (Bamps–Pironio, eq. (28)). Taking expectations gives
the tilted bound `α⟨X₀⟩ + ⟨C⟩ ≤ √(8 + 2α²)` in every dimension, and optimising over `α` gives
the trade-off between the bias of Alice's key observable and the CHSH value.

## Main results

* `chshOp`, `chshExpect` — the CHSH operator and its expectation in an operator `ρ`
* `tilted_chsh_sos_identity` — `2β(β − αX₀ − C) = P₁² + P₂²` in any real algebra
* `tilted_chsh_le` — `α⟨X₀⟩ + ⟨C⟩ ≤ √(8 + 2α²)·tr(ρK)` for a positive `K` commuting with the
  observables
* `sq_add_sq_le_two_of_forall_mul_add_le` — the scalar step from the tilted family
* `CHSHStrategy.sq_add_sq_le_two` — `⟨A₀⟩² + (S/2)² ≤ 2` for every quantum CHSH strategy
* `diGuess` — the device-independent guessing bound `1/2 + 1/2 √(2 − S²/4)`

## References

* C. Bamps, S. Pironio — *Sum-of-squares decompositions for a family of
  Clauser-Horne-Shimony-Holt-like inequalities and their application to self-testing*,
  PRA 91, 052111, 2015, eq. (28)
* S. Pironio et al. — *Random numbers certified by Bell's theorem*, Nature 464, 2010
* A. Acín, S. Massar, S. Pironio — *Randomness versus nonlocality and entanglement*,
  PRL 108, 100402, 2012
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder
open Matrix
open CatCrypt.Quantum CatCrypt.Quantum.TensorProduct

noncomputable section

namespace CatCrypt.Quantum.Programs.CHSH

/-- The CHSH operator `X₀Y₀ + X₀Y₁ + X₁Y₀ − X₁Y₁`. -/
def chshOp {R : Type*} [Ring R] (X Y : Fin 2 → R) : R :=
  X 0 * Y 0 + X 0 * Y 1 + X 1 * Y 0 - X 1 * Y 1

/-- The CHSH value `Re tr(ρ C)` of an operator `ρ` for observables `X`, `Y` on one space. -/
def chshExpect {n : Type*} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ)
    (X Y : Fin 2 → Matrix n n ℂ) : ℝ :=
  (ρ * chshOp X Y).trace.re

/-- Bamps–Pironio sum of squares (their eq. (28)) for the tilted CHSH operator, in any ring
with involutions `Xₓ`, `Y_y` such that each `Xₓ` commutes with each `Y_y`, and `β² = 8 + 2α²`. -/
theorem tilted_chsh_sos_identity {R : Type*} [Ring R] [Algebra ℝ R] (X Y : Fin 2 → R)
    (α β : ℝ) (hβ : β * β = 8 + 2 * α ^ 2) (hX : ∀ x, X x * X x = 1) (hY : ∀ y, Y y * Y y = 1)
    (hXY : ∀ x y, Y y * X x = X x * Y y) :
    (2 * β) • (β • (1 : R) - (α • X 0 + chshOp X Y)) =
      (2 • X 0 - (β / 2) • (Y 0 + Y 1) +
          (α / 2) • (X 0 * (Y 0 + Y 1) - X 1 * (Y 0 - Y 1))) ^ 2 +
        (2 • X 1 - (β / 2) • (Y 0 - Y 1) +
          (α / 2) • (X 0 * (Y 0 - Y 1) - X 1 * (Y 0 + Y 1))) ^ 2 := by
  have hXX : ∀ x w, X x * (X x * w) = w := fun x w => by rw [← mul_assoc, hX, one_mul]
  have hYX : ∀ x y w, Y y * (X x * w) = X x * (Y y * w) := fun x y w => by
    rw [← mul_assoc, hXY, mul_assoc]
  simp only [chshOp, sq, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat, mul_add, add_mul, mul_sub,
    sub_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, mul_assoc, hX, hY,
    hXY, hXX, hYX, mul_one]
  match_scalars <;> first | ring1 | linear_combination hβ

/-- For a positive semidefinite `ρ`, a positive semidefinite `K` and a Hermitian `P` commuting
with `K`, `Re tr(ρ K P²) ≥ 0`. -/
theorem re_trace_mul_mul_self_nonneg_of_commute {n : Type*} [Fintype n]
    {ρ K P : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hK : K.PosSemidef) (hPh : Pᴴ = P)
    (hKP : K * P = P * K) :
    0 ≤ (ρ * K * (P * P)).trace.re := by
  have hcyc : (ρ * K * (P * P)).trace = (P * ρ * Pᴴ * K).trace := by
    rw [hPh, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc, hKP]
  rw [hcyc]
  exact (hρ.mul_mul_conjTranspose_same P).re_trace_mul_nonneg hK

/-- **Tilted CHSH bound** in commuting-operator form, weighted by a positive `K` commuting with
the observables: `α ⟨X₀⟩ + ⟨C⟩ ≤ √(8 + 2α²) · tr(ρK)` for every real `α`. -/
theorem tilted_chsh_le {n : Type*} [Fintype n] [DecidableEq n] {ρ K : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hK : K.PosSemidef) {X Y : Fin 2 → Matrix n n ℂ}
    (hXh : ∀ x, (X x).IsHermitian) (hYh : ∀ y, (Y y).IsHermitian)
    (hX : ∀ x, X x * X x = 1) (hY : ∀ y, Y y * Y y = 1)
    (hXY : ∀ x y, Y y * X x = X x * Y y)
    (hKX : ∀ x, K * X x = X x * K) (hKY : ∀ y, K * Y y = Y y * K) (α : ℝ) :
    α * (ρ * K * X 0).trace.re + chshExpect (ρ * K) X Y
      ≤ Real.sqrt (8 + 2 * α ^ 2) * (ρ * K).trace.re := by
  set β := Real.sqrt (8 + 2 * α ^ 2) with hβdef
  have hβ : β * β = 8 + 2 * α ^ 2 := Real.mul_self_sqrt (by positivity)
  have hβpos : 0 < β := Real.sqrt_pos.mpr (by positivity)
  have hsos := tilted_chsh_sos_identity X Y α β hβ hX hY hXY
  set P₁ : Matrix n n ℂ := 2 • X 0 - (β / 2) • (Y 0 + Y 1) +
    (α / 2) • (X 0 * (Y 0 + Y 1) - X 1 * (Y 0 - Y 1)) with hP₁
  set P₂ : Matrix n n ℂ := 2 • X 1 - (β / 2) • (Y 0 - Y 1) +
    (α / 2) • (X 0 * (Y 0 - Y 1) - X 1 * (Y 0 + Y 1)) with hP₂
  have hXe : ∀ x, (X x)ᴴ = X x := fun x => (hXh x).eq
  have hYe : ∀ y, (Y y)ᴴ = Y y := fun y => (hYh y).eq
  have hP₁h : P₁ᴴ = P₁ := by
    simp only [hP₁, conjTranspose_add, conjTranspose_sub, conjTranspose_smul, conjTranspose_mul,
      hXe, hYe, star_trivial, mul_add, mul_sub, hXY]
  have hP₂h : P₂ᴴ = P₂ := by
    simp only [hP₂, conjTranspose_add, conjTranspose_sub, conjTranspose_smul, conjTranspose_mul,
      hXe, hYe, star_trivial, mul_add, mul_sub, hXY]
  have cX : ∀ x, Commute K (X x) := hKX
  have cY : ∀ y, Commute K (Y y) := hKY
  have hKP₁ : K * P₁ = P₁ * K :=
    Commute.eq (Commute.add_right
      (Commute.sub_right (Commute.smul_right (cX 0) (2 : ℕ))
        (Commute.smul_right (Commute.add_right (cY 0) (cY 1)) (β / 2)))
      (Commute.smul_right (Commute.sub_right
        (Commute.mul_right (cX 0) (Commute.add_right (cY 0) (cY 1)))
        (Commute.mul_right (cX 1) (Commute.sub_right (cY 0) (cY 1)))) (α / 2)))
  have hKP₂ : K * P₂ = P₂ * K :=
    Commute.eq (Commute.add_right
      (Commute.sub_right (Commute.smul_right (cX 1) (2 : ℕ))
        (Commute.smul_right (Commute.sub_right (cY 0) (cY 1)) (β / 2)))
      (Commute.smul_right (Commute.sub_right
        (Commute.mul_right (cX 0) (Commute.sub_right (cY 0) (cY 1)))
        (Commute.mul_right (cX 1) (Commute.add_right (cY 0) (cY 1)))) (α / 2)))
  have h₁ := re_trace_mul_mul_self_nonneg_of_commute hρ hK hP₁h hKP₁
  have h₂ := re_trace_mul_mul_self_nonneg_of_commute hρ hK hP₂h hKP₂
  have htr : (ρ * K * (P₁ * P₁)).trace.re + (ρ * K * (P₂ * P₂)).trace.re =
      (2 * β) * (β * (ρ * K).trace.re - (α * (ρ * K * X 0).trace.re +
        chshExpect (ρ * K) X Y)) := by
    have e := congrArg (fun M => (ρ * K * M).trace.re) hsos
    simp only [sq] at e
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at e
    rw [← e]
    simp only [chshExpect, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one,
      Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_add, Complex.smul_re, Complex.sub_re,
      Complex.add_re, smul_eq_mul]
  nlinarith

/-- `|⟨X⟩| ≤ tr(ρK)` for a Hermitian involution `X` commuting with a positive `K`
(from `1 ± X = (1 ± X)²/2`). -/
theorem abs_re_trace_mul_le_of_involutive {n : Type*} [Fintype n] [DecidableEq n]
    {ρ K X : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hK : K.PosSemidef) (hXh : X.IsHermitian)
    (hX : X * X = 1) (hKX : K * X = X * K) :
    |(ρ * K * X).trace.re| ≤ (ρ * K).trace.re := by
  have hp : 0 ≤ (ρ * K * ((1 + X) * (1 + X))).trace.re :=
    re_trace_mul_mul_self_nonneg_of_commute hρ hK (by simp [hXh.eq])
      (by simp only [mul_add, add_mul, mul_one, one_mul, hKX])
  have hm : 0 ≤ (ρ * K * ((1 - X) * (1 - X))).trace.re :=
    re_trace_mul_mul_self_nonneg_of_commute hρ hK (by simp [hXh.eq])
      (by simp only [mul_sub, sub_mul, mul_one, one_mul, hKX])
  have ep : (1 + X) * (1 + X) = (1 + X) + (1 + X) := by
    simp only [add_mul, mul_add, one_mul, mul_one, hX]
    abel
  have em : (1 - X) * (1 - X) = (1 - X) + (1 - X) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hX]
    abel
  rw [ep] at hp
  rw [em] at hm
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re] at hp hm
  rw [abs_le]
  constructor <;> linarith

/-- Scalar step: the linear family of tilted bounds forces `m² + (S/2)² ≤ 2`. -/
theorem sq_add_sq_le_two_of_forall_mul_add_le {m S : ℝ} (hS : 0 < S)
    (h : ∀ α : ℝ, α * m + S ≤ Real.sqrt (8 + 2 * α ^ 2)) :
    m ^ 2 + (S / 2) ^ 2 ≤ 2 := by
  have hα := h (4 * m / S)
  set u := 4 * m ^ 2 + S ^ 2 with hu
  have hupos : 0 < u := by positivity
  have hlhs : 4 * m / S * m + S = u / S := by
    field_simp
    ring
  have hrhs : Real.sqrt (8 + 2 * (4 * m / S) ^ 2) = Real.sqrt (8 * u) / S := by
    have e : 8 + 2 * (4 * m / S) ^ 2 = 8 * u / S ^ 2 := by
      rw [hu]
      field_simp
      ring
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hS.le]
  rw [hlhs, hrhs] at hα
  have h1 : u ≤ Real.sqrt (8 * u) := (div_le_div_iff_of_pos_right hS).mp hα
  have h2 : u ^ 2 ≤ 8 * u := by
    grind only [Real.le_sqrt']
  nlinarith

/-- **Single-state trade-off** `⟨A₀⟩² + (S/2)² ≤ 2` (Pironio et al. 2010; Acín–Massar–Pironio
2012), for every quantum CHSH strategy, in every dimension. -/
theorem CHSHStrategy.sq_add_sq_le_two (strat : CHSHStrategy) (hq : strat.IsQuantum) :
    (strat.state * (strat.aliceObs 0 ⊗ₖ (1 : Matrix (Fin strat.dB) (Fin strat.dB) ℂ))).trace.re
        ^ 2 + (chshValue strat / 2) ^ 2 ≤ 2 := by
  set X : Fin 2 → Matrix (Fin (strat.dA * strat.dB)) (Fin (strat.dA * strat.dB)) ℂ :=
    fun x => strat.aliceObs x ⊗ₖ (1 : Matrix (Fin strat.dB) (Fin strat.dB) ℂ) with hXd
  set Y : Fin 2 → Matrix (Fin (strat.dA * strat.dB)) (Fin (strat.dA * strat.dB)) ℂ :=
    fun y => (1 : Matrix (Fin strat.dA) (Fin strat.dA) ℂ) ⊗ₖ strat.bobObs y with hYd
  change (strat.state * X 0).trace.re ^ 2 + _ ≤ 2
  have hYX : ∀ x y, Y y * X x = X x * Y y := fun x y => by
    simp only [hXd, hYd, kronecker_mul_kronecker, Matrix.mul_one, Matrix.one_mul]
  have hXX : ∀ x, X x * X x = 1 := fun x => by
    simp only [hXd, kronecker_mul_kronecker, hq.alice_sq, Matrix.mul_one, kronecker_one_one]
  have hYY : ∀ y, Y y * Y y = 1 := fun y => by
    simp only [hYd, kronecker_mul_kronecker, hq.bob_sq, Matrix.mul_one, kronecker_one_one]
  have hXh : ∀ x, (X x).IsHermitian := fun x => by
    simp only [IsHermitian, hXd, conjTranspose_kronecker, (hq.alice_hermitian x).eq,
      Matrix.conjTranspose_one]
  have hYh : ∀ y, (Y y).IsHermitian := fun y => by
    simp only [IsHermitian, hYd, conjTranspose_kronecker, (hq.bob_hermitian y).eq,
      Matrix.conjTranspose_one]
  have hS : chshValue strat = chshExpect strat.state X Y := by
    simp only [chshValue, chshExpect, chshOp, hXd, hYd, kronecker_mul_kronecker, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub,
      Complex.add_re, Complex.sub_re]
  have hρ := hq.state_posSemidef
  have htr : strat.state.trace.re = 1 := by rw [hq.trace_state, Complex.one_re]
  have key : ∀ Y' : Fin 2 → Matrix (Fin (strat.dA * strat.dB)) (Fin (strat.dA * strat.dB)) ℂ,
      (∀ y, (Y' y).IsHermitian) → (∀ y, Y' y * Y' y = 1) → (∀ x y, Y' y * X x = X x * Y' y) →
      ∀ α : ℝ, α * (strat.state * X 0).trace.re + chshExpect strat.state X Y' ≤
        Real.sqrt (8 + 2 * α ^ 2) := fun Y' h₁ h₂ h₃ α => by
    have h := tilted_chsh_le hρ PosSemidef.one hXh h₁ hXX h₂ h₃ (fun x => by simp)
      (fun y => by simp) α
    simpa only [Matrix.mul_one, htr, mul_one] using h
  have hneg : chshExpect strat.state X (-Y) = -chshExpect strat.state X Y := by
    have e : chshOp X (-Y) = -chshOp X Y := by
      simp only [chshOp, Pi.neg_apply, mul_neg]
      abel
    rw [chshExpect, chshExpect, e, Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re]
  rw [hS]
  rcases lt_trichotomy (chshExpect strat.state X Y) 0 with h | h | h
  · have hb := sq_add_sq_le_two_of_forall_mul_add_le (neg_pos.mpr h) fun α => by
      have h' := key (-Y) (fun y => (hYh y).neg) (fun y => by simp only [Pi.neg_apply,
        neg_mul_neg, hYY]) (fun x y => by simp only [Pi.neg_apply, neg_mul, mul_neg, hYX]) α
      rwa [hneg] at h'
    nlinarith [hb]
  · rw [h]
    have ha := abs_re_trace_mul_le_of_involutive hρ PosSemidef.one (hXh 0) (hXX 0) (by simp)
    simp only [Matrix.mul_one, htr] at ha
    nlinarith [abs_le.mp ha]
  · exact sq_add_sq_le_two_of_forall_mul_add_le h (key Y hYh hYY hYX)

/-- The DI guessing bound `g(S) = 1/2 + 1/2 √(2 − S²/4)`. -/
def diGuess (S : ℝ) : ℝ := 1 / 2 + 1 / 2 * Real.sqrt (2 - S ^ 2 / 4)

/-- `diGuess` is antitone on `S ≥ 0`. -/
theorem diGuess_le_diGuess {S₀ S : ℝ} (h₀ : 0 ≤ S₀) (h : S₀ ≤ S) : diGuess S ≤ diGuess S₀ := by
  unfold diGuess
  gcongr

/-- A CHSH value above the classical bound gives a guessing probability below one. -/
theorem diGuess_lt_one {S : ℝ} (h : 2 < S) : diGuess S < 1 := by
  unfold diGuess
  have : Real.sqrt (2 - S ^ 2 / 4) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    nlinarith
  linarith

/-- At the Tsirelson bound the guessing probability is `1/2`. -/
theorem diGuess_two_mul_sqrt_two : diGuess (2 * Real.sqrt 2) = 1 / 2 := by
  unfold diGuess
  have : (2 * Real.sqrt 2) ^ 2 = 8 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [this]
  norm_num

end CatCrypt.Quantum.Programs.CHSH
