/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Programs.CHSH

@[expose] public section

set_option autoImplicit false

/-!
# Bell's theorem: the CHSH inequality and its quantum violation

A local hidden-variable model of the CHSH experiment has a hidden variable `λ` drawn from
a finite distribution `μ`; given `λ`, Alice's answer to setting `x` and Bob's answer to
setting `y` are `±1`-valued random variables, independent given `λ`, so only their
conditional expectations `A x λ, B y λ ∈ [-1, 1]` enter the correlators
`E(x, y) = ∑ λ, μ λ · A x λ · B y λ`. Deterministic `±1` answers are the case
`A x λ, B y λ ∈ {-1, 1}`.

## Main definitions

* `LHVModel Λ` — a local hidden-variable model over a finite hidden-variable type `Λ`.
* `LHVModel.correlator`, `LHVModel.chshValue` — the correlators and the CHSH value
  `E(0,0) + E(0,1) + E(1,0) - E(1,1)`.
* `LHVModel.ofDeterministic` — the model of deterministic `±1` answers.

## Main results

* `LHVModel.chshValue_le_two` — Bell's inequality (CHSH form): every local
  hidden-variable model has CHSH value at most `2`.
* `LHVModel.abs_chshValue_le_two` — `|S| ≤ 2`.
* `LHVModel.chshValue_lt_optimalCHSH` — the separation: the quantum strategy
  `optimalCHSH` (a Bell state with Pauli observables) has CHSH value `2√2`, strictly
  above the value of every local hidden-variable model.
* `LHVModel.chshValue_add_le_optimalCHSH` — the gap: `S + (2√2 - 2) ≤ 2√2`.

## References

* Bell, *On the Einstein Podolsky Rosen paradox*, Physics 1 (1964)
* Clauser, Horne, Shimony, Holt, *Proposed experiment to test local hidden-variable
  theories*, Phys. Rev. Lett. 23 (1969)
-/

open CatCrypt.Quantum.Programs.CHSH

namespace CatCrypt.Quantum.Programs.BellCHSH

/-- A local hidden-variable model of the CHSH experiment: a probability distribution `μ`
on a finite type `Λ` of hidden variables, and for each hidden variable the conditional
expectations of Alice's and Bob's `±1` answers to each of the two settings. -/
structure LHVModel (Λ : Type) [Fintype Λ] where
  /-- The distribution of the hidden variable. -/
  μ : Λ → ℝ
  μ_nonneg : ∀ l, 0 ≤ μ l
  μ_sum : ∑ l, μ l = 1
  /-- Alice's expected answer to setting `x` given the hidden variable. -/
  A : Fin 2 → Λ → ℝ
  /-- Bob's expected answer to setting `y` given the hidden variable. -/
  B : Fin 2 → Λ → ℝ
  abs_A_le : ∀ x l, |A x l| ≤ 1
  abs_B_le : ∀ y l, |B y l| ≤ 1

namespace LHVModel

variable {Λ : Type} [Fintype Λ]

/-- The correlator `E(x, y) = ∑ λ, μ λ · A x λ · B y λ`. -/
def correlator (M : LHVModel Λ) (x y : Fin 2) : ℝ :=
  ∑ l, M.μ l * (M.A x l * M.B y l)

/-- The CHSH value `E(0,0) + E(0,1) + E(1,0) - E(1,1)`. -/
def chshValue (M : LHVModel Λ) : ℝ :=
  M.correlator 0 0 + M.correlator 0 1 + M.correlator 1 0 - M.correlator 1 1

/-- The CHSH value as one expectation over the hidden variable. -/
theorem chshValue_eq_sum (M : LHVModel Λ) :
    M.chshValue = ∑ l, M.μ l * (M.A 0 l * M.B 0 l + M.A 0 l * M.B 1 l +
      M.A 1 l * M.B 0 l - M.A 1 l * M.B 1 l) := by
  simp only [chshValue, correlator, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Bell's inequality (CHSH form).** Every local hidden-variable model has CHSH value
at most `2`. -/
theorem chshValue_le_two (M : LHVModel Λ) : M.chshValue ≤ 2 := by
  rw [chshValue_eq_sum]
  calc ∑ l, M.μ l * (M.A 0 l * M.B 0 l + M.A 0 l * M.B 1 l +
        M.A 1 l * M.B 0 l - M.A 1 l * M.B 1 l)
      ≤ ∑ l, M.μ l * 2 := by
        refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (M.μ_nonneg l)
        exact chsh_algebraic_bound _ _ _ _ (M.abs_A_le 0 l) (M.abs_A_le 1 l)
          (M.abs_B_le 0 l) (M.abs_B_le 1 l)
    _ = 2 := by rw [← Finset.sum_mul, M.μ_sum, one_mul]

/-- Swapping the sign of Alice's answers negates the CHSH value. -/
def negA (M : LHVModel Λ) : LHVModel Λ where
  μ := M.μ
  μ_nonneg := M.μ_nonneg
  μ_sum := M.μ_sum
  A x l := -M.A x l
  B := M.B
  abs_A_le x l := by rw [abs_neg]; exact M.abs_A_le x l
  abs_B_le := M.abs_B_le

theorem chshValue_negA (M : LHVModel Λ) : M.negA.chshValue = -M.chshValue := by
  simp only [chshValue, correlator, negA, neg_mul, mul_neg, Finset.sum_neg_distrib]
  ring

/-- **Bell's inequality, two-sided**: `|S| ≤ 2` for every local hidden-variable model. -/
theorem abs_chshValue_le_two (M : LHVModel Λ) : |M.chshValue| ≤ 2 := by
  refine abs_le.mpr ⟨?_, M.chshValue_le_two⟩
  have := M.negA.chshValue_le_two
  rw [chshValue_negA] at this
  linarith

/-- The local hidden-variable model of deterministic answers: `a x l, b y l ∈ {-1, 1}`. -/
def ofDeterministic (μ : Λ → ℝ) (hμ : ∀ l, 0 ≤ μ l) (hsum : ∑ l, μ l = 1)
    (a b : Fin 2 → Λ → ℝ) (ha : ∀ x l, a x l = 1 ∨ a x l = -1)
    (hb : ∀ y l, b y l = 1 ∨ b y l = -1) : LHVModel Λ where
  μ := μ
  μ_nonneg := hμ
  μ_sum := hsum
  A := a
  B := b
  abs_A_le x l := by rcases ha x l with h | h <;> simp [h]
  abs_B_le y l := by rcases hb y l with h | h <;> simp [h]

/-- **Bell's theorem, separation.** The CHSH value of every local hidden-variable model
is strictly below the value `2√2` of the quantum strategy `optimalCHSH`. -/
theorem chshValue_lt_optimalCHSH (M : LHVModel Λ) :
    M.chshValue < CHSH.chshValue optimalCHSH :=
  lt_of_le_of_lt M.chshValue_le_two optimalCHSH_beats_classical

/-- The quantum value exceeds every local hidden-variable value by at least
`2√2 - 2 > 0`. -/
theorem chshValue_add_le_optimalCHSH (M : LHVModel Λ) :
    M.chshValue + (2 * Real.sqrt 2 - 2) ≤ CHSH.chshValue optimalCHSH ∧
      0 < 2 * Real.sqrt 2 - 2 := by
  rw [optimalCHSH_value]
  refine ⟨by linarith [M.chshValue_le_two], ?_⟩
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

end LHVModel

end CatCrypt.Quantum.Programs.BellCHSH
