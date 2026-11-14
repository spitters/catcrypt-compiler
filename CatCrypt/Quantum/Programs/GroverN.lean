/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Programs.DeutschJozsaSimonN
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Grover's search for one marked item among `N`

For a finite set of `N` items with one marked item `w`, the Grover iteration is
`G = D O_w`, with the phase oracle `O_w = 1 - 2 |w⟩⟨w|` and the diffusion
`D = 2 |s⟩⟨s| - 1` about the uniform state `|s⟩ = N^{-1/2} Σₓ |x⟩`. The plane spanned by
`|w⟩` and the unit vector `|r⟩ ∝ Σ_{x ≠ w} |x⟩` is invariant: with `sin θ = 1/√N`,
`|s⟩ = sin θ |w⟩ + cos θ |r⟩`, and `G` rotates the plane by `2θ`. So after `k` iterations
the state is `sin((2k+1)θ) |w⟩ + cos((2k+1)θ) |r⟩`, and the marked item is measured with
probability `sin²((2k+1)θ)`. With `k = ⌊π/(4θ)⌋` the angle `(2k+1)θ` lies within `θ` of
`π/2`, so the success probability is at least `cos² θ = 1 - 1/N`.

On `n` qubits (`N = 2ⁿ`, items `Bits n`) the uniform state is `H_n |0…0⟩` and the diffusion
is `H_n (2 |0⟩⟨0| - 1) H_n`, the circuit of the algorithm.

## Main definitions

* `markedOracle w`, `diffusion`, `groverIter w` — the oracle, the diffusion and the iteration.
* `uniform` — the uniform state; `angle` — `θ = arcsin (1/√N)`.
* `perp w` — the unit vector of the invariant plane orthogonal to `|w⟩`.

## Main results

* `groverIter_pow_mulVec_uniform` — after `k` iterations the state is
  `sin((2k+1)θ) |w⟩ + cos((2k+1)θ) |r⟩`.
* `grover_success_prob` — the marked item is measured with probability `sin²((2k+1)θ)`.
* `grover_success_prob_optimal` — with `k = ⌊π/(4θ)⌋` the success probability is at least
  `1 - 1/N`.
* `uniform_eq_hadamardN`, `diffusion_eq_hadamardN` — on `n` qubits the uniform state and the
  diffusion are given by the `n`-qubit Hadamard transform.

## References

* Grover, *A fast quantum mechanical algorithm for database search*, STOC 1996.
* Nielsen, Chuang, *Quantum Computation and Quantum Information*, Section 6.1.
-/

@[expose] public section

set_option autoImplicit false

open Matrix

noncomputable section

namespace CatCrypt.Quantum.Programs.GroverN

open DeutschJozsaSimonN (basisKet)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The phase oracle of the marked item `w`: `-1` on `|w⟩`, `1` elsewhere. -/
def markedOracle (w : ι) : Matrix ι ι ℂ := Matrix.diagonal fun i => if i = w then -1 else 1

variable (ι) in
/-- The diffusion `2 |s⟩⟨s| - 1` about the uniform state, with entries `2/N - δᵢⱼ`. -/
def diffusion : Matrix ι ι ℂ :=
  Matrix.of fun i j => 2 / (Fintype.card ι : ℂ) - if i = j then 1 else 0

/-- One Grover iteration: the oracle, then the diffusion. -/
def groverIter (w : ι) : Matrix ι ι ℂ := diffusion ι * markedOracle w

variable (ι) in
/-- The uniform state `N^{-1/2} Σₓ |x⟩`. -/
def uniform : ι → ℂ := fun _ => (((Real.sqrt (Fintype.card ι))⁻¹ : ℝ) : ℂ)

variable (ι) in
/-- The rotation angle `θ = arcsin (1/√N)`. -/
def angle : ℝ := Real.arcsin (Real.sqrt (Fintype.card ι))⁻¹

/-- The unit vector `(N-1)^{-1/2} Σ_{x ≠ w} |x⟩`, orthogonal to `|w⟩`. -/
def perp (w : ι) : ι → ℂ :=
  fun i => if i = w then 0 else (((Real.sqrt ((Fintype.card ι : ℝ) - 1))⁻¹ : ℝ) : ℂ)

/-- The state `a |w⟩ + b |r⟩` of the invariant plane. -/
def planeVec (w : ι) (a b : ℝ) : ι → ℂ := fun i => if i = w then (a : ℂ) else b * perp w i

/-! ## The angle -/

omit [DecidableEq ι] in
theorem one_le_card (w : ι) : (1 : ℝ) ≤ Fintype.card ι := by
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨w⟩

omit [DecidableEq ι] in
theorem one_le_sqrt_card (w : ι) : (1 : ℝ) ≤ Real.sqrt (Fintype.card ι) :=
  Real.one_le_sqrt.mpr (one_le_card w)

omit [DecidableEq ι] in
theorem sin_angle (w : ι) : Real.sin (angle ι) = (Real.sqrt (Fintype.card ι))⁻¹ := by
  have h0 : (0 : ℝ) ≤ (Real.sqrt (Fintype.card ι))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  exact Real.sin_arcsin (by linarith) (inv_le_one_of_one_le₀ (one_le_sqrt_card w))

omit [DecidableEq ι] in
theorem cos_angle (w : ι) :
    Real.cos (angle ι) = Real.sqrt ((Fintype.card ι : ℝ) - 1) / Real.sqrt (Fintype.card ι) := by
  have hN := one_le_card w
  rw [angle, Real.cos_arcsin, inv_pow, Real.sq_sqrt (by linarith), ← Real.sqrt_div' _ (by linarith)]
  congr 1
  field_simp

omit [DecidableEq ι] in
theorem angle_pos (w : ι) : 0 < angle ι :=
  Real.arcsin_pos.mpr (inv_pos.mpr (by linarith [one_le_sqrt_card w]))

omit [DecidableEq ι] in
theorem angle_le_pi_div_two : angle ι ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _

/-! ## The invariant plane -/

omit [DecidableEq ι] in
theorem two_le_card_of_ne {w i : ι} (hi : i ≠ w) : (2 : ℝ) ≤ Fintype.card ι := by
  have : 1 < Fintype.card ι := Fintype.one_lt_card_iff.mpr ⟨i, w, hi⟩
  exact_mod_cast this

/-- `|s⟩ = sin θ |w⟩ + cos θ |r⟩`. -/
theorem uniform_eq_planeVec (w : ι) :
    uniform ι = planeVec w (Real.sin (angle ι)) (Real.cos (angle ι)) := by
  funext i
  by_cases hi : i = w
  · simp [uniform, planeVec, hi, sin_angle w]
  · have h2 := two_le_card_of_ne hi
    have hM : 0 < Real.sqrt ((Fintype.card ι : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
    have hr : Real.cos (angle ι) * (Real.sqrt ((Fintype.card ι : ℝ) - 1))⁻¹
        = (Real.sqrt (Fintype.card ι))⁻¹ := by
      rw [cos_angle w]
      field_simp
    simp only [uniform, planeVec, perp, hi, ite_false]
    exact_mod_cast hr.symm

/-- The oracle flips the sign of the `|w⟩` component. -/
theorem markedOracle_mulVec_planeVec (w : ι) (a b : ℝ) :
    markedOracle w *ᵥ planeVec w a b = planeVec w (-a) b := by
  funext i
  by_cases hi : i = w <;> simp [markedOracle, planeVec, perp, hi, mulVec_diagonal]

theorem diffusion_mulVec_apply (v : ι → ℂ) (i : ι) :
    (diffusion ι *ᵥ v) i = 2 / (Fintype.card ι : ℂ) * ∑ j, v j - v i := by
  simp [diffusion, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]

theorem sum_planeVec (w : ι) (a b : ℝ) :
    ∑ j, planeVec w a b j = (a : ℂ) + b * (Real.sqrt ((Fintype.card ι : ℝ) - 1) : ℝ) := by
  have hc : ∀ i ∈ ({w}ᶜ : Finset ι), planeVec w a b i
      = (b : ℂ) * (((Real.sqrt ((Fintype.card ι : ℝ) - 1))⁻¹ : ℝ) : ℂ) := by
    intro i hi
    rw [Finset.mem_compl, Finset.mem_singleton] at hi
    simp [planeVec, perp, hi]
  have hN : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨w⟩
  have hr : ((Fintype.card ι : ℝ) - 1) * (Real.sqrt ((Fintype.card ι : ℝ) - 1))⁻¹
      = Real.sqrt ((Fintype.card ι : ℝ) - 1) := by
    rw [← div_eq_mul_inv, Real.div_sqrt]
  rw [Fintype.sum_eq_add_sum_compl w, Finset.sum_congr rfl hc, Finset.sum_const,
    Finset.card_compl, Finset.card_singleton, nsmul_eq_mul, Nat.cast_sub hN]
  have hrC : ((Fintype.card ι : ℂ) - 1) * (((Real.sqrt ((Fintype.card ι : ℝ) - 1))⁻¹ : ℝ) : ℂ)
      = ((Real.sqrt ((Fintype.card ι : ℝ) - 1) : ℝ) : ℂ) := by exact_mod_cast hr
  simp only [planeVec, ite_true, Nat.cast_one]
  linear_combination (b : ℂ) * hrC

/-- **`G` rotates the plane by `2θ`.** -/
theorem groverIter_mulVec_planeVec (w : ι) (φ : ℝ) :
    groverIter w *ᵥ planeVec w (Real.sin φ) (Real.cos φ)
      = planeVec w (Real.sin (φ + 2 * angle ι)) (Real.cos (φ + 2 * angle ι)) := by
  funext i
  have hN := one_le_card w
  have hsN : 0 < Real.sqrt (Fintype.card ι) := by linarith [one_le_sqrt_card w]
  have hsN2 : Real.sqrt (Fintype.card ι) ^ 2 = Fintype.card ι := Real.sq_sqrt (by linarith)
  have hsM2 : Real.sqrt ((Fintype.card ι : ℝ) - 1) ^ 2 = (Fintype.card ι : ℝ) - 1 :=
    Real.sq_sqrt (by linarith)
  rw [groverIter, ← mulVec_mulVec, markedOracle_mulVec_planeVec, diffusion_mulVec_apply, sum_planeVec,
    Real.sin_add, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul, sin_angle w, cos_angle w]
  have hsNC : ((Real.sqrt (Fintype.card ι) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsN.ne'
  have hsN2C : ((Real.sqrt (Fintype.card ι) : ℝ) : ℂ) ^ 2 = Fintype.card ι := by exact_mod_cast hsN2
  have hsM2C : ((Real.sqrt ((Fintype.card ι : ℝ) - 1) : ℝ) : ℂ) ^ 2 = (Fintype.card ι : ℂ) - 1 := by
    exact_mod_cast hsM2
  have hNC : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (Fintype.card ι : ℝ) ≠ 0)
  by_cases hi : i = w
  · simp only [planeVec, hi, ite_true]
    push_cast
    field_simp
    rw [hsN2C, hsM2C]; ring
  · have h2 := two_le_card_of_ne hi
    have hsM : 0 < Real.sqrt ((Fintype.card ι : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
    have hsMC : ((Real.sqrt ((Fintype.card ι : ℝ) - 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsM.ne'
    simp only [planeVec, perp, hi, ite_false]
    push_cast
    field_simp
    rw [hsN2C]; ring

/-- **The state after `k` iterations** is `sin((2k+1)θ) |w⟩ + cos((2k+1)θ) |r⟩`. -/
theorem groverIter_pow_mulVec_uniform (w : ι) (k : ℕ) :
    (groverIter w ^ k) *ᵥ uniform ι
      = planeVec w (Real.sin ((2 * k + 1) * angle ι)) (Real.cos ((2 * k + 1) * angle ι)) := by
  induction k with
  | zero =>
    simp only [pow_zero, one_mulVec, Nat.cast_zero, mul_zero, zero_add, one_mul]
    exact uniform_eq_planeVec w
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, groverIter_mulVec_planeVec]
    congr 2 <;> push_cast <;> ring

/-- **Success probability.** After `k` iterations the marked item is measured with
probability `sin²((2k+1)θ)`. -/
theorem grover_success_prob (w : ι) (k : ℕ) :
    ‖((groverIter w ^ k) *ᵥ uniform ι) w‖ ^ 2 = Real.sin ((2 * k + 1) * angle ι) ^ 2 := by
  rw [groverIter_pow_mulVec_uniform]
  simp only [planeVec, ite_true, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Optimal number of iterations.** With `k = ⌊π/(4θ)⌋` the success probability is at least
`1 - 1/N`. -/
theorem grover_success_prob_optimal (w : ι) :
    1 - 1 / (Fintype.card ι : ℝ)
      ≤ ‖((groverIter w ^ ⌊Real.pi / (4 * angle ι)⌋₊) *ᵥ uniform ι) w‖ ^ 2 := by
  rw [grover_success_prob]
  have hθ := angle_pos w
  have hθ2 : angle ι ≤ Real.pi / 2 := angle_le_pi_div_two
  have h4 : 0 < 4 * angle ι := by linarith
  have hk1 : (⌊Real.pi / (4 * angle ι)⌋₊ : ℝ) ≤ Real.pi / (4 * angle ι) :=
    Nat.floor_le (div_nonneg Real.pi_pos.le h4.le)
  have hk2 : Real.pi / (4 * angle ι) < ⌊Real.pi / (4 * angle ι)⌋₊ + 1 := Nat.lt_floor_add_one _
  have a1 := (le_div_iff₀ h4).mp hk1
  have a2 := (div_lt_iff₀ h4).mp hk2
  have hb : |(2 * (⌊Real.pi / (4 * angle ι)⌋₊ : ℝ) + 1) * angle ι - Real.pi / 2| ≤ angle ι := by
    rw [abs_le]; constructor <;> nlinarith
  have hcos : Real.cos (angle ι)
      ≤ Real.cos ((2 * (⌊Real.pi / (4 * angle ι)⌋₊ : ℝ) + 1) * angle ι - Real.pi / 2) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hb
    rwa [Real.cos_abs] at h
  have hc0 : 0 ≤ Real.cos (angle ι) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ2⟩
  have hcos2 : Real.cos (angle ι) ^ 2 = 1 - 1 / (Fintype.card ι : ℝ) := by
    rw [Real.cos_sq', sin_angle w, inv_pow, Real.sq_sqrt (by linarith [one_le_card w])]
    ring
  rw [← Real.cos_sub_pi_div_two, ← hcos2]
  exact pow_le_pow_left₀ hc0 hcos 2

/-! ## On `n` qubits -/

open DeutschJozsaSimonN (Bits hadamardN hadamardN_apply hadamardN_mul_self sqrt2_pow_sq sgn)

theorem card_bits (n : ℕ) : Fintype.card (Bits n) = 2 ^ n := by
  simp [Bits]

theorem sqrt_two_pow (n : ℕ) : Real.sqrt (2 ^ n) = Real.sqrt 2 ^ n := by
  rw [show (2 : ℝ) ^ n = (Real.sqrt 2 ^ n) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]]
  exact Real.sqrt_sq (by positivity)

theorem hadamardN_apply_zero_left {n : ℕ} (y : Bits n) :
    hadamardN n 0 y = 1 / (Real.sqrt 2 : ℂ) ^ n := by
  simp [hadamardN_apply, sgn]

theorem hadamardN_apply_zero_right {n : ℕ} (x : Bits n) :
    hadamardN n x 0 = 1 / (Real.sqrt 2 : ℂ) ^ n := by
  simp [hadamardN_apply, sgn]

/-- On `n` qubits the uniform state is `H_n |0…0⟩`. -/
theorem uniform_eq_hadamardN (n : ℕ) : uniform (Bits n) = hadamardN n *ᵥ basisKet 0 := by
  funext x
  simp only [uniform, mulVec, dotProduct, basisKet, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, hadamardN_apply_zero_right, card_bits]
  rw [Nat.cast_pow, Nat.cast_ofNat, sqrt_two_pow]
  push_cast
  rw [one_div]

/-- On `n` qubits the diffusion is `H_n (2 |0⟩⟨0| - 1) H_n`. -/
theorem diffusion_eq_hadamardN (n : ℕ) :
    diffusion (Bits n)
      = hadamardN n * Matrix.diagonal (fun x => if x = 0 then 1 else -1) * hadamardN n := by
  ext i j
  have hH := congrFun (congrFun (hadamardN_mul_self (n := n)) i) j
  simp only [Matrix.mul_apply, Matrix.one_apply] at hH
  have hd : ∀ k : Bits n, hadamardN n i k * (if k = 0 then 1 else -1) * hadamardN n k j
      = 2 * (if k = 0 then hadamardN n i k * hadamardN n k j else 0)
        - hadamardN n i k * hadamardN n k j := by
    intro k; split_ifs <;> ring
  rw [Matrix.mul_apply]
  simp only [diffusion, Matrix.of_apply, Matrix.mul_diagonal, hd,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hH,
    hadamardN_apply_zero_left, hadamardN_apply_zero_right, card_bits]
  rw [one_div_mul_one_div, sqrt2_pow_sq]
  push_cast
  ring

end CatCrypt.Quantum.Programs.GroverN
