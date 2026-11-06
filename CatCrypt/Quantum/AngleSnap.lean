/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.ApproxEmit
public import CatCrypt.Quantum.QrunchFuse

/-!
# Angle snapping of imported statements, with an operator norm bound

An imported angle is a `PiLin` `a + b·π` whose rational part `a` is the decimal a floating
point printer wrote for a rational multiple of `π`. Angle snapping replaces an angle whose
rational part lies within the tolerance `10⁻¹²` of `j·π/2^k` (`k ≤ 4`, `j` an integer) by the
exact angle `(b + j/2^k)·π`. Whether an angle is snapped is decided on rationals, against the
rational `piLo` of `ExpIBall`; the moved distance `|j·π/2^k − a|` is bounded from above by
the rational `snapDist a j k`, computed from the enclosure `piLo < π < piLo + 10⁻²⁰`, so the
bound holds whatever the decision returns.

The matrix of a statement is Lipschitz in each of its angles in the `ℓ²` operator norm:
with constant `1/2` for the angle of `rx`, `ry`, `rz` and the first angle of `u`, and with
constant `1` for the angle of `p` and `cp` and the two phase angles of `u` and `u2`.
`snapQ` snaps every angle of a list of statements and returns the sum, over the snapped
angles, of the constant times the moved-distance bound.

## Main definitions

* `snapDist`, `snapFind`, `snapAngle` — the bound of the moved distance, the decision and
  the snapping of one angle.
* `snapGate`, `snapQ` — angle snapping of a statement and of a list, with the bound.

## Main results

* `abs_toReal_snapAngle_sub_le` — the moved distance is at most the returned bound.
* `norm_rxMatrix_sub_le`, `norm_ryMatrix_sub_le`, `norm_rzMatrix_sub_le`,
  `norm_rzGate_sub_le`, `norm_uMatrix_sub_le` — the Lipschitz bounds of the gate matrices.
* `norm_qelibListMatrix_snapQ_sub_le` — the operator norm of the difference of the matrices
  of the snapped and the input list is at most the returned bound.
* `length_snapQ`, `cxCount_snapQ` — angle snapping keeps the length and the `cx` count.
-/

@[expose] public section

set_option autoImplicit false

open Complex
open scoped Matrix.Norms.L2Operator
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.OpenQASMImport
open CatCrypt.Quantum.OpenQASMImportGates
open CatCrypt.Quantum.Qelib
open CatCrypt.Quantum.ControlledGates (ctrlMatrix proj0 proj1)
open CatCrypt.Quantum.Synthesis.IntervalArith
  (piLo piLo_lt_pi pi_lt_piLo_add norm_exp_I_sub_exp_I_le norm_embedGate1_le embed1Hom
    listMatrix_mem_unitaryGroup)
open CatCrypt.Quantum.QrunchFuse (isCx cxCount)
open CatCrypt.Quantum.QFT (listMatrix)

namespace CatCrypt.Quantum.AngleSnap

variable {n : ℕ}

/-! ## Snapping one angle -/

/-- The snapping tolerance `10⁻¹²`, in radians. -/
def snapTol : ℚ := 1 / 10 ^ 12

/-- A rational upper bound of `|j·π/2^k − a|`, from `piLo < π < piLo + 10⁻²⁰`. -/
def snapDist (a : ℚ) (j : ℤ) (k : ℕ) : ℚ :=
  |(j : ℚ) * piLo / 2 ^ k - a| + |(j : ℚ)| / 2 ^ k / 10 ^ 20

/-- The first `k ≤ 4` and the integer `j` nearest to `a·2^k/π` such that `a` lies within
`snapTol` of `j·π/2^k`, with `π` read as `piLo`. -/
def snapFind (a : ℚ) : Option (ℤ × ℕ) :=
  (List.range 5).findSome? fun k =>
    let j := round (a * 2 ^ k / piLo)
    if |(j : ℚ) * piLo / 2 ^ k - a| ≤ snapTol then some (j, k) else none

/-- Angle snapping of `a + b·π`: `(b + j/2^k)·π` when `snapFind a` returns `(j, k)`, with the
bound `snapDist a j k` of the moved distance; the angle itself with the bound `0` otherwise. -/
def snapAngle (p : PiLin) : PiLin × ℚ :=
  if p.a = 0 then (p, 0) else
    match snapFind p.a with
    | some (j, k) => (⟨0, p.b + (j : ℚ) / 2 ^ k⟩, snapDist p.a j k)
    | none => (p, 0)

/-- `|j·π/2^k − a| ≤ snapDist a j k`. -/
theorem abs_sub_le_snapDist (a : ℚ) (j : ℤ) (k : ℕ) :
    |(j : ℝ) / 2 ^ k * Real.pi - a| ≤ (snapDist a j k : ℝ) := by
  have h1 : (j : ℝ) / 2 ^ k * Real.pi - a =
      ((j : ℝ) * piLo / 2 ^ k - a) + (j : ℝ) / 2 ^ k * (Real.pi - piLo) := by ring
  have h2 : |Real.pi - piLo| ≤ 1 / 10 ^ 20 := by
    rw [abs_le]
    constructor <;> linarith [piLo_lt_pi, pi_lt_piLo_add]
  rw [h1]
  refine (abs_add_le _ _).trans ?_
  simp only [snapDist]
  push_cast
  rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)]
  have h3 : 0 ≤ |(j : ℝ)| / 2 ^ k := by positivity
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  have h5 : |(j : ℝ)| / 2 ^ k / 10 ^ 20 = |(j : ℝ)| / 2 ^ k * (1 / 10 ^ 20) := by ring
  linarith

/-- **The moved distance.** Whatever `snapFind` returns, the snapped angle is within the
returned bound of the input angle. -/
theorem abs_toReal_snapAngle_sub_le (p : PiLin) :
    |(snapAngle p).1.toReal - p.toReal| ≤ ((snapAngle p).2 : ℝ) := by
  unfold snapAngle
  split_ifs with h
  · simp
  · rcases hf : snapFind p.a with _ | ⟨j, k⟩
    · simp
    · simp only
      have := abs_sub_le_snapDist p.a j k
      have he : PiLin.toReal ⟨0, p.b + (j : ℚ) / 2 ^ k⟩ - p.toReal =
          (j : ℝ) / 2 ^ k * Real.pi - p.a := by
        simp only [PiLin.toReal]; push_cast; ring
      rw [he]
      exact this

/-! ## Lipschitz bounds of the gate matrices -/

/-- The norm of a matrix of the form `[[α, β], [−β̄, ᾱ]]` squared is `‖α‖² + ‖β‖²`. -/
theorem sq_norm_su2 (α β : ℂ) :
    ‖(!![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α] : Matrix (Fin 2) (Fin 2) ℂ)‖ ^ 2
      = ‖α‖ ^ 2 + ‖β‖ ^ 2 := by
  set M : Matrix (Fin 2) (Fin 2) ℂ := !![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α]
  have h : star M * M = ((‖α‖ ^ 2 + ‖β‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.sq_norm, Complex.normSq_eq_conj_mul_self] <;> ring
  have := CStarRing.norm_star_mul_self (x := M)
  rw [h, norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)] at this
  rw [sq, ← this]

/-- A bound of the norm of `[[α, β], [−β̄, ᾱ]]` from a bound of `‖α‖² + ‖β‖²`. -/
theorem norm_su2_le {α β : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : ‖α‖ ^ 2 + ‖β‖ ^ 2 ≤ r ^ 2) :
    ‖(!![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α] : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ r := by
  have := sq_norm_su2 α β
  nlinarith [norm_nonneg (!![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α] :
    Matrix (Fin 2) (Fin 2) ℂ)]

/-- A bound of the norm of a diagonal `2 × 2` matrix from bounds of its entries. -/
theorem norm_diagonal2_le {a b : ℂ} {r : ℝ} (hr : 0 ≤ r) (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) :
    ‖(Matrix.diagonal ![a, b] : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ r := by
  rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hr]
  intro i
  fin_cases i <;> simpa

/-- `(cos x − cos y)² + (sin x − sin y)² = ‖e^{ix} − e^{iy}‖²`. -/
theorem sq_cos_sub_add_sq_sin_sub (x y : ℝ) :
    (Real.cos x - Real.cos y) ^ 2 + (Real.sin x - Real.sin y) ^ 2 =
      ‖exp (I * x) - exp (I * y)‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, mul_comm I, mul_comm I,
    Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im]
  ring

/-- `(cos x − cos y)² + (sin x − sin y)² ≤ (x − y)²`. -/
theorem sq_cos_sub_add_sq_sin_sub_le (x y : ℝ) :
    (Real.cos x - Real.cos y) ^ 2 + (Real.sin x - Real.sin y) ^ 2 ≤ (x - y) ^ 2 := by
  rw [sq_cos_sub_add_sq_sin_sub, ← sq_abs (x - y)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_exp_I_sub_exp_I_le x y) 2

/-- `rx` is `1/2`-Lipschitz in its angle. -/
theorem norm_rxMatrix_sub_le (s t : ℝ) : ‖rxMatrix s - rxMatrix t‖ ≤ |s - t| / 2 := by
  have he : rxMatrix s - rxMatrix t =
      !![((Real.cos (s / 2) - Real.cos (t / 2) : ℝ) : ℂ),
        -I * ((Real.sin (s / 2) - Real.sin (t / 2) : ℝ) : ℂ);
        -(starRingEnd ℂ) (-I * ((Real.sin (s / 2) - Real.sin (t / 2) : ℝ) : ℂ)),
        (starRingEnd ℂ) ((Real.cos (s / 2) - Real.cos (t / 2) : ℝ) : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rxMatrix, -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.conj_ofReal] <;> ring
  rw [he]
  refine norm_su2_le (by positivity) ?_
  have := sq_cos_sub_add_sq_sin_sub_le (s / 2) (t / 2)
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, div_pow]
  rw [← sq_abs (s - t)] at *
  nlinarith [sq_abs (s - t)]

/-- `ry` is `1/2`-Lipschitz in its angle. -/
theorem norm_ryMatrix_sub_le (s t : ℝ) : ‖ryMatrix s - ryMatrix t‖ ≤ |s - t| / 2 := by
  have he : ryMatrix s - ryMatrix t =
      !![((Real.cos (s / 2) - Real.cos (t / 2) : ℝ) : ℂ),
        -((Real.sin (s / 2) - Real.sin (t / 2) : ℝ) : ℂ);
        -(starRingEnd ℂ) (-((Real.sin (s / 2) - Real.sin (t / 2) : ℝ) : ℂ)),
        (starRingEnd ℂ) ((Real.cos (s / 2) - Real.cos (t / 2) : ℝ) : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ryMatrix, -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.conj_ofReal,
        neg_add_eq_sub]
  rw [he]
  refine norm_su2_le (by positivity) ?_
  have := sq_cos_sub_add_sq_sin_sub_le (s / 2) (t / 2)
  simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_abs (s - t)]

/-- `ry` has norm at most `1`. -/
theorem norm_ryMatrix_le (t : ℝ) : ‖ryMatrix t‖ ≤ 1 := by
  have he : ryMatrix t =
      !![((Real.cos (t / 2) : ℝ) : ℂ), -((Real.sin (t / 2) : ℝ) : ℂ);
        -(starRingEnd ℂ) (-((Real.sin (t / 2) : ℝ) : ℂ)),
        (starRingEnd ℂ) ((Real.cos (t / 2) : ℝ) : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ryMatrix, -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.conj_ofReal]
  rw [he]
  refine norm_su2_le zero_le_one ?_
  simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [Real.cos_sq_add_sin_sq (t / 2)]

/-- `rz` is `1/2`-Lipschitz in its angle. -/
theorem norm_rzMatrix_sub_le (s t : ℝ) : ‖rzMatrix s - rzMatrix t‖ ≤ |s - t| / 2 := by
  have he : rzMatrix s - rzMatrix t =
      Matrix.diagonal ![exp (I * ((-(s / 2) : ℝ) : ℂ)) - exp (I * ((-(t / 2) : ℝ) : ℂ)),
        exp (I * ((s / 2 : ℝ) : ℂ)) - exp (I * ((t / 2 : ℝ) : ℂ))] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rzMatrix]
  rw [he]
  refine norm_diagonal2_le (by positivity) ?_ ?_
  · refine (norm_exp_I_sub_exp_I_le _ _).trans (le_of_eq ?_)
    rw [show -(s / 2) - -(t / 2) = -((s - t) / 2) by ring, abs_neg, abs_div, abs_two]
  · refine (norm_exp_I_sub_exp_I_le _ _).trans (le_of_eq ?_)
    rw [show s / 2 - t / 2 = (s - t) / 2 by ring, abs_div, abs_two]

/-- `p` is `1`-Lipschitz in its angle. -/
theorem norm_rzGate_sub_le (s t : ℝ) : ‖rzGate s - rzGate t‖ ≤ |s - t| := by
  have he : rzGate s - rzGate t =
      Matrix.diagonal ![0, exp (I * (s : ℂ)) - exp (I * (t : ℂ))] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rzGate]
  rw [he]
  exact norm_diagonal2_le (abs_nonneg _) (by simp) (norm_exp_I_sub_exp_I_le s t)

/-- `p` has norm at most `1`. -/
theorem norm_rzGate_le (t : ℝ) : ‖rzGate t‖ ≤ 1 := by
  have he : rzGate t = Matrix.diagonal ![1, exp (I * (t : ℂ))] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rzGate]
  rw [he]
  exact norm_diagonal2_le zero_le_one (by simp) (by rw [Complex.norm_exp_I_mul_ofReal])

/-- The error of a product of factors of norm at most `1` is at most the sum of the errors
of the factors. -/
theorem norm_mul_sub_mul_le {R : Type*} [NormedRing R] {A A' B B' : R} (hA : ‖A‖ ≤ 1)
    (hB' : ‖B'‖ ≤ 1) : ‖A * B - A' * B'‖ ≤ ‖A - A'‖ + ‖B - B'‖ := by
  have h : A * B - A' * B' = A * (B - B') + (A - A') * B' := by noncomm_ring
  rw [h]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_mul_le A (B - B')
  have h2 := norm_mul_le (A - A') B'
  nlinarith [norm_nonneg (B - B'), norm_nonneg (A - A')]

/-- `U(θ, φ, λ) = p(φ) · ry(θ) · p(λ)`. -/
theorem uMatrix_eq (θ φ l : ℝ) : uMatrix θ φ l = rzGate φ * ryMatrix θ * rzGate l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMatrix, rzGate, ryMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.exp_add,
      mul_add] <;> ring

/-- `U` is `1/2`-Lipschitz in its first angle and `1`-Lipschitz in the other two. -/
theorem norm_uMatrix_sub_le (θ φ l θ' φ' l' : ℝ) :
    ‖uMatrix θ' φ' l' - uMatrix θ φ l‖ ≤ |θ' - θ| / 2 + |φ' - φ| + |l' - l| := by
  rw [uMatrix_eq, uMatrix_eq]
  have h0 : ‖rzGate φ' * ryMatrix θ'‖ ≤ 1 := by
    have h := mul_le_mul (norm_rzGate_le φ') (norm_ryMatrix_le θ') (norm_nonneg _) zero_le_one
    rw [one_mul] at h
    exact (norm_mul_le _ _).trans h
  have h1 : ‖rzGate φ' * ryMatrix θ' * rzGate l' - rzGate φ * ryMatrix θ * rzGate l‖ ≤
      ‖rzGate φ' * ryMatrix θ' - rzGate φ * ryMatrix θ‖ + ‖rzGate l' - rzGate l‖ :=
    norm_mul_sub_mul_le h0 (norm_rzGate_le l)
  have h2 : ‖rzGate φ' * ryMatrix θ' - rzGate φ * ryMatrix θ‖ ≤
      ‖rzGate φ' - rzGate φ‖ + ‖ryMatrix θ' - ryMatrix θ‖ :=
    norm_mul_sub_mul_le (norm_rzGate_le φ') (norm_ryMatrix_le θ)
  linarith [norm_rzGate_sub_le φ' φ, norm_ryMatrix_sub_le θ' θ, norm_rzGate_sub_le l' l]

/-! ## Snapping statements -/

/-- Angle snapping of a statement, with the sum over its snapped angles of the Lipschitz
constant times the moved-distance bound. -/
def snapGate : QGate n → QGate n × ℚ
  | .rx q θ => ((.rx q (snapAngle θ).1), (snapAngle θ).2 / 2)
  | .ry q θ => ((.ry q (snapAngle θ).1), (snapAngle θ).2 / 2)
  | .rz q θ => ((.rz q (snapAngle θ).1), (snapAngle θ).2 / 2)
  | .p q θ => ((.p q (snapAngle θ).1), (snapAngle θ).2)
  | .cp c t θ => ((.cp c t (snapAngle θ).1), (snapAngle θ).2)
  | .u q θ φ l => ((.u q (snapAngle θ).1 (snapAngle φ).1 (snapAngle l).1),
      (snapAngle θ).2 / 2 + (snapAngle φ).2 + (snapAngle l).2)
  | .u2 q φ l => ((.u2 q (snapAngle φ).1 (snapAngle l).1), (snapAngle φ).2 + (snapAngle l).2)
  | g => (g, 0)

/-- Angle snapping of a list of statements, with the sum of the bounds of the statements. -/
def snapQ (l : List (QGate n)) : List (QGate n) × ℚ :=
  (l.map fun g => (snapGate g).1, (l.map fun g => (snapGate g).2).sum)

/-- `snapQ` on a cons. -/
theorem snapQ_cons (g : QGate n) (l : List (QGate n)) :
    snapQ (g :: l) = ((snapGate g).1 :: (snapQ l).1, (snapGate g).2 + (snapQ l).2) := by
  simp [snapQ]

/-- `embedGate1` commutes with subtraction. -/
theorem embedGate1_sub (q : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n q A - embedGate1 n q B = embedGate1 n q (A - B) :=
  (map_sub (embed1Hom q) A B).symm

/-- **One statement.** The matrix of the snapped statement is within the returned bound of
the matrix of the statement. -/
theorem norm_qelibMatrix_snapGate_sub_le (g : QGate n) :
    ‖qelibMatrix (snapGate g).1 - qelibMatrix g‖ ≤ ((snapGate g).2 : ℝ) := by
  cases g with
  | rx q θ =>
    simp only [snapGate, qelibMatrix]
    rw [embedGate1_sub]
    refine (norm_embedGate1_le _ _).trans ((norm_rxMatrix_sub_le _ _).trans ?_)
    have := abs_toReal_snapAngle_sub_le θ
    push_cast
    linarith
  | ry q θ =>
    simp only [snapGate, qelibMatrix]
    rw [embedGate1_sub]
    refine (norm_embedGate1_le _ _).trans ((norm_ryMatrix_sub_le _ _).trans ?_)
    have := abs_toReal_snapAngle_sub_le θ
    push_cast
    linarith
  | rz q θ =>
    simp only [snapGate, qelibMatrix]
    rw [embedGate1_sub]
    refine (norm_embedGate1_le _ _).trans ((norm_rzMatrix_sub_le _ _).trans ?_)
    have := abs_toReal_snapAngle_sub_le θ
    push_cast
    linarith
  | p q θ =>
    simp only [snapGate, qelibMatrix]
    rw [embedGate1_sub]
    exact (norm_embedGate1_le _ _).trans
      ((norm_rzGate_sub_le _ _).trans (abs_toReal_snapAngle_sub_le θ))
  | u q θ φ l =>
    simp only [snapGate, qelibMatrix]
    rw [embedGate1_sub]
    refine (norm_embedGate1_le _ _).trans ((norm_uMatrix_sub_le _ _ _ _ _ _).trans ?_)
    have h1 := abs_toReal_snapAngle_sub_le θ
    have h2 := abs_toReal_snapAngle_sub_le φ
    have h3 := abs_toReal_snapAngle_sub_le l
    push_cast
    linarith
  | u2 q φ l =>
    simp only [snapGate, qelibMatrix]
    rw [embedGate1_sub]
    refine (norm_embedGate1_le _ _).trans ((norm_uMatrix_sub_le _ _ _ _ _ _).trans ?_)
    have h2 := abs_toReal_snapAngle_sub_le φ
    have h3 := abs_toReal_snapAngle_sub_le l
    push_cast
    simp only [sub_self, abs_zero, zero_div, zero_add]
    linarith
  | cp c t θ =>
    simp only [snapGate, qelibMatrix, ctrlMatrix]
    rw [add_sub_add_left_eq_sub, ← mul_sub, embedGate1_sub]
    refine (norm_mul_le _ _).trans ?_
    have hp : ‖embedGate1 n c proj1‖ ≤ 1 := by
      refine (norm_embedGate1_le _ _).trans ?_
      have he : proj1 = Matrix.diagonal ![0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [proj1]
      rw [he]
      exact norm_diagonal2_le zero_le_one (by simp) (by simp)
    have hd := (norm_embedGate1_le t _).trans
      ((norm_rzGate_sub_le _ _).trans (abs_toReal_snapAngle_sub_le θ))
    calc _ ≤ 1 * ‖embedGate1 n t (rzGate (snapAngle θ).1.toReal - rzGate θ.toReal)‖ :=
          mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hd
  | _ => simp [snapGate]

/-- The matrix of a statement with distinct operands has norm at most `1`. -/
theorem norm_qelibMatrix_le_one (g : QGate n) (hg : Distinct g) : ‖qelibMatrix g‖ ≤ 1 := by
  have h1 : ‖listMatrix (lowerQ g)‖ ≤ 1 :=
    (CStarRing.norm_of_mem_unitary (listMatrix_mem_unitaryGroup (lowerQ g))).le
  rw [listMatrix_lowerQ g hg, norm_smul, Complex.norm_exp_I_mul_ofReal, one_mul] at h1
  exact h1

theorem distinct_snapGate (g : QGate n) : Distinct (snapGate g).1 ↔ Distinct g := by
  cases g <;> simp [snapGate, Distinct]

/-- The matrix of a list of statements with distinct operands has norm at most `1`. -/
theorem norm_qelibListMatrix_le_one (l : List (QGate n)) (hl : ∀ g ∈ l, Distinct g) :
    ‖qelibListMatrix l‖ ≤ 1 := by
  induction l with
  | nil => exact norm_one.le
  | cons g l ih =>
    simp only [qelibListMatrix]
    refine (norm_mul_le _ _).trans ?_
    have h1 := ih fun x hx => hl x (List.mem_cons_of_mem g hx)
    have h2 := norm_qelibMatrix_le_one g (hl g List.mem_cons_self)
    nlinarith [norm_nonneg (qelibListMatrix l), norm_nonneg (qelibMatrix g)]

/-- **Angle snapping is within its bound.** For a list of statements with distinct operands,
the operator norm of the difference of the matrices of the snapped list and of the list is at
most the bound `snapQ` returns. -/
theorem norm_qelibListMatrix_snapQ_sub_le (l : List (QGate n)) (hl : ∀ g ∈ l, Distinct g) :
    ‖qelibListMatrix (snapQ l).1 - qelibListMatrix l‖ ≤ ((snapQ l).2 : ℝ) := by
  induction l with
  | nil => simp [snapQ, qelibListMatrix]
  | cons g l ih =>
    have hl' : ∀ x ∈ l, Distinct x := fun x hx => hl x (List.mem_cons_of_mem g hx)
    have h1 := ih hl'
    have h2 := norm_qelibMatrix_snapGate_sub_le g
    have hA : ‖qelibListMatrix (snapQ l).1‖ ≤ 1 := by
      refine norm_qelibListMatrix_le_one _ fun x hx => ?_
      simp only [snapQ, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (distinct_snapGate y).2 (hl' y hy)
    have hB := norm_qelibMatrix_le_one g (hl g List.mem_cons_self)
    rw [snapQ_cons]
    simp only [qelibListMatrix]
    refine (norm_mul_sub_mul_le hA hB).trans ?_
    push_cast
    linarith

/-- Angle snapping keeps the length. -/
theorem length_snapQ (l : List (QGate n)) : (snapQ l).1.length = l.length := by
  simp [snapQ]

/-- Angle snapping keeps the `cx` count. -/
theorem cxCount_snapQ (l : List (QGate n)) : cxCount (snapQ l).1 = cxCount l := by
  have h : ∀ g : QGate n, isCx (snapGate g).1 = isCx g := by
    intro g; cases g <;> rfl
  simp only [snapQ, cxCount, List.countP_map]
  exact List.countP_congr fun g _ => by simp [Function.comp, h]

end CatCrypt.Quantum.AngleSnap
