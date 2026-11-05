/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.CBall
public import CatCrypt.Quantum.PiLin
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Enclosures of `e^{iθ}` at exact angles and of `1/√2`

`expIBall p` is a computable ball containing `exp (I · toReal p)` for an exact angle
`p = a + b·π` (`PiLin`). The angle is first reduced by a whole number `r` of quarter turns,
chosen from a rational value of `π`; the reduction is exact on `PiLin` (it changes `b` to
`b - r/2`), and the factor `e^{irπ/2} = i^r` is an exact rotation of the ball (`rotI`).
The reduced angle `a + b'·π` lies within `|b'|·10⁻²⁰` of the rational `m = a + b'·π₀`, where
`π₀ = 3.14159265358979323846` and `π₀ < π < π₀ + 10⁻²⁰` (`Real.pi_gt_d20`,
`Real.pi_lt_d20`). Then `exp (I · m)` is enclosed by its Taylor polynomial of `20` terms,
evaluated in ball arithmetic, widened by the remainder bound `2 |m|²⁰ / 20!` of
`Complex.exp_bound'`, and the distance `|t - m|` is added, since `exp (I ·)` is
`1`-Lipschitz on the reals (`Real.norm_exp_I_mul_ofReal_sub_one_le`).

`invSqrt2` is a ball containing `1/√2`, the entry of the Hadamard matrix, with centre
`⌊2^p/√2⌋ / 2^p` and radius `2^-p` at the working precision `p`.

## Main definitions

* `taylorAux` — the Taylor partial sums of `exp` as balls.
* `expIQ` — a ball containing `exp (I · m)` at a rational `m`.
* `rotI` — the exact rotation of a ball by `i^q`.
* `expIBall` — a ball containing `exp (I · toReal p)` at an exact angle `p`.
* `invSqrt2` — a ball containing `1/√2`.

## Main results

* `mem_taylorAux` — the Taylor partial sum lies in its ball.
* `mem_expIQ`, `mem_expIQ_widen` — soundness at a rational and near a rational.
* `mem_expIBall` — `exp (I · toReal p)` lies in `expIBall p`.
* `mem_invSqrt2` — `1/√2` lies in `invSqrt2`.
-/

@[expose] public section

set_option autoImplicit false

open Complex

namespace CatCrypt.Quantum.Synthesis.IntervalArith

open CBall

/-! ## Taylor sums of `exp` -/

/-- The pair of balls for the Taylor partial sum `∑_{k<m} z^k/k!` and the term `z^m/m!`,
for `z` in the ball `Z`. -/
def taylorAux (Z : CBall) : ℕ → CBall × CBall
  | 0 => (CBall.zero, CBall.one)
  | m + 1 =>
    let st := taylorAux Z m
    (add st.1 st.2, CBall.mul (ofQ (1 / (m + 1 : ℚ))) (CBall.mul st.2 Z))

theorem mem_taylorAux {x : ℂ} {Z : CBall} (hx : Mem x Z) (m : ℕ) :
    Mem (∑ k ∈ Finset.range m, x ^ k / k.factorial) (taylorAux Z m).1 ∧
      Mem (x ^ m / m.factorial) (taylorAux Z m).2 := by
  induction m with
  | zero => simpa [taylorAux] using And.intro mem_zero mem_one
  | succ m ih =>
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_range_succ]
      exact mem_add ih.1 ih.2
    · have h : x ^ (m + 1) / ((m + 1).factorial : ℂ) =
          (((1 / (m + 1 : ℚ)) : ℚ) : ℂ) * (x ^ m / m.factorial * x) := by
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
      rw [h]
      exact mem_mul (mem_ofQ _) (mem_mul ih.2 hx)

/-- The number of Taylor terms of `expIQ`. -/
def taylorN : ℕ := 20

/-- A ball containing `exp (I · m)` for a rational `m`: for `|m| ≤ 10`, the Taylor sum of
`taylorN` terms widened by the remainder `2 M^20 / 20!` with `M ≥ |m|` on the grid
`2^-8 ℤ`, at the ball `i · ofQ m` of `i·m`; otherwise the unit disc. -/
def expIQ (m : ℚ) : CBall :=
  if |m| ≤ 10 then
    widen (2 * ceilD 8 |m| ^ taylorN / taylorN.factorial)
      (taylorAux (CBall.mul iI (ofQ m)) taylorN).1
  else unit

theorem mem_expIQ (m : ℚ) : Mem (exp (I * ((m : ℝ) : ℂ))) (expIQ m) := by
  unfold expIQ
  split
  · next hm =>
    have hx : Mem (I * ((m : ℝ) : ℂ)) (CBall.mul iI (ofQ m)) := by
      simpa using mem_mul mem_iI (mem_ofQ m)
    refine mem_widen (mem_taylorAux hx taylorN).1 ?_
    have hn : ‖I * ((m : ℝ) : ℂ)‖ = |(m : ℝ)| := by simp
    have hb := Complex.exp_bound' (x := I * ((m : ℝ) : ℂ)) (n := taylorN) (by
      rw [hn, taylorN]
      have : |(m : ℝ)| ≤ 10 := by exact_mod_cast hm
      norm_num
      linarith)
    refine hb.trans ?_
    rw [hn]
    have hM : |(m : ℝ)| ≤ (ceilD 8 |m| : ℝ) := by exact_mod_cast le_ceilD 8 |m|
    have hpow : |(m : ℝ)| ^ taylorN ≤ (ceilD 8 |m| : ℝ) ^ taylorN :=
      pow_le_pow_left₀ (abs_nonneg _) hM _
    have hf : (0 : ℝ) < taylorN.factorial := by exact_mod_cast Nat.factorial_pos _
    push_cast
    rw [div_mul_eq_mul_div, mul_comm _ (2 : ℝ)]
    gcongr
  · exact mem_unit (by rw [norm_exp_I_mul_ofReal])

/-- `exp (I ·)` is `1`-Lipschitz on the reals. -/
theorem norm_exp_I_sub_exp_I_le (t s : ℝ) :
    ‖exp (I * (t : ℂ)) - exp (I * (s : ℂ))‖ ≤ |t - s| := by
  have h : exp (I * (t : ℂ)) - exp (I * (s : ℂ)) =
      exp (I * (s : ℂ)) * (exp (I * ((t - s : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    push_cast
    ring_nf
  rw [h, norm_mul, norm_exp_I_mul_ofReal, one_mul]
  simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := t - s)

theorem mem_expIQ_widen {t : ℝ} {m e : ℚ} (h : |t - m| ≤ (e : ℝ)) :
    Mem (exp (I * (t : ℂ))) (widen e (expIQ m)) :=
  mem_widen (mem_expIQ m) ((norm_exp_I_sub_exp_I_le t m).trans h)

/-! ## Exact angles -/

/-- The rational `3.14159265358979323846`, within `10⁻²⁰` below `π`. -/
def piLo : ℚ := 314159265358979323846 / 10 ^ 20

theorem piLo_lt_pi : (piLo : ℝ) < Real.pi := by
  have h := Real.pi_gt_d20
  simp only [piLo]
  push_cast
  linarith

theorem pi_lt_piLo_add : Real.pi < piLo + 1 / 10 ^ 20 := by
  have h := Real.pi_lt_d20
  simp only [piLo]
  push_cast
  linarith

/-- The ball rotated `q` times by the exact multiplication by `i`. -/
def rotI : ℕ → CBall → CBall
  | 0, B => B
  | q + 1, B => CBall.mul iI (rotI q B)

theorem mem_rotI {z : ℂ} {B : CBall} (h : Mem z B) : ∀ q, Mem (I ^ q * z) (rotI q B)
  | 0 => by simpa [rotI] using h
  | q + 1 => by
    rw [pow_succ', mul_assoc]
    exact mem_mul mem_iI (mem_rotI h q)

theorem exp_pi_div_two_mul_I' : exp ((Real.pi / 2 : ℝ) * I) = I := by
  rw [Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring

/-- A ball containing `exp (I · toReal p)` for the exact angle `p = a + b·π`. With `r` the
number of quarter turns rounded from `p / (π₀/2)`, `r = 4k + q` and `0 ≤ q < 4`, the angle is
`a + b'·π + 2kπ + q·π/2` for `b' = b - 2k - q/2`; the reduced angle `a + b'·π` lies within
`|b'|·10⁻²⁰` of the rational `a + b'·π₀`, and `e^{iqπ/2} = i^q` is an exact rotation. -/
def expIBall (p : PiLin) : CBall :=
  let r : ℤ := _root_.round ((p.a + p.b * piLo) / (piLo / 2))
  let b' := p.b - 2 * (r / 4 : ℤ) - (r % 4 : ℤ) / 2
  rotI (r % 4).toNat (widen (|b'| / 10 ^ 20) (expIQ (p.a + b' * piLo)))

theorem mem_expIBall (p : PiLin) : Mem (exp (I * (PiLin.toReal p : ℂ))) (expIBall p) := by
  unfold expIBall
  set r : ℤ := _root_.round ((p.a + p.b * piLo) / (piLo / 2))
  set k : ℤ := r / 4
  set q : ℤ := r % 4
  set b' := p.b - 2 * k - q / 2
  have hq : (((q.toNat : ℕ) : ℤ) : ℂ) = (q : ℂ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
  have hred : exp (I * (PiLin.toReal p : ℂ)) =
      I ^ q.toNat * exp (I * (((p.a : ℝ) + b' * Real.pi : ℝ) : ℂ)) := by
    have h : I * (PiLin.toReal p : ℂ) =
        I * (((p.a : ℝ) + b' * Real.pi : ℝ) : ℂ) + (k : ℂ) * (2 * Real.pi * I) +
          (q.toNat : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
      rw [show ((q.toNat : ℕ) : ℂ) = (((q.toNat : ℕ) : ℤ) : ℂ) by norm_cast, hq]
      simp only [PiLin.toReal, b']
      push_cast
      ring
    rw [h, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
      Complex.exp_nat_mul, exp_pi_div_two_mul_I', mul_comm]
  rw [hred]
  apply mem_rotI
  apply mem_expIQ_widen
  have h1 := piLo_lt_pi
  have h2 := pi_lt_piLo_add
  have he : ((p.a : ℝ) + b' * Real.pi) - ((p.a + b' * piLo : ℚ) : ℝ) =
      (b' : ℝ) * (Real.pi - piLo) := by push_cast; ring
  have hpos : (0 : ℝ) < Real.pi - piLo := by linarith
  rw [he, abs_mul, abs_of_pos hpos]
  push_cast
  calc |(b' : ℝ)| * (Real.pi - piLo) ≤ |(b' : ℝ)| * (1 / 10 ^ 20) := by gcongr; linarith
    _ = |(b' : ℝ)| / 10 ^ 20 := by ring
    _ = _ := by simp [b', k, q]

/-! ## The entry `1/√2` of the Hadamard matrix -/

/-- A ball containing `1/√2`: centre mantissa `⌊√(2·4^(p-1))⌋ = ⌊2^p/√2⌋`, radius mantissa
`1`, at the working precision `p`. -/
def invSqrt2 : CBall := ⟨(Nat.sqrt (2 * 4 ^ (prec - 1)) : ℤ), 0, 1⟩

theorem mem_invSqrt2 : Mem ((1 / Real.sqrt 2 : ℝ) : ℂ) invSqrt2 := by
  set N : ℕ := 2 * 4 ^ (prec - 1)
  set M : ℕ := Nat.sqrt N
  have hp1 : (2 : ℝ) ^ prec = 2 ^ (prec - 1) * 2 := by rw [← pow_succ]; rfl
  have hsq : Real.sqrt (N : ℝ) = Real.sqrt 2 * 2 ^ (prec - 1) := by
    have : (N : ℝ) = 2 * (2 ^ (prec - 1)) ^ 2 := by
      simp only [N]; push_cast; rw [← pow_mul, mul_comm (prec - 1) 2, pow_mul]; norm_num
    rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  have hx : (1 / Real.sqrt 2 : ℝ) = Real.sqrt (N : ℝ) / 2 ^ prec := by
    rw [hsq, hp1]
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  have hlo : (M : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hhi : Real.sqrt N < M + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  have key : |1 / Real.sqrt 2 - (M : ℝ) / 2 ^ prec| ≤ 1 / 2 ^ prec := by
    rw [hx, ← sub_div, abs_div, abs_of_pos hp, abs_of_nonneg (by linarith)]
    gcongr
    linarith
  simp only [Mem, MemAt, invSqrt2, centerAt]
  convert key using 1
  · rw [← Real.norm_eq_abs, ← Complex.norm_real]
    congr 1
    push_cast
    ring
  · push_cast
    ring

end CatCrypt.Quantum.Synthesis.IntervalArith
