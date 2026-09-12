/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Complex.Basic


@[expose] public section
set_option autoImplicit false

/-!
# `norm_sqrt` tactic

Normalizes products of `(↑(Real.sqrt n) : ℂ)` and its inverse by rewriting:
- `√n * √n → n`
- `(√n)⁻¹ * (√n)⁻¹ → n⁻¹`
- `√n * (√n)⁻¹ → 1`
-/

/-! ## Rewrite lemmas (in root namespace for macro access) -/

theorem _root_.ofReal_sqrt_mul_self {r : ℝ} (hr : 0 ≤ r) :
    (↑(Real.sqrt r) : ℂ) * (↑(Real.sqrt r) : ℂ) = ↑r := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]

theorem _root_.ofReal_sqrt_sq {r : ℝ} (hr : 0 ≤ r) :
    (↑(Real.sqrt r) : ℂ) ^ 2 = ↑r := by
  rw [sq, ofReal_sqrt_mul_self hr]

theorem _root_.ofReal_sqrt_inv_mul_self {r : ℝ} (hr : 0 ≤ r) :
    (↑(Real.sqrt r) : ℂ)⁻¹ * (↑(Real.sqrt r) : ℂ)⁻¹ = (↑r : ℂ)⁻¹ := by
  rw [← mul_inv, ofReal_sqrt_mul_self hr]

theorem _root_.ofReal_sqrt_inv_sq {r : ℝ} (hr : 0 ≤ r) :
    (↑(Real.sqrt r) : ℂ)⁻¹ ^ 2 = (↑r : ℂ)⁻¹ := by
  rw [sq, ofReal_sqrt_inv_mul_self hr]

theorem _root_.ofReal_sqrt_mul_inv {r : ℝ} (hr : 0 < r) :
    (↑(Real.sqrt r) : ℂ) * (↑(Real.sqrt r) : ℂ)⁻¹ = 1 := by
  apply mul_inv_cancel₀; simp [Real.sqrt_ne_zero'.mpr hr]

theorem _root_.ofReal_sqrt_inv_mul {r : ℝ} (hr : 0 < r) :
    (↑(Real.sqrt r) : ℂ)⁻¹ * (↑(Real.sqrt r) : ℂ) = 1 := by
  apply inv_mul_cancel₀; simp [Real.sqrt_ne_zero'.mpr hr]

/-- Normalize expressions involving `(↑(Real.sqrt n) : ℂ)` and its inverse,
then close with `ring`.

Strategy: `simp` with the √n rewrite lemmas to eliminate squared terms,
then close with `ring` / `norm_num` / `push_cast; ring`. -/
macro "norm_sqrt" : tactic => `(tactic|
  first
  | ring
  | norm_num
  | (simp only [
       ofReal_sqrt_mul_self (by norm_num),
       ofReal_sqrt_inv_mul_self (by norm_num),
       ofReal_sqrt_mul_inv (by norm_num),
       ofReal_sqrt_inv_mul (by norm_num),
       ofReal_sqrt_sq (by norm_num),
       ofReal_sqrt_inv_sq (by norm_num),
       mul_one, one_mul]
     first | rfl | ring | norm_num | (push_cast; ring) | (push_cast; rfl)))

/-! ## Smoke tests -/

-- √2 * √2 = 2
example : (↑(Real.sqrt 2) : ℂ) * (↑(Real.sqrt 2) : ℂ) = 2 := by
  rw [ofReal_sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]; push_cast; rfl

-- (√2)⁻¹ * (√2)⁻¹ = 2⁻¹
example : (↑(Real.sqrt 2) : ℂ)⁻¹ * (↑(Real.sqrt 2) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  rw [ofReal_sqrt_inv_mul_self (by norm_num : (0:ℝ) ≤ 2)]; push_cast; rfl

-- √2 * (√2)⁻¹ = 1
example : (↑(Real.sqrt 2) : ℂ) * (↑(Real.sqrt 2) : ℂ)⁻¹ = 1 := by
  exact ofReal_sqrt_mul_inv (by norm_num)

-- (√2)⁻¹ * √2 = 1
example : (↑(Real.sqrt 2) : ℂ)⁻¹ * (↑(Real.sqrt 2) : ℂ) = 1 := by
  exact ofReal_sqrt_inv_mul (by norm_num)

-- √3 * √3 = 3
example : (↑(Real.sqrt 3) : ℂ) * (↑(Real.sqrt 3) : ℂ) = 3 := by
  rw [ofReal_sqrt_mul_self (by norm_num : (0:ℝ) ≤ 3)]; push_cast; rfl
