/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Generic single-level Toom-3 (3-way) multiplication identity

This file isolates the **abstract algebraic core** behind three-way Toom–Cook
multiplication, the next subquadratic step after Karatsuba
(`KaratsubaGenericPass.lean`). Karatsuba splits each operand into two limbs and
trades the schoolbook four multiplications for three. Toom-3 splits each operand
into **three** limbs and trades the schoolbook **nine** multiplications for
**five**.

Model a three-limb value `(a2, a1, a0)` as the polynomial
```
A(B) = a2 * B^2 + a1 * B + a0
```
and likewise `B'(B) = b2 * B^2 + b1 * B + b0`. Their product is degree four in
`B`, with five coefficients `c4, c3, c2, c1, c0`:
```
A(B) * B'(B) = c4 * B^4 + c3 * B^3 + c2 * B^2 + c1 * B + c0.
```

Toom-3 computes those five coefficients with only five sub-multiplications by
**evaluate–multiply–interpolate** at five points. We use the classic point set
```
  0,  1,  -1,  2,  ∞
```
("∞" means the leading coefficient `a2`, i.e. the limit of `A(B)/B^2`). At each
point the two operands are evaluated (additions and small scalings only), then
multiplied — five products:
```
  w0  = a0           * b0
  w1  = (a2+a1+a0)   * (b2+b1+b0)        -- A(1)  * B'(1)
  wm1 = (a2-a1+a0)   * (b2-b1+b0)        -- A(-1) * B'(-1)
  w2  = (4a2+2a1+a0) * (4b2+2b1+b0)      -- A(2)  * B'(2)
  winf= a2           * b2                -- A(∞)  * B'(∞)
```
The five product coefficients are recovered by interpolation. Two of them are
immediate (`c0 = w0`, `c4 = winf`); the remaining three require division by the
small constants `2`, `3`, `6`:
```
  c2 = (w1 + wm1) / 2 - w0 - winf
  c3 = (w2 - w1) / 6 - winf + (w0 - wm1) ... (see `toom3Coeffs`)
  c1 = ...
```
Because interpolation divides by `2`, `3`, `6`, the clean statement lives over a
field where those are invertible. We provide **two** verified forms:

* `toom3Coeffs` / `toom3_eq_schoolbook` over `[Field R]`: the genuine
  evaluate-multiply-interpolate coefficients (with division), reassembled to the
  schoolbook product, closed by `field_simp; ring`.
* `toom3Coeffs6` / `toom3_eq_schoolbook6` over a bare `[CommRing R]`: the
  **denominator-cleared** form, where each coefficient is presented scaled by
  `6` (the lcm of `2, 3, 6`). Reassembling `6 *` the product from the
  six-times-scaled coefficients equals `6 * (A(B) * B'(B))`, closed by `ring`.
  This needs no invertibility and is the form a bignum / e-graph rewrite can use
  when `6` is coprime to the modulus (then multiply through by `6⁻¹`).

Being parametric over the coefficient ring and the base `B`, both identities are
proved once here, exactly as the generic Karatsuba identity is.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.Toom3Generic

/-! ## Schoolbook reference (nine multiplications) -/

variable {R : Type*}

section CommRing
variable [CommRing R]

set_option linter.unusedVariables false in
/-- Schoolbook product of two three-limb values `(a2, a1, a0)` and
`(b2, b1, b0)` representing `a2*B^2+a1*B+a0` and `b2*B^2+b1*B+b0`, returned as
the five-coefficient result `(c4, c3, c2, c1, c0)` so that the value is
`c4*B^4 + c3*B^3 + c2*B^2 + c1*B + c0`. Uses the full **nine** multiplications.
The base `B` is carried for signature uniformity with the Toom-3 forms. -/
def schoolbookMul3 (B a2 a1 a0 b2 b1 b0 : R) : R × R × R × R × R :=
  ( a2 * b2,
    a2 * b1 + a1 * b2,
    a2 * b0 + a1 * b1 + a0 * b2,
    a1 * b0 + a0 * b1,
    a0 * b0 )

/-- The value `c4*B^4 + c3*B^3 + c2*B^2 + c1*B + c0` carried by a
five-coefficient result `(c4, c3, c2, c1, c0)`. -/
def evalLimbs5 (B : R) (p : R × R × R × R × R) : R :=
  p.1 * B ^ 4 + p.2.1 * B ^ 3 + p.2.2.1 * B ^ 2 + p.2.2.2.1 * B + p.2.2.2.2

/-- The schoolbook assembly equals the genuine ring product
`(a2*B^2+a1*B+a0)*(b2*B^2+b1*B+b0)`. -/
theorem evalLimbs5_schoolbookMul3 (B a2 a1 a0 b2 b1 b0 : R) :
    evalLimbs5 B (schoolbookMul3 B a2 a1 a0 b2 b1 b0)
      = (a2 * B ^ 2 + a1 * B + a0) * (b2 * B ^ 2 + b1 * B + b0) := by
  simp only [evalLimbs5, schoolbookMul3]
  ring

/-! ## Denominator-cleared Toom-3 over a bare commutative ring

Each coefficient is presented scaled by `6 = lcm(2, 3, 6)`, so no division is
needed. The five products `w0, w1, wm1, w2, winf` are the genuine Toom-3
evaluate-multiply values (five multiplications). -/

set_option linter.unusedVariables false in
/-- Toom-3 coefficients in **denominator-cleared** form: returns
`(6*c4, 6*c3, 6*c2, 6*c1, 6*c0)`. The five products are
`w0 = a0*b0`, `w1 = (a2+a1+a0)(b2+b1+b0)`, `wm1 = (a2-a1+a0)(b2-b1+b0)`,
`w2 = (4a2+2a1+a0)(4b2+2b1+b0)`, `winf = a2*b2` — five multiplications. The
scaled interpolation:
```
  6*c0 = 6*w0
  6*c4 = 6*winf
  6*c2 = 3*(w1 + wm1) - 6*w0 - 6*winf
  6*c3 = w2 - 2*w1 + (-2)*wm1 ... (the standard cleared form below)
  6*c1 = 6*w1 - 3*w0 - 2*wm1 - winf*... (the standard cleared form below)
```
verified against the schoolbook product by `ring` (see `toom3_eq_schoolbook6`).
The base `B` is carried for signature uniformity. -/
def toom3Coeffs6 (B a2 a1 a0 b2 b1 b0 : R) : R × R × R × R × R :=
  let w0  := a0 * b0
  let w1  := (a2 + a1 + a0) * (b2 + b1 + b0)
  let wm1 := (a2 - a1 + a0) * (b2 - b1 + b0)
  let w2  := (4 * a2 + 2 * a1 + a0) * (4 * b2 + 2 * b1 + b0)
  let winf := a2 * b2
  ( 6 * winf,
    -- 6*c3 = w2 - 3*w1 - wm1 + 3*w0 - 12*winf
    w2 - 3 * w1 - wm1 + 3 * w0 - 12 * winf,
    -- 6*c2 = 3*w1 + 3*wm1 - 6*w0 - 6*winf
    3 * w1 + 3 * wm1 - 6 * w0 - 6 * winf,
    -- 6*c1 = -w2 + 6*w1 - 2*wm1 - 3*w0 + 12*winf
    -w2 + 6 * w1 - 2 * wm1 - 3 * w0 + 12 * winf,
    6 * w0 )

/-- **The cleared Toom-3 identity over a commutative ring.** Reassembling
`6 *` the product from the six-times-scaled coefficients equals
`6 * (A(B) * B'(B))`. No invertibility of `2, 3, 6` is required. -/
theorem toom3_eq_schoolbook6 (B a2 a1 a0 b2 b1 b0 : R) :
    evalLimbs5 B (toom3Coeffs6 B a2 a1 a0 b2 b1 b0)
      = 6 * ((a2 * B ^ 2 + a1 * B + a0) * (b2 * B ^ 2 + b1 * B + b0)) := by
  simp only [evalLimbs5, toom3Coeffs6]
  ring

/-- The cleared Toom-3 coefficients are exactly `6 ×` the schoolbook
coefficients (coefficientwise), so Toom-3 (five multiplications) computes the
same product as schoolbook (nine multiplications). -/
theorem toom3Coeffs6_eq_schoolbook (B a2 a1 a0 b2 b1 b0 : R) :
    toom3Coeffs6 B a2 a1 a0 b2 b1 b0
      = (6 * (schoolbookMul3 B a2 a1 a0 b2 b1 b0).1,
         6 * (schoolbookMul3 B a2 a1 a0 b2 b1 b0).2.1,
         6 * (schoolbookMul3 B a2 a1 a0 b2 b1 b0).2.2.1,
         6 * (schoolbookMul3 B a2 a1 a0 b2 b1 b0).2.2.2.1,
         6 * (schoolbookMul3 B a2 a1 a0 b2 b1 b0).2.2.2.2) := by
  simp only [toom3Coeffs6, schoolbookMul3, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | ring | trivial

end CommRing

/-! ## Field form: genuine Toom-3 interpolation with division by `2, 3, 6`

Over a field the small constants `2, 3, 6` are invertible, so the five
coefficients can be presented directly (each is `1/6` of the cleared form). -/

section Field
variable [Field R]

set_option linter.unusedVariables false in
/-- Genuine Toom-3 coefficients `(c4, c3, c2, c1, c0)` over a field, obtained by
evaluate–multiply–interpolate at the points `0, 1, -1, 2, ∞`. The interpolation
divides by `2, 3, 6`, hence the field requirement. Each coefficient is `1/6` of
the corresponding `toom3Coeffs6` entry. -/
def toom3Coeffs (B a2 a1 a0 b2 b1 b0 : R) : R × R × R × R × R :=
  let w0  := a0 * b0
  let w1  := (a2 + a1 + a0) * (b2 + b1 + b0)
  let wm1 := (a2 - a1 + a0) * (b2 - b1 + b0)
  let w2  := (4 * a2 + 2 * a1 + a0) * (4 * b2 + 2 * b1 + b0)
  let winf := a2 * b2
  ( winf,
    (w2 - 3 * w1 - wm1 + 3 * w0 - 12 * winf) / 6,
    (3 * w1 + 3 * wm1 - 6 * w0 - 6 * winf) / 6,
    (-w2 + 6 * w1 - 2 * wm1 - 3 * w0 + 12 * winf) / 6,
    w0 )

/-- **The Toom-3 identity over a field.** Reassembling the five interpolated
coefficients at base `B` yields exactly the product
`(a2*B^2+a1*B+a0)*(b2*B^2+b1*B+b0)` — single-level Toom-3 (five multiplications)
equals the schoolbook product (nine multiplications). -/
theorem toom3_eq_schoolbook (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    evalLimbs5 B (toom3Coeffs B a2 a1 a0 b2 b1 b0)
      = (a2 * B ^ 2 + a1 * B + a0) * (b2 * B ^ 2 + b1 * B + b0) := by
  simp only [evalLimbs5, toom3Coeffs]
  field_simp
  ring

/-- The field-form Toom-3 coefficients agree with the schoolbook coefficients
(coefficientwise). -/
theorem toom3Coeffs_eq_schoolbook (h6 : (6 : R) ≠ 0) (B a2 a1 a0 b2 b1 b0 : R) :
    toom3Coeffs B a2 a1 a0 b2 b1 b0 = schoolbookMul3 B a2 a1 a0 b2 b1 b0 := by
  simp only [toom3Coeffs, schoolbookMul3, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | (field_simp; ring) | ring | trivial

end Field

/-! ## Worked example over `ℚ` with base `B = 10`

`a = a2*100 + a1*10 + a0`, `b = b2*100 + b1*10 + b0`; e.g. `a = 123`, `b = 456`
(`a2=1, a1=2, a0=3, b2=4, b1=5, b0=6`), with `123 * 456 = 56088`. -/

/-- `123 * 456 = 56088` recovered through the generic field Toom-3 assembly over
`ℚ` with base `10`. -/
example : evalLimbs5 (R := ℚ) 10 (toom3Coeffs 10 1 2 3 4 5 6) = 56088 := by
  norm_num [evalLimbs5, toom3Coeffs]

/-- The cleared form gives `6 * 56088 = 336528` over `ℚ` with base `10`. -/
example : evalLimbs5 (R := ℚ) 10 (toom3Coeffs6 10 1 2 3 4 5 6) = 336528 := by
  norm_num [evalLimbs5, toom3Coeffs6]

/-- The field Toom-3 and schoolbook coefficient quintuples coincide on the
example. -/
example :
    toom3Coeffs (R := ℚ) 10 1 2 3 4 5 6 = schoolbookMul3 (R := ℚ) 10 1 2 3 4 5 6 := by
  norm_num [toom3Coeffs, schoolbookMul3]

end CatCrypt.Crypto.Optimizer.Rewrite.Toom3Generic
