/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.Ring

/-!
# Pure-integer Toom-Cook evaluation and interpolation algebra

The evaluation/interpolation algebra shared by the recursive Toom-Cook
multipliers on the `BigNat` carrier, over the abstract `Int`/`Nat` operand
values.  Every declaration here is a pure `Int`/`Nat` function or a
`ring`-closed recombination identity, independent of any limb-list carrier or
machine kernel.

## Main results

* `toom3_schoolbook_split` — the Toom-3 schoolbook 3-way split identity over
  `Nat`: the product of two degree-2 polynomials in `B` expressed through the
  five convolution coefficients.
* `evalsInt4` / `subProductsInt4` — the Toom-4 seven-point operand evaluation
  at `{0, 1, -1, 2, -2, 3, ∞}` and the seven sub-products of a pair of
  evaluations.
* `toom4Interpolate720` — the Toom-4 interpolation recovering `720 ×` each of
  the seven schoolbook coefficients from the seven sub-products, with
  denominator `720 = 2⁴·3²·5` the Vandermonde determinant.
* `toom4_recombine_int_h0`..`toom4_recombine_int_h6` — the seven recombination
  identities, each stating that the interpolated `720`-scaled coefficient
  equals `720 ×` the corresponding schoolbook convolution.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ToomInterpolation

/-! ## Toom-3 schoolbook split -/

/-- **The Toom-3 schoolbook 3-way split identity (over `Nat`).**  Splitting
    each operand into 3 chunks `(a₀, a₁, a₂)` and `(c₀, c₁, c₂)` at base `B`,
    the product is the degree-4 polynomial in `B` with coefficients given by
    the convolution `h_i = Σ_{j+k=i} aⱼ · cₖ`.  Pure `ring` over `Nat`. -/
theorem toom3_schoolbook_split (a0 a1 a2 c0 c1 c2 B : Nat) :
    (a0 + B * a1 + B * B * a2) * (c0 + B * c1 + B * B * c2)
      = a0 * c0
        + B * (a0 * c1 + a1 * c0)
        + B * B * (a0 * c2 + a1 * c1 + a2 * c0)
        + B * B * B * (a1 * c2 + a2 * c1)
        + B * B * B * B * (a2 * c2) := by
  ring

/-! ## Toom-4 evaluation and sub-products -/

/-- The 7 operand-evaluations at `{0, 1, -1, 2, -2, 3, ∞}`.

    Returned as a 7-tuple `(a(0), a(1), a(-1), a(2), a(-2), a(3), a(∞))`. -/
def evalsInt4 (a0 a1 a2 a3 : Int) : Int × Int × Int × Int × Int × Int × Int :=
  ( a0                                          -- a(0)   = a₀
  , a0 + a1 + a2 + a3                           -- a(1)
  , a0 - a1 + a2 - a3                           -- a(-1)
  , a0 + 2 * a1 + 4 * a2 + 8 * a3               -- a(2)
  , a0 - 2 * a1 + 4 * a2 - 8 * a3               -- a(-2)
  , a0 + 3 * a1 + 9 * a2 + 27 * a3              -- a(3)
  , a3 )                                        -- a(∞)   = a₃  (leading)

/-- The 7 sub-product values from a pair of operand-evaluations.

    Returned as a 7-tuple
    `(v(0), v(1), v(-1), v(2), v(-2), v(3), v(∞))`. -/
def subProductsInt4 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    Int × Int × Int × Int × Int × Int × Int :=
  let (av0, av1, avm1, av2, avm2, av3, avi) := evalsInt4 a0 a1 a2 a3
  let (bv0, bv1, bvm1, bv2, bvm2, bv3, bvi) := evalsInt4 b0 b1 b2 b3
  ( av0  * bv0
  , av1  * bv1
  , avm1 * bvm1
  , av2  * bv2
  , avm2 * bvm2
  , av3  * bv3
  , avi  * bvi )

/-- **Toom-4 interpolation (720× scaled) at `{0, 1, -1, 2, -2, 3, ∞}`** —
    recovers `720 ×` each of the 7 schoolbook coefficients from the 7
    sub-products `(v0, v1, vm1, v2, vm2, v3, vinf)`.  Integer coefficients;
    valid in any commutative ring containing `ℤ`.

    The denominator `720 = 2⁴·3²·5` is the determinant of the 7×7
    Vandermonde at `{0, 1, -1, 2, -2, 3, ∞}`.  Choosing integer points
    (instead of Bodrato's half-integer `{0, ±1, ±1/2, 2, ∞}`) avoids
    rational arithmetic; the price is the slightly larger denominator
    (720 vs 360).

    Returned as `(720·h₀, 720·h₁, 720·h₂, 720·h₃, 720·h₄, 720·h₅, 720·h₆)`. -/
def toom4Interpolate720 (v0 v1 vm1 v2 vm2 v3 vinf : Int) :
    Int × Int × Int × Int × Int × Int × Int :=
  ( 720 * v0                                                                          -- 720 h₀
  , -240 * v0 + 720 * v1 - 360 * vm1 - 180 * v2 + 36 * vm2 + 24 * v3 - 8640 * vinf    -- 720 h₁
  , -900 * v0 + 480 * v1 + 480 * vm1 - 30 * v2 - 30 * vm2 + 2880 * vinf               -- 720 h₂
  , 300 * v0 - 420 * v1 - 30 * vm1 + 210 * v2 - 30 * vm2 - 30 * v3 + 10800 * vinf     -- 720 h₃
  , 180 * v0 - 120 * v1 - 120 * vm1 + 30 * v2 + 30 * vm2 - 3600 * vinf                -- 720 h₄
  , -60 * v0 + 60 * v1 + 30 * vm1 - 30 * v2 - 6 * vm2 + 6 * v3 - 2160 * vinf          -- 720 h₅
  , 720 * vinf )                                                                      -- 720 h₆

/-! ## Toom-4 recombination identities -/

/-- **Toom-4 recombination, h₀ component.**  The 0-th interpolated
    coefficient (scaled by 720) equals 720 × the schoolbook constant
    coefficient `a₀ b₀`. -/
theorem toom4_recombine_int_h0 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    (toom4Interpolate720
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.2).1
      = 720 * (a0 * b0) := by
  simp only [subProductsInt4, evalsInt4, toom4Interpolate720]

/-- **Toom-4 recombination, h₁ component.**  Equals `720·(a₀b₁ + a₁b₀)`. -/
theorem toom4_recombine_int_h1 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    (toom4Interpolate720
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.2).2.1
      = 720 * (a0 * b1 + a1 * b0) := by
  simp only [subProductsInt4, evalsInt4, toom4Interpolate720]
  ring

/-- **Toom-4 recombination, h₂ component.**  Equals
    `720·(a₀b₂ + a₁b₁ + a₂b₀)`. -/
theorem toom4_recombine_int_h2 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    (toom4Interpolate720
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.2).2.2.1
      = 720 * (a0 * b2 + a1 * b1 + a2 * b0) := by
  simp only [subProductsInt4, evalsInt4, toom4Interpolate720]
  ring

/-- **Toom-4 recombination, h₃ component.**  Equals
    `720·(a₀b₃ + a₁b₂ + a₂b₁ + a₃b₀)`. -/
theorem toom4_recombine_int_h3 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    (toom4Interpolate720
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.2).2.2.2.1
      = 720 * (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) := by
  simp only [subProductsInt4, evalsInt4, toom4Interpolate720]
  ring

/-- **Toom-4 recombination, h₄ component.**  Equals
    `720·(a₁b₃ + a₂b₂ + a₃b₁)`. -/
theorem toom4_recombine_int_h4 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    (toom4Interpolate720
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.2).2.2.2.2.1
      = 720 * (a1 * b3 + a2 * b2 + a3 * b1) := by
  simp only [subProductsInt4, evalsInt4, toom4Interpolate720]
  ring

/-- **Toom-4 recombination, h₅ component.**  Equals `720·(a₂b₃ + a₃b₂)`. -/
theorem toom4_recombine_int_h5 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    (toom4Interpolate720
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.2).2.2.2.2.2.1
      = 720 * (a2 * b3 + a3 * b2) := by
  simp only [subProductsInt4, evalsInt4, toom4Interpolate720]
  ring

/-- **Toom-4 recombination, h₆ component.**  The leading coefficient
    `720 · a₃ b₃`. -/
theorem toom4_recombine_int_h6 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    (toom4Interpolate720
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.1
      (subProductsInt4 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.2).2.2.2.2.2.2
      = 720 * (a3 * b3) := by
  simp only [subProductsInt4, evalsInt4, toom4Interpolate720]

end CatCrypt.Crypto.SecureCompilation.ToomInterpolation
