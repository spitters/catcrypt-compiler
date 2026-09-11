/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Tactic.Ring

/-!
# Ring-generic Karatsuba / Toom-2 recombination

The Karatsuba split multiplies two degree-1 "digits"
`A = a₀ + Bᵐ·a₁` and `B = b₀ + Bᵐ·b₁` from three products of the coefficients,
recombining them as `a₀b₀ + Bᵐ·(a₀b₁ + a₁b₀) + B²ᵐ·(a₁b₁)`.  The middle
coefficient `a₀b₁ + a₁b₀` is obtained from one extra multiplication,
`(a₀+a₁)(b₀+b₁) - a₀b₀ - a₁b₁`, giving the three-multiplication cost.

The same algebraic identity governs three domains that are proved separately
elsewhere in the workspace:

* integer limb multiplication over `ℕ`
  (`CatCrypt.Crypto.Jasmin.Mpn.KaratsubaPrototype.karatsuba_recombine`),
* polynomial multiplication (`ToomCookEmit.toomCook3_eq_schoolbook`'s Toom-2
  specialisation), and
* quadratic field-extension multiplication (`Fp2` towers).

This module states the recombination once over an arbitrary commutative ring
and exhibits the per-domain forms as instances, so the three strands are one
identity rather than three.

## Main results

* `karatsuba_recombine_ring` — the recombination in additive middle form.
* `karatsuba_recombine_ring_sub` — the recombination in three-multiplication
  (subtractive) middle form.
* `karatsuba_mid_eq` — the three-multiplication saving `(a₀+a₁)(b₀+b₁) -
  a₀b₀ - a₁b₁ = a₀b₁ + a₁b₀`.
* `karatsuba_recombine_int`, `karatsuba_recombine_nat` — integer instances; the
  `ℕ` form is the truncating-subtraction shadow of the `ℤ` identity.
* `karatsuba_recombine_poly` — the polynomial instance over `Polynomial R`.
* `karatsubaStep`, `karatsubaStep_eval` — the degree-1 recombination core as a
  function on coefficients together with its evaluation-at-a-point correctness.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.KaratsubaRingCore

open Polynomial

/-! ## The ring-generic recombination -/

/-- The three-multiplication saving: over any commutative ring the middle
    coefficient `a₀b₁ + a₁b₀` equals `(a₀+a₁)(b₀+b₁) - a₀b₀ - a₁b₁`, which uses
    one multiplication in place of two. -/
theorem karatsuba_mid_eq {R : Type*} [CommRing R] (a0 a1 b0 b1 : R) :
    (a0 + a1) * (b0 + b1) - a0 * b0 - a1 * b1 = a0 * b1 + a1 * b0 := by
  ring

/-- **The Karatsuba recombination, additive middle form.**  For a base `Bm`,
    `(a₀ + Bm·a₁)(b₀ + Bm·b₁) = a₀b₀ + Bm·(a₀b₁ + a₁b₀) + Bm²·(a₁b₁)`. -/
theorem karatsuba_recombine_ring {R : Type*} [CommRing R] (a0 a1 b0 b1 Bm : R) :
    (a0 + Bm * a1) * (b0 + Bm * b1)
      = a0 * b0 + Bm * (a0 * b1 + a1 * b0) + Bm * Bm * (a1 * b1) := by
  ring

/-- **The Karatsuba recombination, three-multiplication (subtractive) middle
    form.**  The middle coefficient is written as
    `(a₀+a₁)(b₀+b₁) - a₀b₀ - a₁b₁`; over a general ring this is ring
    subtraction, not the truncating subtraction of the `ℕ` form. -/
theorem karatsuba_recombine_ring_sub {R : Type*} [CommRing R] (a0 a1 b0 b1 Bm : R) :
    (a0 + Bm * a1) * (b0 + Bm * b1)
      = a0 * b0 + Bm * ((a0 + a1) * (b0 + b1) - a0 * b0 - a1 * b1)
          + Bm * Bm * (a1 * b1) := by
  ring

/-! ## Integer instances -/

/-- Integer instance of `karatsuba_recombine_ring` at `R := ℤ`. -/
theorem karatsuba_recombine_int (a0 a1 b0 b1 Bm : ℤ) :
    (a0 + Bm * a1) * (b0 + Bm * b1)
      = a0 * b0 + Bm * (a0 * b1 + a1 * b0) + Bm * Bm * (a1 * b1) :=
  karatsuba_recombine_ring a0 a1 b0 b1 Bm

/-- The `ℕ` form of the recombination, in subtractive middle form.  Over `ℕ` the
    subtraction is truncating, so the middle bracket is proved equal to
    `a₀b₁ + a₁b₀` from `(a₀+a₁)(b₀+b₁) ≥ a₀b₀ + a₁b₁` before recombining.  This
    is the truncating-subtraction shadow of `karatsuba_recombine_int`; it is the
    identity proved directly over limbs in
    `Jasmin.Mpn.KaratsubaPrototype.karatsuba_recombine`. -/
theorem karatsuba_recombine_nat (a0 a1 b0 b1 Bm : ℕ) :
    (a0 + Bm * a1) * (b0 + Bm * b1)
      = a0 * b0 + Bm * ((a0 + a1) * (b0 + b1) - a0 * b0 - a1 * b1)
          + Bm * Bm * (a1 * b1) := by
  have hmid : (a0 + a1) * (b0 + b1) - a0 * b0 - a1 * b1 = a0 * b1 + a1 * b0 := by
    have hexpand : (a0 + a1) * (b0 + b1) = a0 * b0 + a0 * b1 + a1 * b0 + a1 * b1 := by
      ring
    omega
  rw [hmid]; ring

/-! ## Polynomial instance -/

/-- Polynomial instance of `karatsuba_recombine_ring` at `R := Polynomial R`.
    This is the ring-generic content of the Toom-2 specialisation of
    `ToomCookEmit.toomCook3_eq_schoolbook`: with the base `Bm = X^m` the split
    digits are the low/high halves of a polynomial and the recombination is the
    schoolbook product of two two-chunk polynomials. -/
theorem karatsuba_recombine_poly {R : Type*} [CommRing R]
    (a0 a1 b0 b1 Bm : Polynomial R) :
    (a0 + Bm * a1) * (b0 + Bm * b1)
      = a0 * b0 + Bm * (a0 * b1 + a1 * b0) + Bm * Bm * (a1 * b1) :=
  karatsuba_recombine_ring a0 a1 b0 b1 Bm

/-- Field-extension shape: `karatsuba_recombine_ring` at `R := ZMod q`, the
    coefficient ring of a quadratic `Fp2` tower. -/
theorem karatsuba_recombine_zmod (q : ℕ) (a0 a1 b0 b1 Bm : ZMod q) :
    (a0 + Bm * a1) * (b0 + Bm * b1)
      = a0 * b0 + Bm * (a0 * b1 + a1 * b0) + Bm * Bm * (a1 * b1) :=
  karatsuba_recombine_ring a0 a1 b0 b1 Bm

/-! ## The degree-1 recombination core

The recombination as a function on coefficients: `karatsubaStep` maps the four
input coefficients (and the base) to the three output coefficients using three
multiplications, and `karatsubaStep_eval` states that evaluating the output
digit at the base equals the product of the two input digits.  This is the
one-level (degree-1) case of the general convolution core. -/

/-- The three output coefficients `(c₀, c₁, c₂)` of the degree-1 Karatsuba
    recombination, computed from three products `a₀b₀`, `(a₀+a₁)(b₀+b₁)`,
    `a₁b₁`. -/
def karatsubaStep {R : Type*} [CommRing R] (a0 a1 b0 b1 : R) : R × R × R :=
  let z0 := a0 * b0
  let z2 := a1 * b1
  let z1 := (a0 + a1) * (b0 + b1) - z0 - z2
  (z0, z1, z2)

/-- Evaluate a three-coefficient result `(c₀, c₁, c₂)` at the base `Bm` as the
    degree-2 digit `c₀ + Bm·c₁ + Bm²·c₂`. -/
def evalTriple {R : Type*} [CommRing R] (Bm : R) (c : R × R × R) : R :=
  c.1 + Bm * c.2.1 + Bm * Bm * c.2.2

/-- Correctness of the degree-1 recombination core: evaluating
    `karatsubaStep a₀ a₁ b₀ b₁` at the base `Bm` equals the product of the two
    input digits `(a₀ + Bm·a₁)(b₀ + Bm·b₁)`. -/
theorem karatsubaStep_eval {R : Type*} [CommRing R] (a0 a1 b0 b1 Bm : R) :
    evalTriple Bm (karatsubaStep a0 a1 b0 b1)
      = (a0 + Bm * a1) * (b0 + Bm * b1) := by
  simp only [karatsubaStep, evalTriple]
  ring

end CatCrypt.Crypto.SecureCompilation.KaratsubaRingCore
