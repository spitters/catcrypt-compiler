/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Data.ZMod.Defs


@[expose] public section
set_option autoImplicit false

/-!
# `poly_zp` empirical baseline

Test cases for the algebraic layers of the `poly_zp` tactic over
`ZMod (2^255 - 19)`.

## Contents

1. **`ring` over `ZMod (2^255 - 19)` closes 25-term schoolbook**
   expansions. Tier 0a (2-limb mul) and 0d (5-limb mul, 25 terms) each
   close with a single `ring` call.

2. **`(2 : Fp25519)^255 = 19` is proved by `native_decide`** in <1s;
   `decide` exceeds the recursion stack on this large-modulus identity.

3. **`linear_combination` with manual hints closes the full radix-2^51
   reduction identity**: Tier 2's `five_limb_radix51_mul_spec` states
   exactly the spec form that `mulBody_correct`'s algebraic side needs.

Reduction by `2^255 ≡ 19` (layer C) and the `ring` finish (layer D) are
therefore a single `linear_combination` call given the right hint.

## Scope

`poly_zp` also has two layers outside this module:

- **Layer A (bv_to_nat)**: lift BitVec-64 polynomial expressions (with
  `addCarry`, `mulx`, `bzhi`, `shrdImm`, `imulImm`) to Nat / `ZMod p`.
- **Layer B (carry-chain elimination)**: collapse ADCX/ADOX/ADD/ADC
  chains threading through the symbolic execution.
-/

namespace CatCrypt.Tactics.PolyZpTest

abbrev Fp25519 : Type := ZMod (2^255 - 19)

/-! ## Tier 0a: 2-limb mul over a *generic* CommRing — control case.

Control case: `ring` closes small polynomials over a general `CommRing`
quickly; the `ZMod p` cases add the elaboration cost of `ZMod p`
for `p = 2^255 - 19`. -/

example {R : Type} [CommRing R] (a₀ a₁ b₀ b₁ : R) :
    (a₀ + a₁ * 2^51) * (b₀ + b₁ * 2^51)
    = a₀ * b₀
      + (a₀ * b₁ + a₁ * b₀) * 2^51
      + a₁ * b₁ * 2^102 := by
  ring

/-! ## Tier 0b: 5-limb mul over a generic CommRing.

Tests whether the polynomial-expansion side of `ring` scales without
the ZMod p kernel-reduction overhead. -/

/-! ## Tier 0b': 3-limb mul with abstract base. -/

example {R : Type} [CommRing R] (a₀ a₁ a₂ b₀ b₁ b₂ x : R) :
    (a₀ + a₁ * x + a₂ * x^2) *
    (b₀ + b₁ * x + b₂ * x^2)
    = a₀ * b₀
      + (a₀ * b₁ + a₁ * b₀) * x
      + (a₀ * b₂ + a₁ * b₁ + a₂ * b₀) * x^2
      + (a₁ * b₂ + a₂ * b₁) * x^3
      + a₂ * b₂ * x^4 := by
  ring

/-! ## Tier 0c: 5-limb mul over abstract CommRing.

The full 5×5 = 25-term schoolbook product. -/

example {R : Type} [CommRing R] (a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ x : R) :
    (a₀ + a₁ * x + a₂ * x^2 + a₃ * x^3 + a₄ * x^4) *
    (b₀ + b₁ * x + b₂ * x^2 + b₃ * x^3 + b₄ * x^4)
    = a₀ * b₀
      + (a₀ * b₁ + a₁ * b₀) * x
      + (a₀ * b₂ + a₁ * b₁ + a₂ * b₀) * x^2
      + (a₀ * b₃ + a₁ * b₂ + a₂ * b₁ + a₃ * b₀) * x^3
      + (a₀ * b₄ + a₁ * b₃ + a₂ * b₂ + a₃ * b₁ + a₄ * b₀) * x^4
      + (a₁ * b₄ + a₂ * b₃ + a₃ * b₂ + a₄ * b₁) * x^5
      + (a₂ * b₄ + a₃ * b₃ + a₄ * b₂) * x^6
      + (a₃ * b₄ + a₄ * b₃) * x^7
      + a₄ * b₄ * x^8 := by
  ring

/-! ## Tier 0d: 5-limb mul over `Fp25519` with abstract base.

This is the realistic shape mulBody_correct will reduce to before the
`2^255 ≡ 19` reduction step. -/

example (a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ x : Fp25519) :
    (a₀ + a₁ * x + a₂ * x^2 + a₃ * x^3 + a₄ * x^4) *
    (b₀ + b₁ * x + b₂ * x^2 + b₃ * x^3 + b₄ * x^4)
    = a₀ * b₀
      + (a₀ * b₁ + a₁ * b₀) * x
      + (a₀ * b₂ + a₁ * b₁ + a₂ * b₀) * x^2
      + (a₀ * b₃ + a₁ * b₂ + a₂ * b₁ + a₃ * b₀) * x^3
      + (a₀ * b₄ + a₁ * b₃ + a₂ * b₂ + a₃ * b₁ + a₄ * b₀) * x^4
      + (a₁ * b₄ + a₂ * b₃ + a₃ * b₂ + a₄ * b₁) * x^5
      + (a₂ * b₄ + a₃ * b₃ + a₄ * b₂) * x^6
      + (a₃ * b₄ + a₄ * b₃) * x^7
      + a₄ * b₄ * x^8 := by
  ring

/-! ## Tier 0e: the `2^255 ≡ 19 (mod p)` reduction identity.

Layer C of `poly_zp` rests on this identity. `ring` does not prove it
(it is a non-polynomial fact about the specific modulus), so it is a
separate lemma proved by evaluation. -/

-- `decide` exceeds the recursion stack on a 255-bit power; `native_decide`
-- compiles to native code and runs in ms.
theorem two_pow_255_eq_19 : (2 : Fp25519)^255 = 19 := by
  native_decide

/-! ## Tier 1: complete pipeline on a 2-limb mul with mod-p reduction.

Combines:
- Polynomial expansion (Layer D — `ring`).
- The `2^255 ≡ 19` rewrite (Layer C).
- A small carry-chain elimination (Layer B — implicit; the inputs are
  already in `ZMod p`, so no carry tracking needed at this level).

Models a simplified version of what mulBody_correct's algebraic-side
identity looks like in miniature: prove a 2-limb-radix product equals
the schoolbook product modulo p.

The challenge is that the input limbs are radix-2^128 (not 2^51), so
the high digit `a₁ * b₁ * 2^256` reduces via `2^255 ≡ 19` to
`a₁ * b₁ * 38`. -/

theorem two_limb_radix128_mul_correct (a₀ a₁ b₀ b₁ : Fp25519) :
    (a₀ + a₁ * 2^128) * (b₀ + b₁ * 2^128)
    = a₀ * b₀
      + (a₀ * b₁ + a₁ * b₀) * 2^128
      + a₁ * b₁ * 2 * 19 := by
  -- Step 1: polynomial expansion gives `… + a₁·b₁·2^256` on the LHS.
  -- Step 2: rewrite `2^256 = 2 · 2^255 = 2 · 19 = 38` via two_pow_255_eq_19.
  -- Step 3: ring closes after the rewrite.
  have h : (2 : Fp25519)^256 = 38 := by
    rw [show (256 : ℕ) = 255 + 1 from rfl, pow_succ, two_pow_255_eq_19]
    ring
  -- Bring the LHS into a form where 2^256 appears explicitly.
  have lhs_expand :
      (a₀ + a₁ * 2^128) * (b₀ + b₁ * 2^128)
      = a₀ * b₀ + (a₀ * b₁ + a₁ * b₀) * 2^128 + a₁ * b₁ * 2^256 := by
    ring
  rw [lhs_expand, h]
  ring

/-! ## Tier 2: 5-limb radix-2^51 mul reduced modulo p.

This is the `carry_mul` algebraic spec — the schoolbook product
of two 5-limb radix-2^51 representations reduced via `2^255 ≡ 19`. It
exercises layer C followed by layer D at the polynomial level for the
`mulBody` scope. -/

/-- An abstract polynomial identity: 5-limb radix-`t` schoolbook
    multiplication, reduced via `t^5 = 19`. Pure ring identity in `t`,
    no specific characteristic of the ring beyond what `ring` proves. -/
theorem five_limb_abstract_mul_with_reduction
    {R : Type} [CommRing R] (a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ t : R)
    (h5 : t^5 = 19) :
    (a₀ + a₁ * t + a₂ * t^2 + a₃ * t^3 + a₄ * t^4) *
    (b₀ + b₁ * t + b₂ * t^2 + b₃ * t^3 + b₄ * t^4)
    = (a₀ * b₀ + 19 * (a₁ * b₄ + a₂ * b₃ + a₃ * b₂ + a₄ * b₁))
      + (a₀ * b₁ + a₁ * b₀
         + 19 * (a₂ * b₄ + a₃ * b₃ + a₄ * b₂)) * t
      + (a₀ * b₂ + a₁ * b₁ + a₂ * b₀
         + 19 * (a₃ * b₄ + a₄ * b₃)) * t^2
      + (a₀ * b₃ + a₁ * b₂ + a₂ * b₁ + a₃ * b₀
         + 19 * (a₄ * b₄)) * t^3
      + (a₀ * b₄ + a₁ * b₃ + a₂ * b₂ + a₃ * b₁ + a₄ * b₀) * t^4 := by
  -- `grobner` (in-kernel Gröbner-basis ideal membership, oracle-free)
  -- synthesises the reduction cofactors from `h5 : t^5 = 19` directly —
  -- no manual `linear_combination` hints, no derived `t^6/t^7/t^8` powers.
  grobner

/-- Concrete instance for `Fp25519` — Curve25519's radix-2^51 layout.
    Specialises the abstract lemma at `t := 2^51` using
    `(2^51)^5 = 2^255 = 19 (mod p)`. -/
theorem five_limb_radix51_mul_spec
    (a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : Fp25519) :
    (a₀ + a₁ * 2^51 + a₂ * (2^51)^2 + a₃ * (2^51)^3 + a₄ * (2^51)^4) *
    (b₀ + b₁ * 2^51 + b₂ * (2^51)^2 + b₃ * (2^51)^3 + b₄ * (2^51)^4)
    = (a₀ * b₀ + 19 * (a₁ * b₄ + a₂ * b₃ + a₃ * b₂ + a₄ * b₁))
      + (a₀ * b₁ + a₁ * b₀
         + 19 * (a₂ * b₄ + a₃ * b₃ + a₄ * b₂)) * 2^51
      + (a₀ * b₂ + a₁ * b₁ + a₂ * b₀
         + 19 * (a₃ * b₄ + a₄ * b₃)) * (2^51)^2
      + (a₀ * b₃ + a₁ * b₂ + a₂ * b₁ + a₃ * b₀
         + 19 * (a₄ * b₄)) * (2^51)^3
      + (a₀ * b₄ + a₁ * b₃ + a₂ * b₂ + a₃ * b₁ + a₄ * b₀) * (2^51)^4 := by
  have h5 : ((2 : Fp25519)^51)^5 = 19 := by
    rw [← pow_mul]; exact two_pow_255_eq_19
  exact five_limb_abstract_mul_with_reduction
    a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ ((2 : Fp25519)^51) h5

end CatCrypt.Tactics.PolyZpTest
