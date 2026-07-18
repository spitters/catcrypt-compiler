/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Generic Legendre symbol — the quadratic-residue test

This file re-exports Mathlib's Legendre symbol (`legendreSym`) as the clean
**quadratic-residue (QR) test** interface used by constant-time field-arithmetic
kernels. The Legendre symbol underlies the *sign decision* in point
decompression (recovering the `y`-coordinate from `x` on an elliptic curve
requires testing whether `x³ + ax + b` is a square) and in hash-to-curve
(map-to-curve picks a representative based on quadratic residuosity). A
constant-time QR test is exactly the Euler-criterion exponentiation
`a^((p-1)/2)`, so the abstract specification that every such kernel realizes is
the cluster of identities below.

For a prime `p` (carried as `[Fact p.Prime]`) and `a : ℤ`, `legendreSym p a` is

* `0` if `a ≡ 0 [ZMOD p]`,
* `1` if `a` is a nonzero square mod `p` (a quadratic residue),
* `-1` otherwise (a quadratic non-residue).

We package the four properties a QR-test kernel must satisfy:

* `legendre_eq_pow` — **Euler's criterion (computation form)**: the symbol equals
  `a^(p/2)` in `ZMod p`. Since `p / 2 = (p - 1) / 2` for an odd prime, this is
  the constant-time exponentiation the kernel actually runs.
* `legendre_one_iff_QR` — the symbol is `1` iff `a` is a square mod `p` (given
  `a ≢ 0`): the QR test is *correct*.
* `legendre_mul` — **multiplicativity** (the homomorphism property): a product
  is a residue iff the factors agree in residuosity. This is what lets the
  test be precomputed/blinded.
* `legendre_neg_one` — the QR-of-`(-1)` law, `legendreSym p (-1) = χ₄ p`, which
  evaluates to `1` exactly when `p ≡ 1 [MOD 4]`. This governs the `±y` sign in
  decompression on curves over such fields.

Worked example: `legendreSym 7 2 = 1` (since `3² = 9 ≡ 2 [MOD 7]`, so `2` is a
QR mod `7`) and `legendreSym 7 3 = -1` (`3` is a non-residue mod `7`).
-/

namespace CatCrypt.Crypto.Optimizer.Rewrite.LegendreSymbolGeneric

open scoped NumberTheorySymbols

variable (p : ℕ) [Fact p.Prime]

/-- **Euler's criterion, computation form.** The Legendre symbol of `a` equals
the constant-time exponentiation `a ^ (p / 2)`, computed in `ZMod p`. For an odd
prime `p`, `p / 2 = (p - 1) / 2`, so this is precisely the exponent a QR-test
kernel raises to. Wraps `legendreSym.eq_pow`. -/
theorem legendre_eq_pow (a : ℤ) :
    (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2) :=
  legendreSym.eq_pow p a

/-- **Correctness of the QR test.** For `a` not divisible by `p`, the Legendre
symbol is `1` iff `a` is a quadratic residue mod `p`. Wraps
`legendreSym.eq_one_iff`. -/
theorem legendre_one_iff_QR {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    legendreSym p a = 1 ↔ IsSquare (a : ZMod p) :=
  legendreSym.eq_one_iff p ha

/-- **Multiplicativity (homomorphism property).** The Legendre symbol of a
product is the product of the Legendre symbols. Wraps `legendreSym.mul`. -/
theorem legendre_mul (a b : ℤ) :
    legendreSym p (a * b) = legendreSym p a * legendreSym p b :=
  legendreSym.mul p a b

/-- **QR of `-1`.** The Legendre symbol of `-1` is `χ₄ p`, which is `1` exactly
when `p ≡ 1 [MOD 4]`. This governs the sign choice in point decompression over
fields where `-1` is (or is not) a square. Wraps `legendreSym.at_neg_one`. -/
theorem legendre_neg_one (hp : p ≠ 2) :
    legendreSym p (-1) = ZMod.χ₄ (p : ZMod 4) :=
  legendreSym.at_neg_one hp

/-! ### Worked example: residuosity mod 7

`2` is a quadratic residue mod `7` (`3² = 9 ≡ 2`), so its Legendre symbol is `1`;
`3` is a non-residue, so its symbol is `-1`. These are decided by `decide`
through Mathlib's `norm_num` extension for `legendreSym`. -/

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

example : legendreSym 7 2 = 1 := by decide

example : legendreSym 7 3 = -1 := by decide

end CatCrypt.Crypto.Optimizer.Rewrite.LegendreSymbolGeneric
