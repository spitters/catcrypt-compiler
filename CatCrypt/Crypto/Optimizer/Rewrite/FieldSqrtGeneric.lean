/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Modular square roots over a finite field (generic)

This module is the field-theoretic foundation of **elliptic-curve point
decompression**: recovering `y` from a compressed point `(x, sign(y))` requires
computing a modular square root of `y² = x³ + a·x + b` in the base field
`ZMod p`.

Two deliverables, both grounded in Mathlib:

* **Euler's criterion** (`isSquare_iff_pow`): a nonzero `a : ZMod p` is a square
  iff `a ^ ((p - 1) / 2) = 1`.  This is a thin re-export of Mathlib's
  `ZMod.euler_criterion` (whose exponent `p / 2` equals `(p - 1) / 2` for odd
  `p`), giving the quadratic-residue test used to decide whether a compressed
  point lies on the curve.

* **The closed-form square root for `p ≡ 3 (mod 4)`** (`sqrt3mod4`,
  `sqrt3mod4_correct`): when `p ≡ 3 (mod 4)`, a square root of a residue `a`
  is `a ^ ((p + 1) / 4)`.  Many cryptographic primes satisfy `p ≡ 3 (mod 4)`
  (e.g. the base-field prime of `secp256k1`), so this closed form replaces the
  general Tonelli–Shanks algorithm.

## Correctness of the closed form

Write `e = (p + 1) / 4`.  For `p ≡ 3 (mod 4)` the divisions are exact, so
`2 * e = (p + 1) / 2` and `(p + 1) / 2 = 1 + (p - 1) / 2`.  Hence

```
(a ^ e) ^ 2 = a ^ (2 * e) = a ^ (1 + (p - 1) / 2) = a * a ^ ((p - 1) / 2).
```

If `a` is a (nonzero) square, Euler's criterion gives `a ^ ((p - 1) / 2) = 1`,
so `(a ^ e) ^ 2 = a`.  The zero case is immediate (`0 ^ e = 0`).
-/

namespace CatCrypt.Crypto.Optimizer.Rewrite.FieldSqrtGeneric

open scoped Classical

variable (p : ℕ) [Fact (Nat.Prime p)]

/-! ### Euler's criterion (quadratic-residue test) -/

/-- For an odd natural number `p`, `p / 2 = (p - 1) / 2` (`Nat` division). -/
private theorem odd_div_two_eq (n : ℕ) (hodd : n % 2 = 1) : n / 2 = (n - 1) / 2 := by
  omega

/-- **Euler's criterion**, re-exported in the `(p - 1) / 2` exponent form: a
nonzero `a : ZMod p` is a square iff `a ^ ((p - 1) / 2) = 1`.

The statement uses the cryptographically standard exponent `(p - 1) / 2`; it
agrees with Mathlib's `ZMod.euler_criterion` (exponent `p / 2`) because `p` is
an odd prime. -/
theorem isSquare_iff_pow {a : ZMod p} (ha : a ≠ 0) :
    IsSquare a ↔ a ^ ((p - 1) / 2) = 1 := by
  rcases (Fact.out (p := p.Prime)).eq_two_or_odd with hp2 | hodd
  · -- `p = 2`: in `ZMod 2` every nonzero element is `1`, hence a square; the
    -- right-hand exponent `(2 - 1) / 2 = 0` makes the power `1` as well.
    subst hp2
    have ha1 : a = 1 := by
      have := ZMod.val_lt a
      interval_cases h : a.val
      · exact absurd ((ZMod.val_eq_zero a).mp h) ha
      · exact (ZMod.natCast_zmod_val a).symm.trans (by rw [h]; rfl)
    subst ha1
    simp
  · rw [ZMod.euler_criterion p ha, odd_div_two_eq p hodd]

/-! ### Closed-form square root for `p ≡ 3 (mod 4)` -/

/-- The explicit modular square root used when `p ≡ 3 (mod 4)`:
`sqrt3mod4 a = a ^ ((p + 1) / 4)`. -/
def sqrt3mod4 (a : ZMod p) : ZMod p := a ^ ((p + 1) / 4)

/-- **Correctness of the `p ≡ 3 (mod 4)` closed form.** If `p ≡ 3 (mod 4)` and
`a : ZMod p` is a square, then `(sqrt3mod4 p a) ^ 2 = a`. -/
theorem sqrt3mod4_correct (hp4 : p % 4 = 3) {a : ZMod p} (hsq : IsSquare a) :
    (sqrt3mod4 p a) ^ 2 = a := by
  rcases eq_or_ne a 0 with rfl | ha
  · -- zero case: `0 ^ e ^ 2 = 0`
    have hpos : 0 < (p + 1) / 4 := by omega
    simp [sqrt3mod4, zero_pow hpos.ne']
  · -- nonzero square: use Euler's criterion
    have heuler : a ^ ((p - 1) / 2) = 1 := (isSquare_iff_pow p ha).mp hsq
    have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_lt.le
    -- exponent arithmetic: `2 * ((p+1)/4) = 1 + (p-1)/2`
    have hexp : 2 * ((p + 1) / 4) = 1 + (p - 1) / 2 := by omega
    calc (sqrt3mod4 p a) ^ 2
        = a ^ (2 * ((p + 1) / 4)) := by
          rw [sqrt3mod4, ← pow_mul, Nat.mul_comm]
      _ = a ^ (1 + (p - 1) / 2) := by rw [hexp]
      _ = a ^ 1 * a ^ ((p - 1) / 2) := by rw [pow_add]
      _ = a := by rw [heuler, pow_one, mul_one]

end CatCrypt.Crypto.Optimizer.Rewrite.FieldSqrtGeneric
