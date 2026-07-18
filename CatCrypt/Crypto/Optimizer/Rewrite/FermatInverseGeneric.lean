/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Fermat constant-time modular inverse (generic correctness certificate)

Cryptographic field arithmetic needs a **constant-time** modular inverse. The
safegcd / Bezout inverse (see `ModInverseGeneric`) is variable-time: its control
flow branches on the input data. The constant-time alternative is Fermat's
little theorem — in `ZMod p` for prime `p`, the inverse of a nonzero `a` is the
fixed exponentiation `a ^ (p - 2)`, with no data-dependent branching:

`a⁻¹ = a ^ (p - 2)`   (for `a ≠ 0`).

This file is the generic correctness certificate underwriting the CT-inverse
rewrite: `fermatInv` computes `a ^ (p - 2)` and we prove it cancels `a` and
agrees with the field inverse `a⁻¹` on nonzero inputs.
-/

namespace CatCrypt.Crypto.Optimizer.Rewrite.FermatInverseGeneric

variable (p : ℕ) [Fact p.Prime]

/-- The Fermat constant-time inverse: a fixed exponentiation `a ^ (p - 2)`,
with no data-dependent control flow. -/
def fermatInv (a : ZMod p) : ZMod p := a ^ (p - 2)

/-- `a * a ^ (p - 2) = 1` for nonzero `a`, by Fermat's little theorem
(`a ^ (p - 1) = 1`) together with `1 + (p - 2) = p - 1` for primes `p ≥ 2`. -/
theorem fermatInv_mul_cancel {a : ZMod p} (ha : a ≠ 0) :
    a * fermatInv p a = 1 := by
  unfold fermatInv
  have h2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  calc a * a ^ (p - 2) = a ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
    _ = 1 := ZMod.pow_card_sub_one_eq_one ha

/-- The Fermat inverse agrees with the field inverse on nonzero inputs. -/
theorem fermatInv_eq_inv {a : ZMod p} (ha : a ≠ 0) :
    fermatInv p a = a⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact fermatInv_mul_cancel p ha)

/-- `fermatInv p 0 = 0`, so the rewrite is total on nonzero inputs and maps `0`
to `0`. This requires `p ≠ 2`: at `p = 2` we have `p - 2 = 0` and `0 ^ 0 = 1`,
so `fermatInv 2 0 = 1 ≠ 0`. Every odd prime (indeed every prime `≠ 2`) is fine. -/
theorem fermatInv_zero (hp : p ≠ 2) : fermatInv p (0 : ZMod p) = 0 := by
  unfold fermatInv
  have h2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [zero_pow (by omega : p - 2 ≠ 0)]

/-- The Fermat inverse is multiplicative, since it is a fixed power. -/
theorem fermatInv_mul (a b : ZMod p) :
    fermatInv p (a * b) = fermatInv p a * fermatInv p b := by
  unfold fermatInv
  rw [mul_pow]

end CatCrypt.Crypto.Optimizer.Rewrite.FermatInverseGeneric
