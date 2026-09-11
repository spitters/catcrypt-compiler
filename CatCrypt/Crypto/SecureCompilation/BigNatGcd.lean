/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.BigNatDivMod

/-!
# Euclidean `gcd` on the `BigNat` carrier

Carrier-level greatest common divisor on the little-endian limb-list carrier
`bignumVal`, computed by the Euclidean algorithm over the verified carrier
`mod` (`BigNatDivMod.mod`). The recursion mirrors `Nat.gcd_rec`
(`Nat.gcd m n = Nat.gcd (n % m) m`), so the value spec is a one-to-one
induction on the same recursion.

## Main results

* `gcd` — carrier Euclid: `gcd a b = b` when `bignumVal a = 0`, else
  `gcd (mod b a) a`, by well-founded recursion decreasing on `bignumVal a`.
* `gcd_val` — `bignumVal (gcd a b) = Nat.gcd (bignumVal a) (bignumVal b)`, for
  arbitrary operands.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNatGcd

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.BigNatDivMod (mod mod_val)

/-- Carrier Euclidean `gcd`: `b` when the first operand is zero, else the
    recursion `gcd (mod b a) a` on the remainder. Decreases on `bignumVal a`. -/
def gcd (a b : List (BitVec 64)) : List (BitVec 64) :=
  if bignumVal a = 0 then b else gcd (mod b a) a
  termination_by bignumVal a
  decreasing_by
    rename_i h
    rw [mod_val]
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- **`gcd` value spec.** `bignumVal (gcd a b) = Nat.gcd (bignumVal a)
    (bignumVal b)`, mirroring `Nat.gcd_rec` on the carrier recursion. -/
theorem gcd_val (a b : List (BitVec 64)) :
    bignumVal (gcd a b) = Nat.gcd (bignumVal a) (bignumVal b) := by
  rw [gcd]
  by_cases h : bignumVal a = 0
  · rw [if_pos h, h, Nat.gcd_zero_left]
  · rw [if_neg h]
    have hlt : bignumVal (mod b a) < bignumVal a := by
      rw [mod_val]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)
    rw [gcd_val (mod b a) a, mod_val, Nat.gcd_rec (bignumVal a) (bignumVal b)]
  termination_by bignumVal a
  decreasing_by
    rw [mod_val]
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

end CatCrypt.Crypto.SecureCompilation.BigNatGcd
