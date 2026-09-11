/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.BigNat

/-!
# BigNatPow: exponentiation on the `BigNat` carrier

Repeated-multiply exponentiation over the verified `BigNat` carrier `mul`
(`CatCrypt.Crypto.SecureCompilation.BigNat`). The abstraction function
`bignumVal` carries the carrier operation to `Nat` exponentiation.

## Main results

* `pow` — carrier exponentiation, `pow a 0 = ofNat 1` and
  `pow a (n+1) = mul (pow a n) a`.
* `pow_val` — `bignumVal (pow a n) = bignumVal a ^ n`.
* `pow_natPow` — the same equation stated with `Nat.pow`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BigNat

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-- Carrier exponentiation by repeated multiplication over the verified `mul`.
    The base case is the one-limb encoding of `1`; each step multiplies by the
    base. -/
def pow (a : List (BitVec 64)) : Nat → List (BitVec 64)
  | 0 => ofNat 1
  | n + 1 => mul (pow a n) a

theorem pow_zero (a : List (BitVec 64)) : pow a 0 = ofNat 1 := rfl

theorem pow_succ (a : List (BitVec 64)) (n : Nat) :
    pow a (n + 1) = mul (pow a n) a := rfl

/-- **Exponentiation.** `bignumVal (pow a n) = bignumVal a ^ n`. -/
theorem pow_val (a : List (BitVec 64)) :
    ∀ n : Nat, bignumVal (pow a n) = bignumVal a ^ n
  | 0 => by rw [pow_zero, toNat_ofNat, _root_.pow_zero]
  | n + 1 => by
      rw [pow_succ, mul_val, pow_val a n, _root_.pow_succ]

/-- `bignumVal (pow a n) = Nat.pow (bignumVal a) n`, the `Nat.pow` form of
    `pow_val`. -/
theorem pow_natPow (a : List (BitVec 64)) (n : Nat) :
    bignumVal (pow a n) = Nat.pow (bignumVal a) n := by
  rw [pow_val, Nat.pow_eq]

end CatCrypt.Crypto.SecureCompilation.BigNat
