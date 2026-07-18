/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Generic modular inversion — the correctness core

This file develops **modular inversion** generically, over an arbitrary modulus
`n`, proving the single property every concrete inversion kernel realizes: for
`a` coprime to `n`, the inverse `a⁻¹` satisfies

```
a * a⁻¹ ≡ 1 [MOD n]
```

This is the abstract correctness target of the safegcd / Fermat inversion
kernels (constant-time modular inverse in field arithmetic). Both routes are
captured:

* **Bézout / extended Euclid** (`modInvBezout`): the extended Euclidean
  algorithm computes integers `s, t` with `gcd a n = a*s + n*t`. When `a` is
  coprime to `n` the gcd is `1`, so `a*s ≡ 1 [ZMOD n]`. The Bézout coefficient
  `s` *is* the modular inverse. We obtain it from
  `Int.gcd_eq_gcd_ab : ↑(Int.gcd a b) = a * Int.gcdA a b + b * Int.gcdB a b`.

* **`ZMod` unit inverse** (`zmod_mul_inv_of_coprime`): in the ring `ZMod n`, a
  coprime element is a unit, and `ZMod.inv` provides its two-sided inverse via
  `ZMod.coe_mul_inv_eq_one`. This is the algebraic shadow of the same fact.

Worked example: `3⁻¹ mod 7 = 5`, since `3 * 5 = 15 ≡ 1 [MOD 7]`
(`modInv_example` below).
-/

namespace CatCrypt.Crypto.Optimizer.Rewrite.ModInverseGeneric

/-! ## Bézout route (extended Euclid) -/

/-- The modular inverse of `a` modulo `n`, defined as the Bézout coefficient of
`a` produced by the extended Euclidean algorithm. When `a` is coprime to `n`
this satisfies `a * modInvBezout a n ≡ 1 [ZMOD n]` (see `modInvBezout_correct`). -/
def modInvBezout (a n : ℤ) : ℤ := Int.gcdA a n

/-- **Bézout correctness of modular inversion.** If `a` is coprime to `n`, the
Bézout coefficient is a left inverse of `a` modulo `n`:
`a * modInvBezout a n ≡ 1 [ZMOD n]`.

This is the integer-level correctness the extended-Euclid (safegcd) inversion
kernel realizes. -/
theorem modInvBezout_correct {a n : ℤ} (h : Int.gcd a n = 1) :
    a * modInvBezout a n ≡ 1 [ZMOD n] := by
  -- Bézout: ↑(gcd a n) = a * gcdA a n + n * gcdB a n.
  have hb := Int.gcd_eq_gcd_ab a n
  -- With gcd = 1 this reads 1 = a * gcdA + n * gcdB.
  rw [h] at hb
  -- 1 - a * gcdA = n * gcdB is divisible by n, which is exactly `≡ [ZMOD n]`.
  refine (Int.modEq_iff_dvd.mpr ?_).symm
  refine ⟨-(Int.gcdB a n), ?_⟩
  unfold modInvBezout
  push_cast at hb ⊢
  linarith [hb]

/-! ## `ZMod` route (unit inverse) -/

/-- **`ZMod` correctness of modular inversion.** If `a` is coprime to `n`, then
its image in `ZMod n` has `ZMod.inv` as a two-sided inverse:
`(a : ZMod n) * (a : ZMod n)⁻¹ = 1`.

This is the algebraic shadow of `modInvBezout_correct`; the Fermat-power
inversion kernel realizes this `ZMod`-level statement. -/
theorem zmod_mul_inv_of_coprime {n : ℕ} {a : ℕ} (h : Nat.Coprime a n) :
    (a : ZMod n) * (a : ZMod n)⁻¹ = 1 := by
  rw [ZMod.coe_mul_inv_eq_one a h]

/-! ## Worked example -/

/-- `3⁻¹ ≡ 5 [MOD 7]`, since `3 * 5 = 15 ≡ 1 [MOD 7]`. The `ZMod 7` inverse of
`3` is `5`. -/
example : (3 : ZMod 7) * (3 : ZMod 7)⁻¹ = 1 :=
  zmod_mul_inv_of_coprime (by decide)

/-- The Bézout inverse of `3` modulo `7` is a left inverse: `3 * 3⁻¹ ≡ 1 [ZMOD 7]`. -/
example : (3 : ℤ) * modInvBezout 3 7 ≡ 1 [ZMOD 7] :=
  modInvBezout_correct (by decide)

end CatCrypt.Crypto.Optimizer.Rewrite.ModInverseGeneric
