/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `f255lit` of the secp256k1 base-field tree

`Nat.Prime f255lit` for the 128-bit factor
`f255lit = 255515944373312847190720520512484175977`, proved by a Lucas/Pratt
certificate with witness `3`. This is a leaf node: every prime factor of
`f255lit - 1` is below `2^32`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Secp256k1P.Node255

open CatCrypt.PrattCertificate

/-- Prime factor of the secp256k1 tree requiring a nested Lucas certificate. -/
def f255lit : Nat := 255515944373312847190720520512484175977

/-- Full prime factorization of `f255lit - 1`; product `= f255lit - 1`. -/
def f255Factors : List Nat := [2, 2, 2, 7, 7, 11, 1627, 2657, 4423, 41201, 96557, 7240687, 107590001]

theorem f255_prod : f255Factors.prod = f255lit - 1 := by decide

theorem f255_factors_prime : ∀ q ∈ f255Factors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem f255_fermat : powMod 3 (f255lit - 1) f255lit = 1 := by decide

theorem f255_witness :
    ∀ q ∈ f255Factors, powMod 3 ((f255lit - 1) / q) f255lit ≠ 1 := by
  decide

/-- `Nat.Prime f255lit`, machine-checked by a nested Lucas certificate. -/
theorem f255_prime : Nat.Prime f255lit :=
  lucas_of_certificate f255lit (by decide) 3 f255Factors
    f255_prod f255_factors_prime f255_fermat f255_witness

end CatCrypt.Crypto.Util.Secp256k1P.Node255
