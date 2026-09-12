/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `g174lit` of the secp256k1 group-order tree

`Nat.Prime g174lit` for the factor `g174lit = 174723607534414371449`, proved by
a Lucas/Pratt certificate with witness `3`. This is a leaf node: every prime
factor of `g174lit - 1` is below `2^32`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Secp256k1N.Node174

open CatCrypt.PrattCertificate

/-- Prime factor of the secp256k1 tree requiring a nested Lucas certificate. -/
def g174lit : Nat := 174723607534414371449

/-- Full prime factorization of `g174lit - 1`; product `= g174lit - 1`. -/
def g174Factors : List Nat := [2, 2, 2, 17, 59, 4051, 120233, 44706919]

theorem g174_prod : g174Factors.prod = g174lit - 1 := by decide

theorem g174_factors_prime : ∀ q ∈ g174Factors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem g174_fermat : powMod 3 (g174lit - 1) g174lit = 1 := by decide

theorem g174_witness :
    ∀ q ∈ g174Factors, powMod 3 ((g174lit - 1) / q) g174lit ≠ 1 := by
  decide

/-- `Nat.Prime g174lit`, machine-checked by a nested Lucas certificate. -/
theorem g174_prime : Nat.Prime g174lit :=
  lucas_of_certificate g174lit (by decide) 3 g174Factors
    g174_prod g174_factors_prime g174_fermat g174_witness

end CatCrypt.Crypto.Util.Secp256k1N.Node174
