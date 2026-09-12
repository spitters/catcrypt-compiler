/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `g297lit` of the secp256k1 group-order tree

`Nat.Prime g297lit` for the factor `g297lit = 297159362677`, proved by a
Lucas/Pratt certificate with witness `2`. This is a leaf node whose modulus is
below `2^64`, so the Fermat and witness checks are discharged by `decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Secp256k1N.Node297

open CatCrypt.PrattCertificate

/-- Prime factor of the secp256k1 tree requiring a nested Lucas certificate. -/
def g297lit : Nat := 297159362677

/-- Full prime factorization of `g297lit - 1`; product `= g297lit - 1`. -/
def g297Factors : List Nat := [2, 2, 3, 3, 11, 461, 1627771]

theorem g297_prod : g297Factors.prod = g297lit - 1 := by decide

theorem g297_factors_prime : ∀ q ∈ g297Factors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem g297_fermat : powMod 2 (g297lit - 1) g297lit = 1 := by decide

theorem g297_witness :
    ∀ q ∈ g297Factors, powMod 2 ((g297lit - 1) / q) g297lit ≠ 1 := by decide

/-- `Nat.Prime g297lit`, machine-checked by a nested Lucas certificate. -/
theorem g297_prime : Nat.Prime g297lit :=
  lucas_of_certificate g297lit (by decide) 2 g297Factors
    g297_prod g297_factors_prime g297_fermat g297_witness

end CatCrypt.Crypto.Util.Secp256k1N.Node297
