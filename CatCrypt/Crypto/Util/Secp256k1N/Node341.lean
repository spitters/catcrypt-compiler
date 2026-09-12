/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.Secp256k1N.Node290

/-!
# Lucas certificate node `g341lit` of the secp256k1 group-order tree

`Nat.Prime g341lit` for the factor
`g341lit = 341948486974166000522343609283189`, proved by a Lucas/Pratt
certificate with witness `2`. The factorization of `g341lit - 1` uses the
nested prime `g290lit` from `Node290`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Secp256k1N.Node341

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Secp256k1N.Node290

/-- Prime factor of the secp256k1 tree requiring a nested Lucas certificate. -/
def g341lit : Nat := 341948486974166000522343609283189

/-- Prime factors of `g341lit - 1` below `2^32`. -/
def g341SmallFactors : List Nat := [2, 2, 3, 3, 3, 109]

/-- Full prime factorization of `g341lit - 1`; product `= g341lit - 1`. -/
def g341Factors : List Nat := g341SmallFactors ++ [g290lit]

theorem g341_prod : g341Factors.prod = g341lit - 1 := by decide

theorem g341_small_prime : ∀ q ∈ g341SmallFactors, Nat.Prime q := by decide

theorem g341_factors_prime : ∀ q ∈ g341Factors, Nat.Prime q := by
  intro q hq
  simp only [g341Factors, List.mem_append] at hq
  rcases hq with h | h
  · exact g341_small_prime q h
  · fin_cases h
    · exact g290_prime

theorem g341_fermat : powMod 2 (g341lit - 1) g341lit = 1 := by decide

theorem g341_witness :
    ∀ q ∈ g341Factors, powMod 2 ((g341lit - 1) / q) g341lit ≠ 1 := by
  decide

/-- `Nat.Prime g341lit`, machine-checked by a nested Lucas certificate. -/
theorem g341_prime : Nat.Prime g341lit :=
  lucas_of_certificate g341lit (by decide) 2 g341Factors
    g341_prod g341_factors_prime g341_fermat g341_witness

end CatCrypt.Crypto.Util.Secp256k1N.Node341
