/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.Secp256k1N.Node297

/-!
# Lucas certificate node `g290lit` of the secp256k1 group-order tree

`Nat.Prime g290lit` for the factor `g290lit = 29047611873442575647497758179`,
proved by a Lucas/Pratt certificate with witness `2`. The factorization of
`g290lit - 1` uses the nested prime `g297lit` from `Node297`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Secp256k1N.Node290

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Secp256k1N.Node297

/-- Prime factor of the secp256k1 tree requiring a nested Lucas certificate. -/
def g290lit : Nat := 29047611873442575647497758179

/-- Prime factors of `g290lit - 1` below `2^32`. -/
def g290SmallFactors : List Nat := [2, 293, 305873, 545358713]

/-- Full prime factorization of `g290lit - 1`; product `= g290lit - 1`. -/
def g290Factors : List Nat := g290SmallFactors ++ [g297lit]

theorem g290_prod : g290Factors.prod = g290lit - 1 := by decide

theorem g290_small_prime : ∀ q ∈ g290SmallFactors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem g290_factors_prime : ∀ q ∈ g290Factors, Nat.Prime q := by
  intro q hq
  simp only [g290Factors, List.mem_append] at hq
  rcases hq with h | h
  · exact g290_small_prime q h
  · fin_cases h
    · exact g297_prime

theorem g290_fermat : powMod 2 (g290lit - 1) g290lit = 1 := by decide

theorem g290_witness :
    ∀ q ∈ g290Factors, powMod 2 ((g290lit - 1) / q) g290lit ≠ 1 := by
  decide

/-- `Nat.Prime g290lit`, machine-checked by a nested Lucas certificate. -/
theorem g290_prime : Nat.Prime g290lit :=
  lucas_of_certificate g290lit (by decide) 2 g290Factors
    g290_prod g290_factors_prime g290_fermat g290_witness

end CatCrypt.Crypto.Util.Secp256k1N.Node290
