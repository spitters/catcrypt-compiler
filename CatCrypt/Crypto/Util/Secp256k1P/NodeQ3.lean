/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.Secp256k1P.Node132
public import CatCrypt.Crypto.Util.Secp256k1P.Node255

/-!
# Lucas certificate node `q3lit` of the secp256k1 base-field tree

`Nat.Prime q3lit` for the 237-bit factor
`q3lit = 205115282021455665897114700593932402728804164701536103180137503955397371`,
proved by a Lucas/Pratt certificate with witness `10`. The factorization of
`q3lit - 1` uses the nested primes `f132lit` (`Node132`) and `f255lit`
(`Node255`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Secp256k1P.NodeQ3

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Secp256k1P.Node132
open CatCrypt.Crypto.Util.Secp256k1P.Node255

/-- Prime factor of the secp256k1 tree requiring a nested Lucas certificate. -/
def q3lit : Nat := 205115282021455665897114700593932402728804164701536103180137503955397371

/-- Prime factors of `q3lit - 1` below `2^32`. -/
def q3SmallFactors : List Nat := [2, 3, 5, 29, 29, 31, 7723]

/-- Full prime factorization of `q3lit - 1`; product `= q3lit - 1`. -/
def q3Factors : List Nat := q3SmallFactors ++ [f132lit, f255lit]

theorem q3_prod : q3Factors.prod = q3lit - 1 := by decide

theorem q3_small_prime : ∀ q ∈ q3SmallFactors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem q3_factors_prime : ∀ q ∈ q3Factors, Nat.Prime q := by
  intro q hq
  simp only [q3Factors, List.mem_append] at hq
  rcases hq with h | h
  · exact q3_small_prime q h
  · fin_cases h
    · exact f132_prime
    · exact f255_prime

theorem q3_fermat : powMod 10 (q3lit - 1) q3lit = 1 := by decide

theorem q3_witness :
    ∀ q ∈ q3Factors, powMod 10 ((q3lit - 1) / q) q3lit ≠ 1 := by
  decide

/-- `Nat.Prime q3lit`, machine-checked by a nested Lucas certificate. -/
theorem q3_prime : Nat.Prime q3lit :=
  lucas_of_certificate q3lit (by decide) 10 q3Factors
    q3_prod q3_factors_prime q3_fermat q3_witness

end CatCrypt.Crypto.Util.Secp256k1P.NodeQ3
