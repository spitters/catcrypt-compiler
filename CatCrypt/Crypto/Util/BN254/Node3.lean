/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate
import CatCrypt.Crypto.Util.BN254.Node2

/-!
# BN254 primality certificate — nested factor node `pf3`

Lucas certificate for the nested prime factor
`13427688667394608761327070753331941386769` in the BN254 base-field prime
chain, using the sub-certificate `pf2` from `Node2`. The modulus exceeds
`2^64`, so the Fermat and witness checks stay on `native_decide`; the product
check reduces by `decide`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.BN254.Node3

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BN254.Node2

/-- Nested prime factor `13427688667394608761327070753331941386769`
    (`134`-bit). `N - 1 = 2^4 · 3 · 7 · 11 · 1853641 · 4562087 · 173171039 · 2480874801745591`. -/
def pf3 : Nat := 13427688667394608761327070753331941386769

/-- The `< 2^32` prime factors of `pf3 - 1` (with multiplicity). -/
def pf3Small : List Nat := List.replicate 4 2 ++ [3, 7, 11, 1853641, 4562087, 173171039]

/-- All prime factors of `pf3 - 1`, with multiplicity; product is `pf3 - 1`. -/
def pf3Factors : List Nat :=
  pf3Small ++ [pf2]

theorem pf3_prod : pf3Factors.prod = pf3 - 1 := by decide

theorem pf3_smallPrime : ∀ q ∈ pf3Small, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem pf3_primeFactors : ∀ q ∈ pf3Factors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact pf3_smallPrime q h
  · fin_cases h
    · exact pf2_prime

theorem pf3_fermat : powMod 17 (pf3 - 1) pf3 = 1 := by native_decide

theorem pf3_witness :
    ∀ q ∈ pf3Factors, powMod 17 ((pf3 - 1) / q) pf3 ≠ 1 := by
  native_decide

/-- `Nat.Prime pf3`, machine-checked by a Lucas certificate (witness `17`). -/
theorem pf3_prime : Nat.Prime pf3 :=
  lucas_of_certificate pf3 (by decide) 17 pf3Factors
    pf3_prod pf3_primeFactors pf3_fermat pf3_witness

end CatCrypt.Crypto.Util.BN254.Node3
