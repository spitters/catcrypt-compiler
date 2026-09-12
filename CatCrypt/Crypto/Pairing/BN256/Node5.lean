/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public meta import CatCrypt.Crypto.Pairing.BN256.Node4
public import CatCrypt.Crypto.Pairing.BN256.Node4

/-!
# BN256 primality certificate — nested factor node `pf5`

Lucas certificate for the nested prime factor
`1374947842730272154058024133` in the BN256 base-field prime chain, using the
sub-certificate `pf4` from `Node4`. The modulus exceeds `2^64`, so the Fermat
and witness checks stay on `native_decide`; the product check reduces by
`decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Pairing.BN256.Node5

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Pairing.BN256.Node4

/-- Nested prime factor `1374947842730272154058024133`
    (`91`-bit). `N - 1 = 2^2 · 3 · 79 · 1187 · 3593 · 4159 · 81767558454161`. -/
def pf5 : Nat := 1374947842730272154058024133

/-- The `< 2^32` prime factors of `pf5 - 1` (with multiplicity). -/
def pf5Small : List Nat := List.replicate 2 2 ++ [3, 79, 1187, 3593, 4159]

/-- All prime factors of `pf5 - 1`, with multiplicity; product is `pf5 - 1`. -/
def pf5Factors : List Nat :=
  pf5Small ++ [pf4]

theorem pf5_prod : pf5Factors.prod = pf5 - 1 := by decide

theorem pf5_smallPrime : ∀ q ∈ pf5Small, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem pf5_primeFactors : ∀ q ∈ pf5Factors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact pf5_smallPrime q h
  · fin_cases h
    · exact pf4_prime

theorem pf5_fermat : powMod 2 (pf5 - 1) pf5 = 1 := by decide

theorem pf5_witness :
    ∀ q ∈ pf5Factors, powMod 2 ((pf5 - 1) / q) pf5 ≠ 1 := by
  decide

/-- `Nat.Prime pf5`, machine-checked by a Lucas certificate (witness `2`). -/
theorem pf5_prime : Nat.Prime pf5 :=
  lucas_of_certificate pf5 (by decide) 2 pf5Factors
    pf5_prod pf5_primeFactors pf5_fermat pf5_witness

end CatCrypt.Crypto.Pairing.BN256.Node5
