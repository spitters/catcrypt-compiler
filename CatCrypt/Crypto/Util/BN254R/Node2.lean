/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public meta import CatCrypt.Crypto.Util.BN254R.Node1
public import CatCrypt.Crypto.Util.BN254R.Node1

/-!
# BN254 scalar-field certificate — nested factor node `pf2`

Lucas certificate for the nested prime factor `1670836401704629` in the BN254
scalar-field order chain, using the sub-certificate `pf1` from `Node1`. The
modulus is below `2^64`, so the Fermat, witness, and product checks reduce by
`decide` and only the small-factor primality uses `native_decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BN254R.Node2

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BN254R.Node1

/-- Nested prime factor `1670836401704629`
    (`51`-bit). `N - 1 = 2^2 · 3^4 · 5156902474397`. -/
def pf2 : Nat := 1670836401704629

/-- The `< 2^32` prime factors of `pf2 - 1` (with multiplicity). -/
def pf2Small : List Nat := List.replicate 2 2 ++ [3, 3, 3, 3]

/-- All prime factors of `pf2 - 1`, with multiplicity; product is `pf2 - 1`. -/
def pf2Factors : List Nat :=
  pf2Small ++ [pf1]

theorem pf2_prod : pf2Factors.prod = pf2 - 1 := by decide

theorem pf2_smallPrime : ∀ q ∈ pf2Small, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem pf2_primeFactors : ∀ q ∈ pf2Factors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact pf2_smallPrime q h
  · fin_cases h
    · exact pf1_prime

theorem pf2_fermat : powMod 2 (pf2 - 1) pf2 = 1 := by decide

theorem pf2_witness :
    ∀ q ∈ pf2Factors, powMod 2 ((pf2 - 1) / q) pf2 ≠ 1 := by decide

/-- `Nat.Prime pf2`, machine-checked by a Lucas certificate (witness `2`). -/
theorem pf2_prime : Nat.Prime pf2 :=
  lucas_of_certificate pf2 (by decide) 2 pf2Factors
    pf2_prod pf2_primeFactors pf2_fermat pf2_witness

end CatCrypt.Crypto.Util.BN254R.Node2
