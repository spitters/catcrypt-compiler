/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate

/-!
# BN254 primality certificate — nested factor node `pf1`

Lucas certificate for the nested prime factor `35385462869` in the BN254
base-field prime chain. One node of the split `BN254PrimeCert` certificate; the
modulus is below `2^64`, so the Fermat, witness, and product checks reduce by
`decide` and only the small-factor primality uses `native_decide`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.BN254.Node1

open CatCrypt.PrattCertificate

/-- Nested prime factor `35385462869`
    (`36`-bit). `N - 1 = 2^2 · 7 · 1263766531`. -/
def pf1 : Nat := 35385462869

/-- All prime factors of `pf1 - 1`, with multiplicity; product is `pf1 - 1`. -/
def pf1Factors : List Nat := List.replicate 2 2 ++ [7, 1263766531]

theorem pf1_prod : pf1Factors.prod = pf1 - 1 := by decide

theorem pf1_primeFactors : ∀ q ∈ pf1Factors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem pf1_fermat : powMod 2 (pf1 - 1) pf1 = 1 := by native_decide

theorem pf1_witness :
    ∀ q ∈ pf1Factors, powMod 2 ((pf1 - 1) / q) pf1 ≠ 1 := by native_decide

/-- `Nat.Prime pf1`, machine-checked by a Lucas certificate (witness `2`). -/
theorem pf1_prime : Nat.Prime pf1 :=
  lucas_of_certificate pf1 (by decide) 2 pf1Factors
    pf1_prod pf1_primeFactors pf1_fermat pf1_witness

end CatCrypt.Crypto.Util.BN254.Node1
