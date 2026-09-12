/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# BN256 primality certificate — nested factor node `pf4`

Lucas certificate for the nested prime factor `81767558454161` in the BN256
base-field prime chain. One node of the split `BN256PrimeCert` certificate; the
modulus is below `2^64`, so the Fermat, witness, and product checks reduce by
`decide` and only the small-factor primality uses `native_decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Pairing.BN256.Node4

open CatCrypt.PrattCertificate

/-- Nested prime factor `81767558454161`
    (`47`-bit). `N - 1 = 2^4 · 5 · 151573 · 6743249`. -/
def pf4 : Nat := 81767558454161

/-- All prime factors of `pf4 - 1`, with multiplicity; product is `pf4 - 1`. -/
def pf4Factors : List Nat := List.replicate 4 2 ++ [5, 151573, 6743249]

theorem pf4_prod : pf4Factors.prod = pf4 - 1 := by decide

theorem pf4_primeFactors : ∀ q ∈ pf4Factors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem pf4_fermat : powMod 3 (pf4 - 1) pf4 = 1 := by decide

theorem pf4_witness :
    ∀ q ∈ pf4Factors, powMod 3 ((pf4 - 1) / q) pf4 ≠ 1 := by decide

/-- `Nat.Prime pf4`, machine-checked by a Lucas certificate (witness `3`). -/
theorem pf4_prime : Nat.Prime pf4 :=
  lucas_of_certificate pf4 (by decide) 3 pf4Factors
    pf4_prod pf4_primeFactors pf4_fermat pf4_witness

end CatCrypt.Crypto.Pairing.BN256.Node4
