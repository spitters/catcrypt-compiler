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
# BN254 scalar-field certificate — nested factor node `pf3`

Lucas certificate for the nested prime factor `65865678001877903` in the BN254
scalar-field order chain. One node of the split `BN254RPrimeCert` certificate;
the modulus is below `2^64`, so the Fermat, witness, and product checks reduce
by `decide` and only the small-factor primality uses `native_decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BN254R.Node3

open CatCrypt.PrattCertificate

/-- Nested prime factor `65865678001877903`
    (`56`-bit). `N - 1 = 2 · 83 · 379 · 1637 · 639533339`. -/
def pf3 : Nat := 65865678001877903

/-- All prime factors of `pf3 - 1`, with multiplicity; product is `pf3 - 1`. -/
def pf3Factors : List Nat := List.replicate 1 2 ++ [83, 379, 1637, 639533339]

theorem pf3_prod : pf3Factors.prod = pf3 - 1 := by decide

theorem pf3_primeFactors : ∀ q ∈ pf3Factors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem pf3_fermat : powMod 5 (pf3 - 1) pf3 = 1 := by decide

theorem pf3_witness :
    ∀ q ∈ pf3Factors, powMod 5 ((pf3 - 1) / q) pf3 ≠ 1 := by decide

/-- `Nat.Prime pf3`, machine-checked by a Lucas certificate (witness `5`). -/
theorem pf3_prime : Nat.Prime pf3 :=
  lucas_of_certificate pf3 (by decide) 5 pf3Factors
    pf3_prod pf3_primeFactors pf3_fermat pf3_witness

end CatCrypt.Crypto.Util.BN254R.Node3
