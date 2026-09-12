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
# BN254 scalar-field certificate — nested factor node `pf0`

Lucas certificate for the nested prime factor `12048837557` in the BN254
scalar-field order chain. One node of the split `BN254RPrimeCert` certificate;
the modulus is below `2^64`, so the Fermat, witness, and product checks reduce
by `decide` and only the small-factor primality uses `native_decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BN254R.Node0

open CatCrypt.PrattCertificate

/-- Nested prime factor `12048837557`
    (`34`-bit). `N - 1 = 2^2 · 7^2 · 661 · 93001`. -/
def pf0 : Nat := 12048837557

/-- All prime factors of `pf0 - 1`, with multiplicity; product is `pf0 - 1`. -/
def pf0Factors : List Nat := List.replicate 2 2 ++ [7, 7, 661, 93001]

theorem pf0_prod : pf0Factors.prod = pf0 - 1 := by decide

theorem pf0_primeFactors : ∀ q ∈ pf0Factors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem pf0_fermat : powMod 2 (pf0 - 1) pf0 = 1 := by decide

theorem pf0_witness :
    ∀ q ∈ pf0Factors, powMod 2 ((pf0 - 1) / q) pf0 ≠ 1 := by decide

/-- `Nat.Prime pf0`, machine-checked by a Lucas certificate (witness `2`). -/
theorem pf0_prime : Nat.Prime pf0 :=
  lucas_of_certificate pf0 (by decide) 2 pf0Factors
    pf0_prod pf0_primeFactors pf0_fermat pf0_witness

end CatCrypt.Crypto.Util.BN254R.Node0
