/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `g107lit` of the secp256k1 group-order tree

`Nat.Prime g107lit` for the factor `g107lit = 107361793816595537`, proved by a
Lucas/Pratt certificate with witness `3`. This is a leaf node whose modulus is
below `2^64`, so the Fermat and witness checks are discharged by `decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Secp256k1N.Node107

open CatCrypt.PrattCertificate

/-- Prime factor of the secp256k1 tree requiring a nested Lucas certificate. -/
def g107lit : Nat := 107361793816595537

/-- Full prime factorization of `g107lit - 1`; product `= g107lit - 1`. -/
def g107Factors : List Nat := List.replicate 4 2 ++ [16699, 85831, 4681609]

theorem g107_prod : g107Factors.prod = g107lit - 1 := by decide

theorem g107_factors_prime : ∀ q ∈ g107Factors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem g107_fermat : powMod 3 (g107lit - 1) g107lit = 1 := by decide

theorem g107_witness :
    ∀ q ∈ g107Factors, powMod 3 ((g107lit - 1) / q) g107lit ≠ 1 := by decide

/-- `Nat.Prime g107lit`, machine-checked by a nested Lucas certificate. -/
theorem g107_prime : Nat.Prime g107lit :=
  lucas_of_certificate g107lit (by decide) 3 g107Factors
    g107_prod g107_factors_prime g107_fermat g107_witness

end CatCrypt.Crypto.Util.Secp256k1N.Node107
