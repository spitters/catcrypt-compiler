/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Leaf sub-certificate: `5247740253619` (a factor of `vestaAlit - 1`)

`Nat.Prime vestaA1lit` via a Lucas/Pratt certificate. This is a leaf of the
Vesta base-field primality certificate.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Vesta.Node1

open CatCrypt.PrattCertificate

/-- The 43-bit prime `5247740253619`, a factor of `vestaAlit - 1`. -/
def vestaA1lit : Nat := 5247740253619

/-- Prime factors of `vestaA1lit - 1`; product is `vestaA1lit - 1`. -/
def vestaA1Factors : List Nat := [2, 3, 3, 3, 17, 71, 80513981]

theorem vestaA1_prod : vestaA1Factors.prod = vestaA1lit - 1 := by decide
theorem vestaA1_factors_prime : ∀ q ∈ vestaA1Factors, Nat.Prime q := by
  intro q hq; fin_cases hq <;> norm_num
theorem vestaA1_fermat : powMod 2 (vestaA1lit - 1) vestaA1lit = 1 := by decide
theorem vestaA1_witness :
    ∀ q ∈ vestaA1Factors, powMod 2 ((vestaA1lit - 1) / q) vestaA1lit ≠ 1 := by
  decide

theorem vestaA1_prime : Nat.Prime vestaA1lit :=
  lucas_of_certificate vestaA1lit (by decide) 2 vestaA1Factors
    vestaA1_prod vestaA1_factors_prime vestaA1_fermat vestaA1_witness

end CatCrypt.Crypto.Util.Vesta.Node1
