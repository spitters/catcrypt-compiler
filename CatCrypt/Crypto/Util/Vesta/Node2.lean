/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Leaf sub-certificate: `5239247429827` (a factor of `vestaBlit - 1`)

`Nat.Prime vestaB1lit` via a Lucas/Pratt certificate. This is a leaf of the
Vesta base-field primality certificate.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Vesta.Node2

open CatCrypt.PrattCertificate

/-- The 43-bit prime `5239247429827`, a factor of `vestaBlit - 1`. -/
def vestaB1lit : Nat := 5239247429827

/-- Prime factors of `vestaB1lit - 1`; product is `vestaB1lit - 1`. -/
def vestaB1Factors : List Nat := [2, 3, 3, 757, 12149, 31649]

theorem vestaB1_prod : vestaB1Factors.prod = vestaB1lit - 1 := by decide
theorem vestaB1_factors_prime : ∀ q ∈ vestaB1Factors, Nat.Prime q := by
  intro q hq; fin_cases hq <;> norm_num
theorem vestaB1_fermat : powMod 2 (vestaB1lit - 1) vestaB1lit = 1 := by decide
theorem vestaB1_witness :
    ∀ q ∈ vestaB1Factors, powMod 2 ((vestaB1lit - 1) / q) vestaB1lit ≠ 1 := by
  decide

theorem vestaB1_prime : Nat.Prime vestaB1lit :=
  lucas_of_certificate vestaB1lit (by decide) 2 vestaB1Factors
    vestaB1_prod vestaB1_factors_prime vestaB1_fermat vestaB1_witness

end CatCrypt.Crypto.Util.Vesta.Node2
