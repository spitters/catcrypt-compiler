/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `1436833069313`

A leaf node of the P-384 group-order primality certificate. `Nat.Prime p8b1lit`
with `p8b1lit - 1 = 2⁸·16979·330563` and witness `3`. This is a factor of
`p8Blit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384N.NodeB1

open CatCrypt.PrattCertificate

def p8b1lit : Nat := 1436833069313
def p8b1Factors : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 16979, 330563]
theorem p8b1_prod : p8b1Factors.prod = p8b1lit - 1 := by decide
theorem p8b1_factors_prime : ∀ q ∈ p8b1Factors, Nat.Prime q := by
  intro q hq
  simp only [p8b1Factors] at hq
  fin_cases hq <;> norm_num
theorem p8b1_fermat : powMod 3 (p8b1lit - 1) p8b1lit = 1 := by decide
theorem p8b1_witness :
    ∀ q ∈ p8b1Factors, powMod 3 ((p8b1lit - 1) / q) p8b1lit ≠ 1 := by decide
theorem p8b1_prime : Nat.Prime p8b1lit :=
  lucas_of_certificate p8b1lit (by decide) 3 p8b1Factors
    p8b1_prod p8b1_factors_prime p8b1_fermat p8b1_witness

end CatCrypt.Crypto.Util.P384N.NodeB1
