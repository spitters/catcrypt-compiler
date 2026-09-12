/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `44925942675193`

A leaf node of the P-384 base-field primality certificate. `Nat.Prime p7qLlit`
with `p7qLlit - 1 = 2³·3·3517·532247449` and witness `5`. This is a factor of
`p7qKlit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384P.NodeL

open CatCrypt.PrattCertificate

def p7qLlit : Nat := 44925942675193
def p7qLFactors : List Nat := [2, 2, 2, 3, 3517, 532247449]
theorem p7qL_prod : p7qLFactors.prod = p7qLlit - 1 := by decide
theorem p7qL_factors_prime : ∀ q ∈ p7qLFactors, Nat.Prime q := by
  intro q hq
  simp only [p7qLFactors] at hq
  fin_cases hq <;> norm_num
theorem p7qL_fermat : powMod 5 (p7qLlit - 1) p7qLlit = 1 := by decide
theorem p7qL_witness :
    ∀ q ∈ p7qLFactors, powMod 5 ((p7qLlit - 1) / q) p7qLlit ≠ 1 := by decide
theorem p7qL_prime : Nat.Prime p7qLlit :=
  lucas_of_certificate p7qLlit (by decide) 5 p7qLFactors
    p7qL_prod p7qL_factors_prime p7qL_fermat p7qL_witness

end CatCrypt.Crypto.Util.P384P.NodeL
