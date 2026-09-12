/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `53448597593`

A leaf node of the P-384 base-field primality certificate. `Nat.Prime p7qElit`
with `p7qElit - 1 = 2³·13·513928823` and witness `3`. This is a factor of
`p7qDlit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384P.NodeE

open CatCrypt.PrattCertificate

def p7qElit : Nat := 53448597593
def p7qEFactors : List Nat := [2, 2, 2, 13, 513928823]
theorem p7qE_prod : p7qEFactors.prod = p7qElit - 1 := by decide
theorem p7qE_factors_prime : ∀ q ∈ p7qEFactors, Nat.Prime q := by
  intro q hq
  simp only [p7qEFactors] at hq
  fin_cases hq <;> norm_num
theorem p7qE_fermat : powMod 3 (p7qElit - 1) p7qElit = 1 := by decide
theorem p7qE_witness :
    ∀ q ∈ p7qEFactors, powMod 3 ((p7qElit - 1) / q) p7qElit ≠ 1 := by decide
theorem p7qE_prime : Nat.Prime p7qElit :=
  lucas_of_certificate p7qElit (by decide) 3 p7qEFactors
    p7qE_prod p7qE_factors_prime p7qE_fermat p7qE_witness

end CatCrypt.Crypto.Util.P384P.NodeE
