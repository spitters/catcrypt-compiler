/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `807145746439`

A leaf node of the P-384 base-field primality certificate. `Nat.Prime p7qAlit`
with `p7qAlit - 1 = 2·3·47·2862218959` and witness `3`. This is a factor of
`p384Plit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384P.NodeA

open CatCrypt.PrattCertificate

def p7qAlit : Nat := 807145746439
def p7qAFactors : List Nat := [2, 3, 47, 2862218959]
theorem p7qA_prod : p7qAFactors.prod = p7qAlit - 1 := by decide
theorem p7qA_factors_prime : ∀ q ∈ p7qAFactors, Nat.Prime q := by
  intro q hq
  simp only [p7qAFactors] at hq
  fin_cases hq <;> norm_num
theorem p7qA_fermat : powMod 3 (p7qAlit - 1) p7qAlit = 1 := by decide
theorem p7qA_witness :
    ∀ q ∈ p7qAFactors, powMod 3 ((p7qAlit - 1) / q) p7qAlit ≠ 1 := by decide
theorem p7qA_prime : Nat.Prime p7qAlit :=
  lucas_of_certificate p7qAlit (by decide) 3 p7qAFactors
    p7qA_prod p7qA_factors_prime p7qA_fermat p7qA_witness

end CatCrypt.Crypto.Util.P384P.NodeA
