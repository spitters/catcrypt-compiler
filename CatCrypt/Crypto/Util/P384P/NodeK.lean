/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384P.NodeL

/-!
# Lucas certificate node `35581458644053887931343`

A node of the P-384 base-field primality certificate. `Nat.Prime p7qKlit` with
`p7qKlit - 1 = 2·17·41·568151·p7qLlit` and witness `5`, using the child node
`L`. This is a factor of `p7qJlit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384P.NodeK

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384P.NodeL

def p7qKlit : Nat := 35581458644053887931343
def p7qKFactors : List Nat := [2, 17, 41, 568151, p7qLlit]
theorem p7qK_prod : p7qKFactors.prod = p7qKlit - 1 := by decide
theorem p7qK_factors_prime : ∀ q ∈ p7qKFactors, Nat.Prime q := by
  intro q hq
  simp only [p7qKFactors] at hq
  fin_cases hq <;> first | exact p7qL_prime | norm_num
theorem p7qK_fermat : powMod 5 (p7qKlit - 1) p7qKlit = 1 := by decide
theorem p7qK_witness :
    ∀ q ∈ p7qKFactors, powMod 5 ((p7qKlit - 1) / q) p7qKlit ≠ 1 := by decide
theorem p7qK_prime : Nat.Prime p7qKlit :=
  lucas_of_certificate p7qKlit (by decide) 5 p7qKFactors
    p7qK_prod p7qK_factors_prime p7qK_fermat p7qK_witness

end CatCrypt.Crypto.Util.P384P.NodeK
