/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384P.NodeE

/-!
# Lucas certificate node `1357291859799823621`

A node of the P-384 base-field primality certificate. `Nat.Prime p7qDlit` with
`p7qDlit - 1 = 2²·3·5·67·6317·p7qElit` and witness `2`, using the child node
`E`. This is a factor of `p7qQlit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384P.NodeD

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384P.NodeE

def p7qDlit : Nat := 1357291859799823621
def p7qDFactors : List Nat := [2, 2, 3, 5, 67, 6317, p7qElit]
theorem p7qD_prod : p7qDFactors.prod = p7qDlit - 1 := by decide
theorem p7qD_factors_prime : ∀ q ∈ p7qDFactors, Nat.Prime q := by
  intro q hq
  simp only [p7qDFactors] at hq
  fin_cases hq <;> first | exact p7qE_prime | norm_num
theorem p7qD_fermat : powMod 2 (p7qDlit - 1) p7qDlit = 1 := by decide
theorem p7qD_witness :
    ∀ q ∈ p7qDFactors, powMod 2 ((p7qDlit - 1) / q) p7qDlit ≠ 1 := by decide
theorem p7qD_prime : Nat.Prime p7qDlit :=
  lucas_of_certificate p7qDlit (by decide) 2 p7qDFactors
    p7qD_prod p7qD_factors_prime p7qD_fermat p7qD_witness

end CatCrypt.Crypto.Util.P384P.NodeD
