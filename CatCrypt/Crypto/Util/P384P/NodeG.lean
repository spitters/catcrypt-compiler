/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384P.NodeH

/-!
# Lucas certificate node `413244619895455989650825325680172591660047`

A node of the P-384 base-field primality certificate. `Nat.Prime p7qGlit` with
`p7qGlit - 1 = 2·17·97·6051631·p7qHlit` and witness `5`, using the child node
`H`. This is a factor of `p7qFlit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384P.NodeG

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384P.NodeH

def p7qGlit : Nat := 413244619895455989650825325680172591660047
def p7qGFactors : List Nat := [2, 17, 97, 6051631, p7qHlit]
theorem p7qG_prod : p7qGFactors.prod = p7qGlit - 1 := by decide
theorem p7qG_factors_prime : ∀ q ∈ p7qGFactors, Nat.Prime q := by
  intro q hq
  simp only [p7qGFactors] at hq
  fin_cases hq <;> first | exact p7qH_prime | norm_num
theorem p7qG_fermat : powMod 5 (p7qGlit - 1) p7qGlit = 1 := by decide
theorem p7qG_witness :
    ∀ q ∈ p7qGFactors, powMod 5 ((p7qGlit - 1) / q) p7qGlit ≠ 1 := by decide
theorem p7qG_prime : Nat.Prime p7qGlit :=
  lucas_of_certificate p7qGlit (by decide) 5 p7qGFactors
    p7qG_prod p7qG_factors_prime p7qG_fermat p7qG_witness

end CatCrypt.Crypto.Util.P384P.NodeG
