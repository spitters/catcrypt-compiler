/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384P.NodeI

/-!
# Lucas certificate node `20705423504133292078628634597817`

A node of the P-384 base-field primality certificate. `Nat.Prime p7qHlit` with
`p7qHlit - 1 = 2³·3·p7qIlit` and witness `5`, using the child node `I`.
This is a factor of `p7qGlit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384P.NodeH

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384P.NodeI

def p7qHlit : Nat := 20705423504133292078628634597817
def p7qHFactors : List Nat := [2, 2, 2, 3, p7qIlit]
theorem p7qH_prod : p7qHFactors.prod = p7qHlit - 1 := by decide
theorem p7qH_factors_prime : ∀ q ∈ p7qHFactors, Nat.Prime q := by
  intro q hq
  simp only [p7qHFactors] at hq
  fin_cases hq <;> first | exact p7qI_prime | norm_num
theorem p7qH_fermat : powMod 5 (p7qHlit - 1) p7qHlit = 1 := by decide
theorem p7qH_witness :
    ∀ q ∈ p7qHFactors, powMod 5 ((p7qHlit - 1) / q) p7qHlit ≠ 1 := by decide
theorem p7qH_prime : Nat.Prime p7qHlit :=
  lucas_of_certificate p7qHlit (by decide) 5 p7qHFactors
    p7qH_prod p7qH_factors_prime p7qH_fermat p7qH_witness

end CatCrypt.Crypto.Util.P384P.NodeH
