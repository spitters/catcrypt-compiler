/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384N.NodeM6

/-!
# Lucas certificate node `426632512014427833817`

A node of the P-384 group-order primality certificate. `Nat.Prime p8m5lit` with
`p8m5lit - 1 = 2³·3·13·89·659·p8m6lit` and witness `11`, using the child node
`M6`. This is a factor of `p8m4lit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384N.NodeM5

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384N.NodeM6

def p8m5lit : Nat := 426632512014427833817
def p8m5Factors : List Nat := [2, 2, 2, 3, 13, 89, 659, p8m6lit]
theorem p8m5_prod : p8m5Factors.prod = p8m5lit - 1 := by decide
theorem p8m5_factors_prime : ∀ q ∈ p8m5Factors, Nat.Prime q := by
  intro q hq
  simp only [p8m5Factors] at hq
  fin_cases hq <;> first | exact p8m6_prime | norm_num
theorem p8m5_fermat : powMod 11 (p8m5lit - 1) p8m5lit = 1 := by decide
theorem p8m5_witness :
    ∀ q ∈ p8m5Factors, powMod 11 ((p8m5lit - 1) / q) p8m5lit ≠ 1 := by decide
theorem p8m5_prime : Nat.Prime p8m5lit :=
  lucas_of_certificate p8m5lit (by decide) 11 p8m5Factors
    p8m5_prod p8m5_factors_prime p8m5_fermat p8m5_witness

end CatCrypt.Crypto.Util.P384N.NodeM5
