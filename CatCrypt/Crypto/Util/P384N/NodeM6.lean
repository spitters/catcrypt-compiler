/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384N.NodeM7

/-!
# Lucas certificate node `23314383343543`

A node of the P-384 group-order primality certificate. `Nat.Prime p8m6lit` with
`p8m6lit - 1 = 2·3·17·p8m7lit` and witness `3`, using the child node `M7`.
This is a factor of `p8m5lit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384N.NodeM6

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384N.NodeM7

def p8m6lit : Nat := 23314383343543
def p8m6Factors : List Nat := [2, 3, 17, p8m7lit]
theorem p8m6_prod : p8m6Factors.prod = p8m6lit - 1 := by decide
theorem p8m6_factors_prime : ∀ q ∈ p8m6Factors, Nat.Prime q := by
  intro q hq
  simp only [p8m6Factors] at hq
  fin_cases hq <;> first | exact p8m7_prime | norm_num
theorem p8m6_fermat : powMod 3 (p8m6lit - 1) p8m6lit = 1 := by decide
theorem p8m6_witness :
    ∀ q ∈ p8m6Factors, powMod 3 ((p8m6lit - 1) / q) p8m6lit ≠ 1 := by decide
theorem p8m6_prime : Nat.Prime p8m6lit :=
  lucas_of_certificate p8m6lit (by decide) 3 p8m6Factors
    p8m6_prod p8m6_factors_prime p8m6_fermat p8m6_witness

end CatCrypt.Crypto.Util.P384N.NodeM6
