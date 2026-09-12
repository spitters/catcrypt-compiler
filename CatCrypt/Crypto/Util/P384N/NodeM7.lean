/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `228572385721`

A leaf node of the P-384 group-order primality certificate. `Nat.Prime p8m7lit`
with `p8m7lit - 1 = 2³·3·5·7·272109983` and witness `23`. This is a factor of
`p8m6lit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384N.NodeM7

open CatCrypt.PrattCertificate

def p8m7lit : Nat := 228572385721
def p8m7Factors : List Nat := [2, 2, 2, 3, 5, 7, 272109983]
theorem p8m7_prod : p8m7Factors.prod = p8m7lit - 1 := by decide
theorem p8m7_factors_prime : ∀ q ∈ p8m7Factors, Nat.Prime q := by
  intro q hq
  simp only [p8m7Factors] at hq
  fin_cases hq <;> norm_num
theorem p8m7_fermat : powMod 23 (p8m7lit - 1) p8m7lit = 1 := by decide
theorem p8m7_witness :
    ∀ q ∈ p8m7Factors, powMod 23 ((p8m7lit - 1) / q) p8m7lit ≠ 1 := by decide
theorem p8m7_prime : Nat.Prime p8m7lit :=
  lucas_of_certificate p8m7lit (by decide) 23 p8m7Factors
    p8m7_prod p8m7_factors_prime p8m7_fermat p8m7_witness

end CatCrypt.Crypto.Util.P384N.NodeM7
