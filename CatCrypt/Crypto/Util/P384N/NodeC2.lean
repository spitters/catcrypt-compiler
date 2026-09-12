/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384N.NodeM3a
public import CatCrypt.Crypto.Util.P384N.NodeM3b

/-!
# Lucas certificate node `C2 = 1059392654943455286185473617842338478315215895509773412096307`

A node of the P-384 group-order primality certificate. `Nat.Prime p8C2lit` with
`p8C2lit - 1 = 2·251·248431·8463023·p8m3alit·p8m3blit` and witness `2`, using
the child nodes `M3a`, `M3b`. This is a factor of `p8Blit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384N.NodeC2

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384N.NodeM3a
open CatCrypt.Crypto.Util.P384N.NodeM3b

def p8C2lit : Nat := 1059392654943455286185473617842338478315215895509773412096307
def p8C2Factors : List Nat := [2, 251, 248431, 8463023, p8m3alit, p8m3blit]
theorem p8C2_prod : p8C2Factors.prod = p8C2lit - 1 := by decide
theorem p8C2_factors_prime : ∀ q ∈ p8C2Factors, Nat.Prime q := by
  intro q hq
  simp only [p8C2Factors] at hq
  fin_cases hq <;>
    first
      | exact p8m3a_prime
      | exact p8m3b_prime
      | norm_num
theorem p8C2_fermat : powMod 2 (p8C2lit - 1) p8C2lit = 1 := by decide
theorem p8C2_witness :
    ∀ q ∈ p8C2Factors, powMod 2 ((p8C2lit - 1) / q) p8C2lit ≠ 1 := by decide
theorem p8C2_prime : Nat.Prime p8C2lit :=
  lucas_of_certificate p8C2lit (by decide) 2 p8C2Factors
    p8C2_prod p8C2_factors_prime p8C2_fermat p8C2_witness

end CatCrypt.Crypto.Util.P384N.NodeC2
