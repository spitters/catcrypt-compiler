/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384N.NodeM4

/-!
# Lucas certificate node `17942392077136950785977011829`

A node of the P-384 group-order primality certificate. `Nat.Prime p8m3blit`
with `p8m3blit - 1 = 2²·3·p8m4lit` and witness `6`, using the child node `M4`.
This is a factor of `p8C2lit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384N.NodeM3b

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384N.NodeM4

def p8m3blit : Nat := 17942392077136950785977011829
def p8m3bFactors : List Nat := [2, 2, 3, p8m4lit]
theorem p8m3b_prod : p8m3bFactors.prod = p8m3blit - 1 := by decide
theorem p8m3b_factors_prime : ∀ q ∈ p8m3bFactors, Nat.Prime q := by
  intro q hq
  simp only [p8m3bFactors] at hq
  fin_cases hq <;> first | exact p8m4_prime | norm_num
theorem p8m3b_fermat : powMod 6 (p8m3blit - 1) p8m3blit = 1 := by decide
theorem p8m3b_witness :
    ∀ q ∈ p8m3bFactors, powMod 6 ((p8m3blit - 1) / q) p8m3blit ≠ 1 := by decide
theorem p8m3b_prime : Nat.Prime p8m3blit :=
  lucas_of_certificate p8m3blit (by decide) 6 p8m3bFactors
    p8m3b_prod p8m3b_factors_prime p8m3b_fermat p8m3b_witness

end CatCrypt.Crypto.Util.P384N.NodeM3b
