/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384N.NodeM5

/-!
# Lucas certificate node `1495199339761412565498084319`

A node of the P-384 group-order primality certificate. `Nat.Prime p8m4lit` with
`p8m4lit - 1 = 2·3³·64901·p8m5lit` and witness `6`, using the child node `M5`.
This is a factor of `p8m3blit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384N.NodeM4

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384N.NodeM5

def p8m4lit : Nat := 1495199339761412565498084319
def p8m4Factors : List Nat := [2, 3, 3, 3, 64901, p8m5lit]
theorem p8m4_prod : p8m4Factors.prod = p8m4lit - 1 := by decide
theorem p8m4_factors_prime : ∀ q ∈ p8m4Factors, Nat.Prime q := by
  intro q hq
  simp only [p8m4Factors] at hq
  fin_cases hq <;> first | exact p8m5_prime | norm_num
theorem p8m4_fermat : powMod 6 (p8m4lit - 1) p8m4lit = 1 := by decide
theorem p8m4_witness :
    ∀ q ∈ p8m4Factors, powMod 6 ((p8m4lit - 1) / q) p8m4lit ≠ 1 := by decide
theorem p8m4_prime : Nat.Prime p8m4lit :=
  lucas_of_certificate p8m4lit (by decide) 6 p8m4Factors
    p8m4_prod p8m4_factors_prime p8m4_fermat p8m4_witness

end CatCrypt.Crypto.Util.P384N.NodeM4
