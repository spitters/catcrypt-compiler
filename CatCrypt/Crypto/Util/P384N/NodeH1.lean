/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `120699720968197491947347`

A leaf node of the P-384 group-order primality certificate. `Nat.Prime p8h1lit`
with `p8h1lit - 1 = 2·3·13·34429·154950581·290064143` and witness `3`. This is a
factor of `p8hintlit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384N.NodeH1

open CatCrypt.PrattCertificate

def p8h1lit : Nat := 120699720968197491947347
def p8h1Factors : List Nat := [2, 3, 13, 34429, 154950581, 290064143]
theorem p8h1_prod : p8h1Factors.prod = p8h1lit - 1 := by decide
theorem p8h1_factors_prime : ∀ q ∈ p8h1Factors, Nat.Prime q := by
  intro q hq
  simp only [p8h1Factors] at hq
  fin_cases hq <;> norm_num
theorem p8h1_fermat : powMod 3 (p8h1lit - 1) p8h1lit = 1 := by decide
theorem p8h1_witness :
    ∀ q ∈ p8h1Factors, powMod 3 ((p8h1lit - 1) / q) p8h1lit ≠ 1 := by decide
theorem p8h1_prime : Nat.Prime p8h1lit :=
  lucas_of_certificate p8h1lit (by decide) 3 p8h1Factors
    p8h1_prod p8h1_factors_prime p8h1_fermat p8h1_witness

end CatCrypt.Crypto.Util.P384N.NodeH1
