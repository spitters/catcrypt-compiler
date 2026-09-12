/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384N.NodeH1

/-!
# Lucas certificate node `1124679999981664229965379347`

A node of the P-384 group-order primality certificate. `Nat.Prime p8hintlit`
with `p8hintlit - 1 = 2·3·1553·p8h1lit` and witness `2`, using the child node
`H1`. This is a factor of `p384Nlit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384N.NodeHint

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384N.NodeH1

def p8hintlit : Nat := 1124679999981664229965379347
def p8hintFactors : List Nat := [2, 3, 1553, p8h1lit]
theorem p8hint_prod : p8hintFactors.prod = p8hintlit - 1 := by decide
theorem p8hint_factors_prime : ∀ q ∈ p8hintFactors, Nat.Prime q := by
  intro q hq
  simp only [p8hintFactors] at hq
  fin_cases hq <;> first | exact p8h1_prime | norm_num
theorem p8hint_fermat : powMod 2 (p8hintlit - 1) p8hintlit = 1 := by decide
theorem p8hint_witness :
    ∀ q ∈ p8hintFactors, powMod 2 ((p8hintlit - 1) / q) p8hintlit ≠ 1 := by decide
theorem p8hint_prime : Nat.Prime p8hintlit :=
  lucas_of_certificate p8hintlit (by decide) 2 p8hintFactors
    p8hint_prod p8hint_factors_prime p8hint_fermat p8hint_witness

end CatCrypt.Crypto.Util.P384N.NodeHint
