/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.Vesta.Node1

/-!
# Sub-certificate: `1690502597179744445941507` (a factor of `vestalit - 1`)

`Nat.Prime vestaAlit` via a Lucas/Pratt certificate. Its largest factor exceeds
`2^32` and is proved prime by the nested certificate `vestaA1_prime`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Vesta.Node3

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Vesta.Node1

/-- The 81-bit prime `1690502597179744445941507`, a factor of `vestalit - 1`. -/
def vestaAlit : Nat := 1690502597179744445941507

/-- The below-`2^32` prime factors of `vestaAlit - 1` (`4129989133 < 2^32`). -/
def vestaASmallFactors : List Nat := [2, 3, 13, 4129989133]

/-- All prime factors of `vestaAlit - 1`; the last exceeds `2^32`. -/
def vestaAFactors : List Nat := vestaASmallFactors ++ [vestaA1lit]

theorem vestaA_prod : vestaAFactors.prod = vestaAlit - 1 := by decide
theorem vestaA_factors_prime : ∀ q ∈ vestaAFactors, Nat.Prime q := by
  intro q hq; fin_cases hq <;> first | exact vestaA1_prime | norm_num
theorem vestaA_fermat : powMod 2 (vestaAlit - 1) vestaAlit = 1 := by decide
theorem vestaA_witness :
    ∀ q ∈ vestaAFactors, powMod 2 ((vestaAlit - 1) / q) vestaAlit ≠ 1 := by
  decide

theorem vestaA_prime : Nat.Prime vestaAlit :=
  lucas_of_certificate vestaAlit (by decide) 2 vestaAFactors
    vestaA_prod vestaA_factors_prime vestaA_fermat vestaA_witness

end CatCrypt.Crypto.Util.Vesta.Node3
