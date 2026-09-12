/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384P.NodeJ

/-!
# Lucas certificate node `862725979338887169942859774909`

A node of the P-384 base-field primality certificate. `Nat.Prime p7qIlit` with
`p7qIlit - 1 = 2²·3²·p7qJlit` and witness `2`, using the child node `J`.
This is a factor of `p7qHlit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384P.NodeI

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384P.NodeJ

def p7qIlit : Nat := 862725979338887169942859774909
def p7qIFactors : List Nat := [2, 2, 3, 3, p7qJlit]
theorem p7qI_prod : p7qIFactors.prod = p7qIlit - 1 := by decide
theorem p7qI_factors_prime : ∀ q ∈ p7qIFactors, Nat.Prime q := by
  intro q hq
  simp only [p7qIFactors] at hq
  fin_cases hq <;> first | exact p7qJ_prime | norm_num
theorem p7qI_fermat : powMod 2 (p7qIlit - 1) p7qIlit = 1 := by decide
theorem p7qI_witness :
    ∀ q ∈ p7qIFactors, powMod 2 ((p7qIlit - 1) / q) p7qIlit ≠ 1 := by decide
theorem p7qI_prime : Nat.Prime p7qIlit :=
  lucas_of_certificate p7qIlit (by decide) 2 p7qIFactors
    p7qI_prod p7qI_factors_prime p7qI_fermat p7qI_witness

end CatCrypt.Crypto.Util.P384P.NodeI
