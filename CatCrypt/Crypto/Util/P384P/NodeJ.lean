/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384P.NodeK

/-!
# Lucas certificate node `23964610537191310276190549303`

A node of the P-384 base-field primality certificate. `Nat.Prime p7qJlit` with
`p7qJlit - 1 = 2·336757·p7qKlit` and witness `5`, using the child node `K`.
This is a factor of `p7qIlit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384P.NodeJ

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384P.NodeK

def p7qJlit : Nat := 23964610537191310276190549303
def p7qJFactors : List Nat := [2, 336757, p7qKlit]
theorem p7qJ_prod : p7qJFactors.prod = p7qJlit - 1 := by decide
theorem p7qJ_factors_prime : ∀ q ∈ p7qJFactors, Nat.Prime q := by
  intro q hq
  simp only [p7qJFactors] at hq
  fin_cases hq <;> first | exact p7qK_prime | norm_num
theorem p7qJ_fermat : powMod 5 (p7qJlit - 1) p7qJlit = 1 := by decide
theorem p7qJ_witness :
    ∀ q ∈ p7qJFactors, powMod 5 ((p7qJlit - 1) / q) p7qJlit ≠ 1 := by decide
theorem p7qJ_prime : Nat.Prime p7qJlit :=
  lucas_of_certificate p7qJlit (by decide) 5 p7qJFactors
    p7qJ_prod p7qJ_factors_prime p7qJ_fermat p7qJ_witness

end CatCrypt.Crypto.Util.P384P.NodeJ
