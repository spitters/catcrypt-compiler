/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.BLS12381P.Node4

/-!
# Lucas certificate node `p₂ = 1125266252156850182658904441386709967`

A node of the BLS12-381 base-field primality certificate. `Nat.Prime p2` with
`p2 - 1 = 2 · 3373 · 43670061551 · p₄` and witness `5`, using the child node `p₄`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12381P.Node2

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12381P.Node4

/-- Nested prime `1125266252156850182658904441386709967` (`p₂`); references `p₄`. -/
def p2 : Nat := 1125266252156850182658904441386709967
/-- Prime factors of `p₂ - 1`. -/
def p2Factors : List Nat := [2, 3373, 43670061551, p4]
theorem p2Factors_prod : p2Factors.prod = p2 - 1 := by decide
theorem p2Factors_prime : ∀ q ∈ p2Factors, Nat.Prime q := by
  intro q hq; simp only [p2Factors] at hq
  fin_cases hq <;> first | exact p4_prime | norm_num
theorem p2Fermat : powMod 5 (p2 - 1) p2 = 1 := by decide
theorem p2Witness : ∀ q ∈ p2Factors, powMod 5 ((p2 - 1) / q) p2 ≠ 1 := by decide
theorem p2_prime : Nat.Prime p2 :=
  lucas_of_certificate p2 (by decide) 5 p2Factors p2Factors_prod p2Factors_prime p2Fermat p2Witness

end CatCrypt.Crypto.Util.BLS12381P.Node2
