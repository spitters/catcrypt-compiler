/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `p₄ = 3819663927398918131021`

A leaf node of the BLS12-381 base-field primality certificate. `Nat.Prime p4`
with `p4 - 1 = 2² · 3² · 5 · 19 · 113 · 755057 · 13090036741` and witness `6`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12381P.Node4

open CatCrypt.PrattCertificate

/-- Nested prime `3819663927398918131021` (`p₄`). -/
def p4 : Nat := 3819663927398918131021
/-- Prime factors of `p₄ - 1`. -/
def p4Factors : List Nat := [2, 2, 3, 3, 5, 19, 113, 755057, 13090036741]
theorem p4Factors_prod : p4Factors.prod = p4 - 1 := by decide
theorem p4Factors_prime : ∀ q ∈ p4Factors, Nat.Prime q := by
  intro q hq; simp only [p4Factors] at hq; fin_cases hq <;> norm_num
theorem p4Fermat : powMod 6 (p4 - 1) p4 = 1 := by decide
theorem p4Witness : ∀ q ∈ p4Factors, powMod 6 ((p4 - 1) / q) p4 ≠ 1 := by decide
theorem p4_prime : Nat.Prime p4 :=
  lucas_of_certificate p4 (by decide) 6 p4Factors p4Factors_prod p4Factors_prime p4Fermat p4Witness

end CatCrypt.Crypto.Util.BLS12381P.Node4
