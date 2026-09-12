/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `p₉ = 9272813673901`

A leaf node of the BLS12-381 base-field primality certificate. `Nat.Prime p9`
with `p9 - 1 = 2² · 3 · 5² · 7 · 7577 · 582767` and witness `2`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12381P.Node9

open CatCrypt.PrattCertificate

/-- Nested prime `9272813673901` (`p₉`). -/
def p9 : Nat := 9272813673901
/-- Prime factors of `p₉ - 1`. -/
def p9Factors : List Nat := [2, 2, 3, 5, 5, 7, 7577, 582767]
theorem p9Factors_prod : p9Factors.prod = p9 - 1 := by decide
theorem p9Factors_prime : ∀ q ∈ p9Factors, Nat.Prime q := by
  intro q hq; simp only [p9Factors] at hq; fin_cases hq <;> norm_num
theorem p9Fermat : powMod 2 (p9 - 1) p9 = 1 := by decide
theorem p9Witness : ∀ q ∈ p9Factors, powMod 2 ((p9 - 1) / q) p9 ≠ 1 := by decide
theorem p9_prime : Nat.Prime p9 :=
  lucas_of_certificate p9 (by decide) 2 p9Factors p9Factors_prod p9Factors_prime p9Fermat p9Witness

end CatCrypt.Crypto.Util.BLS12381P.Node9
