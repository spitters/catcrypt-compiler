/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `p₈ = 64881703735777`

A leaf node of the BLS12-381 base-field primality certificate. `Nat.Prime p8`
with `p8 - 1 = 2⁵ · 3⁷ · 927093389` and witness `5`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12381P.Node8

open CatCrypt.PrattCertificate

/-- Nested prime `64881703735777` (`p₈`). -/
def p8 : Nat := 64881703735777
/-- Prime factors of `p₈ - 1`. -/
def p8Factors : List Nat := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 927093389]
theorem p8Factors_prod : p8Factors.prod = p8 - 1 := by decide
theorem p8Factors_prime : ∀ q ∈ p8Factors, Nat.Prime q := by
  intro q hq; simp only [p8Factors] at hq; fin_cases hq <;> norm_num
theorem p8Fermat : powMod 5 (p8 - 1) p8 = 1 := by decide
theorem p8Witness : ∀ q ∈ p8Factors, powMod 5 ((p8 - 1) / q) p8 ≠ 1 := by decide
theorem p8_prime : Nat.Prime p8 :=
  lucas_of_certificate p8 (by decide) 5 p8Factors p8Factors_prod p8Factors_prime p8Fermat p8Witness

end CatCrypt.Crypto.Util.BLS12381P.Node8
