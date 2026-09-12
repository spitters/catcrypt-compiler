/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.BLS12381P.Node7

/-!
# Lucas certificate node `p₆ = 7259797099061183477`

A node of the BLS12-381 base-field primality certificate. `Nat.Prime p6` with
`p6 - 1 = 2² · 941 · p₇` and witness `2`, using the child node `p₇`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12381P.Node6

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12381P.Node7

/-- Nested prime `7259797099061183477` (`p₆`); references `p₇`. -/
def p6 : Nat := 7259797099061183477
/-- Prime factors of `p₆ - 1`. -/
def p6Factors : List Nat := [2, 2, 941, p7]
theorem p6Factors_prod : p6Factors.prod = p6 - 1 := by decide
theorem p6Factors_prime : ∀ q ∈ p6Factors, Nat.Prime q := by
  intro q hq; simp only [p6Factors] at hq
  fin_cases hq <;> first | exact p7_prime | norm_num
theorem p6Fermat : powMod 2 (p6 - 1) p6 = 1 := by decide
theorem p6Witness : ∀ q ∈ p6Factors, powMod 2 ((p6 - 1) / q) p6 ≠ 1 := by decide
theorem p6_prime : Nat.Prime p6 :=
  lucas_of_certificate p6 (by decide) 2 p6Factors p6Factors_prod p6Factors_prime p6Fermat p6Witness

end CatCrypt.Crypto.Util.BLS12381P.Node6
