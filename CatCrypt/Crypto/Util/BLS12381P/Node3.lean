/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.BLS12381P.Node8

/-!
# Lucas certificate node `p₃ = 92691255082156974996979`

A node of the BLS12-381 base-field primality certificate. `Nat.Prime p3` with
`p3 - 1 = 2 · 3 · 31 · 467 · 16447 · p₈` and witness `3`, using the child node `p₈`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12381P.Node3

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12381P.Node8

/-- Nested prime `92691255082156974996979` (`p₃`); references `p₈`. -/
def p3 : Nat := 92691255082156974996979
/-- Prime factors of `p₃ - 1`. -/
def p3Factors : List Nat := [2, 3, 31, 467, 16447, p8]
theorem p3Factors_prod : p3Factors.prod = p3 - 1 := by decide
theorem p3Factors_prime : ∀ q ∈ p3Factors, Nat.Prime q := by
  intro q hq; simp only [p3Factors] at hq
  fin_cases hq <;> first | exact p8_prime | norm_num
theorem p3Fermat : powMod 3 (p3 - 1) p3 = 1 := by decide
theorem p3Witness : ∀ q ∈ p3Factors, powMod 3 ((p3 - 1) / q) p3 ≠ 1 := by decide
theorem p3_prime : Nat.Prime p3 :=
  lucas_of_certificate p3 (by decide) 3 p3Factors p3Factors_prod p3Factors_prime p3Fermat p3Witness

end CatCrypt.Crypto.Util.BLS12381P.Node3
