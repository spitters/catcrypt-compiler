/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.BLS12381P.Node9

/-!
# Lucas certificate node `p₇ = 1928745244171409`

A node of the BLS12-381 base-field primality certificate. `Nat.Prime p7` with
`p7 - 1 = 2⁴ · 13 · p₉` and witness `3`, using the child node `p₉`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12381P.Node7

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12381P.Node9

/-- Nested prime `1928745244171409` (`p₇`); `p₇ - 1` has the large prime factor `p₉`. -/
def p7 : Nat := 1928745244171409
/-- Prime factors of `p₇ - 1`. -/
def p7Factors : List Nat := [2, 2, 2, 2, 13, p9]
theorem p7Factors_prod : p7Factors.prod = p7 - 1 := by decide
theorem p7Factors_prime : ∀ q ∈ p7Factors, Nat.Prime q := by
  intro q hq; simp only [p7Factors] at hq
  fin_cases hq <;> first | exact p9_prime | norm_num
theorem p7Fermat : powMod 3 (p7 - 1) p7 = 1 := by decide
theorem p7Witness : ∀ q ∈ p7Factors, powMod 3 ((p7 - 1) / q) p7 ≠ 1 := by decide
theorem p7_prime : Nat.Prime p7 :=
  lucas_of_certificate p7 (by decide) 3 p7Factors p7Factors_prod p7Factors_prime p7Fermat p7Witness

end CatCrypt.Crypto.Util.BLS12381P.Node7
