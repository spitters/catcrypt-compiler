/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.BLS12381P.Node6

/-!
# Lucas certificate node `p₅ = 2584487767265781317813`

A node of the BLS12-381 base-field primality certificate. `Nat.Prime p5` with
`p5 - 1 = 2² · 89 · p₆` and witness `2`, using the child node `p₆`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12381P.Node5

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12381P.Node6

/-- Nested prime `2584487767265781317813` (`p₅`); references `p₆`. -/
def p5 : Nat := 2584487767265781317813
/-- Prime factors of `p₅ - 1`. -/
def p5Factors : List Nat := [2, 2, 89, p6]
theorem p5Factors_prod : p5Factors.prod = p5 - 1 := by decide
theorem p5Factors_prime : ∀ q ∈ p5Factors, Nat.Prime q := by
  intro q hq; simp only [p5Factors] at hq
  fin_cases hq <;> first | exact p6_prime | norm_num
theorem p5Fermat : powMod 2 (p5 - 1) p5 = 1 := by decide
theorem p5Witness : ∀ q ∈ p5Factors, powMod 2 ((p5 - 1) / q) p5 ≠ 1 := by decide
theorem p5_prime : Nat.Prime p5 :=
  lucas_of_certificate p5 (by decide) 2 p5Factors p5Factors_prod p5Factors_prime p5Fermat p5Witness

end CatCrypt.Crypto.Util.BLS12381P.Node5
