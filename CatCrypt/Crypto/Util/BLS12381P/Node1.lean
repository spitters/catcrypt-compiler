/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.BLS12381P.Node3
public import CatCrypt.Crypto.Util.BLS12381P.Node2

/-!
# Lucas certificate node
`p₁ = 15778400344354997994418419698270088123916926905054652752758194827714659`

A node of the BLS12-381 base-field primality certificate. `Nat.Prime p1` with
`p1 - 1 = 2 · 3 · 53 · 475709467 · p₃ · p₂` and witness `2`, using the child
nodes `p₃` and `p₂`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12381P.Node1

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12381P.Node3
open CatCrypt.Crypto.Util.BLS12381P.Node2

/-- Nested prime
`15778400344354997994418419698270088123916926905054652752758194827714659` (`p₁`);
references `p₃` and `p₂`. -/
def p1 : Nat := 15778400344354997994418419698270088123916926905054652752758194827714659
/-- Prime factors of `p₁ - 1`. -/
def p1Factors : List Nat := [2, 3, 53, 475709467, p3, p2]
theorem p1Factors_prod : p1Factors.prod = p1 - 1 := by decide
theorem p1Factors_prime : ∀ q ∈ p1Factors, Nat.Prime q := by
  intro q hq; simp only [p1Factors] at hq
  fin_cases hq <;> first | exact p3_prime | exact p2_prime | norm_num
theorem p1Fermat : powMod 2 (p1 - 1) p1 = 1 := by decide
theorem p1Witness : ∀ q ∈ p1Factors, powMod 2 ((p1 - 1) / q) p1 ≠ 1 := by decide
theorem p1_prime : Nat.Prime p1 :=
  lucas_of_certificate p1 (by decide) 2 p1Factors p1Factors_prod p1Factors_prime p1Fermat p1Witness

end CatCrypt.Crypto.Util.BLS12381P.Node1
