/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `s₁ = 6633514200929891813`

A leaf node of the BLS12-377 base-field primality certificate. `Nat.Prime s1`
with `s1 - 1 = 2² · 19 · 25537 · 47521 · 71924131` and witness `2`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12377P.Node1

open CatCrypt.PrattCertificate

/-- Nested prime `6633514200929891813` (`s₁`). -/
def s1 : Nat := 6633514200929891813
/-- Prime factors of `s₁ - 1`. -/
def s1Factors : List Nat := [2, 2, 19, 25537, 47521, 71924131]
theorem s1Factors_prod : s1Factors.prod = s1 - 1 := by decide
theorem s1Factors_prime : ∀ q ∈ s1Factors, Nat.Prime q := by
  intro q hq; simp only [s1Factors] at hq; fin_cases hq <;> norm_num
theorem s1Fermat : powMod 2 (s1 - 1) s1 = 1 := by decide
theorem s1Witness : ∀ q ∈ s1Factors, powMod 2 ((s1 - 1) / q) s1 ≠ 1 := by decide
theorem s1_prime : Nat.Prime s1 :=
  lucas_of_certificate s1 (by decide) 2 s1Factors s1Factors_prod s1Factors_prime s1Fermat s1Witness

end CatCrypt.Crypto.Util.BLS12377P.Node1
