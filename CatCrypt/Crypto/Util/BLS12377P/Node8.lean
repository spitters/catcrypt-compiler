/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `s₈ = 1844934619849`

A leaf node of the BLS12-377 base-field primality certificate. `Nat.Prime s8`
with `s8 - 1 = 2³ · 3 · 76872275827` and witness `14`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12377P.Node8

open CatCrypt.PrattCertificate

/-- Nested prime `1844934619849` (`s₈`). -/
def s8 : Nat := 1844934619849
/-- Prime factors of `s₈ - 1`. -/
def s8Factors : List Nat := [2, 2, 2, 3, 76872275827]
theorem s8Factors_prod : s8Factors.prod = s8 - 1 := by decide
theorem s8Factors_prime : ∀ q ∈ s8Factors, Nat.Prime q := by
  intro q hq; simp only [s8Factors] at hq; fin_cases hq <;> norm_num
theorem s8Fermat : powMod 14 (s8 - 1) s8 = 1 := by decide
theorem s8Witness : ∀ q ∈ s8Factors, powMod 14 ((s8 - 1) / q) s8 ≠ 1 := by decide
theorem s8_prime : Nat.Prime s8 :=
  lucas_of_certificate s8 (by decide) 14 s8Factors s8Factors_prod s8Factors_prime s8Fermat s8Witness

end CatCrypt.Crypto.Util.BLS12377P.Node8
