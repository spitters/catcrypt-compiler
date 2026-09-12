/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `s₉ = 5187222954756607`

A leaf node of the BLS12-377 base-field primality certificate. `Nat.Prime s9`
with `s9 - 1 = 2 · 3 · 19 · 5301089 · 8583511` and witness `3`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12377P.Node9

open CatCrypt.PrattCertificate

/-- Nested prime `5187222954756607` (`s₉`). -/
def s9 : Nat := 5187222954756607
/-- Prime factors of `s₉ - 1`. -/
def s9Factors : List Nat := [2, 3, 19, 5301089, 8583511]
theorem s9Factors_prod : s9Factors.prod = s9 - 1 := by decide
theorem s9Factors_prime : ∀ q ∈ s9Factors, Nat.Prime q := by
  intro q hq; simp only [s9Factors] at hq; fin_cases hq <;> norm_num
theorem s9Fermat : powMod 3 (s9 - 1) s9 = 1 := by decide
theorem s9Witness : ∀ q ∈ s9Factors, powMod 3 ((s9 - 1) / q) s9 ≠ 1 := by decide
theorem s9_prime : Nat.Prime s9 :=
  lucas_of_certificate s9 (by decide) 3 s9Factors s9Factors_prod s9Factors_prime s9Fermat s9Witness

end CatCrypt.Crypto.Util.BLS12377P.Node9
