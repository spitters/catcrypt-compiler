/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.BLS12377P.Node6

/-!
# Lucas certificate node `s₅ = 97931919162730131689321`

A node of the BLS12-377 base-field primality certificate. `Nat.Prime s5` with
`s5 - 1 = 2³ · 5 · 11 · s₆` and witness `3`, using the child node `s₆`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12377P.Node5

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12377P.Node6

/-- Nested prime `97931919162730131689321` (`s₅`); references `s₆`. -/
def s5 : Nat := 97931919162730131689321
/-- Prime factors of `s₅ - 1`. -/
def s5Factors : List Nat := [2, 2, 2, 5, 11, s6]
theorem s5Factors_prod : s5Factors.prod = s5 - 1 := by decide
theorem s5Factors_prime : ∀ q ∈ s5Factors, Nat.Prime q := by
  intro q hq; simp only [s5Factors] at hq
  fin_cases hq <;> first | exact s6_prime | norm_num
theorem s5Fermat : powMod 3 (s5 - 1) s5 = 1 := by decide
theorem s5Witness : ∀ q ∈ s5Factors, powMod 3 ((s5 - 1) / q) s5 ≠ 1 := by decide
theorem s5_prime : Nat.Prime s5 :=
  lucas_of_certificate s5 (by decide) 3 s5Factors s5Factors_prod s5Factors_prime s5Fermat s5Witness

end CatCrypt.Crypto.Util.BLS12377P.Node5
