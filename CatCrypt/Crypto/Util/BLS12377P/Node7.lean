/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.BLS12377P.Node8

/-!
# Lucas certificate node `s₇ = 111286271775829695101`

A node of the BLS12-377 base-field primality certificate. `Nat.Prime s7` with
`s7 - 1 = 2² · 5² · 73 · 8263 · s₈` and witness `2`, using the child node `s₈`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12377P.Node7

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12377P.Node8

/-- Nested prime `111286271775829695101` (`s₇`); references `s₈`. -/
def s7 : Nat := 111286271775829695101
/-- Prime factors of `s₇ - 1`. -/
def s7Factors : List Nat := [2, 2, 5, 5, 73, 8263, s8]
theorem s7Factors_prod : s7Factors.prod = s7 - 1 := by decide
theorem s7Factors_prime : ∀ q ∈ s7Factors, Nat.Prime q := by
  intro q hq; simp only [s7Factors] at hq
  fin_cases hq <;> first | exact s8_prime | norm_num
theorem s7Fermat : powMod 2 (s7 - 1) s7 = 1 := by decide
theorem s7Witness : ∀ q ∈ s7Factors, powMod 2 ((s7 - 1) / q) s7 ≠ 1 := by decide
theorem s7_prime : Nat.Prime s7 :=
  lucas_of_certificate s7 (by decide) 2 s7Factors s7Factors_prod s7Factors_prime s7Fermat s7Witness

end CatCrypt.Crypto.Util.BLS12377P.Node7
