/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.BLS12377P.Node7

/-!
# Lucas certificate node `s₆ = 222572543551659390203`

A node of the BLS12-377 base-field primality certificate. `Nat.Prime s6` with
`s6 - 1 = 2 · s₇` and witness `2`, using the child node `s₇`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12377P.Node6

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12377P.Node7

/-- Nested prime `222572543551659390203` (`s₆`); references `s₇`. -/
def s6 : Nat := 222572543551659390203
/-- Prime factors of `s₆ - 1`. -/
def s6Factors : List Nat := [2, s7]
theorem s6Factors_prod : s6Factors.prod = s6 - 1 := by decide
theorem s6Factors_prime : ∀ q ∈ s6Factors, Nat.Prime q := by
  intro q hq; simp only [s6Factors] at hq
  fin_cases hq <;> first | exact s7_prime | norm_num
theorem s6Fermat : powMod 2 (s6 - 1) s6 = 1 := by decide
theorem s6Witness : ∀ q ∈ s6Factors, powMod 2 ((s6 - 1) / q) s6 ≠ 1 := by decide
theorem s6_prime : Nat.Prime s6 :=
  lucas_of_certificate s6 (by decide) 2 s6Factors s6Factors_prod s6Factors_prime s6Fermat s6Witness

end CatCrypt.Crypto.Util.BLS12377P.Node6
