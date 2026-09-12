/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.BLS12377P.Node9

/-!
# Lucas certificate node `s₄ = 7880826209898991662826602799`

A node of the BLS12-377 base-field primality certificate. `Nat.Prime s4` with
`s4 - 1 = 2 · 3 · 53 · 4777599223 · s₉` and witness `21`, using the child node `s₉`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12377P.Node4

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12377P.Node9

/-- Nested prime `7880826209898991662826602799` (`s₄`); references `s₉`. -/
def s4 : Nat := 7880826209898991662826602799
/-- Prime factors of `s₄ - 1`. -/
def s4Factors : List Nat := [2, 3, 53, 4777599223, s9]
theorem s4Factors_prod : s4Factors.prod = s4 - 1 := by decide
theorem s4Factors_prime : ∀ q ∈ s4Factors, Nat.Prime q := by
  intro q hq; simp only [s4Factors] at hq
  fin_cases hq <;> first | exact s9_prime | norm_num
theorem s4Fermat : powMod 21 (s4 - 1) s4 = 1 := by decide
theorem s4Witness : ∀ q ∈ s4Factors, powMod 21 ((s4 - 1) / q) s4 ≠ 1 := by decide
theorem s4_prime : Nat.Prime s4 :=
  lucas_of_certificate s4 (by decide) 21 s4Factors s4Factors_prod s4Factors_prime s4Fermat s4Witness

end CatCrypt.Crypto.Util.BLS12377P.Node4
