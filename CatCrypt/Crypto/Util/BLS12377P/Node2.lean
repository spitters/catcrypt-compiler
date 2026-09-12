/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.BLS12377P.Node3
public import CatCrypt.Crypto.Util.BLS12377P.Node4

/-!
# Lucas certificate node
`s₂ = 73387170334035996766247648424745786170238574695861388454532790956181`

The 226-bit prime factor of `p - 1` for the BLS12-377 base field. `Nat.Prime s2`
with `s2 - 1 = 2² · 5 · 11 · 23 · 494527005853 · s₃ · s₄` and witness `3`, using
the child nodes `s₃` and `s₄`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12377P.Node2

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12377P.Node3
open CatCrypt.Crypto.Util.BLS12377P.Node4

/-- Nested prime
`73387170334035996766247648424745786170238574695861388454532790956181` (`s₂`,
the 226-bit factor of `p - 1`); references `s₃` and `s₄`. -/
def s2 : Nat := 73387170334035996766247648424745786170238574695861388454532790956181
/-- Prime factors of `s₂ - 1`. -/
def s2Factors : List Nat := [2, 2, 5, 11, 23, 494527005853, s3, s4]
theorem s2Factors_prod : s2Factors.prod = s2 - 1 := by decide
theorem s2Factors_prime : ∀ q ∈ s2Factors, Nat.Prime q := by
  intro q hq; simp only [s2Factors] at hq
  fin_cases hq <;> first | exact s3_prime | exact s4_prime | norm_num
theorem s2Fermat : powMod 3 (s2 - 1) s2 = 1 := by decide
theorem s2Witness : ∀ q ∈ s2Factors, powMod 3 ((s2 - 1) / q) s2 ≠ 1 := by decide
theorem s2_prime : Nat.Prime s2 :=
  lucas_of_certificate s2 (by decide) 3 s2Factors s2Factors_prod s2Factors_prime s2Fermat s2Witness

end CatCrypt.Crypto.Util.BLS12377P.Node2
