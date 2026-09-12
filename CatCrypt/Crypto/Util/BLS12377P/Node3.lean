/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.BLS12377P.Node5

/-!
# Lucas certificate node `s₃ = 3721412928183745004194199`

A node of the BLS12-377 base-field primality certificate. `Nat.Prime s3` with
`s3 - 1 = 2 · 19 · s₅` and witness `13`, using the child node `s₅`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12377P.Node3

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12377P.Node5

/-- Nested prime `3721412928183745004194199` (`s₃`); references `s₅`. -/
def s3 : Nat := 3721412928183745004194199
/-- Prime factors of `s₃ - 1`. -/
def s3Factors : List Nat := [2, 19, s5]
theorem s3Factors_prod : s3Factors.prod = s3 - 1 := by decide
theorem s3Factors_prime : ∀ q ∈ s3Factors, Nat.Prime q := by
  intro q hq; simp only [s3Factors] at hq
  fin_cases hq <;> first | exact s5_prime | norm_num
theorem s3Fermat : powMod 13 (s3 - 1) s3 = 1 := by decide
theorem s3Witness : ∀ q ∈ s3Factors, powMod 13 ((s3 - 1) / q) s3 ≠ 1 := by decide
theorem s3_prime : Nat.Prime s3 :=
  lucas_of_certificate s3 (by decide) 13 s3Factors s3Factors_prod s3Factors_prime s3Fermat s3Witness

end CatCrypt.Crypto.Util.BLS12377P.Node3
