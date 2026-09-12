/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `F3 = 46076956964474543`

A leaf node of the P-256 base-field primality certificate. `Nat.Prime p256F3lit`
with `p256F3lit - 1 = 2·23·18169·78283·704251` and witness `5`. `F3` divides
`M − 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P256.NodeF3

open CatCrypt.PrattCertificate

def p256F3lit : Nat := 46076956964474543

def p256F3Factors : List Nat := [2, 23, 18169, 78283, 704251]

theorem p256F3Factors_prod : p256F3Factors.prod = p256F3lit - 1 := by decide
theorem p256F3Factors_prime : ∀ q ∈ p256F3Factors, Nat.Prime q := by
  intro q hq
  simp only [p256F3Factors] at hq
  fin_cases hq <;> norm_num
theorem p256F3Fermat : powMod 5 (p256F3lit - 1) p256F3lit = 1 := by decide
theorem p256F3Witness :
    ∀ q ∈ p256F3Factors, powMod 5 ((p256F3lit - 1) / q) p256F3lit ≠ 1 := by decide

theorem p256F3lit_prime : Nat.Prime p256F3lit :=
  lucas_of_certificate p256F3lit (by decide) 5 p256F3Factors
    p256F3Factors_prod p256F3Factors_prime p256F3Fermat p256F3Witness

end CatCrypt.Crypto.Util.P256.NodeF3
