/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `F1 = 34282281433`

A leaf node of the P-256 base-field primality certificate. `Nat.Prime p256F1lit`
with `p256F1lit - 1 = 2³·3·7·204061199` and witness `17`. `F1` divides `M − 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P256.NodeF1

open CatCrypt.PrattCertificate

def p256F1lit : Nat := 34282281433

def p256F1Factors : List Nat := [2, 2, 2, 3, 7, 204061199]

theorem p256F1Factors_prod : p256F1Factors.prod = p256F1lit - 1 := by decide
theorem p256F1Factors_prime : ∀ q ∈ p256F1Factors, Nat.Prime q := by
  intro q hq
  simp only [p256F1Factors] at hq
  fin_cases hq <;> norm_num
theorem p256F1Fermat : powMod 17 (p256F1lit - 1) p256F1lit = 1 := by decide
theorem p256F1Witness :
    ∀ q ∈ p256F1Factors, powMod 17 ((p256F1lit - 1) / q) p256F1lit ≠ 1 := by decide

theorem p256F1lit_prime : Nat.Prime p256F1lit :=
  lucas_of_certificate p256F1lit (by decide) 17 p256F1Factors
    p256F1Factors_prod p256F1Factors_prime p256F1Fermat p256F1Witness

end CatCrypt.Crypto.Util.P256.NodeF1
