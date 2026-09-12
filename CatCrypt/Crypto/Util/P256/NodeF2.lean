/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P256.NodeG

/-!
# Lucas certificate node `F2 = 11290956913871`

A node of the P-256 base-field primality certificate. `Nat.Prime p256F2lit` with
`p256F2lit - 1 = 2·5·17·G` and witness `13`. `F2` divides `M − 1` and uses the
child node `G`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P256.NodeF2

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P256.NodeG

def p256F2lit : Nat := 11290956913871

def p256F2Factors : List Nat := [2, 5, 17, p256Glit]

theorem p256F2Factors_prod : p256F2Factors.prod = p256F2lit - 1 := by decide
theorem p256F2Factors_prime : ∀ q ∈ p256F2Factors, Nat.Prime q := by
  intro q hq
  simp only [p256F2Factors] at hq
  fin_cases hq <;> first | exact p256Glit_prime | norm_num
theorem p256F2Fermat : powMod 13 (p256F2lit - 1) p256F2lit = 1 := by decide
theorem p256F2Witness :
    ∀ q ∈ p256F2Factors, powMod 13 ((p256F2lit - 1) / q) p256F2lit ≠ 1 := by decide

theorem p256F2lit_prime : Nat.Prime p256F2lit :=
  lucas_of_certificate p256F2lit (by decide) 13 p256F2Factors
    p256F2Factors_prod p256F2Factors_prime p256F2Fermat p256F2Witness

end CatCrypt.Crypto.Util.P256.NodeF2
