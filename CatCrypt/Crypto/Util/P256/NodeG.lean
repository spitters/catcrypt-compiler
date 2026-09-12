/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `G = 66417393611`

A leaf node of the P-256 base-field primality certificate. `Nat.Prime p256Glit`
with `p256Glit - 1 = 2·5·53·173·197·3677` and witness `6`. `G` divides `F2 − 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P256.NodeG

open CatCrypt.PrattCertificate

def p256Glit : Nat := 66417393611

def p256GFactors : List Nat := [2, 5, 53, 173, 197, 3677]

theorem p256GFactors_prod : p256GFactors.prod = p256Glit - 1 := by decide
theorem p256GFactors_prime : ∀ q ∈ p256GFactors, Nat.Prime q := by
  intro q hq
  simp only [p256GFactors] at hq
  fin_cases hq <;> norm_num
theorem p256GFermat : powMod 6 (p256Glit - 1) p256Glit = 1 := by decide
theorem p256GWitness : ∀ q ∈ p256GFactors, powMod 6 ((p256Glit - 1) / q) p256Glit ≠ 1 := by
  decide

theorem p256Glit_prime : Nat.Prime p256Glit :=
  lucas_of_certificate p256Glit (by decide) 6 p256GFactors
    p256GFactors_prod p256GFactors_prime p256GFermat p256GWitness

end CatCrypt.Crypto.Util.P256.NodeG
