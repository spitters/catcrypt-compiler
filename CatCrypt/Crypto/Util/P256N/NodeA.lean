/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `A = 1002328039319`

A leaf node of the P-256 group-order primality certificate. `Nat.Prime p256nAlit`
with `p256nAlit - 1 = 2·126241·3969899` and witness `19`. `A` divides `n − 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P256N.NodeA

open CatCrypt.PrattCertificate

def p256nAlit : Nat := 1002328039319

def p256nAFactors : List Nat := [2, 126241, 3969899]

theorem p256nAFactors_prod : p256nAFactors.prod = p256nAlit - 1 := by decide
theorem p256nAFactors_prime : ∀ q ∈ p256nAFactors, Nat.Prime q := by
  intro q hq
  simp only [p256nAFactors] at hq
  fin_cases hq <;> norm_num
theorem p256nAFermat : powMod 19 (p256nAlit - 1) p256nAlit = 1 := by decide
theorem p256nAWitness :
    ∀ q ∈ p256nAFactors, powMod 19 ((p256nAlit - 1) / q) p256nAlit ≠ 1 := by decide

theorem p256nAlit_prime : Nat.Prime p256nAlit :=
  lucas_of_certificate p256nAlit (by decide) 19 p256nAFactors
    p256nAFactors_prod p256nAFactors_prime p256nAFermat p256nAWitness

end CatCrypt.Crypto.Util.P256N.NodeA
