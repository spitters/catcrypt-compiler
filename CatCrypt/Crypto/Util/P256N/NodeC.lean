/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `C = 208150935158385979`

A leaf node of the P-256 group-order primality certificate. `Nat.Prime p256nClit`
with `p256nClit - 1 = 2·3·11·43·127·3023·191039911` and witness `2`. `C` divides
`B − 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P256N.NodeC

open CatCrypt.PrattCertificate

def p256nClit : Nat := 208150935158385979

def p256nCFactors : List Nat := [2, 3, 11, 43, 127, 3023, 191039911]

theorem p256nCFactors_prod : p256nCFactors.prod = p256nClit - 1 := by decide
theorem p256nCFactors_prime : ∀ q ∈ p256nCFactors, Nat.Prime q := by
  intro q hq
  simp only [p256nCFactors] at hq
  fin_cases hq <;> norm_num
theorem p256nCFermat : powMod 2 (p256nClit - 1) p256nClit = 1 := by decide
theorem p256nCWitness :
    ∀ q ∈ p256nCFactors, powMod 2 ((p256nClit - 1) / q) p256nClit ≠ 1 := by decide

theorem p256nClit_prime : Nat.Prime p256nClit :=
  lucas_of_certificate p256nClit (by decide) 2 p256nCFactors
    p256nCFactors_prod p256nCFactors_prime p256nCFermat p256nCWitness

end CatCrypt.Crypto.Util.P256N.NodeC
