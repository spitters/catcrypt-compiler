/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P256N.NodeC

/-!
# Lucas certificate node `B = 2624747550333869278416773953`

A node of the P-256 group-order primality certificate. `Nat.Prime p256nBlit` with
`p256nBlit - 1 = 2⁶·3²·1297·16879·C` and witness `7`. `B` divides `n − 1` and
uses the child node `C`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P256N.NodeB

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P256N.NodeC

def p256nBlit : Nat := 2624747550333869278416773953

def p256nBFactors : List Nat := [2, 2, 2, 2, 2, 2, 3, 3, 1297, 16879, p256nClit]

theorem p256nBFactors_prod : p256nBFactors.prod = p256nBlit - 1 := by decide
theorem p256nBFactors_prime : ∀ q ∈ p256nBFactors, Nat.Prime q := by
  intro q hq
  simp only [p256nBFactors] at hq
  fin_cases hq <;> first | exact p256nClit_prime | norm_num
theorem p256nBFermat : powMod 7 (p256nBlit - 1) p256nBlit = 1 := by decide
theorem p256nBWitness :
    ∀ q ∈ p256nBFactors, powMod 7 ((p256nBlit - 1) / q) p256nBlit ≠ 1 := by decide

theorem p256nBlit_prime : Nat.Prime p256nBlit :=
  lucas_of_certificate p256nBlit (by decide) 7 p256nBFactors
    p256nBFactors_prod p256nBFactors_prime p256nBFermat p256nBWitness

end CatCrypt.Crypto.Util.P256N.NodeB
