/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `529709925838459440593`

A leaf node of the P-384 base-field primality certificate. `Nat.Prime p7qClit`
with `p7qClit - 1 = 2⁴·7·181·105957871·246608641` and witness `3`. This is a
factor of `p7qQlit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384P.NodeC

open CatCrypt.PrattCertificate

def p7qClit : Nat := 529709925838459440593
def p7qCFactors : List Nat := [2, 2, 2, 2, 7, 181, 105957871, 246608641]
theorem p7qC_prod : p7qCFactors.prod = p7qClit - 1 := by decide
theorem p7qC_factors_prime : ∀ q ∈ p7qCFactors, Nat.Prime q := by
  intro q hq
  simp only [p7qCFactors] at hq
  fin_cases hq <;> norm_num
theorem p7qC_fermat : powMod 3 (p7qClit - 1) p7qClit = 1 := by decide
theorem p7qC_witness :
    ∀ q ∈ p7qCFactors, powMod 3 ((p7qClit - 1) / q) p7qClit ≠ 1 := by decide
theorem p7qC_prime : Nat.Prime p7qClit :=
  lucas_of_certificate p7qClit (by decide) 3 p7qCFactors
    p7qC_prod p7qC_factors_prime p7qC_fermat p7qC_witness

end CatCrypt.Crypto.Util.P384P.NodeC
