/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384N.NodeN1

/-!
# Lucas certificate node `55942463741690639`

A node of the P-384 group-order primality certificate. `Nat.Prime p8m3alit`
with `p8m3alit - 1 = 2·7·107·p8n1lit` and witness `7`, using the child node
`N1`. This is a factor of `p8C2lit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384N.NodeM3a

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384N.NodeN1

def p8m3alit : Nat := 55942463741690639
def p8m3aFactors : List Nat := [2, 7, 107, p8n1lit]
theorem p8m3a_prod : p8m3aFactors.prod = p8m3alit - 1 := by decide
theorem p8m3a_factors_prime : ∀ q ∈ p8m3aFactors, Nat.Prime q := by
  intro q hq
  simp only [p8m3aFactors] at hq
  fin_cases hq <;> first | exact p8n1_prime | norm_num
theorem p8m3a_fermat : powMod 7 (p8m3alit - 1) p8m3alit = 1 := by decide
theorem p8m3a_witness :
    ∀ q ∈ p8m3aFactors, powMod 7 ((p8m3alit - 1) / q) p8m3alit ≠ 1 := by decide
theorem p8m3a_prime : Nat.Prime p8m3alit :=
  lucas_of_certificate p8m3alit (by decide) 7 p8m3aFactors
    p8m3a_prod p8m3a_factors_prime p8m3a_fermat p8m3a_witness

end CatCrypt.Crypto.Util.P384N.NodeM3a
