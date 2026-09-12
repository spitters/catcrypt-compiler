/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `37344768852931`

A leaf node of the P-384 group-order primality certificate. `Nat.Prime p8n1lit`
with `p8n1lit - 1 = 2·3·5·7·11²·149·9863677` and witness `3`. This is a factor
of `p8m3alit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384N.NodeN1

open CatCrypt.PrattCertificate

def p8n1lit : Nat := 37344768852931
def p8n1Factors : List Nat := [2, 3, 5, 7, 11, 11, 149, 9863677]
theorem p8n1_prod : p8n1Factors.prod = p8n1lit - 1 := by decide
theorem p8n1_factors_prime : ∀ q ∈ p8n1Factors, Nat.Prime q := by
  intro q hq
  simp only [p8n1Factors] at hq
  fin_cases hq <;> norm_num
theorem p8n1_fermat : powMod 3 (p8n1lit - 1) p8n1lit = 1 := by decide
theorem p8n1_witness :
    ∀ q ∈ p8n1Factors, powMod 3 ((p8n1lit - 1) / q) p8n1lit ≠ 1 := by decide
theorem p8n1_prime : Nat.Prime p8n1lit :=
  lucas_of_certificate p8n1lit (by decide) 3 p8n1Factors
    p8n1_prod p8n1_factors_prime p8n1_fermat p8n1_witness

end CatCrypt.Crypto.Util.P384N.NodeN1
