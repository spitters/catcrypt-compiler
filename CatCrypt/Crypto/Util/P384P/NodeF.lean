/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384P.NodeG

/-!
# Lucas certificate node `12397338596863679689524759770405177749801411`

A node of the P-384 base-field primality certificate. `Nat.Prime p7qFlit` with
`p7qFlit - 1 = 2·3·5·p7qGlit` and witness `2`, using the child node `G`.
This is a factor of `p7qQlit - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384P.NodeF

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384P.NodeG

def p7qFlit : Nat := 12397338596863679689524759770405177749801411
def p7qFFactors : List Nat := [2, 3, 5, p7qGlit]
theorem p7qF_prod : p7qFFactors.prod = p7qFlit - 1 := by decide
theorem p7qF_factors_prime : ∀ q ∈ p7qFFactors, Nat.Prime q := by
  intro q hq
  simp only [p7qFFactors] at hq
  fin_cases hq <;> first | exact p7qG_prime | norm_num
theorem p7qF_fermat : powMod 2 (p7qFlit - 1) p7qFlit = 1 := by decide
theorem p7qF_witness :
    ∀ q ∈ p7qFFactors, powMod 2 ((p7qFlit - 1) / q) p7qFlit ≠ 1 := by decide
theorem p7qF_prime : Nat.Prime p7qFlit :=
  lucas_of_certificate p7qFlit (by decide) 2 p7qFFactors
    p7qF_prod p7qF_factors_prime p7qF_fermat p7qF_witness

end CatCrypt.Crypto.Util.P384P.NodeF
