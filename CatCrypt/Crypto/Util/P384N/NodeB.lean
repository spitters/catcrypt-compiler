/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P384N.NodeB1
public import CatCrypt.Crypto.Util.P384N.NodeC2

/-!
# Lucas certificate node `B`, the 281-bit factor of `p384Nlit - 1`

A node of the P-384 group-order primality certificate. `Nat.Prime p8Blit` with
`p8Blit - 1 = 2·3·5·151·347·1276987·p8b1lit·p8C2lit` and witness `12`, using
the child nodes `B1`, `C2`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P384N.NodeB

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P384N.NodeB1
open CatCrypt.Crypto.Util.P384N.NodeC2

def p8Blit : Nat :=
  3055465788140352002733946906144561090641249606160407884365391979704929268480326390471
def p8BFactors : List Nat := [2, 3, 5, 151, 347, 1276987, p8b1lit, p8C2lit]
theorem p8B_prod : p8BFactors.prod = p8Blit - 1 := by decide
theorem p8B_factors_prime : ∀ q ∈ p8BFactors, Nat.Prime q := by
  intro q hq
  simp only [p8BFactors] at hq
  fin_cases hq <;>
    first
      | exact p8b1_prime
      | exact p8C2_prime
      | norm_num
theorem p8B_fermat : powMod 12 (p8Blit - 1) p8Blit = 1 := by decide
theorem p8B_witness :
    ∀ q ∈ p8BFactors, powMod 12 ((p8Blit - 1) / q) p8Blit ≠ 1 := by decide
theorem p8B_prime : Nat.Prime p8Blit :=
  lucas_of_certificate p8Blit (by decide) 12 p8BFactors
    p8B_prod p8B_factors_prime p8B_fermat p8B_witness

end CatCrypt.Crypto.Util.P384N.NodeB
