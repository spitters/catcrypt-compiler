/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P256.NodeF1
public import CatCrypt.Crypto.Util.P256.NodeF2
public import CatCrypt.Crypto.Util.P256.NodeF3

/-!
# Lucas certificate node `M = 774023187263532362759620327192479577272145303`

A node of the P-256 base-field primality certificate. `Nat.Prime p256Mlit` with
`p256Mlit - 1 = 2·3²·2411·F1·F2·F3` and witness `3`. `M` divides `L − 1` and uses
the child nodes `F1`, `F2`, `F3`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P256.NodeM

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P256.NodeF1
open CatCrypt.Crypto.Util.P256.NodeF2
open CatCrypt.Crypto.Util.P256.NodeF3

def p256Mlit : Nat := 774023187263532362759620327192479577272145303

def p256MFactors : List Nat := [2, 3, 3, 2411, p256F1lit, p256F2lit, p256F3lit]

theorem p256MFactors_prod : p256MFactors.prod = p256Mlit - 1 := by decide
theorem p256MFactors_prime : ∀ q ∈ p256MFactors, Nat.Prime q := by
  intro q hq
  simp only [p256MFactors] at hq
  fin_cases hq <;>
    first
      | exact p256F1lit_prime
      | exact p256F2lit_prime
      | exact p256F3lit_prime
      | norm_num
theorem p256MFermat : powMod 3 (p256Mlit - 1) p256Mlit = 1 := by decide
theorem p256MWitness :
    ∀ q ∈ p256MFactors, powMod 3 ((p256Mlit - 1) / q) p256Mlit ≠ 1 := by decide

theorem p256Mlit_prime : Nat.Prime p256Mlit :=
  lucas_of_certificate p256Mlit (by decide) 3 p256MFactors
    p256MFactors_prod p256MFactors_prime p256MFermat p256MWitness

end CatCrypt.Crypto.Util.P256.NodeM
