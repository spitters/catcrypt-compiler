/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.P256.NodeM

/-!
# Lucas certificate node `L = 835945042244614951780389953367877943453916927241`

The 160-bit prime cofactor of `p − 1` for the P-256 base field. `Nat.Prime
p256Llit` with `p256Llit - 1 = 2³·3³·5·M` and witness `11`, using the child
node `M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P256.NodeL

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P256.NodeM

def p256Llit : Nat := 835945042244614951780389953367877943453916927241

def p256LFactors : List Nat := [2, 2, 2, 3, 3, 3, 5, p256Mlit]

theorem p256LFactors_prod : p256LFactors.prod = p256Llit - 1 := by decide
theorem p256LFactors_prime : ∀ q ∈ p256LFactors, Nat.Prime q := by
  intro q hq
  simp only [p256LFactors] at hq
  fin_cases hq <;> first | exact p256Mlit_prime | norm_num
theorem p256LFermat : powMod 11 (p256Llit - 1) p256Llit = 1 := by decide
theorem p256LWitness :
    ∀ q ∈ p256LFactors, powMod 11 ((p256Llit - 1) / q) p256Llit ≠ 1 := by decide

theorem p256Llit_prime : Nat.Prime p256Llit :=
  lucas_of_certificate p256Llit (by decide) 11 p256LFactors
    p256LFactors_prod p256LFactors_prime p256LFermat p256LWitness

end CatCrypt.Crypto.Util.P256.NodeL
