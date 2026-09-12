/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Leaf sub-certificate: `22160661629` (a factor of `pallasBlit - 1`)

`Nat.Prime pallasB1lit` via a Lucas/Pratt certificate. This is a leaf of the
Pallas base-field primality certificate.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Pallas.Node2

open CatCrypt.PrattCertificate

/-- The 35-bit prime `22160661629`, a factor of `pallasBlit - 1`. -/
def pallasB1lit : Nat := 22160661629

/-- Prime factors of `pallasB1lit - 1`; product is `pallasB1lit - 1`. -/
def pallasB1Factors : List Nat := [2, 2, 7, 19, 41655379]

theorem pallasB1_prod : pallasB1Factors.prod = pallasB1lit - 1 := by decide
theorem pallasB1_factors_prime : ∀ q ∈ pallasB1Factors, Nat.Prime q := by
  intro q hq; fin_cases hq <;> norm_num
theorem pallasB1_fermat : powMod 3 (pallasB1lit - 1) pallasB1lit = 1 := by decide
theorem pallasB1_witness :
    ∀ q ∈ pallasB1Factors, powMod 3 ((pallasB1lit - 1) / q) pallasB1lit ≠ 1 := by
  decide

theorem pallasB1_prime : Nat.Prime pallasB1lit :=
  lucas_of_certificate pallasB1lit (by decide) 3 pallasB1Factors
    pallasB1_prod pallasB1_factors_prime pallasB1_fermat pallasB1_witness

end CatCrypt.Crypto.Util.Pallas.Node2
