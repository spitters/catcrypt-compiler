/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Leaf sub-certificate: `325086459374267` (a factor of `pallasBlit - 1`)

`Nat.Prime pallasB2lit` via a Lucas/Pratt certificate. This is a leaf of the
Pallas base-field primality certificate.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Pallas.Node3

open CatCrypt.PrattCertificate

/-- The 49-bit prime `325086459374267`, a factor of `pallasBlit - 1`. -/
def pallasB2lit : Nat := 325086459374267

/-- Prime factors of `pallasB2lit - 1`; product is `pallasB2lit - 1`. -/
def pallasB2Factors : List Nat := [2, 509, 413527, 772231]

theorem pallasB2_prod : pallasB2Factors.prod = pallasB2lit - 1 := by decide
theorem pallasB2_factors_prime : ∀ q ∈ pallasB2Factors, Nat.Prime q := by
  intro q hq; fin_cases hq <;> norm_num
theorem pallasB2_fermat : powMod 2 (pallasB2lit - 1) pallasB2lit = 1 := by decide
theorem pallasB2_witness :
    ∀ q ∈ pallasB2Factors, powMod 2 ((pallasB2lit - 1) / q) pallasB2lit ≠ 1 := by
  decide

theorem pallasB2_prime : Nat.Prime pallasB2lit :=
  lucas_of_certificate pallasB2lit (by decide) 2 pallasB2Factors
    pallasB2_prod pallasB2_factors_prime pallasB2_fermat pallasB2_witness

end CatCrypt.Crypto.Util.Pallas.Node3
