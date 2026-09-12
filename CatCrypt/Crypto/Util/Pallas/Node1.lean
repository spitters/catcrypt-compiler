/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Leaf sub-certificate: `417677162933` (a factor of `pallasAlit - 1`)

`Nat.Prime pallasA1lit` via a Lucas/Pratt certificate. This is a leaf of the
Pallas base-field primality certificate.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Pallas.Node1

open CatCrypt.PrattCertificate

/-- The 39-bit prime `417677162933`, a factor of `pallasAlit - 1`. -/
def pallasA1lit : Nat := 417677162933

/-- Prime factors of `pallasA1lit - 1`; product is `pallasA1lit - 1`. -/
def pallasA1Factors : List Nat := [2, 2, 59, 1973, 897019]

theorem pallasA1_prod : pallasA1Factors.prod = pallasA1lit - 1 := by decide
theorem pallasA1_factors_prime : ∀ q ∈ pallasA1Factors, Nat.Prime q := by
  intro q hq; fin_cases hq <;> norm_num
theorem pallasA1_fermat : powMod 2 (pallasA1lit - 1) pallasA1lit = 1 := by decide
theorem pallasA1_witness :
    ∀ q ∈ pallasA1Factors, powMod 2 ((pallasA1lit - 1) / q) pallasA1lit ≠ 1 := by
  decide

theorem pallasA1_prime : Nat.Prime pallasA1lit :=
  lucas_of_certificate pallasA1lit (by decide) 2 pallasA1Factors
    pallasA1_prod pallasA1_factors_prime pallasA1_fermat pallasA1_witness

end CatCrypt.Crypto.Util.Pallas.Node1
