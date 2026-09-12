/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.Pallas.Node1

/-!
# Sub-certificate: `539204044132271846773` (a factor of `pallaslit - 1`)

`Nat.Prime pallasAlit` via a Lucas/Pratt certificate. Its largest factor
exceeds `2^32` and is proved prime by the nested certificate `pallasA1_prime`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Pallas.Node4

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Pallas.Node1

/-- The 69-bit prime `539204044132271846773`, a factor of `pallaslit - 1`. -/
def pallasAlit : Nat := 539204044132271846773

/-- The below-`2^32` prime factors of `pallasAlit - 1`, with multiplicity. -/
def pallasASmallFactors : List Nat := [2, 2, 3, 3, 3, 3, 3, 89, 14923]

/-- All prime factors of `pallasAlit - 1`; the last exceeds `2^32`. -/
def pallasAFactors : List Nat := pallasASmallFactors ++ [pallasA1lit]

theorem pallasA_prod : pallasAFactors.prod = pallasAlit - 1 := by decide
theorem pallasA_factors_prime : ∀ q ∈ pallasAFactors, Nat.Prime q := by
  intro q hq; fin_cases hq <;> first | exact pallasA1_prime | norm_num
theorem pallasA_fermat : powMod 5 (pallasAlit - 1) pallasAlit = 1 := by decide
theorem pallasA_witness :
    ∀ q ∈ pallasAFactors, powMod 5 ((pallasAlit - 1) / q) pallasAlit ≠ 1 := by
  decide

theorem pallasA_prime : Nat.Prime pallasAlit :=
  lucas_of_certificate pallasAlit (by decide) 5 pallasAFactors
    pallasA_prod pallasA_factors_prime pallasA_fermat pallasA_witness

end CatCrypt.Crypto.Util.Pallas.Node4
