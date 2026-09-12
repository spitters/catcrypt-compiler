/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.Vesta.Node2

/-!
# Sub-certificate: `10427374428728808478656897599072717`

`Nat.Prime vestaBlit` via a Lucas/Pratt certificate. Its largest factor exceeds
`2^32` and is proved prime by the nested certificate `vestaB1_prime`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Vesta.Node4

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Vesta.Node2

/-- The 114-bit prime `10427374428728808478656897599072717`, a factor of
    `vestalit - 1`. -/
def vestaBlit : Nat := 10427374428728808478656897599072717

/-- The below-`2^32` prime factors of `vestaBlit - 1` (`399082391 < 2^32`). -/
def vestaBSmallFactors : List Nat := [2, 2, 294793, 4229279, 399082391]

/-- All prime factors of `vestaBlit - 1`; the last exceeds `2^32`. -/
def vestaBFactors : List Nat := vestaBSmallFactors ++ [vestaB1lit]

theorem vestaB_prod : vestaBFactors.prod = vestaBlit - 1 := by decide
theorem vestaB_factors_prime : ∀ q ∈ vestaBFactors, Nat.Prime q := by
  intro q hq; fin_cases hq <;> first | exact vestaB1_prime | norm_num
theorem vestaB_fermat : powMod 2 (vestaBlit - 1) vestaBlit = 1 := by decide
theorem vestaB_witness :
    ∀ q ∈ vestaBFactors, powMod 2 ((vestaBlit - 1) / q) vestaBlit ≠ 1 := by
  decide

theorem vestaB_prime : Nat.Prime vestaBlit :=
  lucas_of_certificate vestaBlit (by decide) 2 vestaBFactors
    vestaB_prod vestaB_factors_prime vestaB_fermat vestaB_witness

end CatCrypt.Crypto.Util.Vesta.Node4
