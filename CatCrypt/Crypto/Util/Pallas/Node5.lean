/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.Pallas.Node2
public import CatCrypt.Crypto.Util.Pallas.Node3

/-!
# Sub-certificate: `8999194758858563409123804352480028797519453`

`Nat.Prime pallasBlit` via a Lucas/Pratt certificate. Its two largest factors
exceed `2^32` and are proved prime by the nested certificates `pallasB1_prime`
and `pallasB2_prime`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Pallas.Node5

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Pallas.Node2
open CatCrypt.Crypto.Util.Pallas.Node3

/-- The 143-bit prime `8999194758858563409123804352480028797519453`, a factor of
    `pallaslit - 1`. -/
def pallasBlit : Nat := 8999194758858563409123804352480028797519453

/-- The below-`2^32` prime factors of `pallasBlit - 1`, with multiplicity. -/
def pallasBSmallFactors : List Nat := [2, 2, 3, 3, 3, 3, 11, 2531, 115603, 1197907]

/-- All prime factors of `pallasBlit - 1`; the last two exceed `2^32`. -/
def pallasBFactors : List Nat := pallasBSmallFactors ++ [pallasB1lit, pallasB2lit]

theorem pallasB_prod : pallasBFactors.prod = pallasBlit - 1 := by decide
theorem pallasB_factors_prime : ∀ q ∈ pallasBFactors, Nat.Prime q := by
  intro q hq
  fin_cases hq <;> first | exact pallasB1_prime | exact pallasB2_prime | norm_num
theorem pallasB_fermat : powMod 2 (pallasBlit - 1) pallasBlit = 1 := by decide
theorem pallasB_witness :
    ∀ q ∈ pallasBFactors, powMod 2 ((pallasBlit - 1) / q) pallasBlit ≠ 1 := by
  decide

theorem pallasB_prime : Nat.Prime pallasBlit :=
  lucas_of_certificate pallasBlit (by decide) 2 pallasBFactors
    pallasB_prod pallasB_factors_prime pallasB_fermat pallasB_witness

end CatCrypt.Crypto.Util.Pallas.Node5
