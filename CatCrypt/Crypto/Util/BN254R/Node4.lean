/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public meta import CatCrypt.Crypto.Util.BN254R.Node3
public import CatCrypt.Crypto.Util.BN254R.Node3

/-!
# BN254 scalar-field certificate — nested factor node `pf4`

Lucas certificate for the nested prime factor
`13818364434197438864469338081` in the BN254 scalar-field order chain, using
the sub-certificate `pf3` from `Node3`. The modulus exceeds `2^64`, so the
Fermat and witness checks stay on `native_decide`; the product check reduces by
`decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BN254R.Node4

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BN254R.Node3

/-- Nested prime factor `13818364434197438864469338081`
    (`94`-bit). `N - 1 = 2^5 · 5 · 823 · 1593227 · 65865678001877903`. -/
def pf4 : Nat := 13818364434197438864469338081

/-- The `< 2^32` prime factors of `pf4 - 1` (with multiplicity). -/
def pf4Small : List Nat := List.replicate 5 2 ++ [5, 823, 1593227]

/-- All prime factors of `pf4 - 1`, with multiplicity; product is `pf4 - 1`. -/
def pf4Factors : List Nat :=
  pf4Small ++ [pf3]

theorem pf4_prod : pf4Factors.prod = pf4 - 1 := by decide

theorem pf4_smallPrime : ∀ q ∈ pf4Small, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem pf4_primeFactors : ∀ q ∈ pf4Factors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact pf4_smallPrime q h
  · fin_cases h
    · exact pf3_prime

theorem pf4_fermat : powMod 3 (pf4 - 1) pf4 = 1 := by decide

theorem pf4_witness :
    ∀ q ∈ pf4Factors, powMod 3 ((pf4 - 1) / q) pf4 ≠ 1 := by
  decide

/-- `Nat.Prime pf4`, machine-checked by a Lucas certificate (witness `3`). -/
theorem pf4_prime : Nat.Prime pf4 :=
  lucas_of_certificate pf4 (by decide) 3 pf4Factors
    pf4_prod pf4_primeFactors pf4_fermat pf4_witness

end CatCrypt.Crypto.Util.BN254R.Node4
