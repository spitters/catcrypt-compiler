/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public meta import CatCrypt.Crypto.Util.P25519.NodeA
public import CatCrypt.Crypto.Util.P25519.NodeA

/-!
# P25519 primality certificate — nested factor node `pfB`

Lucas certificate for the nested prime factor `72106336199` in the
`2^255 - 19` prime chain, using the sub-certificate `pfA` from `NodeA`. The
product check reduces by `decide` and the Fermat and witness checks by
`native_decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P25519.NodeB

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P25519.NodeA

/-- Nested prime factor `72106336199`
    (`37`-bit). `N - 1 = 2 · 13 · 2773320623`. -/
def pfB : Nat := 72106336199

/-- The `< 2^25` prime factors of `pfB - 1` (with multiplicity). -/
def pfBSmall : List Nat := [2, 13]

/-- All prime factors of `pfB - 1`, with multiplicity; product is `pfB - 1`. -/
def pfBFactors : List Nat := pfBSmall ++ [pfA]

theorem pfB_prod : pfBFactors.prod = pfB - 1 := by decide

theorem pfB_smallPrime : ∀ q ∈ pfBSmall, Nat.Prime q := by
  intro q hq; fin_cases hq <;> norm_num

theorem pfB_primeFactors : ∀ q ∈ pfBFactors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact pfB_smallPrime q h
  · fin_cases h
    · exact pfA_prime

theorem pfB_fermat : powMod 7 (pfB - 1) pfB = 1 := by decide

theorem pfB_witness :
    ∀ q ∈ pfBFactors, powMod 7 ((pfB - 1) / q) pfB ≠ 1 := by decide

/-- `Nat.Prime pfB`, machine-checked by a Lucas certificate (witness `7`). -/
theorem pfB_prime : Nat.Prime pfB :=
  lucas_of_certificate pfB (by decide) 7 pfBFactors
    pfB_prod pfB_primeFactors pfB_fermat pfB_witness

end CatCrypt.Crypto.Util.P25519.NodeB
