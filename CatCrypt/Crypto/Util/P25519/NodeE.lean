/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public meta import CatCrypt.Crypto.Util.P25519.NodeB
public import CatCrypt.Crypto.Util.P25519.NodeB
public meta import CatCrypt.Crypto.Util.P25519.NodeC
public import CatCrypt.Crypto.Util.P25519.NodeC

/-!
# P25519 primality certificate — nested factor node `pfE`

Lucas certificate for the nested prime factor
`75445702479781427272750846543864801` in the `2^255 - 19` prime chain, using
the sub-certificates `pfB` from `NodeB` and `pfC` from `NodeC`. The product
check reduces by `decide` and the Fermat and witness checks by `native_decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P25519.NodeE

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P25519.NodeB
open CatCrypt.Crypto.Util.P25519.NodeC

/-- Nested prime factor `75445702479781427272750846543864801`
    (`116`-bit). `N - 1 = 2^5 · 3^2 · 5^2 · 75707 · 72106336199 · 1919519569386763`. -/
def pfE : Nat := 75445702479781427272750846543864801

/-- The `< 2^25` prime factors of `pfE - 1` (with multiplicity). -/
def pfESmall : List Nat := List.replicate 5 2 ++ [3, 3, 5, 5, 75707]

/-- All prime factors of `pfE - 1`, with multiplicity; product is `pfE - 1`. -/
def pfEFactors : List Nat := pfESmall ++ [pfB, pfC]

theorem pfE_prod : pfEFactors.prod = pfE - 1 := by decide

theorem pfE_smallPrime : ∀ q ∈ pfESmall, Nat.Prime q := by
  intro q hq; fin_cases hq <;> norm_num

theorem pfE_primeFactors : ∀ q ∈ pfEFactors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact pfE_smallPrime q h
  · fin_cases h
    · exact pfB_prime
    · exact pfC_prime

theorem pfE_fermat : powMod 7 (pfE - 1) pfE = 1 := by decide

theorem pfE_witness :
    ∀ q ∈ pfEFactors, powMod 7 ((pfE - 1) / q) pfE ≠ 1 := by decide

/-- `Nat.Prime pfE`, machine-checked by a Lucas certificate (witness `7`). -/
theorem pfE_prime : Nat.Prime pfE :=
  lucas_of_certificate pfE (by decide) 7 pfEFactors
    pfE_prod pfE_primeFactors pfE_fermat pfE_witness

end CatCrypt.Crypto.Util.P25519.NodeE
