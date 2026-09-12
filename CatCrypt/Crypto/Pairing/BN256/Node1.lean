/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public meta import CatCrypt.Crypto.Pairing.BN256.Node0
public import CatCrypt.Crypto.Pairing.BN256.Node0

/-!
# BN256 primality certificate — nested factor node `pf1`

Lucas certificate for the nested prime factor `572629249706155373` in the BN256
base-field prime chain, using the sub-certificate `pf0` from `Node0`. The
modulus is below `2^64`, so the Fermat, witness, and product checks reduce by
`decide` and only the small-factor primality uses `native_decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Pairing.BN256.Node1

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Pairing.BN256.Node0

/-- Nested prime factor `572629249706155373`
    (`59`-bit). `N - 1 = 2^2 · 10259 · 13954314497177`. -/
def pf1 : Nat := 572629249706155373

/-- The `< 2^32` prime factors of `pf1 - 1` (with multiplicity). -/
def pf1Small : List Nat := List.replicate 2 2 ++ [10259]

/-- All prime factors of `pf1 - 1`, with multiplicity; product is `pf1 - 1`. -/
def pf1Factors : List Nat :=
  pf1Small ++ [pf0]

theorem pf1_prod : pf1Factors.prod = pf1 - 1 := by decide

theorem pf1_smallPrime : ∀ q ∈ pf1Small, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem pf1_primeFactors : ∀ q ∈ pf1Factors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact pf1_smallPrime q h
  · fin_cases h
    · exact pf0_prime

theorem pf1_fermat : powMod 2 (pf1 - 1) pf1 = 1 := by decide

theorem pf1_witness :
    ∀ q ∈ pf1Factors, powMod 2 ((pf1 - 1) / q) pf1 ≠ 1 := by decide

/-- `Nat.Prime pf1`, machine-checked by a Lucas certificate (witness `2`). -/
theorem pf1_prime : Nat.Prime pf1 :=
  lucas_of_certificate pf1 (by decide) 2 pf1Factors
    pf1_prod pf1_primeFactors pf1_fermat pf1_witness

end CatCrypt.Crypto.Pairing.BN256.Node1
