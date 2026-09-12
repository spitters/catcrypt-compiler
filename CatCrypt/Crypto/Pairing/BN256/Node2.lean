/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public meta import CatCrypt.Crypto.Pairing.BN256.Node1
public import CatCrypt.Crypto.Pairing.BN256.Node1

/-!
# BN256 primality certificate — nested factor node `pf2`

Lucas certificate for the nested prime factor `1145258499412310747` in the
BN256 base-field prime chain, using the sub-certificate `pf1` from `Node1`. The
modulus is below `2^64`, so the Fermat, witness, and product checks reduce by
`decide` and only the small-factor primality uses `native_decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Pairing.BN256.Node2

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Pairing.BN256.Node1

/-- Nested prime factor `1145258499412310747`
    (`60`-bit). `N - 1 = 2 · 572629249706155373`. -/
def pf2 : Nat := 1145258499412310747

/-- The `< 2^32` prime factors of `pf2 - 1` (with multiplicity). -/
def pf2Small : List Nat := List.replicate 1 2

/-- All prime factors of `pf2 - 1`, with multiplicity; product is `pf2 - 1`. -/
def pf2Factors : List Nat :=
  pf2Small ++ [pf1]

theorem pf2_prod : pf2Factors.prod = pf2 - 1 := by decide

theorem pf2_smallPrime : ∀ q ∈ pf2Small, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem pf2_primeFactors : ∀ q ∈ pf2Factors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact pf2_smallPrime q h
  · fin_cases h
    · exact pf1_prime

theorem pf2_fermat : powMod 2 (pf2 - 1) pf2 = 1 := by decide

theorem pf2_witness :
    ∀ q ∈ pf2Factors, powMod 2 ((pf2 - 1) / q) pf2 ≠ 1 := by decide

/-- `Nat.Prime pf2`, machine-checked by a Lucas certificate (witness `2`). -/
theorem pf2_prime : Nat.Prime pf2 :=
  lucas_of_certificate pf2 (by decide) 2 pf2Factors
    pf2_prod pf2_primeFactors pf2_fermat pf2_witness

end CatCrypt.Crypto.Pairing.BN256.Node2
