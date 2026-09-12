/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public meta import CatCrypt.Crypto.Pairing.BN256.Node2
public import CatCrypt.Crypto.Pairing.BN256.Node2

/-!
# BN256 primality certificate — nested factor node `pf3`

Lucas certificate for the nested prime factor `5332323573263718838033` in the
BN256 base-field prime chain, using the sub-certificate `pf2` from `Node2`. The
modulus exceeds `2^64`, so the Fermat and witness checks stay on `native_decide`;
the product check reduces by `decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Pairing.BN256.Node3

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Pairing.BN256.Node2

/-- Nested prime factor `5332323573263718838033`
    (`73`-bit). `N - 1 = 2^4 · 3 · 97 · 1145258499412310747`. -/
def pf3 : Nat := 5332323573263718838033

/-- The `< 2^32` prime factors of `pf3 - 1` (with multiplicity). -/
def pf3Small : List Nat := List.replicate 4 2 ++ [3, 97]

/-- All prime factors of `pf3 - 1`, with multiplicity; product is `pf3 - 1`. -/
def pf3Factors : List Nat :=
  pf3Small ++ [pf2]

theorem pf3_prod : pf3Factors.prod = pf3 - 1 := by decide

theorem pf3_smallPrime : ∀ q ∈ pf3Small, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem pf3_primeFactors : ∀ q ∈ pf3Factors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact pf3_smallPrime q h
  · fin_cases h
    · exact pf2_prime

theorem pf3_fermat : powMod 7 (pf3 - 1) pf3 = 1 := by decide

theorem pf3_witness :
    ∀ q ∈ pf3Factors, powMod 7 ((pf3 - 1) / q) pf3 ≠ 1 := by
  decide

/-- `Nat.Prime pf3`, machine-checked by a Lucas certificate (witness `7`). -/
theorem pf3_prime : Nat.Prime pf3 :=
  lucas_of_certificate pf3 (by decide) 7 pf3Factors
    pf3_prod pf3_primeFactors pf3_fermat pf3_witness

end CatCrypt.Crypto.Pairing.BN256.Node3
