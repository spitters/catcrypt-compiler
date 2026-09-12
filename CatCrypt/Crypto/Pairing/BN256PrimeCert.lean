/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Pairing.BN256.Node3
public import CatCrypt.Crypto.Pairing.BN256.Node5

/-!
# Machine-checked primality of the BN256 (Cloudflare bn256) base-field prime

`Nat.Prime bn256lit` via a Lucas/Pratt certificate. The base-field prime is
`p = 0x8fb501e34aa387f9aa6fecb86184dc21ee5b88d120b5b59e185cac6c5e089667`
(BN seed `u = 0x5A76AE9AEC588301`, `y² = x³ + 3`). Two prime factors of
`p - 1` exceed `2^32` (the 73-bit `5332323573263718838033` and the 91-bit
`1374947842730272154058024133`), so each carries its own nested Lucas
certificate. The nested factors are proved in the per-node files
`BN256.Node0`–`BN256.Node5`; this file assembles the top node. Factor data
corroborated against AUCurves `bn256_prime_certif.v`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Pairing.BN256PrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Pairing.BN256.Node3
open CatCrypt.Crypto.Pairing.BN256.Node5

/-- The certified prime `65000549695646603732796438742359905742825358107623003571877145026864184071783`
    (`256`-bit), the BN256 base-field modulus (definitionally equal to
    `CatCrypt.Crypto.Pairing.BN256PairingTowerEmit.BN256Prime`).
    `N - 1 = 2 · 3^2 · 151 · 500393 · 1868033^3 · 5332323573263718838033 · 1374947842730272154058024133`. -/
def bn256lit : Nat := 65000549695646603732796438742359905742825358107623003571877145026864184071783

/-- The `< 2^32` prime factors of `bn256lit - 1` (with multiplicity). -/
def bn256litSmall : List Nat := List.replicate 1 2 ++ [3, 3, 151, 500393, 1868033, 1868033, 1868033]

/-- All prime factors of `bn256lit - 1`, with multiplicity; product is `bn256lit - 1`. -/
def bn256litFactors : List Nat :=
  bn256litSmall ++ [pf3, pf5]

theorem bn256lit_prod : bn256litFactors.prod = bn256lit - 1 := by decide

theorem bn256lit_smallPrime : ∀ q ∈ bn256litSmall, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem bn256lit_primeFactors : ∀ q ∈ bn256litFactors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact bn256lit_smallPrime q h
  · fin_cases h
    · exact pf3_prime
    · exact pf5_prime

theorem bn256lit_fermat : powMod 3 (bn256lit - 1) bn256lit = 1 := by decide

theorem bn256lit_witness :
    ∀ q ∈ bn256litFactors, powMod 3 ((bn256lit - 1) / q) bn256lit ≠ 1 := by
  decide

/-- `Nat.Prime bn256lit`, machine-checked by a Lucas certificate (witness `3`). -/
theorem bn256lit_prime : Nat.Prime bn256lit :=
  lucas_of_certificate bn256lit (by decide) 3 bn256litFactors
    bn256lit_prod bn256lit_primeFactors bn256lit_fermat bn256lit_witness

end CatCrypt.Crypto.Pairing.BN256PrimeCert
