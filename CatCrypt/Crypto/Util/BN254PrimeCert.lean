/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.BN254.Node0
import CatCrypt.Crypto.Util.BN254.Node3

/-!
# Machine-checked primality of the BN254 (alt-bn128) base-field prime

`Nat.Prime bn254lit` via a Lucas/Pratt certificate. The base-field prime is
`p = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47`
(EIP-196 / EIP-197 alt-bn128, `y² = x³ + 3`). Two prime factors of `p - 1`
exceed `2^32` (`11465965001` and the 134-bit
`13427688667394608761327070753331941386769`), so each carries its own nested
Lucas certificate; the deepest chain descends through `2480874801745591` and
`35385462869`. The nested factors are proved in the per-node files
`BN254.Node0`–`BN254.Node3`; this file assembles the top node. Factor data
corroborated against AUCurves `bn254_prime_certif.v`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.BN254PrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BN254.Node0
open CatCrypt.Crypto.Util.BN254.Node3

/-- The certified prime `21888242871839275222246405745257275088696311157297823662689037894645226208583`
    (`254`-bit), the BN254 base-field modulus (definitionally equal to
    `CatCrypt.Util.BN254`).
    `N - 1 = 2 · 3^2 · 13 · 29 · 67 · 229 · 311 · 983 · 11003 · 405928799 · 11465965001 · 13427688667394608761327070753331941386769`. -/
def bn254lit : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- The `< 2^32` prime factors of `bn254lit - 1` (with multiplicity). -/
def bn254litSmall : List Nat := List.replicate 1 2 ++ [3, 3, 13, 29, 67, 229, 311, 983, 11003, 405928799]

/-- All prime factors of `bn254lit - 1`, with multiplicity; product is `bn254lit - 1`. -/
def bn254litFactors : List Nat :=
  bn254litSmall ++ [pf0, pf3]

theorem bn254lit_prod : bn254litFactors.prod = bn254lit - 1 := by decide

theorem bn254lit_smallPrime : ∀ q ∈ bn254litSmall, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem bn254lit_primeFactors : ∀ q ∈ bn254litFactors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact bn254lit_smallPrime q h
  · fin_cases h
    · exact pf0_prime
    · exact pf3_prime

theorem bn254lit_fermat : powMod 3 (bn254lit - 1) bn254lit = 1 := by native_decide

theorem bn254lit_witness :
    ∀ q ∈ bn254litFactors, powMod 3 ((bn254lit - 1) / q) bn254lit ≠ 1 := by
  native_decide

/-- `Nat.Prime bn254lit`, machine-checked by a Lucas certificate (witness `3`). -/
theorem bn254lit_prime : Nat.Prime bn254lit :=
  lucas_of_certificate bn254lit (by decide) 3 bn254litFactors
    bn254lit_prod bn254lit_primeFactors bn254lit_fermat bn254lit_witness

end CatCrypt.Crypto.Util.BN254PrimeCert
