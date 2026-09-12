/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.BN254R.Node2
public import CatCrypt.Crypto.Util.BN254R.Node4

/-!
# Machine-checked primality of the BN254 scalar-field order `r`

`Nat.Prime bn254Rlit` via a Lucas/Pratt certificate. The scalar-field prime is
`r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001`
(alt-bn128 / EIP-196 `Fr`, 2-adicity 28). Two prime factors of `r - 1` exceed
`2^32` (the 51-bit `1670836401704629` and the 94-bit
`13818364434197438864469338081`), so each carries its own nested Lucas
certificate. The nested factors are proved in the per-node files
`BN254R.Node0`–`BN254R.Node4`; this file assembles the top node.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BN254RPrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BN254R.Node2
open CatCrypt.Crypto.Util.BN254R.Node4

/-- The certified prime `21888242871839275222246405745257275088548364400416034343698204186575808495617`
    (`254`-bit), the BN254 scalar-field order `r` (definitionally equal to
    `CatCrypt.Crypto.ECDSA.BN254GroupParam.BN254R`).
    `N - 1 = 2^28 · 3^2 · 13 · 29 · 983 · 11003 · 237073 · 405928799 · 1670836401704629 · 13818364434197438864469338081`. -/
def bn254Rlit : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- The `< 2^32` prime factors of `bn254Rlit - 1` (with multiplicity). -/
def bn254RlitSmall : List Nat := List.replicate 28 2 ++ [3, 3, 13, 29, 983, 11003, 237073, 405928799]

/-- All prime factors of `bn254Rlit - 1`, with multiplicity; product is `bn254Rlit - 1`. -/
def bn254RlitFactors : List Nat :=
  bn254RlitSmall ++ [pf2, pf4]

theorem bn254Rlit_prod : bn254RlitFactors.prod = bn254Rlit - 1 := by decide

theorem bn254Rlit_smallPrime : ∀ q ∈ bn254RlitSmall, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem bn254Rlit_primeFactors : ∀ q ∈ bn254RlitFactors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact bn254Rlit_smallPrime q h
  · fin_cases h
    · exact pf2_prime
    · exact pf4_prime

theorem bn254Rlit_fermat : powMod 5 (bn254Rlit - 1) bn254Rlit = 1 := by decide

theorem bn254Rlit_witness :
    ∀ q ∈ bn254RlitFactors, powMod 5 ((bn254Rlit - 1) / q) bn254Rlit ≠ 1 := by
  decide

/-- `Nat.Prime bn254Rlit`, machine-checked by a Lucas certificate (witness `5`). -/
theorem bn254Rlit_prime : Nat.Prime bn254Rlit :=
  lucas_of_certificate bn254Rlit (by decide) 5 bn254RlitFactors
    bn254Rlit_prod bn254Rlit_primeFactors bn254Rlit_fermat bn254Rlit_witness

end CatCrypt.Crypto.Util.BN254RPrimeCert
