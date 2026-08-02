/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.P25519.NodeF

/-!
# Machine-checked primality of the Curve25519 base-field prime

`Nat.Prime p25519lit` via a nested Lucas/Pratt certificate, where
`p25519lit = 2^255 - 19` is the Curve25519 base-field modulus. The
factorization `p25519lit - 1 = 2^255 - 20 = 2^2 · 3 · 65147 · F` has a
`236`-bit prime factor `F`; each prime factor of `p25519lit - 1`, of `F - 1`,
and recursively down the chain that exceeds `2^25` carries its own nested
Lucas certificate in the per-node files `P25519.NodeA`–`P25519.NodeF`. This
file assembles the top node.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.P25519PrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P25519.NodeF

/-- The certified prime `57896044618658097711785492504343953926634992332820282019728792003956564819949`
    (`255`-bit), the Curve25519 base-field modulus `2^255 - 19`.
    `N - 1 = 2^2 · 3 · 65147 · 74058212732561358302231226437062788676166966415465897661863160754340907`. -/
def p25519lit : Nat := 57896044618658097711785492504343953926634992332820282019728792003956564819949

/-- The `< 2^25` prime factors of `p25519lit - 1` (with multiplicity). -/
def p25519litSmall : List Nat := List.replicate 2 2 ++ [3, 65147]

/-- All prime factors of `p25519lit - 1`, with multiplicity; product is `p25519lit - 1`. -/
def p25519litFactors : List Nat := p25519litSmall ++ [pfF]

theorem p25519lit_prod : p25519litFactors.prod = p25519lit - 1 := by decide

theorem p25519lit_smallPrime : ∀ q ∈ p25519litSmall, Nat.Prime q := by
  intro q hq; fin_cases hq <;> norm_num

theorem p25519lit_primeFactors : ∀ q ∈ p25519litFactors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact p25519lit_smallPrime q h
  · fin_cases h
    · exact pfF_prime

theorem p25519lit_fermat : powMod 2 (p25519lit - 1) p25519lit = 1 := by native_decide

theorem p25519lit_witness :
    ∀ q ∈ p25519litFactors, powMod 2 ((p25519lit - 1) / q) p25519lit ≠ 1 := by
  native_decide

/-- `Nat.Prime p25519lit`, machine-checked by a nested Lucas certificate (witness `2`). -/
theorem p25519lit_prime : Nat.Prime p25519lit :=
  lucas_of_certificate p25519lit (by decide) 2 p25519litFactors
    p25519lit_prod p25519lit_primeFactors p25519lit_fermat p25519lit_witness

end CatCrypt.Crypto.Util.P25519PrimeCert
