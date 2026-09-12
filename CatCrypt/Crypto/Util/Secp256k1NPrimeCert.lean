/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.Secp256k1N.Node107
public import CatCrypt.Crypto.Util.Secp256k1N.Node174
public import CatCrypt.Crypto.Util.Secp256k1N.Node341

/-!
# Machine-checked primality of the secp256k1 group order

`Nat.Prime secp256k1Nlit` for the secp256k1 order `n` via a Lucas/Pratt
certificate with witness `7` and
`n - 1 = 2^6 · 3 · 149 · 631 · A · B · C`, where the three factors
`A = g107lit`, `B = g174lit`, and `C = g341lit` each exceed `2^32` and are
proved prime by nested Lucas certificates in the `Secp256k1N/Node*` files (`C`
recursing through `g290lit` and `g297lit`). Each certificate obligation is its
own lemma so the checks compile independently.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Secp256k1NPrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Secp256k1N.Node107
open CatCrypt.Crypto.Util.Secp256k1N.Node174
open CatCrypt.Crypto.Util.Secp256k1N.Node341

/-- The secp256k1 group order `n`, as a literal (definitionally equal to
    `Util.Secp256k1N`). -/
def secp256k1Nlit : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- Prime factors of `secp256k1Nlit - 1` below `2^32`. -/
def nSmallFactors : List Nat := List.replicate 6 2 ++ [3, 149, 631]

/-- Full prime factorization of `secp256k1Nlit - 1`; product `= secp256k1Nlit - 1`. -/
def nFactors : List Nat := nSmallFactors ++ [g107lit, g174lit, g341lit]

theorem nFactors_prod : nFactors.prod = secp256k1Nlit - 1 := by decide

theorem nSmallFactors_prime : ∀ q ∈ nSmallFactors, Nat.Prime q := by decide

theorem nFactors_prime : ∀ q ∈ nFactors, Nat.Prime q := by
  intro q hq
  simp only [nFactors, List.mem_append] at hq
  rcases hq with h | h
  · exact nSmallFactors_prime q h
  · fin_cases h
    · exact g107_prime
    · exact g174_prime
    · exact g341_prime

theorem nFermat : powMod 7 (secp256k1Nlit - 1) secp256k1Nlit = 1 := by decide

theorem nWitness :
    ∀ q ∈ nFactors, powMod 7 ((secp256k1Nlit - 1) / q) secp256k1Nlit ≠ 1 := by
  decide

/-- `Nat.Prime secp256k1Nlit`, machine-checked by a Lucas certificate. -/
theorem secp256k1Nlit_prime : Nat.Prime secp256k1Nlit :=
  lucas_of_certificate secp256k1Nlit (by decide) 7 nFactors
    nFactors_prod nFactors_prime nFermat nWitness

end CatCrypt.Crypto.Util.Secp256k1NPrimeCert
