/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.Secp256k1P.NodeQ3

/-!
# Machine-checked primality of the secp256k1 base-field prime

`Nat.Prime secp256k1Plit` for `p = 2^256 - 2^32 - 977` via a Lucas/Pratt
certificate with witness `3` and `p - 1 = 2 · 3 · 7 · 13441 · q3`, where the
237-bit factor `q3` is itself proved prime by a nested Lucas certificate. The
nested factor tree is split across the `Secp256k1P/Node*` files, whose primality
lemmas this file reuses; the recursion descends through `q3lit`, `f132lit`,
`f221lit`, `f173lit`, and `f255lit`. Each certificate obligation is its own
lemma so the checks compile independently.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Secp256k1PPrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Secp256k1P.NodeQ3

/-- The secp256k1 base-field prime `p = 2^256 - 2^32 - 977`, as a literal
    (definitionally equal to `Util.Secp256k1P`). -/
def secp256k1Plit : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- Prime factors of `secp256k1Plit - 1` below `2^32`. -/
def pSmallFactors : List Nat := [2, 3, 7, 13441]

/-- Full prime factorization of `secp256k1Plit - 1`; product `= secp256k1Plit - 1`. -/
def pFactors : List Nat := pSmallFactors ++ [q3lit]

theorem pFactors_prod : pFactors.prod = secp256k1Plit - 1 := by decide

theorem pSmallFactors_prime : ∀ q ∈ pSmallFactors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem pFactors_prime : ∀ q ∈ pFactors, Nat.Prime q := by
  intro q hq
  simp only [pFactors, List.mem_append] at hq
  rcases hq with h | h
  · exact pSmallFactors_prime q h
  · fin_cases h
    · exact q3_prime

theorem pFermat : powMod 3 (secp256k1Plit - 1) secp256k1Plit = 1 := by decide

theorem pWitness :
    ∀ q ∈ pFactors, powMod 3 ((secp256k1Plit - 1) / q) secp256k1Plit ≠ 1 := by
  decide

/-- `Nat.Prime secp256k1Plit`, machine-checked by a Lucas certificate. -/
theorem secp256k1Plit_prime : Nat.Prime secp256k1Plit :=
  lucas_of_certificate secp256k1Plit (by decide) 3 pFactors
    pFactors_prod pFactors_prime pFermat pWitness

end CatCrypt.Crypto.Util.Secp256k1PPrimeCert
