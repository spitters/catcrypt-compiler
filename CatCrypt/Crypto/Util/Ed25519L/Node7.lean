/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.Ed25519L.Node6

/-!
# Lucas node `A = 198211423230930754013084525763697`

Primality of the factor `A` of `ℓ - 1`, via `A - 1 = 2^4 · 3 · 23 · 58964693 · E`
with witness `5`, using the child node `E`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Ed25519L.Node7

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Ed25519L.Node6

/-- Prime factor `A` of `ℓ - 1`. -/
def factorA : ℕ := 198211423230930754013084525763697

/-- Prime factors of `A - 1`, with multiplicity. -/
def factorAFactors : List ℕ := [2, 2, 2, 2, 3, 23, 58964693, factorE]

theorem factorAFactors_prod : factorAFactors.prod = factorA - 1 := by decide

theorem factorAFactors_prime : ∀ q ∈ factorAFactors, Nat.Prime q := by
  intro q hq
  simp only [factorAFactors] at hq
  fin_cases hq <;> first | exact factorE_prime | norm_num

theorem factorAFermat : powMod 5 (factorA - 1) factorA = 1 := by decide

theorem factorAWitness :
    ∀ q ∈ factorAFactors, powMod 5 ((factorA - 1) / q) factorA ≠ 1 := by decide

theorem factorA_prime : Nat.Prime factorA :=
  lucas_of_certificate factorA (by decide) 5 factorAFactors
    factorAFactors_prod factorAFactors_prime factorAFermat factorAWitness

end CatCrypt.Crypto.Util.Ed25519L.Node7
