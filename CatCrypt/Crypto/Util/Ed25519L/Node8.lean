/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate
import CatCrypt.Crypto.Util.Ed25519L.Node5

/-!
# Lucas node `B = 276602624281642239937218680557139826668747`

Primality of the factor `B` of `ℓ - 1`, via `B - 1 = 2 · 7 · D` with witness `2`,
using the child node `D`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.Ed25519L.Node8

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Ed25519L.Node5

/-- Prime factor `B` of `ℓ - 1`. -/
def factorB : ℕ := 276602624281642239937218680557139826668747

/-- Prime factors of `B - 1`, with multiplicity. -/
def factorBFactors : List ℕ := [2, 7, factorD]

theorem factorBFactors_prod : factorBFactors.prod = factorB - 1 := by decide

theorem factorBFactors_prime : ∀ q ∈ factorBFactors, Nat.Prime q := by
  intro q hq
  simp only [factorBFactors] at hq
  fin_cases hq <;> first | exact factorD_prime | norm_num

theorem factorBFermat : powMod 2 (factorB - 1) factorB = 1 := by native_decide

theorem factorBWitness :
    ∀ q ∈ factorBFactors, powMod 2 ((factorB - 1) / q) factorB ≠ 1 := by native_decide

theorem factorB_prime : Nat.Prime factorB :=
  lucas_of_certificate factorB (by decide) 2 factorBFactors
    factorBFactors_prod factorBFactors_prime factorBFermat factorBWitness

end CatCrypt.Crypto.Util.Ed25519L.Node8
