/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas node `E = 3044861653679985063343`

Primality of the factor `E` of `A - 1`, via
`E - 1 = 2 · 3 · 11 · 30703 · 82163 · 132667 · 137849` with witness `5`. All
factors of `E - 1` are below `2^32`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.Ed25519L.Node6

open CatCrypt.PrattCertificate

/-- Prime factor `E` appearing in `A - 1`. -/
def factorE : ℕ := 3044861653679985063343

/-- Prime factors of `E - 1`, with multiplicity. -/
def factorEFactors : List ℕ := [2, 3, 11, 30703, 82163, 132667, 137849]

theorem factorEFactors_prod : factorEFactors.prod = factorE - 1 := by decide

theorem factorEFactors_prime : ∀ q ∈ factorEFactors, Nat.Prime q := by
  intro q hq
  simp only [factorEFactors] at hq
  fin_cases hq <;> norm_num

theorem factorEFermat : powMod 5 (factorE - 1) factorE = 1 := by native_decide

theorem factorEWitness :
    ∀ q ∈ factorEFactors, powMod 5 ((factorE - 1) / q) factorE ≠ 1 := by native_decide

theorem factorE_prime : Nat.Prime factorE :=
  lucas_of_certificate factorE (by decide) 5 factorEFactors
    factorEFactors_prod factorEFactors_prime factorEFermat factorEWitness

end CatCrypt.Crypto.Util.Ed25519L.Node6
