/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate
import CatCrypt.Crypto.Util.Ed25519L.Node3
import CatCrypt.Crypto.Util.Ed25519L.Node4

/-!
# Lucas node `D = 19757330305831588566944191468367130476339`

Primality of the factor `D` of `B - 1`, via `D - 1 = 2 · 269 · 213441916511 · G`
with witness `2`, using the child nodes `213441916511` and `G`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.Ed25519L.Node5

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Ed25519L.Node3
open CatCrypt.Crypto.Util.Ed25519L.Node4

/-- Prime factor `D` appearing in `B - 1`. -/
def factorD : ℕ := 19757330305831588566944191468367130476339

/-- Prime factors of `D - 1`, with multiplicity. -/
def factorDFactors : List ℕ := [2, 269, factorF213, factorG]

theorem factorDFactors_prod : factorDFactors.prod = factorD - 1 := by decide

theorem factorDFactors_prime : ∀ q ∈ factorDFactors, Nat.Prime q := by
  intro q hq
  simp only [factorDFactors] at hq
  fin_cases hq <;> first | exact factorF213_prime | exact factorG_prime | norm_num

theorem factorDFermat : powMod 2 (factorD - 1) factorD = 1 := by native_decide

theorem factorDWitness :
    ∀ q ∈ factorDFactors, powMod 2 ((factorD - 1) / q) factorD ≠ 1 := by native_decide

theorem factorD_prime : Nat.Prime factorD :=
  lucas_of_certificate factorD (by decide) 2 factorDFactors
    factorDFactors_prod factorDFactors_prime factorDFermat factorDWitness

end CatCrypt.Crypto.Util.Ed25519L.Node5
