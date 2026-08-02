/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas node `213441916511`

Primality of the factor `213441916511` of `D - 1`, via
`213441916511 - 1 = 2 · 5 · 73 · 292386187` with witness `13`. All factors are
below `2^32`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.Ed25519L.Node4

open CatCrypt.PrattCertificate

/-- Prime factor `213441916511` appearing in `D - 1`. -/
def factorF213 : ℕ := 213441916511

/-- Prime factors of `213441916511 - 1`, with multiplicity. -/
def factorF213Factors : List ℕ := [2, 5, 73, 292386187]

theorem factorF213Factors_prod : factorF213Factors.prod = factorF213 - 1 := by decide

theorem factorF213Factors_prime : ∀ q ∈ factorF213Factors, Nat.Prime q := by
  intro q hq
  simp only [factorF213Factors] at hq
  fin_cases hq <;> norm_num

theorem factorF213Fermat : powMod 13 (factorF213 - 1) factorF213 = 1 := by native_decide

theorem factorF213Witness :
    ∀ q ∈ factorF213Factors, powMod 13 ((factorF213 - 1) / q) factorF213 ≠ 1 := by native_decide

theorem factorF213_prime : Nat.Prime factorF213 :=
  lucas_of_certificate factorF213 (by decide) 13 factorF213Factors
    factorF213Factors_prod factorF213Factors_prime factorF213Fermat factorF213Witness

end CatCrypt.Crypto.Util.Ed25519L.Node4
