/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas node `I = 1257559732178653`

Primality of the factor `I` of `H - 1`, via `I - 1 = 2^2 · 3 · 7 · 23 · 531581 · 1224481`
with witness `2`. All factors of `I - 1` are below `2^32`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.Ed25519L.Node1

open CatCrypt.PrattCertificate

/-- Prime factor `I` appearing in `H - 1`. -/
def factorI : ℕ := 1257559732178653

/-- Prime factors of `I - 1`, with multiplicity. -/
def factorIFactors : List ℕ := [2, 2, 3, 7, 23, 531581, 1224481]

theorem factorIFactors_prod : factorIFactors.prod = factorI - 1 := by decide

theorem factorIFactors_prime : ∀ q ∈ factorIFactors, Nat.Prime q := by
  intro q hq
  simp only [factorIFactors] at hq
  fin_cases hq <;> norm_num

theorem factorIFermat : powMod 2 (factorI - 1) factorI = 1 := by native_decide

theorem factorIWitness :
    ∀ q ∈ factorIFactors, powMod 2 ((factorI - 1) / q) factorI ≠ 1 := by native_decide

theorem factorI_prime : Nat.Prime factorI :=
  lucas_of_certificate factorI (by decide) 2 factorIFactors
    factorIFactors_prod factorIFactors_prime factorIFermat factorIWitness

end CatCrypt.Crypto.Util.Ed25519L.Node1
