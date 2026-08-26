/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate
import CatCrypt.Crypto.Util.Ed25519L.Node1

/-!
# Lucas node `H = 4434155615661930479`

Primality of the factor `H` of `G - 1`, via `H - 1 = 2 · 41 · 43 · I` with witness
`17`, using the child node `I`.
-/

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Ed25519L.Node2

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Ed25519L.Node1

/-- Prime factor `H` appearing in `G - 1`. -/
def factorH : ℕ := 4434155615661930479

/-- Prime factors of `H - 1`, with multiplicity. -/
def factorHFactors : List ℕ := [2, 41, 43, factorI]

theorem factorHFactors_prod : factorHFactors.prod = factorH - 1 := by decide

theorem factorHFactors_prime : ∀ q ∈ factorHFactors, Nat.Prime q := by
  intro q hq
  simp only [factorHFactors] at hq
  fin_cases hq <;> first | exact factorI_prime | norm_num

theorem factorHFermat : powMod 17 (factorH - 1) factorH = 1 := by decide

theorem factorHWitness :
    ∀ q ∈ factorHFactors, powMod 17 ((factorH - 1) / q) factorH ≠ 1 := by decide

theorem factorH_prime : Nat.Prime factorH :=
  lucas_of_certificate factorH (by decide) 17 factorHFactors
    factorHFactors_prod factorHFactors_prime factorHFermat factorHWitness

end CatCrypt.Crypto.Util.Ed25519L.Node2
