/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate
import CatCrypt.Crypto.Util.Ed25519L.Node2

/-!
# Lucas node `G = 172054593956031949258510691`

Primality of the factor `G` of `D - 1`, via `G - 1 = 2 · 5 · 1361 · 2851 · H` with
witness `2`, using the child node `H`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.Ed25519L.Node3

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Ed25519L.Node2

/-- Prime factor `G` appearing in `D - 1`. -/
def factorG : ℕ := 172054593956031949258510691

/-- Prime factors of `G - 1`, with multiplicity. -/
def factorGFactors : List ℕ := [2, 5, 1361, 2851, factorH]

theorem factorGFactors_prod : factorGFactors.prod = factorG - 1 := by decide

theorem factorGFactors_prime : ∀ q ∈ factorGFactors, Nat.Prime q := by
  intro q hq
  simp only [factorGFactors] at hq
  fin_cases hq <;> first | exact factorH_prime | norm_num

theorem factorGFermat : powMod 2 (factorG - 1) factorG = 1 := by native_decide

theorem factorGWitness :
    ∀ q ∈ factorGFactors, powMod 2 ((factorG - 1) / q) factorG ≠ 1 := by native_decide

theorem factorG_prime : Nat.Prime factorG :=
  lucas_of_certificate factorG (by decide) 2 factorGFactors
    factorGFactors_prod factorGFactors_prime factorGFermat factorGWitness

end CatCrypt.Crypto.Util.Ed25519L.Node3
