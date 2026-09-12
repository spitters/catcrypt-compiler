/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.Secp256k1P.Node173

/-!
# Lucas certificate node `f221lit` of the secp256k1 base-field tree

`Nat.Prime f221lit` for the factor `f221lit = 22149492674086928081353`, proved
by a Lucas/Pratt certificate with witness `5`. The factorization of
`f221lit - 1` uses the nested prime `f173lit` from `Node173`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Secp256k1P.Node221

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Secp256k1P.Node173

/-- Prime factor of the secp256k1 tree requiring a nested Lucas certificate. -/
def f221lit : Nat := 22149492674086928081353

/-- Prime factors of `f221lit - 1` below `2^32`. -/
def f221SmallFactors : List Nat := [2, 2, 2, 3, 5323]

/-- Full prime factorization of `f221lit - 1`; product `= f221lit - 1`. -/
def f221Factors : List Nat := f221SmallFactors ++ [f173lit]

theorem f221_prod : f221Factors.prod = f221lit - 1 := by decide

theorem f221_small_prime : ∀ q ∈ f221SmallFactors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem f221_factors_prime : ∀ q ∈ f221Factors, Nat.Prime q := by
  intro q hq
  simp only [f221Factors, List.mem_append] at hq
  rcases hq with h | h
  · exact f221_small_prime q h
  · fin_cases h
    · exact f173_prime

theorem f221_fermat : powMod 5 (f221lit - 1) f221lit = 1 := by decide

theorem f221_witness :
    ∀ q ∈ f221Factors, powMod 5 ((f221lit - 1) / q) f221lit ≠ 1 := by
  decide

/-- `Nat.Prime f221lit`, machine-checked by a nested Lucas certificate. -/
theorem f221_prime : Nat.Prime f221lit :=
  lucas_of_certificate f221lit (by decide) 5 f221Factors
    f221_prod f221_factors_prime f221_fermat f221_witness

end CatCrypt.Crypto.Util.Secp256k1P.Node221
