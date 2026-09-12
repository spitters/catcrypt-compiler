/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public import CatCrypt.Crypto.Util.Secp256k1P.Node221

/-!
# Lucas certificate node `f132lit` of the secp256k1 base-field tree

`Nat.Prime f132lit` for the factor `f132lit = 132896956044521568488119`, proved
by a Lucas/Pratt certificate with witness `6`. The factorization of
`f132lit - 1` uses the nested prime `f221lit` from `Node221`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Secp256k1P.Node132

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Secp256k1P.Node221

/-- Prime factor of the secp256k1 tree requiring a nested Lucas certificate. -/
def f132lit : Nat := 132896956044521568488119

/-- Prime factors of `f132lit - 1` below `2^32`. -/
def f132SmallFactors : List Nat := [2, 3]

/-- Full prime factorization of `f132lit - 1`; product `= f132lit - 1`. -/
def f132Factors : List Nat := f132SmallFactors ++ [f221lit]

theorem f132_prod : f132Factors.prod = f132lit - 1 := by decide

theorem f132_small_prime : ∀ q ∈ f132SmallFactors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem f132_factors_prime : ∀ q ∈ f132Factors, Nat.Prime q := by
  intro q hq
  simp only [f132Factors, List.mem_append] at hq
  rcases hq with h | h
  · exact f132_small_prime q h
  · fin_cases h
    · exact f221_prime

theorem f132_fermat : powMod 6 (f132lit - 1) f132lit = 1 := by decide

theorem f132_witness :
    ∀ q ∈ f132Factors, powMod 6 ((f132lit - 1) / q) f132lit ≠ 1 := by
  decide

/-- `Nat.Prime f132lit`, machine-checked by a nested Lucas certificate. -/
theorem f132_prime : Nat.Prime f132lit :=
  lucas_of_certificate f132lit (by decide) 6 f132Factors
    f132_prod f132_factors_prime f132_fermat f132_witness

end CatCrypt.Crypto.Util.Secp256k1P.Node132
