/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Lucas certificate node `f173lit` of the secp256k1 base-field tree

`Nat.Prime f173lit` for the factor `f173lit = 173378833005251801`, proved by a
Lucas/Pratt certificate with witness `6`. This is a leaf node whose modulus is
below `2^64`, so the Fermat and witness checks are discharged by `decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Secp256k1P.Node173

open CatCrypt.PrattCertificate

/-- Prime factor of the secp256k1 tree requiring a nested Lucas certificate. -/
def f173lit : Nat := 173378833005251801

/-- Full prime factorization of `f173lit - 1`; product `= f173lit - 1`. -/
def f173Factors : List Nat := [2, 2, 2, 5, 5, 2621, 24809, 13331831]

theorem f173_prod : f173Factors.prod = f173lit - 1 := by decide

theorem f173_factors_prime : ∀ q ∈ f173Factors, Nat.Prime q := by intro q hq; fin_cases hq <;> norm_num

theorem f173_fermat : powMod 6 (f173lit - 1) f173lit = 1 := by decide

theorem f173_witness :
    ∀ q ∈ f173Factors, powMod 6 ((f173lit - 1) / q) f173lit ≠ 1 := by decide

/-- `Nat.Prime f173lit`, machine-checked by a nested Lucas certificate. -/
theorem f173_prime : Nat.Prime f173lit :=
  lucas_of_certificate f173lit (by decide) 6 f173Factors
    f173_prod f173_factors_prime f173_fermat f173_witness

end CatCrypt.Crypto.Util.Secp256k1P.Node173
