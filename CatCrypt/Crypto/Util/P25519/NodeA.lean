/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate

/-!
# P25519 primality certificate — nested factor node `pfA`

Lucas certificate for the nested prime factor `2773320623` in the
`2^255 - 19` prime chain. Every prime factor of `pfA - 1` is below `2^25`, so
this node has no child dependencies; the product check reduces by `decide` and
the Fermat and witness checks by `native_decide`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.P25519.NodeA

open CatCrypt.PrattCertificate

/-- Nested prime factor `2773320623`
    (`32`-bit). `N - 1 = 2 · 2437 · 569003`. -/
def pfA : Nat := 2773320623

/-- All prime factors of `pfA - 1`, with multiplicity; product is `pfA - 1`. -/
def pfAFactors : List Nat := [2, 2437, 569003]

theorem pfA_prod : pfAFactors.prod = pfA - 1 := by decide

theorem pfA_primeFactors : ∀ q ∈ pfAFactors, Nat.Prime q := by
  intro q hq; fin_cases hq <;> norm_num

theorem pfA_fermat : powMod 5 (pfA - 1) pfA = 1 := by native_decide

theorem pfA_witness :
    ∀ q ∈ pfAFactors, powMod 5 ((pfA - 1) / q) pfA ≠ 1 := by native_decide

/-- `Nat.Prime pfA`, machine-checked by a Lucas certificate (witness `5`). -/
theorem pfA_prime : Nat.Prime pfA :=
  lucas_of_certificate pfA (by decide) 5 pfAFactors
    pfA_prod pfA_primeFactors pfA_fermat pfA_witness

end CatCrypt.Crypto.Util.P25519.NodeA
