/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate

/-!
# P25519 primality certificate — nested factor node `pfC`

Lucas certificate for the nested prime factor `1919519569386763` in the
`2^255 - 19` prime chain. Every prime factor of `pfC - 1` is below `2^25`, so
this node has no child dependencies; the product check reduces by `decide` and
the Fermat and witness checks by `native_decide`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.P25519.NodeC

open CatCrypt.PrattCertificate

/-- Nested prime factor `1919519569386763`
    (`51`-bit). `N - 1 = 2 · 3 · 7 · 19 · 47^2 · 127 · 8574133`. -/
def pfC : Nat := 1919519569386763

/-- All prime factors of `pfC - 1`, with multiplicity; product is `pfC - 1`. -/
def pfCFactors : List Nat := [2, 3, 7, 19, 47, 47, 127, 8574133]

theorem pfC_prod : pfCFactors.prod = pfC - 1 := by decide

theorem pfC_primeFactors : ∀ q ∈ pfCFactors, Nat.Prime q := by
  intro q hq; fin_cases hq <;> norm_num

theorem pfC_fermat : powMod 2 (pfC - 1) pfC = 1 := by native_decide

theorem pfC_witness :
    ∀ q ∈ pfCFactors, powMod 2 ((pfC - 1) / q) pfC ≠ 1 := by native_decide

/-- `Nat.Prime pfC`, machine-checked by a Lucas certificate (witness `2`). -/
theorem pfC_prime : Nat.Prime pfC :=
  lucas_of_certificate pfC (by decide) 2 pfCFactors
    pfC_prod pfC_primeFactors pfC_fermat pfC_witness

end CatCrypt.Crypto.Util.P25519.NodeC
