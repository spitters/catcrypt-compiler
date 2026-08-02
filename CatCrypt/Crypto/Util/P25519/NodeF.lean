/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate
import CatCrypt.Crypto.Util.P25519.NodeD
import CatCrypt.Crypto.Util.P25519.NodeE

/-!
# P25519 primality certificate — nested factor node `pfF`

Lucas certificate for the `236`-bit nested prime factor
`74058212732561358302231226437062788676166966415465897661863160754340907`, the
large factor of `2^255 - 20`, using the sub-certificates `pfD` from `NodeD` and
`pfE` from `NodeE`. The product check reduces by `decide` and the Fermat and
witness checks by `native_decide`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace CatCrypt.Crypto.Util.P25519.NodeF

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.P25519.NodeD
open CatCrypt.Crypto.Util.P25519.NodeE

/-- Nested prime factor
    `74058212732561358302231226437062788676166966415465897661863160754340907`
    (`236`-bit).
    `N - 1 = 2 · 3 · 353 · 57467 · 132049 · 1923133 · 31757755568855353 · 75445702479781427272750846543864801`. -/
def pfF : Nat := 74058212732561358302231226437062788676166966415465897661863160754340907

/-- The `< 2^25` prime factors of `pfF - 1` (with multiplicity). -/
def pfFSmall : List Nat := [2, 3, 353, 57467, 132049, 1923133]

/-- All prime factors of `pfF - 1`, with multiplicity; product is `pfF - 1`. -/
def pfFFactors : List Nat := pfFSmall ++ [pfD, pfE]

theorem pfF_prod : pfFFactors.prod = pfF - 1 := by decide

theorem pfF_smallPrime : ∀ q ∈ pfFSmall, Nat.Prime q := by
  intro q hq; fin_cases hq <;> norm_num

theorem pfF_primeFactors : ∀ q ∈ pfFFactors, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact pfF_smallPrime q h
  · fin_cases h
    · exact pfD_prime
    · exact pfE_prime

theorem pfF_fermat : powMod 2 (pfF - 1) pfF = 1 := by native_decide

theorem pfF_witness :
    ∀ q ∈ pfFFactors, powMod 2 ((pfF - 1) / q) pfF ≠ 1 := by native_decide

/-- `Nat.Prime pfF`, machine-checked by a Lucas certificate (witness `2`). -/
theorem pfF_prime : Nat.Prime pfF :=
  lucas_of_certificate pfF (by decide) 2 pfFFactors
    pfF_prod pfF_primeFactors pfF_fermat pfF_witness

end CatCrypt.Crypto.Util.P25519.NodeF
