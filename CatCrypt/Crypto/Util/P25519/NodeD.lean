/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# P25519 primality certificate — nested factor node `pfD`

Lucas certificate for the nested prime factor `31757755568855353` in the
`2^255 - 19` prime chain. Every prime factor of `pfD - 1` is below `2^25`, so
this node has no child dependencies; the product check reduces by `decide` and
the Fermat and witness checks by `native_decide`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.P25519.NodeD

open CatCrypt.PrattCertificate

/-- Nested prime factor `31757755568855353`
    (`55`-bit). `N - 1 = 2^3 · 3 · 31 · 107 · 223 · 4153 · 430751`. -/
def pfD : Nat := 31757755568855353

/-- All prime factors of `pfD - 1`, with multiplicity; product is `pfD - 1`. -/
def pfDFactors : List Nat := List.replicate 3 2 ++ [3, 31, 107, 223, 4153, 430751]

theorem pfD_prod : pfDFactors.prod = pfD - 1 := by decide

theorem pfD_primeFactors : ∀ q ∈ pfDFactors, Nat.Prime q := by
  intro q hq; fin_cases hq <;> norm_num

theorem pfD_fermat : powMod 10 (pfD - 1) pfD = 1 := by decide

theorem pfD_witness :
    ∀ q ∈ pfDFactors, powMod 10 ((pfD - 1) / q) pfD ≠ 1 := by decide

/-- `Nat.Prime pfD`, machine-checked by a Lucas certificate (witness `10`). -/
theorem pfD_prime : Nat.Prime pfD :=
  lucas_of_certificate pfD (by decide) 10 pfDFactors
    pfD_prod pfD_primeFactors pfD_fermat pfD_witness

end CatCrypt.Crypto.Util.P25519.NodeD
