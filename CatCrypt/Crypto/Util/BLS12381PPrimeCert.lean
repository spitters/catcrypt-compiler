/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public meta import CatCrypt.Crypto.Util.BLS12381P.Node5
public import CatCrypt.Crypto.Util.BLS12381P.Node5
public meta import CatCrypt.Crypto.Util.BLS12381P.Node1
public import CatCrypt.Crypto.Util.BLS12381P.Node1

/-!
# Machine-checked primality of the BLS12-381 base-field prime `p`

`Nat.Prime bls12381Plit` (the 381-bit BLS12-381 `G1` base-field characteristic,
`= CatCrypt.Util.BLS12381`) via a nested Lucas/Pratt certificate.

`p - 1` factors completely as

```
p - 1 = 2 · 3² · 11 · 23 · 47 · 10177 · 859267 · 52437899
          · 2584487767265781317813
          · 15778400344354997994418419698270088123916926905054652752758194827714659
```

with witness `2`. The last two factors are themselves large primes; each carries
its own nested Lucas certificate, transcribed from the AUCurves Coqprime
`bls12_prime_certif.v` Pocklington tree (whose factored part is a complete
factorization of `p - 1` — every node's cofactor is `1`). The recursion bottoms
out at the ten nodes whose primes exceed `10¹²`. The subordinate nodes live in
`CatCrypt/Crypto/Util/BLS12381P/`, deepest first: `p₅` reaches down through
`p₆`, `p₇`, `p₉`; `p₁` reaches down through `p₃`, `p₈` and `p₂`, `p₄`.

Each certificate node is its own module so the `native_decide` Fermat/witness
checks compile independently under a bounded memory budget.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12381PPrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12381P.Node5
open CatCrypt.Crypto.Util.BLS12381P.Node1

/-- The BLS12-381 `G1` base-field prime `p`, as a literal (definitionally equal to
    `CatCrypt.Util.BLS12381`). -/
def bls12381Plit : Nat :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

/-- The prime factors of `p - 1`, with multiplicity; product is `p - 1`. -/
def bls12381PFactors : List Nat :=
  [2, 3, 3, 11, 23, 47, 10177, 859267, 52437899, p5, p1]

theorem bls12381PFactors_prod : bls12381PFactors.prod = bls12381Plit - 1 := by decide

theorem bls12381PFactors_prime : ∀ q ∈ bls12381PFactors, Nat.Prime q := by
  intro q hq; simp only [bls12381PFactors] at hq
  fin_cases hq <;> first | exact p5_prime | exact p1_prime | norm_num

theorem bls12381PFermat : powMod 2 (bls12381Plit - 1) bls12381Plit = 1 := by decide

theorem bls12381PWitness :
    ∀ q ∈ bls12381PFactors, powMod 2 ((bls12381Plit - 1) / q) bls12381Plit ≠ 1 := by
  decide

/-- `Nat.Prime bls12381Plit`, machine-checked by a nested Lucas certificate. -/
theorem bls12381Plit_prime : Nat.Prime bls12381Plit :=
  lucas_of_certificate bls12381Plit (by decide) 2 bls12381PFactors
    bls12381PFactors_prod bls12381PFactors_prime bls12381PFermat bls12381PWitness

end CatCrypt.Crypto.Util.BLS12381PPrimeCert
