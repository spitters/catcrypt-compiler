/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public meta import CatCrypt.Crypto.Util.BLS12377P.Node1
public import CatCrypt.Crypto.Util.BLS12377P.Node1
public meta import CatCrypt.Crypto.Util.BLS12377P.Node2
public import CatCrypt.Crypto.Util.BLS12377P.Node2

/-!
# Machine-checked primality of the BLS12-377 base-field prime `p`

`Nat.Prime bls12377Plit` (the 377-bit Zexe / Aleo BLS12-377 base-field
characteristic, `= CatCrypt.Crypto.Pairing.BLS12377PairingTowerEmit.BLS377Prime`)
via a nested Lucas/Pratt certificate. The witness for `p` is `15` and

```
p - 1 = 2⁴⁶ · 3 · 7 · 13 · 53 · 409 · 499 · 2557
          · 6633514200929891813
          · 73387170334035996766247648424745786170238574695861388454532790956181.
```

The AUCurves Coqprime `bls12_377_prime_certif.v` is a *partial* Pocklington
certificate: it factors only `2⁴⁶ · 3 · 7 · 13 · 409 · 6633514200929891813` and
leaves the rest (`53 · 499 · 2557` and the 226-bit prime
`73387170334035996766247648424745786170238574695861388454532790956181`) in the
unfactored Pocklington cofactor. The Lucas criterion needs the complete
factorization, so the 226-bit factor's whole subtree is reconstructed here. The
subordinate nodes live in `CatCrypt/Crypto/Util/BLS12377P/`, deepest first: `s₁`
is a leaf; `s₂` descends through `s₃`, `s₅`, `s₆`, `s₇`, `s₈` and through `s₄`,
`s₉`. Ten nodes have primes exceeding `10¹²` and carry nested certificates.

Each certificate node is its own module so the `native_decide` Fermat/witness
checks compile independently.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.BLS12377PPrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.BLS12377P.Node1
open CatCrypt.Crypto.Util.BLS12377P.Node2

/-- The BLS12-377 base-field prime `p`, as a literal (definitionally equal to
    `CatCrypt.Crypto.Pairing.BLS12377PairingTowerEmit.BLS377Prime`). -/
def bls12377Plit : Nat :=
  258664426012969094010652733694893533536393512754914660539884262666720468348340822774968888139573360124440321458177

/-- The prime factors of `p - 1`, with multiplicity; product is `p - 1`. The
    forty-six factors of `2` are the `2`-adicity of `p - 1`. -/
def bls12377PFactors : List Nat :=
  List.replicate 46 2 ++ [3, 7, 13, 53, 409, 499, 2557, s1, s2]

theorem bls12377PFactors_prod : bls12377PFactors.prod = bls12377Plit - 1 := by decide

theorem bls12377PFactors_prime : ∀ q ∈ bls12377PFactors, Nat.Prime q := by
  intro q hq; simp only [bls12377PFactors] at hq
  rw [List.mem_append] at hq
  rcases hq with h | h
  · rw [List.mem_replicate] at h; obtain ⟨-, rfl⟩ := h; exact Nat.prime_two
  · fin_cases h <;> first | exact s1_prime | exact s2_prime | norm_num

theorem bls12377PFermat : powMod 15 (bls12377Plit - 1) bls12377Plit = 1 := by decide

theorem bls12377PWitness :
    ∀ q ∈ bls12377PFactors, powMod 15 ((bls12377Plit - 1) / q) bls12377Plit ≠ 1 := by
  decide

/-- `Nat.Prime bls12377Plit`, machine-checked by a nested Lucas certificate. -/
theorem bls12377Plit_prime : Nat.Prime bls12377Plit :=
  lucas_of_certificate bls12377Plit (by decide) 15 bls12377PFactors
    bls12377PFactors_prod bls12377PFactors_prime bls12377PFermat bls12377PWitness

end CatCrypt.Crypto.Util.BLS12377PPrimeCert
