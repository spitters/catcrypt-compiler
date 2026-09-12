/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the BLS12-381 scalar-field order

`Nat.Prime bls12381Rlit` via a Lucas/Pratt certificate: witness `7` and the
factorization `r - 1 = 2^32 · 3 · 11 · 19 · 10177 · 125527 · 859267 · 906349^2
· 2508409 · 2529403 · 52437899 · 254760293^2`. Each of the four certificate
obligations is its own lemma so the checks compile independently.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Bls12381RPrimeCert

open CatCrypt.PrattCertificate

/-- The BLS12-381 G1 subgroup order / scalar-field prime `r`, as a literal
    (definitionally equal to `Bls12381G1GroupParam.Bls12381R`). -/
def bls12381Rlit : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- The prime factors of `r - 1`, with multiplicity; product is `r - 1`. -/
def rMinusOneFactors : List Nat :=
  List.replicate 32 2 ++
    [3, 11, 19, 10177, 125527, 859267, 906349, 906349,
     2508409, 2529403, 52437899, 254760293, 254760293]

theorem rFactors_prod : rMinusOneFactors.prod = bls12381Rlit - 1 := by decide

theorem rFactors_prime : ∀ q ∈ rMinusOneFactors, Nat.Prime q := by
  intro q hq
  simp only [rMinusOneFactors, List.mem_append, List.mem_replicate] at hq
  rcases hq with ⟨-, rfl⟩ | hq
  · exact Nat.prime_two
  · fin_cases hq <;> norm_num

theorem rFermat : powMod 7 (bls12381Rlit - 1) bls12381Rlit = 1 := by decide

theorem rWitness :
    ∀ q ∈ rMinusOneFactors, powMod 7 ((bls12381Rlit - 1) / q) bls12381Rlit ≠ 1 := by
  decide

/-- `Nat.Prime bls12381Rlit`, machine-checked by a Lucas certificate. -/
theorem bls12381Rlit_prime : Nat.Prime bls12381Rlit :=
  lucas_of_certificate bls12381Rlit (by decide) 7 rMinusOneFactors
    rFactors_prod rFactors_prime rFermat rWitness

end CatCrypt.Crypto.Util.Bls12381RPrimeCert
