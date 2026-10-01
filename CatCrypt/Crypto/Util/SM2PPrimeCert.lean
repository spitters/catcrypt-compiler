/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate

/-!
# Machine-checked primality of the SM2 base-field prime

`Nat.Prime sm2Plit` via a Lucas/Pratt certificate, where `sm2Plit` is the SM2
base-field prime `2^256 - 2^224 - 2^96 + 2^64 - 1`
`= 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`
(GB/T 32918.5). Every factor of a `p - 1` that exceeds `2^32` is proved prime by
its own Lucas certificate; the factors below `2^32` are proved prime by `norm_num`.
The tree is small enough that all nodes live in this module:

```
p - 1 = 2·43·30223·A·B·C·D                                    (witness 13)
  A = 4641351449027,      A - 1 = 2·769·3017783777            (witness 2)
  B = 348253387243,       B - 1 = 2·3·61·5303·179429          (witness 3)
  C = 417514796639753,    C - 1 = 2³·7·367·2473·8214737       (witness 3)
  D = 66013261729388519804782124120027,
                          D - 1 = 2·13·1213·71209·6158099·E   (witness 2)
    E = 4773264379806847, E - 1 = 2·3·7·11·823·34511·363761   (witness 3)
```

## Main results

* `sm2Plit_prime`: `Nat.Prime sm2Plit`.
* `sm2Plit_eq`: `sm2Plit = 2^256 - 2^224 - 2^96 + 2^64 - 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.SM2PPrimeCert

open CatCrypt.PrattCertificate

/-! ## Node `A = 4641351449027` -/

/-- The prime factor `4641351449027` of `sm2Plit - 1`. -/
def sm2Alit : Nat := 4641351449027

/-- The prime factors of `sm2Alit - 1`. -/
def sm2AFactors : List Nat := [2, 769, 3017783777]

theorem sm2AFactors_prod : sm2AFactors.prod = sm2Alit - 1 := by decide
theorem sm2AFactors_prime : ∀ q ∈ sm2AFactors, Nat.Prime q := by
  intro q hq
  simp only [sm2AFactors] at hq
  fin_cases hq <;> norm_num
theorem sm2AFermat : powMod 2 (sm2Alit - 1) sm2Alit = 1 := by decide
theorem sm2AWitness :
    ∀ q ∈ sm2AFactors, powMod 2 ((sm2Alit - 1) / q) sm2Alit ≠ 1 := by decide

/-- `Nat.Prime sm2Alit`, by a Lucas certificate with witness `2`. -/
theorem sm2Alit_prime : Nat.Prime sm2Alit :=
  lucas_of_certificate sm2Alit (by decide) 2 sm2AFactors
    sm2AFactors_prod sm2AFactors_prime sm2AFermat sm2AWitness

/-! ## Node `B = 348253387243` -/

/-- The prime factor `348253387243` of `sm2Plit - 1`. -/
def sm2Blit : Nat := 348253387243

/-- The prime factors of `sm2Blit - 1`. -/
def sm2BFactors : List Nat := [2, 3, 61, 5303, 179429]

theorem sm2BFactors_prod : sm2BFactors.prod = sm2Blit - 1 := by decide
theorem sm2BFactors_prime : ∀ q ∈ sm2BFactors, Nat.Prime q := by
  intro q hq
  simp only [sm2BFactors] at hq
  fin_cases hq <;> norm_num
theorem sm2BFermat : powMod 3 (sm2Blit - 1) sm2Blit = 1 := by decide
theorem sm2BWitness :
    ∀ q ∈ sm2BFactors, powMod 3 ((sm2Blit - 1) / q) sm2Blit ≠ 1 := by decide

/-- `Nat.Prime sm2Blit`, by a Lucas certificate with witness `3`. -/
theorem sm2Blit_prime : Nat.Prime sm2Blit :=
  lucas_of_certificate sm2Blit (by decide) 3 sm2BFactors
    sm2BFactors_prod sm2BFactors_prime sm2BFermat sm2BWitness

/-! ## Node `C = 417514796639753` -/

/-- The prime factor `417514796639753` of `sm2Plit - 1`. -/
def sm2Clit : Nat := 417514796639753

/-- The prime factors of `sm2Clit - 1`, with multiplicity. -/
def sm2CFactors : List Nat := [2, 2, 2, 7, 367, 2473, 8214737]

theorem sm2CFactors_prod : sm2CFactors.prod = sm2Clit - 1 := by decide
theorem sm2CFactors_prime : ∀ q ∈ sm2CFactors, Nat.Prime q := by
  intro q hq
  simp only [sm2CFactors] at hq
  fin_cases hq <;> norm_num
theorem sm2CFermat : powMod 3 (sm2Clit - 1) sm2Clit = 1 := by decide
theorem sm2CWitness :
    ∀ q ∈ sm2CFactors, powMod 3 ((sm2Clit - 1) / q) sm2Clit ≠ 1 := by decide

/-- `Nat.Prime sm2Clit`, by a Lucas certificate with witness `3`. -/
theorem sm2Clit_prime : Nat.Prime sm2Clit :=
  lucas_of_certificate sm2Clit (by decide) 3 sm2CFactors
    sm2CFactors_prod sm2CFactors_prime sm2CFermat sm2CWitness

/-! ## Node `E = 4773264379806847` -/

/-- The prime factor `4773264379806847` of `sm2Dlit - 1`. -/
def sm2Elit : Nat := 4773264379806847

/-- The prime factors of `sm2Elit - 1`. -/
def sm2EFactors : List Nat := [2, 3, 7, 11, 823, 34511, 363761]

theorem sm2EFactors_prod : sm2EFactors.prod = sm2Elit - 1 := by decide
theorem sm2EFactors_prime : ∀ q ∈ sm2EFactors, Nat.Prime q := by
  intro q hq
  simp only [sm2EFactors] at hq
  fin_cases hq <;> norm_num
theorem sm2EFermat : powMod 3 (sm2Elit - 1) sm2Elit = 1 := by decide
theorem sm2EWitness :
    ∀ q ∈ sm2EFactors, powMod 3 ((sm2Elit - 1) / q) sm2Elit ≠ 1 := by decide

/-- `Nat.Prime sm2Elit`, by a Lucas certificate with witness `3`. -/
theorem sm2Elit_prime : Nat.Prime sm2Elit :=
  lucas_of_certificate sm2Elit (by decide) 3 sm2EFactors
    sm2EFactors_prod sm2EFactors_prime sm2EFermat sm2EWitness

/-! ## Node `D = 66013261729388519804782124120027` -/

/-- The prime factor `66013261729388519804782124120027` of `sm2Plit - 1`. -/
def sm2Dlit : Nat := 66013261729388519804782124120027

/-- The prime factors of `sm2Dlit - 1`. -/
def sm2DFactors : List Nat := [2, 13, 1213, 71209, 6158099, sm2Elit]

theorem sm2DFactors_prod : sm2DFactors.prod = sm2Dlit - 1 := by decide
theorem sm2DFactors_prime : ∀ q ∈ sm2DFactors, Nat.Prime q := by
  intro q hq
  simp only [sm2DFactors] at hq
  fin_cases hq <;> first | exact sm2Elit_prime | norm_num
theorem sm2DFermat : powMod 2 (sm2Dlit - 1) sm2Dlit = 1 := by decide
theorem sm2DWitness :
    ∀ q ∈ sm2DFactors, powMod 2 ((sm2Dlit - 1) / q) sm2Dlit ≠ 1 := by decide

/-- `Nat.Prime sm2Dlit`, by a Lucas certificate with witness `2`. -/
theorem sm2Dlit_prime : Nat.Prime sm2Dlit :=
  lucas_of_certificate sm2Dlit (by decide) 2 sm2DFactors
    sm2DFactors_prod sm2DFactors_prime sm2DFermat sm2DWitness

/-! ## The SM2 base prime -/

/-- The SM2 base-field prime `2^256 - 2^224 - 2^96 + 2^64 - 1`, as a literal. -/
def sm2Plit : Nat :=
  0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF

/-- The literal `sm2Plit` is the SM2 base-prime expression. -/
theorem sm2Plit_eq : sm2Plit = 2 ^ 256 - 2 ^ 224 - 2 ^ 96 + 2 ^ 64 - 1 := by decide

/-- The prime factors of `sm2Plit - 1`. -/
def sm2PFactors : List Nat := [2, 43, 30223, sm2Alit, sm2Blit, sm2Clit, sm2Dlit]

theorem sm2PFactors_prod : sm2PFactors.prod = sm2Plit - 1 := by decide
theorem sm2PFactors_prime : ∀ q ∈ sm2PFactors, Nat.Prime q := by
  intro q hq
  simp only [sm2PFactors] at hq
  fin_cases hq <;>
    first
    | exact sm2Alit_prime | exact sm2Blit_prime | exact sm2Clit_prime
    | exact sm2Dlit_prime | norm_num
theorem sm2PFermat : powMod 13 (sm2Plit - 1) sm2Plit = 1 := by decide
theorem sm2PWitness :
    ∀ q ∈ sm2PFactors, powMod 13 ((sm2Plit - 1) / q) sm2Plit ≠ 1 := by decide

/-- `Nat.Prime sm2Plit`, by a Lucas certificate with witness `13`. -/
theorem sm2Plit_prime : Nat.Prime sm2Plit :=
  lucas_of_certificate sm2Plit (by decide) 13 sm2PFactors
    sm2PFactors_prod sm2PFactors_prime sm2PFermat sm2PWitness

end CatCrypt.Crypto.Util.SM2PPrimeCert
