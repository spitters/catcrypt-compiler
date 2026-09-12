/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public meta import CatCrypt.Crypto.Util.Vesta.Node3
public import CatCrypt.Crypto.Util.Vesta.Node3
public meta import CatCrypt.Crypto.Util.Vesta.Node4
public import CatCrypt.Crypto.Util.Vesta.Node4

/-!
# Machine-checked primality of the Pasta Vesta base-field prime

`Nat.Prime vestalit` via a Lucas/Pratt certificate, where `vestalit` is the
Vesta base-field prime
`0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001`
`= 28948022309329048855892746252171976963363056481941647379679742748393362948097`
(definitionally equal to `RelationalFront.vestaQ` / `Util.PallasN`, the Pallas
group order). By the Pasta cycle this is `|E_Pallas|`.

The factorization is
`vestalit - 1 = 2^32 · 3^2 · 1709 · 24859 · 1690502597179744445941507 · 10427374428728808478656897599072717`,
with witness `5`. Two factors exceed `2^32`, so each is proved prime by its own
nested Lucas certificate (`vestaA_prime`, `vestaB_prime`), which recurse once more
through `vestaA1_prime` / `vestaB1_prime`, held in the `Vesta.Node1`–`Vesta.Node4`
sub-certificate files. Each certificate obligation is its own lemma so the
`native_decide` checks compile independently.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.VestaPrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Vesta.Node3
open CatCrypt.Crypto.Util.Vesta.Node4

/-- The Pasta Vesta base-field prime, as a literal (definitionally equal to
    `RelationalFront.vestaQ` / `Util.PallasN`). -/
def vestalit : Nat :=
  0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

/-- The below-`2^32` prime factors of `vestalit - 1`, with multiplicity
    (`2^32 · 3^2 · 1709 · 24859`). -/
def vestaSmallFactors : List Nat := List.replicate 32 2 ++ [3, 3, 1709, 24859]

/-- All prime factors of `vestalit - 1`; the last two exceed `2^32` and are proved
    prime by the nested certificates `vestaA_prime` / `vestaB_prime`. -/
def vestaFactors : List Nat := vestaSmallFactors ++ [vestaAlit, vestaBlit]

theorem vestaFactors_prod : vestaFactors.prod = vestalit - 1 := by decide
theorem vestaFactors_prime : ∀ q ∈ vestaFactors, Nat.Prime q := by
  intro q hq
  fin_cases hq <;> first | exact vestaA_prime | exact vestaB_prime | norm_num
theorem vestaFermat : powMod 5 (vestalit - 1) vestalit = 1 := by decide
theorem vestaWitness :
    ∀ q ∈ vestaFactors, powMod 5 ((vestalit - 1) / q) vestalit ≠ 1 := by
  decide

/-- `Nat.Prime vestalit`, machine-checked by a Lucas certificate. -/
theorem vestalit_prime : Nat.Prime vestalit :=
  lucas_of_certificate vestalit (by decide) 5 vestaFactors
    vestaFactors_prod vestaFactors_prime vestaFermat vestaWitness

end CatCrypt.Crypto.Util.VestaPrimeCert
