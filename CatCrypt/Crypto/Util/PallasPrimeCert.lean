/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Util.PrattCertificate
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.Util.PrattCertificate
public meta import CatCrypt.Crypto.Util.Pallas.Node4
public import CatCrypt.Crypto.Util.Pallas.Node4
public meta import CatCrypt.Crypto.Util.Pallas.Node5
public import CatCrypt.Crypto.Util.Pallas.Node5

/-!
# Machine-checked primality of the Pasta Pallas base-field prime

`Nat.Prime pallaslit` via a Lucas/Pratt certificate, where `pallaslit` is the
Pallas base-field prime
`0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001`
`= 28948022309329048855892746252171976963363056481941560715954676764349967630337`
(definitionally equal to `RelationalFront.pallasQ` / `Halo2PastaFieldEmit.pallasPrime`,
and the Vesta group order). By the Pasta cycle this is `|E_Vesta|`.

The factorization is
`pallaslit - 1 = 2^32 · 3 · 463 · 539204044132271846773 · 8999194758858563409123804352480028797519453`,
with witness `5`. Two factors exceed `2^32`, so each is proved prime by its own
nested Lucas certificate (`pallasA_prime`, `pallasB_prime`), which recurse once
more through `pallasA1_prime` / `pallasB1_prime` / `pallasB2_prime`, held in the
`Pallas.Node1`–`Pallas.Node5` sub-certificate files. Each certificate obligation
is its own lemma so the `native_decide` checks compile independently.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.PallasPrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Pallas.Node4
open CatCrypt.Crypto.Util.Pallas.Node5

/-- The Pasta Pallas base-field prime, as a literal (definitionally equal to
    `RelationalFront.pallasQ`). -/
def pallaslit : Nat :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

/-- The below-`2^32` prime factors of `pallaslit - 1`, with multiplicity
    (`2^32 · 3 · 463`). -/
def pallasSmallFactors : List Nat := List.replicate 32 2 ++ [3, 463]

/-- All prime factors of `pallaslit - 1`; the last two exceed `2^32` and are
    proved prime by the nested certificates `pallasA_prime` / `pallasB_prime`. -/
def pallasFactors : List Nat := pallasSmallFactors ++ [pallasAlit, pallasBlit]

theorem pallasFactors_prod : pallasFactors.prod = pallaslit - 1 := by decide
theorem pallasFactors_prime : ∀ q ∈ pallasFactors, Nat.Prime q := by
  intro q hq
  fin_cases hq <;> first | exact pallasA_prime | exact pallasB_prime | norm_num
theorem pallasFermat : powMod 5 (pallaslit - 1) pallaslit = 1 := by decide
theorem pallasWitness :
    ∀ q ∈ pallasFactors, powMod 5 ((pallaslit - 1) / q) pallaslit ≠ 1 := by
  decide

/-- `Nat.Prime pallaslit`, machine-checked by a Lucas certificate. -/
theorem pallaslit_prime : Nat.Prime pallaslit :=
  lucas_of_certificate pallaslit (by decide) 5 pallasFactors
    pallasFactors_prod pallasFactors_prime pallasFermat pallasWitness

end CatCrypt.Crypto.Util.PallasPrimeCert
