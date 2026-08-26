/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Util.PrattCertificate
import CatCrypt.Crypto.Util.Ed25519L.Node7
import CatCrypt.Crypto.Util.Ed25519L.Node8

/-!
# Machine-checked primality of the Ed25519 group order `ℓ`

`Nat.Prime ed25519Llit` for `ℓ = 2^252 + 27742317777372353535851937790883648493`
via a recursive Lucas/Pratt certificate.

`ℓ - 1 = 2^2 · 3 · 11 · A · B` has two prime factors exceeding `2^32`, so each is
certified by its own nested Lucas certificate; those in turn descend through
`D`, `E`, `G`, `H`, `I`, and `213441916511` until every factor is below `2^32`
and directly checkable. The nested nodes live in the `Ed25519L` sub-directory:

* `ℓ - 1 = 2^2 · 3 · 11 · A · B`,   witness `2`
* `A - 1 = 2^4 · 3 · 23 · 58964693 · E`,   witness `5`   (`Ed25519L.Node7`)
* `B - 1 = 2 · 7 · D`,   witness `2`   (`Ed25519L.Node8`)
* `D - 1 = 2 · 269 · 213441916511 · G`,   witness `2`   (`Ed25519L.Node5`)
* `E - 1 = 2 · 3 · 11 · 30703 · 82163 · 132667 · 137849`,   witness `5`   (`Ed25519L.Node6`)
* `G - 1 = 2 · 5 · 1361 · 2851 · H`,   witness `2`   (`Ed25519L.Node3`)
* `H - 1 = 2 · 41 · 43 · I`,   witness `17`   (`Ed25519L.Node2`)
* `I - 1 = 2^2 · 3 · 7 · 23 · 531581 · 1224481`,   witness `2`   (`Ed25519L.Node1`)
* `213441916511 - 1 = 2 · 5 · 73 · 292386187`,   witness `13`   (`Ed25519L.Node4`)

Each certificate obligation is a separate lemma so the checks compile
independently.
-/

set_option autoImplicit false
set_option maxRecDepth 50000

namespace CatCrypt.Crypto.Util.Ed25519LPrimeCert

open CatCrypt.PrattCertificate
open CatCrypt.Crypto.Util.Ed25519L.Node7
open CatCrypt.Crypto.Util.Ed25519L.Node8

/-! ## `ℓ = 2^252 + 27742317777372353535851937790883648493` -/

/-- The Ed25519 group order `ℓ`, as a literal (definitionally equal to
    `2^252 + 27742317777372353535851937790883648493`). -/
def ed25519Llit : ℕ :=
  0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed

/-- Prime factors of `ℓ - 1`, with multiplicity; product is `ℓ - 1`. -/
def ed25519LFactors : List ℕ := [2, 2, 3, 11, factorA, factorB]

theorem ed25519LFactors_prod : ed25519LFactors.prod = ed25519Llit - 1 := by decide

theorem ed25519LFactors_prime : ∀ q ∈ ed25519LFactors, Nat.Prime q := by
  intro q hq
  simp only [ed25519LFactors] at hq
  fin_cases hq <;> first | exact factorA_prime | exact factorB_prime | norm_num

theorem ed25519LFermat : powMod 2 (ed25519Llit - 1) ed25519Llit = 1 := by decide

theorem ed25519LWitness :
    ∀ q ∈ ed25519LFactors, powMod 2 ((ed25519Llit - 1) / q) ed25519Llit ≠ 1 := by decide

/-- `Nat.Prime ed25519Llit`, machine-checked by a recursive Lucas certificate. -/
theorem ed25519Llit_prime : Nat.Prime ed25519Llit :=
  lucas_of_certificate ed25519Llit (by decide) 2 ed25519LFactors
    ed25519LFactors_prod ed25519LFactors_prime ed25519LFermat ed25519LWitness

end CatCrypt.Crypto.Util.Ed25519LPrimeCert
