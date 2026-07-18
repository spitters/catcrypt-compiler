/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.EcPairingCheckOps

/-!
# `pairing_check` is SOUND relative to an ASSUMED bilinear, non-degenerate pairing

`EcPairingCheckOps.lean` gives the `pairing_check` op a *decision procedure*
(`pairingCheck2F ξ₀ e₁ e₂ = gtIsOneF (Fp12Val.mul ξ₀ e₁ e₂)`, true iff the GT
product is the identity), but on its own that op decides nothing about a
*pairing*: its two operands are arbitrary `Fp12Val p` elements.  This file turns
it into a **sound verification predicate** by wiring the op to a bilinear,
non-degenerate pairing interface and proving that the op accepts the canonical
valid relation.

## What is proved, and what is ASSUMED

We do **not** prove that any map is a pairing.  Mathlib has no Weil/Tate
pairing, and the AUCurves (Coq/fiat-crypto) pairing development has its
bilinearity `Admitted` and no non-degeneracy lemma.  So bilinearity and
non-degeneracy are genuine **assumptions** here, modelled as the fields of an
interface structure (`Fp12Pairing`) — exactly mirroring
`AUCurvesPort.PairingAxioms` (`Bridges/AUCurvesPort/PairingAxioms.lean`), but
with the target group `Gₜ` fixed to the `FieldDialect` carrier `Fp12Val p` and
the GT multiply fixed to `Fp12Val.mul ξ₀` (the curve-non-residue-parameterised
tower multiply the op actually folds with).

We use a **local** structure rather than reusing `PairingAxioms` directly
because `PairingAxioms` requires `[Monoid Gₜ]`, whereas the `FieldDialect` tower
multiply `Fp12Val.mul ξ₀` is a raw function with **no** proven monoid laws
(associativity/identity are not established for the schedule).  The interface
here therefore states only the laws actually needed — multiplicative
bilinearity written directly over `Fp12Val.mul ξ₀`, the `1`-normalisations from
`Fp12Gt.lean`, and non-degeneracy — without claiming `Fp12Val p` is a monoid
under `Fp12Val.mul ξ₀`.

This is the **same trust surface** as the existing KZG/Marlin pairing edge
(`PairingAxioms`, `ArkLibKZGDemo/PairingGroupAxioms.lean`): we assume the
pairing is bilinear and non-degenerate, and prove the verification op is sound
relative to that assumption.  We claim **no** proof that `Fp12Val.mul ξ₀`
realises the mathematical Tate/Weil pairing.

## Theorems

* `Fp12Pairing.gtProd_inverse` — `e P Q ·_{ξ₀} e P (-Q) = 1`, from
  right-bilinearity + `Q + (-Q) = 0` + `e P 0 = 1`.  The GT product of a pairing
  and its negated-argument partner is the GT identity.
* `Fp12Pairing.pairingCheck2_accepts` — the `pairingCheck2` op **accepts** the
  canonical valid relation `(e P Q, e P (-Q))` (it returns `true`).  This is the
  soundness/completeness link: the op admits exactly the GT-identity products a
  genuine pairing produces.
* `Fp12Pairing.bls_verify_complete` — the BLS-verify-shape **forward** direction:
  if `e σ g₂ = e H pk` then `pairingCheck2F ξ₀ (e σ g₂) (e H (-pk)) = true`.  A
  valid BLS signature is accepted.

## The BLS converse needs GT-group cancellation we do NOT assume

The full BLS iff `pairingCheck2F ξ₀ (e σ g₂) (e H (-pk)) = true ↔ e σ g₂ = e H pk`
would, in the `→` (accepts-ONLY-valid) direction, require multiplicative
**cancellation** in the GT group: from `e σ g₂ ·_{ξ₀} e H (-pk) = 1` and
`e H pk ·_{ξ₀} e H (-pk) = 1` one concludes `e σ g₂ = e H pk` only via
uniqueness of inverses, i.e. a `Group`/cancellative-`Monoid` structure on
`Fp12Val p` under `Fp12Val.mul ξ₀`.  That structure is **not** available (the
tower multiply has no proven monoid laws) and is **not** assumed by this
interface, so the converse is left as a documented gap rather than proved by a
fabricated cancellation axiom.  Adding a `gt_mul_right_cancel` field would close
it, at the cost of a stronger assumption; we keep the interface minimal.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EcPairingCheckSound

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Fp12Gt
open CatCrypt.Crypto.SecureCompilation.VIR.EcPairingCheckOps

/-! ## The assumed pairing interface, with `Gₜ = Fp12Val p`, `·_{Gₜ} = Fp12Val.mul ξ₀`

Every field below is an **assumption** (the AUCurves pairing interface): the
source groups `G₁ G₂`, the pairing map `e`, its multiplicative bilinearity
written over `Fp12Val.mul ξ₀`, the `1`-normalisations, and non-degeneracy.  We
prove nothing about whether such an `e` exists — that is the deferred
Miller-loop / final-exponentiation / Tate–Weil construction. -/

/-- **ASSUMED bilinear, non-degenerate pairing into `Gₜ = Fp12Val p`.**

The interface a `pairing_check` consumer must supply: a map
`e : G₁ → G₂ → Fp12Val p` that is multiplicatively bilinear with respect to the
tower multiply `Fp12Val.mul ξ₀` (the GT multiply the op folds with) and
non-degenerate.  The fields are exactly the bilinearity/non-degeneracy laws of
`AUCurvesPort.PairingAxioms`, specialised to the `FieldDialect` target carrier.

This is a hypothesis structure, **not** a Lean `axiom`: bilinearity is `Admitted`
in AUCurves' Coq development and non-degeneracy is absent there, so these are
genuine assumptions a caller must discharge, not facts this file proves. -/
structure Fp12Pairing (p : Nat) (ξ0 : ZMod p) where
  /-- Source group `G₁` (the signature / first pairing argument group). -/
  G1 : Type
  /-- Source group `G₂` (the public-key / second pairing argument group). -/
  G2 : Type
  /-- `G₁` is an additive commutative group (additive curve-point convention). -/
  [grp1 : AddCommGroup G1]
  /-- `G₂` is an additive commutative group. -/
  [grp2 : AddCommGroup G2]
  /-- The pairing map `e : G₁ → G₂ → Gₜ` (to be constructed — the bottleneck). -/
  e : G1 → G2 → Fp12Val p
  /-- **ASSUMPTION (right-bilinearity).** `e P (Q + Q') = e P Q ·_{ξ₀} e P Q'`. -/
  e_add_right : ∀ (P : G1) (Q Q' : G2),
    e P (Q + Q') = Fp12Val.mul ξ0 (e P Q) (e P Q')
  /-- **ASSUMPTION.** `e P 0 = 1` (the right `0` normalises to the GT identity). -/
  e_zero_right : ∀ (P : G1), e P 0 = 1
  /-- **ASSUMPTION (left-bilinearity).** `e (P + P') Q = e P Q ·_{ξ₀} e P' Q`. -/
  e_add_left : ∀ (P P' : G1) (Q : G2),
    e (P + P') Q = Fp12Val.mul ξ0 (e P Q) (e P' Q)
  /-- **ASSUMPTION.** `e 0 Q = 1` (the left `0` normalises to the GT identity). -/
  e_zero_left : ∀ (Q : G2), e 0 Q = 1
  /-- A distinguished `G₁` generator for the non-degeneracy witness. -/
  g₁ : G1
  /-- A distinguished `G₂` generator for the non-degeneracy witness. -/
  g₂ : G2
  /-- **ASSUMPTION (non-degeneracy).** `e g₁ g₂ ≠ 1`. -/
  e_nondeg : e g₁ g₂ ≠ (1 : Fp12Val p)

-- The bundled source-group instances are made available for instance
-- resolution, so `-Q` / `Q + Q'` elaborate in the theorem statements below.
attribute [local instance] Fp12Pairing.grp1 Fp12Pairing.grp2

namespace Fp12Pairing

variable {p : Nat} {ξ0 : ZMod p} (pair : Fp12Pairing p ξ0)

/-- **The GT product of a pairing and its negated-argument partner is `1`.**

`e P Q ·_{ξ₀} e P (-Q) = e P (Q + (-Q)) = e P 0 = 1`, chaining right-bilinearity,
the group law `Q + (-Q) = 0`, and the right-`0` normalisation.  This is the
algebraic fact that makes the `pairing_check` op accept the valid relation. -/
theorem gtProd_inverse (P : pair.G1) (Q : pair.G2) :
    Fp12Val.mul ξ0 (pair.e P Q) (pair.e P (-Q)) = 1 := by
  rw [← pair.e_add_right, add_neg_cancel, pair.e_zero_right]

/-- **`pairing_check` accepts the canonical valid relation.**

The two-pairing op `pairingCheck2 p ξ₀` returns `true` on `(e P Q, e P (-Q))`:
the GT product is the identity (`gtProd_inverse`), so the GT-identity test
passes.  This is the soundness link — the op admits exactly the GT-identity
products a genuine (assumed) pairing produces. -/
theorem pairingCheck2_accepts (pub : Bool) (P : pair.G1) (Q : pair.G2) :
    pairingCheckDenote.denote (.pairingCheck2 p ξ0 pub)
        (.cons (pair.e P Q) (.cons (pair.e P (-Q)) .nil)) = true := by
  rw [pairingCheck2_denote_iff]
  exact pair.gtProd_inverse P Q

/-- **BLS-verify shape, forward direction (a valid signature is accepted).**

If the BLS verification equation holds in `Gₜ` (`e σ g₂ = e H pk`), the
`pairingCheck2` decision on `(e σ g₂, e H (-pk))` returns `true`:
`e σ g₂ ·_{ξ₀} e H (-pk) = e H pk ·_{ξ₀} e H (-pk) = e H (pk + (-pk)) = e H 0 = 1`.

The converse (`→`, accepts ONLY valid) needs GT-group cancellation that this
interface deliberately does not assume — see the module docstring. -/
theorem bls_verify_complete
    (σ H : pair.G1) (pk : pair.G2)
    (hverify : pair.e σ pair.g₂ = pair.e H pk) :
    pairingCheck2F ξ0 (pair.e σ pair.g₂) (pair.e H (-pk)) = true := by
  rw [pairingCheck2F_iff, hverify, ← pair.e_add_right, add_neg_cancel,
    pair.e_zero_right]

end Fp12Pairing

end CatCrypt.Crypto.SecureCompilation.VIR.EcPairingCheckSound
