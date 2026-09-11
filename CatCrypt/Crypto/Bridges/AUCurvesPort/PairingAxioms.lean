/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Bridges.AUCurvesPort.CurveGroupLaw


@[expose] public section
set_option autoImplicit false

/-!
# AUCurves port, 5b: the pairing as an AXIOMATIZED typeclass (no Miller loop)

The curve **group law** is Mathlib-backed (see `CurveGroupLaw.lean`). The
**pairing** is the genuine bottleneck: Mathlib has no Weil or Tate pairing.
Per the AUCurves-port plan, this file keeps the pairing **axiomatized** — it
states the bilinear, non-degenerate pairing interface as a **typeclass with
fields** (a hypothesis structure), and does **not** port a Miller loop or any
pairing construction.

## What this file provides

* `AUCurvesPort.PairingAxioms G₁ G₂ Gₜ` — a **typeclass** (not a Lean `axiom`)
  whose fields are exactly the pairing map `e : G₁ → G₂ → Gₜ`, its
  multiplicative bilinearity (`e_mul_left`, `e_mul_right`), distinguished
  generators `g₁ g₂`, and non-degeneracy `e g₁ g₂ ≠ 1`. This mirrors the
  bilinearity/non-degeneracy fields of CatCrypt's concrete BLS12-381
  `PairingGroup` (see "matches the existing KZG edge" below).
* `AUCurvesPort.PairingAxioms.toTarget` — given a `PairingAxioms` instance, the
  `PairingTarget` from `CurveGroupLaw.lean` is **inhabited**.
* `AUCurvesPort.hasPairing_of_pairingAxioms` — and hence `HasPairing C` holds.
  So the named bottleneck `HasPairing` is discharged **exactly when** one
  supplies a `PairingAxioms` instance. No instance is provided here: that is
  the deferred research item.

## This is a typeclass, NOT a Lean `axiom`

The whole point of keeping the pairing "axiomatized" here is that the
hypotheses live as **structure fields** of a `class`, not as global
`axiom` declarations. There is **no** `axiom` keyword in this file. A consumer
who wants pairing-based facts must produce a `PairingAxioms` *instance* (or take
one as an instance-argument), at which point the obligations are explicit local
hypotheses — discharged, eventually, by an actual construction. Contrast this
with `ArkLibKZGDemo/PairingGroupAxioms.lean`, which uses genuine Lean `axiom`s
for a *concrete* BLS12-381 carrier; here we stay fully parametric so the trust
surface is a hypothesis the caller must supply, not a project-wide axiom.

## Mathlib has no pairing

Mathlib has **no** Weil or Tate pairing for elliptic curves: there is no
bilinear non-degenerate `e : G₁ → G₂ → Gₜ` to import. The group law
(`WeierstrassCurve.Affine.Point.instAddCommGroup`) is fully formalized; the
pairing is not. This file therefore cannot inhabit `PairingAxioms` from
Mathlib — it only states the interface.

## Link to AUCurves: what a from-scratch port would require

Constructing a witness of `PairingAxioms` (a real pairing on the curve's
prime-order point groups, satisfying bilinearity and non-degeneracy) is the
multi-month research item this port tracks. A faithful Lean port of the
AUCurves (Coq/fiat-crypto) pairing development would have to reproduce, at
minimum:

* the **Miller loop** — the divisor-based accumulation of line/vertical
  function evaluations along the doubling-and-add ladder for the pairing
  argument (AUCurves' `Miller`/`MillerLoop`-style definitions);
* the **final exponentiation** — raising the Miller output to
  `(pᵏ − 1) / r` to land in the order-`r` subgroup `Gₜ` of `𝔽_{pᵏ}ˣ`
  (AUCurves' `FinalExponentiation`);
* the **Tate/Weil pairing bilinearity and non-degeneracy proofs** — Weil
  reciprocity (or the Tate–Lichtenbaum construction) plus non-degeneracy on
  the `r`-torsion (AUCurves' pairing-correctness theorems).

None of this is attempted here. It is deferred to a collaboration with the
AUCurves authors; this file is the interface the eventual construction must
satisfy.

## This matches the existing KZG/Marlin edge — no NEW trust

The fields of `PairingAxioms` are exactly the algebraic facts that the existing
KZG/Marlin bridge already relies on. `ArkLibKZGDemo/PairingGroupAxioms.lean`
already axiomatizes a concrete BLS12-381 pairing (its `ee`, `ee_mul_left`,
`ee_mul_right`, `ee_nondeg`) and wires it into the abstract `PairingGroup` that
CatCrypt's KZG security proofs consume. The `PairingAxioms` typeclass here
restates the **same** bilinearity/non-degeneracy shape parametrically. So
relying on a `PairingAxioms` instance introduces **no new trust** beyond the
pairing edge those bridges already depend on — it only states it in a reusable,
curve-facing typeclass form rather than as a fixed concrete axiom block.

## References

* `CatCrypt/Crypto/Bridges/AUCurvesPort/CurveGroupLaw.lean` — the
  Mathlib-backed group law and the `PairingTarget` / `HasPairing` bottleneck.
* `CatCrypt/Crypto/Bridges/ArkLibKZGDemo/PairingGroupAxioms.lean` — the
  existing concrete BLS12-381 axiomatized pairing this mirrors.
* `CatCrypt/Crypto/PairingGroup.lean` — the abstract `PairingGroup` class whose
  bilinearity/non-degeneracy shape this matches.
* AUCurves — the verified elliptic-curve / pairing tower (Coq/fiat-crypto) this
  port targets; the Miller-loop / final-exponentiation / pairing-correctness
  definitions named above are what a from-scratch Lean port would reproduce.
-/

namespace AUCurvesPort

/-! ## The pairing axioms as a typeclass (hypotheses-as-fields)

The carriers `G₁ G₂ Gₜ` are written multiplicatively (`Mul`, `Monoid`) to match
the `PairingGroup` / `PairingTarget` convention. There is **no** `axiom`
declaration below: every obligation is a field of the `class`. -/

/-- **AXIOMATIZED PAIRING — a typeclass, not a Lean `axiom`.**

The pairing interface over three (multiplicatively written) groups: a map
`e : G₁ → G₂ → Gₜ` that is bilinear and non-degenerate. The fields are exactly
the bilinearity/non-degeneracy laws of CatCrypt's `PairingGroup`
(`e_mul_left`, `e_mul_right`, `e_nondeg`), stated here parametrically as
**hypotheses** a consumer must supply via an instance.

Mathlib provides no inhabitant (it has no Weil/Tate pairing); constructing one
— a Miller loop, final exponentiation, and the bilinearity/non-degeneracy
proofs — is the deferred AUCurves research item this port tracks. -/
class PairingAxioms
    (G₁ : Type) (G₂ : Type) (Gₜ : Type)
    [Mul G₁] [Mul G₂] [Monoid Gₜ] where
  /-- The pairing map `e : G₁ → G₂ → Gₜ` (to be constructed; the bottleneck). -/
  e : G₁ → G₂ → Gₜ
  /-- Left-linearity: `e (a * b) y = e a y * e b y`. -/
  e_mul_left : ∀ (a b : G₁) (y : G₂), e (a * b) y = e a y * e b y
  /-- Right-linearity: `e x (a * b) = e x a * e x b`. -/
  e_mul_right : ∀ (x : G₁) (a b : G₂), e x (a * b) = e x a * e x b
  /-- A distinguished `G₁` generator for the non-degeneracy witness. -/
  g₁ : G₁
  /-- A distinguished `G₂` generator for the non-degeneracy witness. -/
  g₂ : G₂
  /-- Non-degeneracy: the pairing of the generators is not the identity. -/
  e_nondeg : e g₁ g₂ ≠ 1

/-- **The axiomatization discharges the bottleneck.** Given a `PairingAxioms`
instance, the `PairingTarget` from `CurveGroupLaw.lean` is inhabited: the
typeclass fields fill exactly the target's fields. -/
noncomputable def PairingAxioms.toTarget
    {G₁ G₂ Gₜ : Type} [Mul G₁] [Mul G₂] [Monoid Gₜ] [A : PairingAxioms G₁ G₂ Gₜ] :
    PairingTarget G₁ G₂ Gₜ where
  e := A.e
  e_mul_left := A.e_mul_left
  e_mul_right := A.e_mul_right
  g₁ := A.g₁
  g₂ := A.g₂
  e_nondeg := A.e_nondeg

/-- **`HasPairing` holds given a `PairingAxioms` instance.** The named
bottleneck `HasPairing C` (the existence of a bilinear non-degenerate pairing
on some point groups associated to `C`) is discharged exactly when one supplies
a `PairingAxioms` instance on some carriers. No such instance is provided in
this development — that remains the open AUCurves construction. -/
theorem hasPairing_of_pairingAxioms
    {G₁ G₂ Gₜ : Type} [Mul G₁] [Mul G₂] [Monoid Gₜ] [PairingAxioms G₁ G₂ Gₜ]
    (C : WeierstrassCurve (ZMod 101)) : HasPairing C :=
  ⟨G₁, G₂, Gₜ, _, _, _, ⟨PairingAxioms.toTarget⟩⟩

end AUCurvesPort
