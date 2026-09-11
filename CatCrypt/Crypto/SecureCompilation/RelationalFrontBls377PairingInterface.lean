/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377MillerLine
public import CatCrypt.Crypto.Bridges.AUCurvesPort.PairingAxioms

/-!
# Plumbing the `bls12_377` pairing COMPUTATION pieces into the abstract pairing interface

`RelationalFrontBls377Fp6` closes the `bls12_377` pairing-field tower
`Fp2_377 ⊂ Fp6_377 ⊂ Fp12_377`, each with a `CommRing` parameterized by the
tower nonresidues `ξ₂, ξ₆` (`Fp12_377.commRing ξ₂ ξ₆`).
`RelationalFrontBls377MillerLine` builds the per-step Miller **line function**
values (`lineTangent`, `lineChord`) and the per-step accumulator update
(`millerStep`), all valued in that `Fp12_377` tower. Those are the
**computation skeleton** of the optimal-Ate pairing: the target group `Gₜ` is
the `Fp12_377` tower, and the Miller loop multiplies line values into a running
`Fp12_377` accumulator.

`AUCurvesPort/CurveGroupLaw.lean` and `AUCurvesPort/PairingAxioms.lean` state
the **abstract pairing interface SHAPE**: a bilinear, non-degenerate map
`e : G₁ → G₂ → Gₜ` (`PairingTarget` / the `PairingAxioms` typeclass) and the
named bottleneck `HasPairing C` (the existence of such a pairing on point
groups associated to a curve `C`). Mathlib has no Weil/Tate pairing, so that
interface is stated but **uninhabited** there.

This module is the **CONNECTION** between the two: it pins the abstract `Gₜ`
carrier slot to the concrete `bls12_377` `Fp12_377` tower, and shows that —
**given** a pairing map satisfying the bilinearity/non-degeneracy fields — the
abstract `HasPairing` bottleneck is dischargeable for `bls12_377`. It does
**not** construct the map.

## What this module provides

* `Bls377PairingData ξ₂ ξ₆ G₁ G₂` — a `structure` capturing exactly what the
  `bls12_377` pairing needs: the source groups `G₁` (the `G1` `r`-torsion over
  `Fp`) and `G₂` (the `G2` `r`-torsion over `Fp2`) as carrier slots, the target
  group **fixed** to `Fp12_377` (with its tower `Monoid` from `commRing ξ₂ ξ₆`),
  and a **candidate** pairing map `e : G₁ → G₂ → Fp12_377` together with the
  bilinearity/non-degeneracy obligations as fields. This is the `bls12_377`
  specialization of `AUCurvesPort.PairingTarget` with `Gₜ := Fp12_377`.

* `bls377_target_of_axioms` — **the plumbing.** Given a
  `PairingAxioms G₁ G₂ Fp12_377` instance (where `Fp12_377` carries the tower
  `Monoid` from `commRing ξ₂ ξ₆`), the abstract `PairingTarget G₁ G₂ Fp12_377`
  is inhabited. The typeclass fields fill the target's fields verbatim; this is
  just `PairingAxioms.toTarget` specialized to the `Fp12_377` carrier.

* `bls377_hasPairing_of_axioms` — **the interface connection.** Given the same
  `PairingAxioms G₁ G₂ Fp12_377` instance, the named bottleneck
  `AUCurvesPort.HasPairing C` holds for any demo curve `C`. So the `bls12_377`
  pairing interface is discharged **exactly when** one supplies a pairing map on
  `(G₁, G₂, Fp12_377)` satisfying the three laws. No such map is constructed
  here.

* `bls377PairingObligation ξ₂ ξ₆ G₁ G₂` — **the named remaining obligation**,
  as a `Prop`: the existence of a `Bls377PairingData` on the `bls12_377` tower.
  This names *exactly* what the deferred Miller-loop completion + Weil/Tate
  divisor theory must produce: a bilinear non-degenerate `e : G₁ → G₂ →
  Fp12_377`. It is a *statement* (a `def` returning a `Prop`), **not** an
  axiom, instance, or theorem — Mathlib offers no foundation to discharge it.

## Honesty boundary

This file connects our **computation skeleton** (the `Fp12_377` tower as `Gₜ`,
the `millerStep`/line functions that accumulate into it) to the **abstract
interface** (`PairingTarget` / `PairingAxioms` / `HasPairing`). It does **not**
construct or prove the pairing:

* **No pairing map is built.** `millerStep` and `lineTangent`/`lineChord` give
  the per-step value and update, but the full Miller loop (the
  doubling-and-add accumulation over the BLS optimal-Ate seed) and the **final
  exponentiation** to land in the order-`r` subgroup are not run here.

* **Bilinearity and non-degeneracy are not proved.** Those are the Weil/Tate
  **divisor theory** (Weil reciprocity / the Tate–Lichtenbaum construction plus
  non-degeneracy on the `r`-torsion), which Mathlib has **no** formalization of.
  They appear here only as the named **fields** of `Bls377PairingData` /
  `PairingAxioms` — the deferred construction, exactly mirroring how
  `AUCurvesPort/PairingAxioms.lean` states the interface without inhabiting it.

The deliverable is the interface **connection** (`Gₜ = Fp12_377` plumbed into
`HasPairing`) plus the **named obligation** (`bls377PairingObligation`). No
`axiom` is asserted; no goal is closed by a placeholder.

## References

* `CatCrypt/Crypto/SecureCompilation/RelationalFrontBls377Fp6.lean` — the
  `Fp12_377` tower and its `commRing ξ₂ ξ₆`.
* `CatCrypt/Crypto/SecureCompilation/RelationalFrontBls377MillerLine.lean` —
  `lineTangent`, `lineChord`, `millerStep` valued in `Fp12_377`.
* `CatCrypt/Crypto/Bridges/AUCurvesPort/CurveGroupLaw.lean` — the abstract
  `PairingTarget` / `HasPairing` interface (the named bottleneck).
* `CatCrypt/Crypto/Bridges/AUCurvesPort/PairingAxioms.lean` — the
  `PairingAxioms` typeclass and `PairingAxioms.toTarget` /
  `hasPairing_of_pairingAxioms` plumbing this specializes to `Fp12_377`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open AUCurvesPort

/-! ## 1. The `Fp12_377` tower as the concrete target group `Gₜ`

The abstract pairing interface's target-group slot `Gₜ` needs a `Monoid`. The
`bls12_377` pairing's target is the `Fp12_377` tower, whose `CommRing` (hence
`Monoid`) is `Fp12_377.commRing ξ₂ ξ₆` — parameterized by the tower nonresidues.
We expose that `Monoid` as the carrier the interface plumbing uses. -/

/-- The `Monoid` structure on the `bls12_377` pairing target `Fp12_377`, taken
    from the tower `CommRing` at nonresidues `ξ₂, ξ₆`. This is the concrete
    `Gₜ`-carrier the abstract pairing interface (`PairingAxioms` / `HasPairing`)
    is plumbed onto. -/
@[reducible] noncomputable def Fp12_377.monoid (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) :
    Monoid Fp12_377 :=
  (Fp12_377.commRing ξ₂ ξ₆).toMonoid

/-! ## 2. The `bls12_377` pairing data structure (`Gₜ` fixed to `Fp12_377`)

`Bls377PairingData` is the `bls12_377` specialization of
`AUCurvesPort.PairingTarget`: the source groups `G₁`, `G₂` are carrier slots
(the `r`-torsion of `G1` over `Fp` and of `G2` over `Fp2`), the target group is
**fixed** to the `Fp12_377` tower, and the bilinearity/non-degeneracy laws are
the **fields** — the deferred construction named, not built. -/

/-- **The `bls12_377` pairing data — the named obligation, as a structure.**

The carrier slots `G₁`, `G₂` (the source point groups; written multiplicatively)
together with a **candidate** pairing map `e : G₁ → G₂ → Fp12_377` into the
`bls12_377` target tower (with its `Monoid` from `commRing ξ₂ ξ₆`), and the
bilinearity / non-degeneracy obligations as fields. Inhabiting this is the
deferred Miller-loop-completion + Weil/Tate divisor theory; the fields name
**exactly** what must be supplied. This is `AUCurvesPort.PairingTarget`
specialized to `Gₜ := Fp12_377`. -/
structure Bls377PairingData
    (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (G₁ : Type) (G₂ : Type) [Mul G₁] [Mul G₂] where
  /-- The candidate pairing map `e : G₁ → G₂ → Fp12_377` (to be constructed via
      the Miller loop + final exponentiation; the bottleneck). -/
  e : G₁ → G₂ → Fp12_377
  /-- Left-linearity: `e (a * b) y = e a y * e b y`, over the `Fp12_377` tower
      `CommRing` multiply at `ξ₂, ξ₆`. -/
  e_mul_left :
    letI := Fp12_377.commRing ξ₂ ξ₆
    ∀ (a b : G₁) (y : G₂), e (a * b) y = e a y * e b y
  /-- Right-linearity: `e x (a * b) = e x a * e x b`. -/
  e_mul_right :
    letI := Fp12_377.commRing ξ₂ ξ₆
    ∀ (x : G₁) (a b : G₂), e x (a * b) = e x a * e x b
  /-- A distinguished `G₁` generator for the non-degeneracy witness. -/
  g₁ : G₁
  /-- A distinguished `G₂` generator for the non-degeneracy witness. -/
  g₂ : G₂
  /-- Non-degeneracy: the pairing of the generators is not `1 : Fp12_377`. -/
  e_nondeg :
    letI := Fp12_377.commRing ξ₂ ξ₆
    e g₁ g₂ ≠ 1

/-! ## 3. The plumbing: a pairing map on `Fp12_377` discharges the abstract interface

Given a `PairingAxioms G₁ G₂ Fp12_377` instance (the abstract bilinearity /
non-degeneracy obligations on the `Fp12_377` target carrier), the abstract
`PairingTarget` is inhabited and the named bottleneck `HasPairing` holds. We do
**not** provide such an instance — that is the deferred construction. -/

/-- **Plumbing — a pairing map on the `Fp12_377` carrier inhabits the abstract
    target.** Given a `PairingAxioms G₁ G₂ Fp12_377` instance (where `Fp12_377`
    carries the tower `Monoid` from `commRing ξ₂ ξ₆`), the abstract
    `AUCurvesPort.PairingTarget G₁ G₂ Fp12_377` is inhabited. This is
    `PairingAxioms.toTarget` specialized to the `bls12_377` target tower: the
    concrete `Gₜ = Fp12_377` slots into the abstract interface. -/
noncomputable def bls377_target_of_axioms
    (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    {G₁ G₂ : Type} [Mul G₁] [Mul G₂]
    [letI := Fp12_377.monoid ξ₂ ξ₆; PairingAxioms G₁ G₂ Fp12_377] :
    letI := Fp12_377.monoid ξ₂ ξ₆
    PairingTarget G₁ G₂ Fp12_377 :=
  letI := Fp12_377.monoid ξ₂ ξ₆
  PairingAxioms.toTarget

/-- **The interface connection — `HasPairing` for `bls12_377`.** Given a
    `PairingAxioms G₁ G₂ Fp12_377` instance on the `bls12_377` target tower, the
    named bottleneck `AUCurvesPort.HasPairing C` holds for any demo curve `C`.
    So the `bls12_377` pairing interface is discharged **exactly when** one
    supplies a bilinear non-degenerate map `e : G₁ → G₂ → Fp12_377`; the
    `Fp12_377` tower (our computation skeleton's target group) plumbs straight
    into the abstract `HasPairing`. No such pairing map is constructed here —
    that is the deferred Miller-loop + Weil/Tate theory. -/
theorem bls377_hasPairing_of_axioms
    (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    {G₁ G₂ : Type} [Mul G₁] [Mul G₂]
    [letI := Fp12_377.monoid ξ₂ ξ₆; PairingAxioms G₁ G₂ Fp12_377]
    (C : WeierstrassCurve (ZMod 101)) :
    HasPairing C :=
  letI := Fp12_377.monoid ξ₂ ξ₆
  hasPairing_of_pairingAxioms (G₁ := G₁) (G₂ := G₂) (Gₜ := Fp12_377) C

/-! ## 4. The named remaining obligation

`bls377PairingObligation` names — as a `Prop`, deliberately not an axiom,
instance, or theorem — exactly what the deferred construction must produce: a
`Bls377PairingData` on the `bls12_377` tower, i.e. a bilinear non-degenerate
`e : G₁ → G₂ → Fp12_377`. This is the `bls12_377` mirror of
`AUCurvesPort.HasPairing`, with the target carrier pinned to our `Fp12_377`
computation skeleton. -/

/-- **The named remaining obligation for the `bls12_377` pairing.**

The existence of a `Bls377PairingData` on the source groups `G₁`, `G₂` and the
`Fp12_377` target tower: a bilinear, non-degenerate `e : G₁ → G₂ → Fp12_377`.
This is a *statement* of what the deferred Miller-loop completion + final
exponentiation + Weil/Tate divisor theory must construct — **not** an axiom,
instance, or theorem. Mathlib has no Weil/Tate pairing, so it is intentionally
left unproved here, exactly as `AUCurvesPort.HasPairing` leaves the abstract
bottleneck unproved. -/
def bls377PairingObligation
    (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (G₁ : Type) (G₂ : Type) [Mul G₁] [Mul G₂] : Prop :=
  Nonempty (Bls377PairingData ξ₂ ξ₆ G₁ G₂)

/-- **The obligation is the data.** A `Bls377PairingData` witness is exactly what
    `bls377PairingObligation` asserts the existence of — the trivial unfolding
    making the named obligation's content explicit. -/
theorem bls377PairingObligation_iff
    (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (G₁ : Type) (G₂ : Type) [Mul G₁] [Mul G₂] :
    bls377PairingObligation ξ₂ ξ₆ G₁ G₂ ↔ Nonempty (Bls377PairingData ξ₂ ξ₆ G₁ G₂) :=
  Iff.rfl

end CatCrypt.Crypto.SecureCompilation.RelationalFront
