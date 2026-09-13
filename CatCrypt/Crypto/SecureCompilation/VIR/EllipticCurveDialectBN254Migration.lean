/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveLowering
public import CatCrypt.Crypto.Pairing.BN254GroupEmit

/-!
# EllipticCurve-dialect BN254 `G1` migration tie (#482-3, step 4 — additive)

Connects the new **EllipticCurve Veir-dialect** group law
(`EllipticCurveDialect.padd`, denoting the abstract `ECPoint` group add) to the
**verified emitted BN254 `G1` group-law kernel** (`Pairing/BN254GroupEmit.lean`:
`emittedAffineAdd`, `emittedAffineAdd_realizes`), the field-leaf composition the
KAT (`bench/bn254_group_compare/`) cross-checks byte-for-byte against the
production EIP-196 `G1` add.

This is the **first curve migrated onto the EllipticCurve dialect**, additively:
neither `EllipticCurveDialect.lean` nor `BN254GroupEmit.lean` is modified.  The
bridge is a structural map

    bnToEC : BN254Point → ECPoint CatCrypt.Util.BN254

(`(x, y) ↦ some (x, y)`) that carries the bespoke affine point into the dialect's
abstract group element.  Composing it with the kernel's full-group realization
(`emittedAffineAdd_realizes`) yields the *migration theorem*: the emitted BN254
`G1` point-add, transported into the EllipticCurve dialect, denotes to the
dialect's `padd` on **distinct** affine points — so the dialect's `padd` is
backed by the **same** emitted field-leaf composition the bespoke KAT validates,
with no new opaque group leaf and no broken KAT.

## The one-tie-per-level payoff

The UC realization ties connect **once per dialect level** (structural) instead
of per-primitive.  In this module:

* the **field** leaves tie once at L3 (`FieldDialect` + the BN254 `Fp2` migration);
* the **group law** ties once at L4 (this file): `bn254_padd_realized` is the
  single structural tie connecting the verified emitted `G1` kernel to the
  dialect's abstract group op.  Every BN254-`G1`-consuming protocol (KZG, the
  pairing tower's `G1` arm, Groth16's `A`/`C`, …) inherits it without re-proving
  the group law.

## What this lands

* `bn254Params` — the BN254 short-Weierstrass parameters `⟨a = 0, b = 3⟩`.
* `bnToEC` / `bnToEC_add_distinct` — the `BN254Point ↪ ECPoint` embedding, and
  the proof that the dialect group add on the embedded distinct points equals the
  bespoke `bn254AffineAdd` with the chord slope.
* `bn254_padd_realized` — the **migration headline**: the emitted BN254 `G1`
  point-add (`emittedAffineAdd`), interpreted through `wireToFp` into the
  dialect's `ECPoint`, denotes to the dialect's `padd` on the interpreted
  distinct affine points.

## Deferred (the continuation)

The `pdbl`/`pmadd`/`psmul`/`pmsm` (Pippenger/Straus) emitted-kernel ties for
BN254, and the migrations of the other curves (BLS12-381 `G1`/`G2`, P-256,
secp256k1, Pasta, Ristretto, Ed25519), are deferred: the EllipticCurve dialect
already *denotes* the full group law + MSM (`EllipticCurveDialect.lean`), and the
same `bnToEC`-style structural embedding lifts each curve's emitted group/MSM
kernel onto the dialect.  Only the `padd` tie is landed here as the
proof-of-concept of the one-tie-per-level structure.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Pairing.BN254GroupEmit
open CatCrypt.Util (BN254Point bn254AffineAdd bn254AffineRx bn254AffineRy)

/-! ## 1. The BN254 short-Weierstrass parameters and the point embedding -/

/-- The BN254 `G1` curve parameters `y² = x³ + 3` (`a = 0`, `b = 3`), as an
    `ECParams` over the BN254 base field. -/
def bn254Params : ECParams CatCrypt.Util.BN254 := ⟨CatCrypt.Util.bn254A, CatCrypt.Util.bn254B⟩

/-- Embed a bespoke affine `BN254Point` into the EllipticCurve dialect's abstract
    group element (`(x, y) ↦ some (x, y)`). -/
def bnToEC (P : BN254Point) : ECPoint CatCrypt.Util.BN254 := ECPoint.aff P.x P.y

@[simp] theorem bnToEC_eq (P : BN254Point) : bnToEC P = some (P.x, P.y) := rfl

/-! ## 2. The dialect group add on embedded distinct points = `bn254AffineAdd`

The dialect's chord-branch group add (`ECParams.add` with `x1 ≠ x2`) computes the
slope `λ = (y₂ − y₁)·(x₂ − x₁)⁻¹` and the coordinate maps `affRx`/`affRy`; with
`a = 0` these are exactly `bn254AffineRx`/`bn254AffineRy` with that same slope, so
the dialect add on the embedded points is the bespoke `bn254AffineAdd` at the
chord slope. -/

/-- The dialect group add on two embedded **distinct** `BN254Point`s equals the
    bespoke `bn254AffineAdd` with the chord slope `(y₂ − y₁)·(x₂ − x₁)⁻¹`. -/
theorem bnToEC_add_distinct (P Q : BN254Point) (hne : P.x ≠ Q.x) :
    bn254Params.add (bnToEC P) (bnToEC Q)
      = bnToEC (bn254AffineAdd ((Q.y - P.y) * (Q.x - P.x)⁻¹) P Q) := by
  simp only [bnToEC, ECPoint.aff, bn254Params, ECParams.add, if_neg hne,
    ECParams.chordSlope, ECParams.affRx, ECParams.affRy,
    bn254AffineAdd, bn254AffineRx, bn254AffineRy]

/-! ## 3. The emitted-kernel migration headline

`emittedAffineAdd_realizes` (the bespoke full-group realization) proves the
emitted BN254 `G1` field-leaf composition equals `bn254AffineAdd` at the chord
slope.  Composing with §2 lands that emitted kernel on the **dialect's** `padd`:
the dialect op is backed by the verified emitted composition over the BN254
base-field leaves, the same one the KAT cross-checks against the EIP-196 `G1`
add. -/

/-- Interpret an on-wire emitted affine point as a dialect group element
    (through the bespoke `WirePoint.toAlg`, then embed). -/
def wirePointToEC (P : WirePoint) : ECPoint CatCrypt.Util.BN254 := bnToEC P.toAlg

/-- **BN254 `G1` migration headline.** For a leaf model `leafSem` passed as a
    parameter, the emitted BN254 `G1` point-add (`emittedAffineAdd leafSem`, whose
    field-leaf `Com`s are denoted through `jasminDenoteWith leafSem`), interpreted
    into the EllipticCurve dialect's `ECPoint` (`wirePointToEC`), denotes to the
    dialect's `padd` on the interpreted **distinct** affine input points — under
    `FieldLeafAgrees prims leafSem` and `FieldRealizes prims`, the hypotheses of
    `emittedAffineAdd_realizes`.

    This is the single **one-tie-per-level** structural tie: the emitted `G1`
    group-law kernel is connected to the dialect's abstract group op, so every
    BN254-`G1` protocol inherits the group law without re-proving it. -/
theorem bn254_padd_realized (leafSem : LeafSem) (prims : FieldPrimitives)
    (hLeaf : FieldLeafAgrees prims leafSem) (hReal : FieldRealizes prims)
    (P Q : WirePoint) (hne : P.toAlg.x ≠ Q.toAlg.x) :
    wirePointToEC (emittedAffineAdd leafSem P Q)
      = ecDenote.denote (.padd CatCrypt.Util.BN254 bn254Params)
          (.cons (wirePointToEC P) (.cons (wirePointToEC Q) .nil)) := by
  -- the dialect `padd` denotation is the abstract group add `bn254Params.add`
  show wirePointToEC (emittedAffineAdd leafSem P Q)
    = bn254Params.add (wirePointToEC P) (wirePointToEC Q)
  -- rewrite the group add on the embedded distinct points to `bn254AffineAdd`
  unfold wirePointToEC
  rw [bnToEC_add_distinct P.toAlg Q.toAlg hne]
  -- and the emitted kernel realizes exactly that `bn254AffineAdd`; the chord
  -- slope coordinates agree because `WirePoint.toAlg` is `wireToFp`-wise.
  rw [emittedAffineAdd_realizes leafSem prims hLeaf hReal P Q]
  rfl

/-! ## 4. Smoke test: the embedding commutes structurally

The identity law transports: `padd O P` on embedded points respects the
embedding (purely structural, no BN254 modulus arithmetic). -/

example (P : BN254Point) :
    bn254Params.add ECPoint.zero (bnToEC P) = bnToEC P := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
