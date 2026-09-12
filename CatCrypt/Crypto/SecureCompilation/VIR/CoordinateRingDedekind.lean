/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure


@[expose] public section
set_option autoImplicit false

/-!
# The affine coordinate ring of a smooth Weierstrass curve is a Dedekind domain

For a Weierstrass curve `W` over a field `F`, the affine coordinate ring
`F[W] = AdjoinRoot W.polynomial` is a free rank-two `F[X]`-module. Over the PID
`F[X]` this makes `F[W]` module-finite, hence integral over `F[X]`, hence
Noetherian and of Krull dimension at most one. A Noetherian integral domain of
dimension at most one that is integrally closed in its fraction field is a
Dedekind domain (`isDedekindDomain_iff`).

Mathlib proves `F[W]` is an integral domain
(`WeierstrassCurve.Affine.CoordinateRing.instIsDomain`) but not that it is a
Dedekind domain. This file supplies the two structural pieces that hold for
every Weierstrass curve — Noetherian and dimension `≤ 1` — and assembles the
Dedekind-domain conclusion from the remaining integrally-closed hypothesis.

The integrally-closed hypothesis is exactly the normality of the coordinate
ring, which for a Weierstrass curve is equivalent to nonsingularity (the curve
being smooth). Mathlib currently has no lemma deriving
`IsIntegrallyClosed F[W]` from the nonsingularity of `W`, so that step is carried
here as a typeclass hypothesis `[IsIntegrallyClosed W.CoordinateRing]`.

## Missing mathlib input

The only unproved input is the normality of the coordinate ring for a
nonsingular curve. The lemma that would discharge the hypothesis is:

`WeierstrassCurve.Affine.CoordinateRing.instIsIntegrallyClosed`:
for `W : WeierstrassCurve.Affine F` with `W.Δ ≠ 0` (equivalently `W.IsElliptic`,
i.e. the curve is nonsingular), `IsIntegrallyClosed W.CoordinateRing`.

Mathlib has neither this lemma nor the general machinery it needs — the
Jacobian smoothness criterion for an affine hypersurface and the implication
"regular ⇒ normal" (Serre) tying `W.Δ ≠ 0` to regularity of the local rings of
`F[W]`, from which integral closedness of a one-dimensional Noetherian domain
follows. `Mathlib/AlgebraicGeometry/EllipticCurve/` proves the group law but
contains no normality/regularity statement about `CoordinateRing`, and
`Mathlib/RingTheory/` has no "regular local ring ⇒ integrally closed" transfer.

## Application

The instance applies to the BLS12-377 curve `y² = x³ + 1` over `ZMod bls377Q`
(a field, since `bls377Q` is prime): it is a `WeierstrassCurve.Affine`, so once
its coordinate ring is supplied as integrally closed, its `IsDedekindDomain`
follows, which is the input the divisor / height-one-spectrum valuation layer
(`DedekindDomain.HeightOneSpectrum`, `DedekindDomain.Factorization`) needs.
-/

namespace WeierstrassCurve.Affine.CoordinateRing

open Polynomial

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- The affine coordinate ring is module-finite over `F[X]`: the defining
polynomial is monic, so `AdjoinRoot` is a finite free module. -/
instance instModuleFinitePolynomial : Module.Finite F[X] W.CoordinateRing :=
  W.monic_polynomial.finite_adjoinRoot

/-- The affine coordinate ring is integral over `F[X]`, being module-finite. -/
instance instIsIntegralPolynomial : Algebra.IsIntegral F[X] W.CoordinateRing :=
  Algebra.IsIntegral.of_finite F[X] W.CoordinateRing

/-- The affine coordinate ring has Krull dimension at most one: it is an integral
extension of the PID `F[X]`, which has dimension at most one. -/
instance instDimensionLEOne : Ring.DimensionLEOne W.CoordinateRing :=
  Ring.DimensionLEOne.of_isIntegral F[X] W.CoordinateRing

/-- The affine coordinate ring of a Weierstrass curve whose coordinate ring is
integrally closed is a Dedekind ring: it is Noetherian (a quotient of the
Noetherian ring `F[X][Y]`), of Krull dimension at most one (integral over the
PID `F[X]`), and integrally closed by hypothesis.

The three fields — `IsNoetherianRing`, `Ring.DimensionLEOne`, and
`IsIntegralClosure W.CoordinateRing W.CoordinateRing (FractionRing …)` (the last
definitionally `IsIntegrallyClosed W.CoordinateRing`) — are all instances in
scope, so the structure is assembled by instance resolution. -/
instance instIsDedekindRing [IsIntegrallyClosed W.CoordinateRing] :
    IsDedekindRing W.CoordinateRing where

/-- The affine coordinate ring of a Weierstrass curve whose coordinate ring is
integrally closed is a Dedekind domain, being an integral domain
(`WeierstrassCurve.Affine.CoordinateRing.instIsDomain`) and a Dedekind ring.

The `[IsIntegrallyClosed W.CoordinateRing]` hypothesis is the normality of the
ring, equivalent to the nonsingularity of `W`; see the module docstring. -/
instance instIsDedekindDomain [IsIntegrallyClosed W.CoordinateRing] :
    IsDedekindDomain W.CoordinateRing :=
  inferInstance

end WeierstrassCurve.Affine.CoordinateRing
