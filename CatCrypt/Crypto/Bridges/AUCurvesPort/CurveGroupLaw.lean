/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false

/-!
# AUCurves port, kickoff: Mathlib-backed curve group law + the stated pairing bottleneck

This file is the **kickoff** of a Lean port of the AUCurves tower → curve →
pairing correctness story, re-anchored on Mathlib's `WeierstrassCurve` group
law. The point of the file is to draw a clean line between what is *reachable*
today and what is *the genuine new theory*:

* **Reachable now (this file).** The elliptic-curve **group law** — point
  addition, negation, the identity at infinity, and the `AddCommGroup`
  structure on points — is taken **directly from Mathlib**
  (`WeierstrassCurve.Affine.Point` and its `instAddCommGroup`). That instance is
  fully proved in Mathlib (via the addition-preserving injection into the ideal
  class group of the affine coordinate ring; see
  `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`). So the
  group-law edge that the existing emit chain
  (`CatCrypt/Crypto/Pairing/Bls12381AUCurves.lean`,
  `BLS12381ProjectiveEmit.lean`) treats as *trusted* becomes, on the abstract
  side, a **Mathlib-backed** connection rather than an axiom: we instantiate a
  concrete short-Weierstrass curve `y² = x³ + b` and exercise the group law
  through Mathlib's own `add_zero`, `add_comm`, `add_neg_cancel`, `add_assoc`.

  We make the connection **concrete** in two complementary ways:

  - **(i) A worked numeric addition.** For the curve `y² = x³ + 3` over
    `ZMod 101`, the two nonsingular points `P = (1, 2)` and `Q = (3, 38)` add
    to `R = (17, 13)` (slope `18`), and `addExample` proves `P + Q = R`
    *through Mathlib's affine addition formula* (`Affine.Point.add_of_X_ne`,
    `slope_of_X_ne`, `addX`, `addY`). The coordinate equalities discharge by
    definitional `ZMod 101` computation. This shows the group law is not just
    abstract but **concretely computable** on a finite field, the same
    arithmetic an emitted point-add performs (only the prime and `b` differ for
    BLS12-381 / BN254).

  - **(ii) The projective coordinate-model homomorphism.** The emitted
    point-add (`BLS12381ProjectiveEmit.lean`) operates on **projective**
    coordinate triples, not affine `Point`s. Mathlib's
    `Projective.Point.toAffine_{add,neg,zero}` prove that the projective
    addition formula on triples maps, under `toAffine`, to the Mathlib affine
    group operation. The lemmas `projAddToAffine`, `projNegToAffine`,
    `projZeroToAffine` below restate these at `demoCurve`: *the group law on
    the projective coordinate model the emitted point-add uses equals the
    Mathlib affine group law*. This is the exact bridge from the coordinate
    representation the bytes manipulate to the abstract group.

* **Partial elsewhere.** The field tower (`Fp`, `Fp2`, `Fp6`, `Fp12`) already
  has partial Lean content under `CatCrypt/Crypto/Pairing/Fp2Tower.lean`,
  `Fp6Fp12TowerImport.lean`, etc. That is not re-derived here.

* **The named bottleneck: the pairing.** Mathlib has **no** Weil or Tate
  pairing — there is no bilinear non-degenerate `e : G₁ → G₂ → Gₜ` to import,
  and building one is the genuine, multi-month new theory (divisors, the Weil
  reciprocity / Tate–Lichtenbaum construction, non-degeneracy on the
  `p`-torsion). This file does **not** construct a pairing. It only **states**
  the target interface as a `structure` whose fields are exactly the
  bilinearity and non-degeneracy laws (the `PairingGroup` shape from
  `CatCrypt/Crypto/PairingGroup.lean`: `e_mul_left`, `e_mul_right`,
  `e_nondeg`). The structure has no inhabitant here — providing one is the open
  work item this port exists to track.

## Curve choice

To keep the kickoff light and fully buildable, the concrete instance uses the
small prime `p = 101` with `b = 3`, i.e. the curve `y² = x³ + 3` over
`ZMod 101`. This is a **demonstration prime**, deliberately not the
BLS12-381 / BN254 base field (those primes are ~254–381 bits; instantiating
`Field (ZMod p)` and the coordinate-ring machinery on them is heavy and brings
no extra content for the group-law connection). The same Mathlib
`WeierstrassCurve` group law applies verbatim to the real BLS12-381 / BN254
base primes — only the prime literal and `b` would change.

## Main definitions

* `AUCurvesPort.demoCurve` — the short-Weierstrass curve `y² = x³ + 3` over
  `ZMod 101`, as a `WeierstrassCurve (ZMod 101)`.
* `AUCurvesPort.demoAffine` — its affine model, carrying Mathlib's group law on
  `Point`.
* `AUCurvesPort.PairingTarget` — the **stated** (uninhabited here) pairing
  interface over a curve's point groups: a bilinear, non-degenerate
  `e : G₁ → G₂ → Gₜ`. This is the named bottleneck.

## Main statements (Mathlib-backed group law)

* `AUCurvesPort.add_zero`, `add_comm`, `add_assoc`, `add_neg_cancel` — small
  lemmas exercising the group law, each discharged by the corresponding Mathlib
  `AddCommGroup` law. These witness that the group law is Mathlib-backed, not
  trusted.
* `AUCurvesPort.addExample` — the worked numeric addition `(1,2) + (3,38) =
  (17,13)` over `ZMod 101` through Mathlib's affine addition formula (5a(i)).
* `AUCurvesPort.projAddToAffine`, `projNegToAffine`, `projZeroToAffine` — the
  projective-coordinate-model homomorphism: `toAffine` carries the projective
  addition/negation/identity to the Mathlib affine group operation (5a(ii)).

## Residual (named, not fabricated)

The connection stops at the **coordinate model**. What `projAddToAffine` does
*not* assert is that the **denotation of the emitted projective point-add**
(the bytes produced by the compiler in `BLS12381ProjectiveEmit.lean`) equals
`demoCurve.toProjective.add` on coordinate triples. That edge —
*denotation of the emitted Jacobian/projective point-add `=` this Mathlib
`add` on `Fin 3 → 𝔽` triples* — is the precise residual. It requires the
emit-denotation infrastructure (a `denote (emitPointAdd) coords = W.add coords`
theorem), which is out of scope here. We name it rather than fake it.

## Trust boundary: the base-field Montgomery multiply (5c)

Both the worked affine addition and the projective coordinate formulas reduce,
at the bottom, to **base-field multiplications**. On the demo prime `101` these
are decidable `ZMod 101` computations closed by `decide` (the field is tiny).
On the **real** BLS12-381 / BN254 base field (a ~381- / ~254-bit prime) the
base-field multiply is the emitted **Montgomery multiply** kernel, and its
correctness is **externalized to a C/GMP KAT**, not gated on a heavy
multi-vector `native_decide` in Lean. (This follows the standing project
lesson — large `native_decide` KATs over many test vectors are avoided as a
proof gate; the KAT lives in an external C/GMP harness instead.) So the honest
trust posture of a full AUCurves pairing port is: the **group-law algebra** is
Mathlib-backed (this file), while the **base-field Montgomery multiply that
the group law calls into** stays **KAT-validated** at the byte level. The
pairing-port effort estimate must budget for that base-field layer remaining a
KAT boundary rather than a closed Lean proof.

## References

* AUCurves: a verified elliptic-curve / pairing tower (the artifact this port
  targets).
* `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` — the proved
  affine group law.
* `CatCrypt/Crypto/PairingGroup.lean` — the abstract `PairingGroup` class whose
  bilinearity/non-degeneracy shape `PairingTarget` mirrors.
-/

namespace AUCurvesPort

open WeierstrassCurve

/-! ## A concrete short-Weierstrass curve `y² = x³ + 3` over `ZMod 101`

The prime `101` is a small demonstration prime (see the module docstring): the
Mathlib group law below applies identically over the real BLS12-381 / BN254
base primes, only the literal changes. -/

/-- `101` is prime; needed for `Field (ZMod 101)`. -/
instance : Fact (Nat.Prime 101) := ⟨by decide⟩

/-- The short-Weierstrass curve `y² = x³ + 3` over `ZMod 101`, written in the
general Weierstrass form `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with
`a₁ = a₂ = a₃ = a₄ = 0` and `a₆ = 3`. This is the `b = 3` family shared by
BN254 and BLS12-381 (their G₁), here over a small demo prime. -/
def demoCurve : WeierstrassCurve (ZMod 101) :=
  ⟨0, 0, 0, 0, 3⟩

/-- The affine model of `demoCurve`. Its nonsingular points
`WeierstrassCurve.Affine.Point` carry Mathlib's fully-proved group law. -/
noncomputable def demoAffine : Affine (ZMod 101) :=
  demoCurve.toAffine

/-! ## The group law is Mathlib-backed (not trusted)

Each lemma below is the corresponding field of Mathlib's
`WeierstrassCurve.Affine.Point.instAddCommGroup`. We restate them at the
concrete curve to make the connection explicit: the group-law edge that the
emit chain treats as trusted is, abstractly, an instance of a proved Mathlib
theorem. -/

/-- Group-law sanity: the point at infinity is a right identity. Discharged by
Mathlib's `AddCommGroup` instance on curve points. -/
theorem add_zero (P : demoAffine.Point) : P + 0 = P :=
  _root_.add_zero P

/-- Group-law sanity: addition of curve points is commutative (from Mathlib). -/
theorem add_comm (P Q : demoAffine.Point) : P + Q = Q + P :=
  _root_.add_comm P Q

/-- Group-law sanity: addition of curve points is associative (from Mathlib). -/
theorem add_assoc (P Q R : demoAffine.Point) : P + Q + R = P + (Q + R) :=
  _root_.add_assoc P Q R

/-- Group-law sanity: every curve point has an inverse, `P + (-P) = 0` (from
Mathlib). This is the negation/inverse edge of the trusted group law, here
Mathlib-backed. -/
theorem add_neg_cancel (P : demoAffine.Point) : P + (-P) = 0 :=
  _root_.add_neg_cancel P

/-- The `AddCommGroup` instance on curve points exists and is Mathlib's, not a
local axiom. Stating it as a `def` makes the dependency explicit. -/
@[reducible] noncomputable def pointGroup : AddCommGroup demoAffine.Point :=
  inferInstance

/-! ## 5a(i): a worked numeric addition through Mathlib's affine formula

We pick two concrete nonsingular points on `y² = x³ + 3` over `ZMod 101` and
prove their sum equals the computed third point — going *through* Mathlib's
affine addition formula (`Affine.Point.add_of_X_ne`, `slope_of_X_ne`, `addX`,
`addY`), not through any local shortcut. This exhibits the group law as
**concretely computable** on a finite field.

The arithmetic: with `P = (1, 2)`, `Q = (3, 38)` and `a₁ = a₂ = a₃ = a₄ = 0`,
the secant slope is `ℓ = (2 - 38) / (1 - 3) = 18` in `ZMod 101`, giving
`x₃ = ℓ² - x₁ - x₂ = 17` and `y₃ = -(ℓ·(x₃ - x₁) + y₁) = 13`. One checks
`13² = 68 = 17³ + 3` in `ZMod 101`, so `R = (17, 13)` is on the curve. -/

/-- `P = (1, 2)` is a nonsingular point of `demoCurve`. The `Nonsingular`
predicate unfolds (`nonsingular_iff`, `equation_iff`) to concrete `ZMod 101`
arithmetic, closed by `decide`. -/
def nsP : demoAffine.Nonsingular (1 : ZMod 101) (2 : ZMod 101) := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  exact ⟨by decide, Or.inl (by decide)⟩

/-- `Q = (3, 38)` is a nonsingular point of `demoCurve`. -/
def nsQ : demoAffine.Nonsingular (3 : ZMod 101) (38 : ZMod 101) := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  exact ⟨by decide, Or.inl (by decide)⟩

/-- `R = (17, 13)` is a nonsingular point of `demoCurve` (it is `P + Q`). -/
def nsR : demoAffine.Nonsingular (17 : ZMod 101) (13 : ZMod 101) := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  exact ⟨by decide, Or.inl (by decide)⟩

/-- **5a(i) — concrete group-law computation.** The sum of the two nonsingular
points `(1, 2)` and `(3, 38)` on `y² = x³ + 3` over `ZMod 101` equals the
point `(17, 13)`, *computed through Mathlib's affine addition formula*. After
rewriting with the distinct-abscissae branch `Affine.Point.add_of_X_ne`, the
two `some` points are equal iff their coordinates agree; the coordinate
equalities (`addX` / `addY` of the `slope_of_X_ne` slope) reduce by
definitional `ZMod 101` computation, which `congr 1` discharges (the
`Nonsingular` proof components match by proof irrelevance). -/
theorem addExample :
    (Affine.Point.some 1 2 nsP + Affine.Point.some 3 38 nsQ : demoAffine.Point)
      = Affine.Point.some 17 13 nsR := by
  rw [Affine.Point.add_of_X_ne (by decide)]
  congr 1

/-! ## 5a(ii): the projective coordinate-model homomorphism

The emitted point-add (`BLS12381ProjectiveEmit.lean`) works on **projective**
coordinate triples `Fin 3 → 𝔽`, not on Mathlib's affine `Point`. Mathlib's
`Projective.Point.toAffine_{add,neg,zero}` establish that the projective
addition formula maps, under the conversion `toAffine`, to the Mathlib affine
group operation. Restating them at `demoCurve` gives the precise link:

  *the group law on the projective coordinate model the emitted point-add uses
  equals the Mathlib affine group law.*

These hold for **arbitrary** nonsingular triples (no concrete computation), so
they capture the formula identity, not a single instance. -/

/-- **5a(ii) — projective addition is the affine group law.** For nonsingular
projective triples `P Q` on `demoCurve`, `toAffine` carries the projective
addition formula to Mathlib's affine point addition. This is the
coordinate-model bridge: the representation the emitted bytes manipulate maps
homomorphically onto the abstract group. -/
theorem projAddToAffine {P Q : Fin 3 → ZMod 101}
    (hP : demoCurve.toProjective.Nonsingular P)
    (hQ : demoCurve.toProjective.Nonsingular Q) :
    Projective.Point.toAffine demoCurve.toProjective (demoCurve.toProjective.add P Q)
      = Projective.Point.toAffine demoCurve.toProjective P
        + Projective.Point.toAffine demoCurve.toProjective Q :=
  Projective.Point.toAffine_add hP hQ

/-- **5a(ii) — projective negation is affine negation.** `toAffine` carries the
projective negation formula to Mathlib's affine point negation. -/
theorem projNegToAffine {P : Fin 3 → ZMod 101}
    (hP : demoCurve.toProjective.Nonsingular P) :
    Projective.Point.toAffine demoCurve.toProjective (demoCurve.toProjective.neg P)
      = -Projective.Point.toAffine demoCurve.toProjective P :=
  Projective.Point.toAffine_neg hP

/-- **5a(ii) — the projective point at infinity maps to the affine identity.** -/
theorem projZeroToAffine :
    Projective.Point.toAffine demoCurve.toProjective ![0, 1, 0] = 0 :=
  Projective.Point.toAffine_zero

/-! ## The pairing target — the NAMED BOTTLENECK

Mathlib has **no** Weil or Tate pairing. There is no bilinear non-degenerate
`e : G₁ → G₂ → Gₜ` to import for an elliptic curve, and constructing one is the
genuine, multi-month new theory (divisors and Weil reciprocity, or the
Tate–Lichtenbaum pairing, plus non-degeneracy on the `p`-torsion).

`PairingTarget` below only **states** the interface we are aiming for. Its
fields are exactly the bilinearity and non-degeneracy laws of CatCrypt's
abstract `PairingGroup` (`CatCrypt/Crypto/PairingGroup.lean`):
`e_mul_left`, `e_mul_right`, `e_nondeg`. **No inhabitant of this structure is
provided here** — providing one (for the curve's actual point groups, with a
genuine pairing) is the open work item this port tracks. We do not assert it as
an axiom and we do not prove it; it is a target signature.

The group operands are written multiplicatively (`Mul`, `One`) to match the
`PairingGroup` convention; for an additive curve-point group one would supply
the multiplicative image (e.g. the `p`-torsion subgroups under the curve group
law) and `Gₜ` the relevant roots-of-unity / `Fp12` units. -/

/-- **STATED, NOT PROVED — the named bottleneck.**

The target pairing interface over three (multiplicatively-written) abelian
groups `G₁`, `G₂`, `Gₜ`: a map `e : G₁ → G₂ → Gₜ` that is bilinear and
non-degenerate. This mirrors the bilinearity/non-degeneracy fields of
`CatCrypt.PairingGroup`.

There is **no** Mathlib Weil/Tate pairing, so this structure is **uninhabited**
in this file by design. Building a witness — i.e. an actual pairing on the
curve's point groups satisfying these three laws — is the genuine new theory
this AUCurves port exists to track. It is intentionally *not* declared as an
axiom or discharged by a placeholder. -/
structure PairingTarget
    (G₁ : Type*) (G₂ : Type*) (Gₜ : Type*)
    [Mul G₁] [Mul G₂] [Monoid Gₜ] where
  /-- The pairing map `e : G₁ → G₂ → Gₜ` (to be constructed; the bottleneck). -/
  e : G₁ → G₂ → Gₜ
  /-- Left-linearity: `e (a * b) y = e a y * e b y`. -/
  e_mul_left : ∀ (a b : G₁) (y : G₂), e (a * b) y = e a y * e b y
  /-- Right-linearity: `e x (a * b) = e x a * e x b`. -/
  e_mul_right : ∀ (x : G₁) (a b : G₂), e x (a * b) = e x a * e x b
  /-- A distinguished generator pair on which the pairing is non-degenerate. -/
  g₁ : G₁
  /-- A distinguished generator pair on which the pairing is non-degenerate. -/
  g₂ : G₂
  /-- Non-degeneracy: the pairing of the generators is not the identity. -/
  e_nondeg : e g₁ g₂ ≠ 1

/-- The pairing-construction obligation, named as a target predicate over a
curve. `HasPairing C` asserts the existence of some `PairingTarget` on some
choice of point groups `G₁ G₂ Gₜ` associated to the curve `C`.

This is the **open goal** of the AUCurves pairing port. It is a `def` returning
a `Prop` (a *statement* of what remains to be built), deliberately **not** an
instance, axiom, or theorem — there is no Mathlib foundation to discharge it.
The choice of `G₁ G₂ Gₜ` is left existential here because pinning them to the
curve's `p`-torsion and the `Fp12` units is itself part of the construction. -/
def HasPairing (_C : WeierstrassCurve (ZMod 101)) : Prop :=
  ∃ (G₁ G₂ Gₜ : Type) (_ : Mul G₁) (_ : Mul G₂) (_ : Monoid Gₜ),
    Nonempty (PairingTarget G₁ G₂ Gₜ)

end AUCurvesPort
