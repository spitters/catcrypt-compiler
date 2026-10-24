/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Field.ZMod

/-!
# An `AddCommGroup` for on-curve EllipticCurve-dialect points (bridge to Mathlib)

The EllipticCurve dialect (`EllipticCurveDialect.lean`) models a short-Weierstrass
curve `y² = x³ + a·x + b` over `F_p = ZMod p` with the *full affine plane* carrier

    ECPoint p := Option (ZMod p × ZMod p)

and a chord/tangent group law `ECParams.add`.  That carrier includes **off-curve**
points, and `ECParams.add` — while defined on all of it — is a group law **only**
on the on-curve subset.  So `AddCommGroup (ECPoint p)` is *false* as stated.

This module defines an `AddCommGroup` on the subtype of
**on-curve** points, obtained by **transporting** Mathlib's proven Weierstrass
point group `WeierstrassCurve.Affine.Point`.  We do **not** reprove associativity
of the chord-tangent law — that is Mathlib's theorem
(`WeierstrassCurve.Affine.Point.instAddCommGroup`, via the class-group / divisor
argument); we transport it across an injection into the dialect carrier.

## What is built

* `toW C : WeierstrassCurve (ZMod p)` — the short-Weierstrass curve with
  `a₁ = a₂ = a₃ = 0`, `a₄ = C.a`, `a₆ = C.b`.
* `toECPoint C : (toW C).toAffine.Point → ECPoint p` — the bridge from a Mathlib
  nonsingular point to the dialect carrier (`zero ↦ none`, `some (x,y) ↦ some (x,y)`).
* `toECPoint_zero` — the identity bridge `0 ↦ none = ECPoint.zero`.
* `onCurve_of_nonsingular` — a Mathlib nonsingular point satisfies the dialect
  `ECParams.onCurve` predicate (the `Equation` ⇒ `onCurve` direction).
* `toECPoint_injective` — the bridge is injective.
* `toECPoint_add` — **the add-correspondence**: the bridge carries Mathlib's
  `Point.add` to the dialect `ECParams.add`.  This matches the dialect's
  `chordSlope`/`tangentSlope`/`affRx`/`affRy` to Mathlib's `slope`/`addX`/`addY`
  for the short-Weierstrass coefficients.
* `EcCurvePoint C` — the on-curve subtype `Set.range (toECPoint C)`.
* `instAddCommGroupEcCurvePoint` — the transported `AddCommGroup`.

## Mathlib lemmas used

`WeierstrassCurve.Affine.Point.add_some`, `WeierstrassCurve.Affine.addX`,
`WeierstrassCurve.Affine.addY`, `WeierstrassCurve.Affine.negAddY`,
`WeierstrassCurve.Affine.negY`, `WeierstrassCurve.Affine.slope_of_X_ne`,
`WeierstrassCurve.Affine.slope_of_Y_ne`, `WeierstrassCurve.Affine.equation_iff`,
`Equiv.addCommGroup`, `Equiv.ofInjective`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

open WeierstrassCurve

variable {p : Nat}

/-! ## 1. The short-Weierstrass curve `toW C` -/

/-- The Mathlib short-Weierstrass curve `y² = x³ + C.a·x + C.b` for the dialect
    curve parameters `C : ECParams p`: `a₁ = a₂ = a₃ = 0`, `a₄ = C.a`, `a₆ = C.b`. -/
def toW (C : ECParams p) : WeierstrassCurve (ZMod p) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := C.a
  a₆ := C.b

@[simp] theorem toW_a₁ (C : ECParams p) : (toW C).a₁ = 0 := rfl
@[simp] theorem toW_a₂ (C : ECParams p) : (toW C).a₂ = 0 := rfl
@[simp] theorem toW_a₃ (C : ECParams p) : (toW C).a₃ = 0 := rfl
@[simp] theorem toW_a₄ (C : ECParams p) : (toW C).a₄ = C.a := rfl
@[simp] theorem toW_a₆ (C : ECParams p) : (toW C).a₆ = C.b := rfl

/-! ## 2. The bridge `toECPoint` from Mathlib points to the dialect carrier -/

section Field

variable [hp : Fact p.Prime]
include hp

/-- For the short-Weierstrass `toW C` (with `a₁ = a₃ = 0`) the Mathlib negation
    `negY x y = -y - a₁·x - a₃` is just `-y`. -/
@[simp] theorem toW_negY (C : ECParams p) (x y : ZMod p) :
    (toW C).toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY]

/-- Bridge a Mathlib nonsingular affine point on `toW C` to the dialect carrier:
    the point at infinity goes to `none` (`ECPoint.zero`), an affine `some (x,y)`
    goes to `ECPoint.aff x y`. -/
def toECPoint (C : ECParams p) : (toW C).toAffine.Point → ECPoint p
  | WeierstrassCurve.Affine.Point.zero => ECPoint.zero
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) _ => ECPoint.aff x y

omit hp in
@[simp] theorem toECPoint_zero (C : ECParams p) :
    toECPoint C 0 = ECPoint.zero := rfl

omit hp in
@[simp] theorem toECPoint_some (C : ECParams p) {x y : ZMod p}
    (h : (toW C).toAffine.Nonsingular x y) :
    toECPoint C (.some (x := x) (y := y) h) = ECPoint.aff x y := rfl

/-- A Mathlib nonsingular point on `toW C` satisfies the dialect on-curve
    predicate `y² = x³ + a·x + b` (the `Equation ⇒ onCurve` direction). -/
theorem onCurve_of_nonsingular (C : ECParams p) {x y : ZMod p}
    (h : (toW C).toAffine.Nonsingular x y) : C.onCurve x y := by
  have he := h.left
  rw [WeierstrassCurve.Affine.equation_iff] at he
  simp only [toW_a₁, toW_a₂, toW_a₃, toW_a₄, toW_a₆] at he
  unfold ECParams.onCurve
  linear_combination he

omit hp in
/-- The bridge `toECPoint` is injective. -/
theorem toECPoint_injective (C : ECParams p) :
    Function.Injective (toECPoint C) := by
  intro P Q hPQ
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some h' => simp [toECPoint, ECPoint.zero, ECPoint.aff] at hPQ
  | some h =>
    cases Q with
    | zero => simp [toECPoint, ECPoint.zero, ECPoint.aff] at hPQ
    | some h' =>
      simp only [toECPoint, ECPoint.aff, Option.some.injEq, Prod.mk.injEq] at hPQ
      obtain ⟨hx, hy⟩ := hPQ
      subst hx; subst hy; rfl

/-! ## 3. Slope correspondence -/

/-- For distinct abscissae the Mathlib `slope` equals the dialect `chordSlope`. -/
theorem toW_slope_X_ne (C : ECParams p) {x1 x2 y1 y2 : ZMod p} (hx : x1 ≠ x2) :
    (toW C).toAffine.slope x1 x2 y1 y2 = C.chordSlope x1 y1 x2 y2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  unfold ECParams.chordSlope
  have h1 : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
  have h2 : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp
  ring

/-- For equal abscissae (and a non-vertical line) the Mathlib `slope` equals the
    dialect `tangentSlope` (the doubling slope `(3x² + a)/(2y)`). -/
theorem toW_slope_Y_ne (C : ECParams p) {x1 x2 y1 y2 : ZMod p} (hx : x1 = x2)
    (hy : y1 ≠ (toW C).toAffine.negY x2 y2) :
    (toW C).toAffine.slope x1 x2 y1 y2 = C.tangentSlope x1 y1 := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy]
  simp only [toW_a₁, toW_a₂, toW_a₄, toW_negY]
  unfold ECParams.tangentSlope
  rw [div_eq_mul_inv]
  congr 1
  · ring
  · congr 1; ring

/-! ## 4. The add-correspondence: `toECPoint` carries `Point.add` to `ECParams.add` -/

/-- **The add-correspondence.** The bridge `toECPoint` carries Mathlib's proven
    Weierstrass point addition `Point.add` to the dialect group law `ECParams.add`.
    The proof matches the dialect's `chordSlope`/`tangentSlope`/`affRx`/`affRy` to
    Mathlib's `slope`/`addX`/`addY` for the short-Weierstrass coefficients
    (`a₁ = a₂ = a₃ = 0`). -/
theorem toECPoint_add (C : ECParams p) (P Q : (toW C).toAffine.Point) :
    toECPoint C (P + Q) = C.add (toECPoint C P) (toECPoint C Q) := by
  cases P with
  | zero =>
    show toECPoint C (0 + Q) = C.add (toECPoint C 0) (toECPoint C Q)
    rw [zero_add]
    simp [toECPoint_zero, ECPoint.zero]
  | some x1 y1 hP =>
    cases Q with
    | zero =>
      show toECPoint C (Affine.Point.some (x := x1) (y := y1) hP + 0)
        = C.add (toECPoint C (Affine.Point.some (x := x1) (y := y1) hP)) (toECPoint C 0)
      rw [add_zero]
      simp [toECPoint_some, toECPoint_zero, ECPoint.zero, ECPoint.aff]
    | some x2 y2 hQ =>
      by_cases hxy : x1 = x2 ∧ y1 = (toW C).toAffine.negY x2 y2
      · -- vertical line: Mathlib add = 0, dialect add = none
        obtain ⟨hxe, hye⟩ := hxy
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxe hye, toECPoint_zero]
        rw [toW_negY] at hye
        simp [hxe, hye, ECParams.add, ECPoint.aff, ECPoint.zero]
      · rw [WeierstrassCurve.Affine.Point.add_some hxy]
        simp only [toECPoint_some, ECParams.add, ECPoint.aff]
        by_cases hx : x1 = x2
        · -- tangent (doubling) case
          have hy : y1 ≠ (toW C).toAffine.negY x2 y2 := fun h => hxy ⟨hx, h⟩
          rw [toW_slope_Y_ne C hx hy, ite_eq_left hx]
          rw [toW_negY] at hy
          rw [ite_eq_right hy]
          simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
            WeierstrassCurve.Affine.negAddY, toW_a₁, toW_a₂, toW_negY,
            ECParams.affRx, ECParams.affRy, Option.some.injEq, Prod.mk.injEq]
          constructor <;> ring
        · -- chord case
          rw [toW_slope_X_ne C hx, ite_eq_right hx]
          simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
            WeierstrassCurve.Affine.negAddY, toW_a₁, toW_a₂, toW_negY,
            ECParams.affRx, ECParams.affRy, Option.some.injEq, Prod.mk.injEq]
          constructor <;> ring

/-! ## 5. The on-curve subtype and the transported `AddCommGroup` -/

/-- The **on-curve dialect points**: the image of Mathlib's nonsingular point set
    `(toW C).toAffine.Point` under the bridge `toECPoint`.  Concretely a dialect
    `ECPoint p` value that lies on the curve, together with `none = O`.
    This — not the full carrier `ECPoint p` — is the set on which `ECParams.add`
    is a group law. -/
def EcCurvePoint (C : ECParams p) : Type :=
  {v : ECPoint p // ∃ P : (toW C).toAffine.Point, toECPoint C P = v}

/-- The bridge as an equivalence between Mathlib's point group and the on-curve
    subtype (it is a bijection because `toECPoint` is injective). -/
noncomputable def ecCurvePointEquiv (C : ECParams p) :
    (toW C).toAffine.Point ≃ EcCurvePoint C :=
  Equiv.ofInjective (toECPoint C) (toECPoint_injective C)

omit hp in
@[simp] theorem ecCurvePointEquiv_val (C : ECParams p) (X : (toW C).toAffine.Point) :
    (ecCurvePointEquiv C X).val = toECPoint C X := rfl

/-- **`AddCommGroup` on the on-curve dialect points.**  Transported from
    Mathlib's proven Weierstrass point group
    `WeierstrassCurve.Affine.Point.instAddCommGroup` across the equivalence
    `ecCurvePointEquiv`.  Associativity/commutativity are Mathlib's theorems (the
    chord-tangent group law is *not* reproved here); only the carrier is
    transported into the dialect. -/
noncomputable instance instAddCommGroupEcCurvePoint (C : ECParams p) :
    AddCommGroup (EcCurvePoint C) :=
  (ecCurvePointEquiv C).symm.addCommGroup

/-- **The transported group operation is the dialect group law.**  The underlying
    `ECPoint p` value of the transported sum `a + b` equals `ECParams.add` of the
    underlying values.  This is what makes the transported `AddCommGroup` a
    statement *about the dialect's own `ECParams.add`*, not an unrelated import. -/
theorem ecCurvePoint_add_val (C : ECParams p) (a b : EcCurvePoint C) :
    (a + b).val = C.add a.val b.val := by
  rw [Equiv.add_def, Equiv.symm_symm, ecCurvePointEquiv_val, toECPoint_add]
  congr 1
  · rw [← ecCurvePointEquiv_val, Equiv.apply_symm_apply]
  · rw [← ecCurvePointEquiv_val, Equiv.apply_symm_apply]

/-- The transported identity is the point at infinity `O = none`. -/
theorem ecCurvePoint_zero_val (C : ECParams p) :
    (0 : EcCurvePoint C).val = ECPoint.zero := by
  rw [Equiv.zero_def (ecCurvePointEquiv C).symm, Equiv.symm_symm, ecCurvePointEquiv_val]
  rfl

end Field

end CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
