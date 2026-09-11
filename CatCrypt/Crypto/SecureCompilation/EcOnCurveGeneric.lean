/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.LinearCombination

/-!
# Generic short-Weierstrass (`a = 0`) on-curve closure of the affine group law

This module pairs the generic affine chord/tangent coordinate maps of
`EcRealizationGeneric.lean` (`ecAffineRx`/`ecAffineRy`/`ecAffineAdd`/`ecAffineDbl`/
`ecTangentSlope`) with the **on-curve predicate** for the curve `y² = x³ + b` and proves the
two standard "the group law preserves the curve" facts, *once*, over an abstract `[Field F]`
and a parametric `b : F`:

* `ecAffineDbl_onCurve` — the tangent-double of an on-curve point (with `y ≠ 0`) lands on the
  curve;
* `ecAffineAdd_onCurve` — the chord-add of two distinct on-curve points lands on the curve.

These are the chord/tangent closure laws: the third intersection of the chord (resp. tangent)
of `y² = x³ + b` with the curve is again on the curve.  They are pure field identities **modulo
the curve relations** `hP : P.y² = P.x³ + b` (and `hQ` for the add), closed by `field_simp`
followed by a `linear_combination` against those relations.

This is the **canonical parametric form** (`@canonical_parametric` — genuinely parametric over
the base field and the curve constant `b`, both of which vary per protocol).  A new curve needs
no new on-curve proof: instantiate at its own `ZMod p` and `b`.

0 sorries; no custom axioms.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.EcOnCurveGeneric

open CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric

universe u

variable {F : Type u} [Field F] (b : F)

/-! ## The on-curve predicate -/

/-- The short-Weierstrass (`a = 0`) on-curve predicate for the curve `y² = x³ + b`. -/
def onCurve (P : ECAffPoint F) : Prop := P.y ^ 2 = P.x ^ 3 + b

/-! ## Closure of the tangent-double -/

/-- **The tangent-double preserves the curve.**  If `P` is on `y² = x³ + b` and `P.y ≠ 0`
    (so the tangent slope is defined), then the affine point-double of `P` at the tangent slope
    `λ = 3x²/(2y)` is again on the curve.  This is the tangent closure law for `a = 0`. -/
theorem ecAffineDbl_onCurve
    (h2 : (2 : F) ≠ 0) (P : ECAffPoint F) (hy : P.y ≠ 0)
    (hP : onCurve b P) :
    onCurve b (ecAffineDbl (ecTangentSlope P.x P.y) P) := by
  unfold onCurve ecAffineDbl ecAffineRx ecAffineRy ecTangentSlope at *
  obtain ⟨x, y⟩ := P
  simp only at *
  field_simp [hy, h2] at hP ⊢
  linear_combination 64 * y ^ 6 * hP

/-! ## Closure of the chord-add -/

/-- **The chord-add preserves the curve.**  If `P` and `Q` are on `y² = x³ + b` and have
    distinct `x`-coordinates (so the chord slope is defined), then the affine point-add of `P`
    and `Q` at the chord slope `λ = (y₂ − y₁)/(x₂ − x₁)` is again on the curve.  This is the
    chord closure law. -/
theorem ecAffineAdd_onCurve
    (P Q : ECAffPoint F) (hx : Q.x - P.x ≠ 0)
    (hP : onCurve b P) (hQ : onCurve b Q) :
    onCurve b (ecAffineAdd ((Q.y - P.y) * (Q.x - P.x)⁻¹) P Q) := by
  unfold onCurve ecAffineAdd ecAffineRx ecAffineRy at *
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  simp only at *
  -- Eliminate the curve constant via `P`'s relation, then close with `Q`'s.
  have hbb : b = y1 ^ 2 - x1 ^ 3 := by linear_combination -hP
  subst hbb
  field_simp [hx]
  linear_combination ((x2 - x1) ^ 3 * (y2 - y1) ^ 2 - (2 * x1 + x2) * (x2 - x1) ^ 5) * hQ

end CatCrypt.Crypto.SecureCompilation.EcOnCurveGeneric
