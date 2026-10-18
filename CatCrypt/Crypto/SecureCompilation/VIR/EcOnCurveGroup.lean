/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.EcPointGroup
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveRewrites

/-!
# The curve points of the dialect carrier and their group law

The EllipticCurve dialect carries points as `ECPoint p = Option (ZMod p × ZMod p)`,
the whole affine plane together with a point at infinity, and `ECParams.add` is
defined on all of it.  `ECParams.add` is a group law only on the points of the
curve: associativity over the whole carrier fails for every base field with more
than four elements (the prose argument is in `X86Backend/EcAssocAudit.lean`).

`IsEcPoint C v` is the predicate cutting the carrier down to the curve: `v` is
the point at infinity, or an affine point satisfying `ECParams.onCurve` at which
the Weierstrass nonsingularity disjunction holds.  It is a polynomial condition
on the coordinates, so it elaborates without the field structure of `ZMod p`.
`isEcPoint_iff_curvePoint` identifies it with membership in the on-curve subtype
`EcCurvePoint C` of `VIR/EcPointGroup.lean`, whose `AddCommGroup` is transported
from `WeierstrassCurve.Affine.Point`, and that identification is what carries the
group law over.  The curve points are closed under the identity, the group law,
the scalar-mul fold, list folds and MSM, and the group axioms hold on them as
theorems; a consumer takes `IsEcPoint C P` on its base point and reaches
associativity through `isEcPoint_assoc`.

## Main results

* `IsEcPoint` — the carrier values that are points of the curve.
* `toW_nonsingular_iff` — Mathlib's nonsingularity of `toW C` at an affine point,
  in the dialect's own terms.
* `isEcPoint_iff_curvePoint` — a curve point is the underlying value of an
  element of the on-curve subtype `EcCurvePoint C`.
* `ecCurvePoint_add_assoc_val`, `ecCurvePoint_add_comm_val` — associativity and
  commutativity of `ECParams.add` on the underlying values of the on-curve
  subtype, from the transported group.
* `isEcPoint_zero`, `isEcPoint_add`, `isEcPoint_smul` — closure of the curve
  points under the identity, the group law and `ECParams.smul`.
* `isEcPoint_assoc`, `isEcPoint_add_comm` — the group axioms at three and two
  curve points of the carrier.
* `isEcPoint_cases`, `onCurve_of_isEcPoint`, `add_zero_or_onCurve` — a curve
  point is the identity or an affine point satisfying `ECParams.onCurve`, and the
  sum of two curve points is again one.
* `isEcPoint_aff` — an affine point on the curve at which the Weierstrass
  nonsingularity disjunction holds is a curve point.
* `isEcPoint_foldl`, `isEcPoint_sum`, `isEcPoint_msm` — closure under the group
  fold of a list of curve points from a curve-point seed, from the identity, and
  under the abstract multi-scalar multiply.
* `smul_add_of_isEcPoint`, `smul_double_of_isEcPoint` — additivity of
  `ECParams.smul` in the exponent at a curve base point, and its doubling step.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EcOnCurveGroup

open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

variable {p : Nat}

/-! ## 1. The curve points of the carrier -/

/-- A dialect carrier value that is a point of the curve: the point at infinity,
    or an affine point satisfying the dialect on-curve predicate
    `y² = x³ + a·x + b` at which the Weierstrass nonsingularity disjunction holds.
    The two disjuncts `3x² + a ≠ 0` and `y + y ≠ 0` are the partial derivatives of
    `y² − x³ − a·x − b`. -/
def IsEcPoint (C : ECParams p) (v : ECPoint p) : Prop :=
  v = ECPoint.zero ∨ ∃ x y : ZMod p, v = ECPoint.aff x y ∧ C.onCurve x y ∧
    (3 * x ^ 2 + C.a ≠ 0 ∨ y + y ≠ 0)

/-- The identity is a curve point. -/
theorem isEcPoint_zero (C : ECParams p) : IsEcPoint C ECPoint.zero :=
  Or.inl rfl

/-- An affine point of the curve at which the Weierstrass nonsingularity
    disjunction holds is a curve point.  The two disjuncts are the partial
    derivatives `3x² + a` and `2y` of `y² − x³ − a·x − b`. -/
theorem isEcPoint_aff (C : ECParams p) {x y : ZMod p} (h : C.onCurve x y)
    (hns : 3 * x ^ 2 + C.a ≠ 0 ∨ y + y ≠ 0) : IsEcPoint C (ECPoint.aff x y) :=
  Or.inr ⟨x, y, rfl, h, hns⟩

/-- A curve point is the identity or an affine point satisfying the dialect
    on-curve predicate `y² = x³ + a·x + b`. -/
theorem isEcPoint_cases (C : ECParams p) {v : ECPoint p} (h : IsEcPoint C v) :
    v = ECPoint.zero ∨ ∃ x y : ZMod p, v = ECPoint.aff x y ∧ C.onCurve x y := by
  rcases h with hz | ⟨x, y, hv, hoc, _⟩
  · exact Or.inl hz
  · exact Or.inr ⟨x, y, hv, hoc⟩

/-- An affine curve point satisfies the dialect on-curve predicate. -/
theorem onCurve_of_isEcPoint (C : ECParams p) {x y : ZMod p}
    (h : IsEcPoint C (ECPoint.aff x y)) : C.onCurve x y := by
  rcases isEcPoint_cases C h with hz | ⟨x', y', heq, hoc⟩
  · exact absurd hz (Option.some_ne_none _)
  · simp only [ECPoint.aff, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨hx, hy⟩ := heq
    subst hx; subst hy
    exact hoc

section Field

variable [Fact (Nat.Prime p)]

/-! ## 2. The group axioms on the on-curve subtype -/

/-- **`ECParams.add` is associative on the underlying values of the on-curve
    subtype `EcCurvePoint C`.**  The transported `AddCommGroup` of
    `VIR/EcPointGroup.lean` carries Mathlib's associativity for
    `WeierstrassCurve.Affine.Point` onto the dialect group law. -/
theorem ecCurvePoint_add_assoc_val (C : ECParams p) (a b c : EcCurvePoint C) :
    C.add (C.add a.val b.val) c.val = C.add a.val (C.add b.val c.val) := by
  simp only [← ecCurvePoint_add_val]
  rw [add_assoc]

/-- `ECParams.add` is commutative on the underlying values of the on-curve
    subtype `EcCurvePoint C`. -/
theorem ecCurvePoint_add_comm_val (C : ECParams p) (a b : EcCurvePoint C) :
    C.add a.val b.val = C.add b.val a.val := by
  simp only [← ecCurvePoint_add_val]
  rw [add_comm]

/-- Mathlib's nonsingularity of `toW C` at an affine point, in the dialect's own
    terms: the on-curve predicate together with the disjunction of the two partial
    derivatives. -/
theorem toW_nonsingular_iff (C : ECParams p) (x y : ZMod p) :
    (toW C).toAffine.Nonsingular x y ↔
      C.onCurve x y ∧ (3 * x ^ 2 + C.a ≠ 0 ∨ y + y ≠ 0) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]
  simp only [toW_a₁, toW_a₂, toW_a₃, toW_a₄, toW_a₆]
  rw [ECParams.onCurve]
  constructor
  · rintro ⟨he, hd⟩
    refine ⟨by linear_combination he, ?_⟩
    rcases hd with hd | hd
    · exact Or.inl fun hc => hd (by linear_combination -hc)
    · exact Or.inr fun hc => hd (by linear_combination hc)
  · rintro ⟨hoc, hd⟩
    refine ⟨by linear_combination hoc, ?_⟩
    rcases hd with hd | hd
    · exact Or.inl fun hc => hd (by linear_combination -hc)
    · exact Or.inr fun hc => hd (by linear_combination hc)

/-- **A curve point is the underlying value of an element of the on-curve subtype
    `EcCurvePoint C`.**  The bridge from the polynomial predicate to the
    transported group. -/
theorem isEcPoint_iff_curvePoint (C : ECParams p) (v : ECPoint p) :
    IsEcPoint C v ↔ ∃ Q : EcCurvePoint C, Q.val = v := by
  constructor
  · rintro (rfl | ⟨x, y, rfl, hoc, hns⟩)
    · exact ⟨0, ecCurvePoint_zero_val C⟩
    · exact ⟨⟨ECPoint.aff x y,
        ⟨.some (x := x) (y := y) ((toW_nonsingular_iff C x y).mpr ⟨hoc, hns⟩), rfl⟩⟩, rfl⟩
  · rintro ⟨Q, rfl⟩
    obtain ⟨W, hW⟩ := Q.property
    cases W with
    | zero => exact Or.inl hW.symm
    | some x y hns =>
      obtain ⟨hoc, hd⟩ := (toW_nonsingular_iff C x y).mp hns
      exact Or.inr ⟨x, y, hW.symm, hoc, hd⟩

/-! ## 3. Closure of the curve points under the group law -/

/-- **The curve points are closed under the dialect group law.**  The sum of two
    curve points is the value of the transported group's sum, hence a curve
    point. -/
theorem isEcPoint_add (C : ECParams p) {u v : ECPoint p}
    (hu : IsEcPoint C u) (hv : IsEcPoint C v) : IsEcPoint C (C.add u v) := by
  obtain ⟨a, rfl⟩ := (isEcPoint_iff_curvePoint C u).mp hu
  obtain ⟨b, rfl⟩ := (isEcPoint_iff_curvePoint C v).mp hv
  exact (isEcPoint_iff_curvePoint C _).mpr ⟨a + b, ecCurvePoint_add_val C a b⟩

/-- **The dialect group law is associative on the curve points.** -/
theorem isEcPoint_assoc (C : ECParams p) {u v w : ECPoint p}
    (hu : IsEcPoint C u) (hv : IsEcPoint C v) (hw : IsEcPoint C w) :
    C.add (C.add u v) w = C.add u (C.add v w) := by
  obtain ⟨a, rfl⟩ := (isEcPoint_iff_curvePoint C u).mp hu
  obtain ⟨b, rfl⟩ := (isEcPoint_iff_curvePoint C v).mp hv
  obtain ⟨c, rfl⟩ := (isEcPoint_iff_curvePoint C w).mp hw
  exact ecCurvePoint_add_assoc_val C a b c

/-- The dialect group law is commutative on the curve points. -/
theorem isEcPoint_add_comm (C : ECParams p) {u v : ECPoint p}
    (hu : IsEcPoint C u) (hv : IsEcPoint C v) : C.add u v = C.add v u := by
  obtain ⟨a, rfl⟩ := (isEcPoint_iff_curvePoint C u).mp hu
  obtain ⟨b, rfl⟩ := (isEcPoint_iff_curvePoint C v).mp hv
  exact ecCurvePoint_add_comm_val C a b

/-- The curve points are closed under the abstract scalar-mul fold. -/
theorem isEcPoint_smul (C : ECParams p) {v : ECPoint p} (h : IsEcPoint C v) (m : Nat) :
    IsEcPoint C (C.smul m v) := by
  induction m with
  | zero => rw [ECParams.smul_zero]; exact isEcPoint_zero C
  | succ k ih => rw [smul_succ]; exact isEcPoint_add C ih h

/-- **The dialect group law of two curve points lands on the curve.**  The sum is
    either the identity or an affine point satisfying `ECParams.onCurve`. -/
theorem add_zero_or_onCurve (C : ECParams p) {u v : ECPoint p}
    (hu : IsEcPoint C u) (hv : IsEcPoint C v) :
    C.add u v = ECPoint.zero
      ∨ ∃ x y : ZMod p, C.add u v = ECPoint.aff x y ∧ C.onCurve x y :=
  isEcPoint_cases C (isEcPoint_add C hu hv)

/-! ## 4. Closure under iterated sums -/

/-- **The group fold of a list of curve points from a curve-point seed stays a
    curve point.**  The seed is arbitrary, so a bucket accumulator that already
    holds a partial sum keeps the invariant across the remaining terms. -/
theorem isEcPoint_foldl (C : ECParams p) (Ps : List (ECPoint p)) :
    ∀ {acc : ECPoint p}, IsEcPoint C acc → (∀ v ∈ Ps, IsEcPoint C v) →
      IsEcPoint C (Ps.foldl C.add acc) := by
  induction Ps with
  | nil => intro acc hacc _; exact hacc
  | cons v Ps ih =>
    intro acc hacc hmem
    simp only [List.foldl_cons]
    exact ih (isEcPoint_add C hacc (hmem v (by simp)))
      (fun w hw => hmem w (by simp [hw]))

/-- **`ECParams.sum` of a list of curve points is a curve point.**  The fold from
    the identity seed. -/
theorem isEcPoint_sum (C : ECParams p) {Ps : List (ECPoint p)}
    (h : ∀ v ∈ Ps, IsEcPoint C v) : IsEcPoint C (C.sum Ps) :=
  isEcPoint_foldl C Ps (isEcPoint_zero C) h

/-- **`ECParams.msm` of terms with curve-point bases is a curve point.**  Each
    term's scalar multiple is a curve point by `isEcPoint_smul`, and their sum by
    `isEcPoint_sum`. -/
theorem isEcPoint_msm (C : ECParams p) {terms : List (Nat × ECPoint p)}
    (h : ∀ t ∈ terms, IsEcPoint C t.2) : IsEcPoint C (C.msm terms) := by
  simp only [ECParams.msm]
  refine isEcPoint_sum C ?_
  intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨t, ht, rfl⟩ := hv
  exact isEcPoint_smul C (h t ht) t.1

/-! ## 5. The scalar-mul fold at a curve base point -/

/-- **`ECParams.smul` is additive in the exponent at a curve point.**  The
    transported group supplies the associativity. -/
theorem smul_add_of_isEcPoint (C : ECParams p) {P : ECPoint p} (hP : IsEcPoint C P)
    (m n : Nat) : C.smul (m + n) P = C.add (C.smul m P) (C.smul n P) := by
  induction n with
  | zero =>
    rw [Nat.add_zero, ECParams.smul_zero, show (ECPoint.zero : ECPoint p) = none from rfl,
      ECParams.add_none_right]
  | succ n ih =>
    rw [← Nat.add_assoc, smul_succ, ih, smul_succ]
    exact isEcPoint_assoc C (isEcPoint_smul C hP m) (isEcPoint_smul C hP n) hP

/-- The doubling step of the exponent at a curve point. -/
theorem smul_double_of_isEcPoint (C : ECParams p) {P : ECPoint p} (hP : IsEcPoint C P)
    (k : Nat) : C.smul (2 * k) P = C.add (C.smul k P) (C.smul k P) := by
  rw [two_mul, smul_add_of_isEcPoint C hP]

end Field

end CatCrypt.Crypto.SecureCompilation.VIR.EcOnCurveGroup
