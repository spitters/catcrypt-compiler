/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Defs
import CatCrypt.Tactic.FieldClear

/-!
# Abstract Edwards curve over `ZMod p`

Mathlib has `WeierstrassCurve` but no Edwards curve abstraction. This
file is the Lean port of `Crypto/Spec/CompleteEdwardsCurve.v` (affine
form) and `Crypto/Curves/Edwards/AffineProofs.v` (group law proofs)
from fiat-crypto, plus the extended-coords formula from
`Crypto/Curves/Edwards/XYZT/Basic.v`.

**Tier B #4.**

## Scope of this file

The Edwards group structure and the key algebraic correctness theorems.
The polynomial identities behind the group law and the extended-coords
correspondence are proved in Lean by `grobner` from the curve equation
and the `T·Z = X·Y` well-formedness constraints. All non-vanishing facts
about the addition-formula denominators reduce to the single leaf
`EdwardsPointAff.affine_denom_nonsquare`, proved from the curve
equations, the square-`a` witness and the non-square-`d` hypothesis
carried by `EdwardsParams F`.

## What's stated here

### Curve parameters

- `EdwardsParams F`: a record bundling `a`, `d`, the non-degeneracy
  conditions `a ≠ 0`, `d ≠ 0`, `a ≠ d`, the characteristic condition
  `(2 : F) ≠ 0`, and the completeness conditions `∃ s, s² = a` and
  `∀ x, x² ≠ d`.
- The Ed25519 instance: `a = -1`, `d = -121665/121666`.

### Affine points and group operation

- `OnCurveAff (E : EdwardsParams F) (x y : F)`: predicate `a·x² + y² = 1 + d·x²·y²`.
- `EdwardsPointAff E`: subtype of `F × F` satisfying `OnCurveAff`.
- `EdwardsPointAff.add`: the (complete, exception-free) Edwards addition
  formula, lifted from the coordinate-level `add_xy`.
- `EdwardsPointAff.zero`: the identity `(0, 1)`.
- `EdwardsPointAff.neg`: negation `(x, y) ↦ (-x, y)`.
- `add_comm`, `add_assoc`, `zero_add`, `add_zero`, `add_neg_self`: the
  commutative-group laws.

### Extended coordinates

- `EdwardsPointExt E`: tuples `(X, Y, Z, T)` with `Z ≠ 0` and `T·Z = X·Y`.
- `EdwardsPointExt.toAff`: projection to affine via `(X/Z, Y/Z)`.
- `m1add`: the extended-coords add formula (specialized at `a = -1`,
  i.e., the dalek `m1` formula).
- `to_affine_m1add`: **the key correctness theorem** — `m1add` on
  extended points projects to `EdwardsPointAff.add` on the corresponding
  affine points.

### Completeness leaf

- `EdwardsPointAff.affine_denom_nonsquare` — `(d·x₁·x₂·y₁·y₂)² ≠ 1`, the
  Lean counterpart of `Curves/Edwards/Pre.v`'s `denominator_nonzero`.
  `add_denom_pos`, `add_denom_neg` and the projective
  `EdwardsPointExt.m1add_ZneZero` are theorems over it.
-/

namespace CatCrypt.Crypto.Jasmin.EdwardsCurve

variable {F : Type*} [Field F]

/-! ## 1. Curve parameters -/

/-- A complete twisted Edwards curve `a·x² + y² = 1 + d·x²·y²` is
    determined by its `(a, d)` parameters in a field `F`, plus the
    non-degeneracy conditions ensuring the addition formula is complete
    (no exceptional cases). -/
structure EdwardsParams (F : Type*) [Field F] where
  /-- Curve parameter `a`. -/
  a : F
  /-- Curve parameter `d`. -/
  d : F
  /-- Non-vanishing of `a` (otherwise the curve degenerates). -/
  a_ne_zero : a ≠ 0
  /-- Non-vanishing of `d`. -/
  d_ne_zero : d ≠ 0
  /-- `a ≠ d` (otherwise complete addition fails on doubled points). -/
  a_ne_d : a ≠ d
  /-- The characteristic of `F` is not `2`. Counterpart of the `char_ge_3`
      hypothesis carried by fiat-crypto's `Crypto/Curves/Edwards/XYZT/Basic.v`
      section context. In characteristic `2` the extended-coordinate
      completeness denominator `(2·Z₁·Z₂)² - (2·d·T₁·T₂)²` vanishes
      identically. -/
  two_ne_zero : (2 : F) ≠ 0
  /-- `a` is a square. Counterpart of fiat-crypto's `square_a` section
      hypothesis in `Crypto/Curves/Edwards/Pre.v`. -/
  square_a : ∃ s : F, s ^ 2 = a
  /-- `d` is not a square. Counterpart of fiat-crypto's `nonsquare_d` section
      hypothesis in `Crypto/Curves/Edwards/Pre.v`. Together with `square_a`
      this is what makes the addition formula complete: at a square `d` the
      denominators `1 ± d·x₁·x₂·y₁·y₂` have on-curve zeros. -/
  nonsquare_d : ∀ x : F, x ^ 2 ≠ d

/-! ## 2. Affine points -/

/-- Predicate: `(x, y)` lies on the curve `a·x² + y² = 1 + d·x²·y²`. -/
def OnCurveAff (E : EdwardsParams F) (x y : F) : Prop :=
  E.a * x^2 + y^2 = 1 + E.d * x^2 * y^2

/-- Affine point on the Edwards curve `E`. -/
structure EdwardsPointAff (E : EdwardsParams F) where
  /-- x-coordinate. -/
  x : F
  /-- y-coordinate. -/
  y : F
  /-- Witness that `(x, y)` lies on the curve. -/
  on_curve : OnCurveAff E x y

namespace EdwardsPointAff

variable {E : EdwardsParams F}

/-- The identity element `(0, 1)`. On-curve trivially:
    `a·0² + 1² = 1 = 1 + d·0²·1²`. -/
def zero (E : EdwardsParams F) : EdwardsPointAff E :=
  { x := 0, y := 1, on_curve := by unfold OnCurveAff; ring }

/-- Negation: `(x, y) ↦ (-x, y)`. On-curve: `(-x)² = x²` so the
    curve equation is unchanged. -/
def neg (P : EdwardsPointAff E) : EdwardsPointAff E :=
  { x := -P.x, y := P.y
    on_curve := by
      have h := P.on_curve
      unfold OnCurveAff at h ⊢
      have : (-P.x)^2 = P.x^2 := by ring
      rw [this]; exact h }

/-! ### Coordinate-only addition

    `add_xy` is the data-side addition, returning the pair `(x', y')` with
    no on-curve obligation. `EdwardsPointAff.add` is `add_xy` paired with
    `add_closure`, so the group laws can be stated at either level. -/

/-- Pure-coordinate Edwards addition formula: `add_xy (Px,Py) (Qx,Qy)`
    returns `(x', y')` ratios. Total function in `F`; division by zero
    gives 0 in the rare degenerate case (which doesn't arise on a
    complete curve like Ed25519). -/
noncomputable def add_xy (E : EdwardsParams F) (Px Py Qx Qy : F) : F × F :=
  ( (Px * Qy + Qx * Py) / (1 + E.d * Px * Qx * Py * Qy)
  , (Py * Qy - E.a * Px * Qx) / (1 - E.d * Px * Qx * Py * Qy) )

/-- **Bernstein–Lange–Niederhagen completeness, affine leaf form.** For two
    on-curve affine points, `(d·Px·Qx·Py·Qy)² ≠ 1`.

    The Lean counterpart of fiat-crypto `src/Curves/Edwards/Pre.v`'s
    `denominator_nonzero`, and follows its proof. Writing `s` for a square
    root of `a` (`EdwardsParams.square_a`) and `u = d·Px·Qx·Py·Qy`, the two
    curve equations and `u² = 1` give

    `(s·Px ± u·Py)² = d · ((s·Qx ± Qy)·Px·Py)²`,

    so whichever of `s·Qx + Qy`, `s·Qx − Qy` is nonzero exhibits a square
    root of `d`, contradicting `EdwardsParams.nonsquare_d`. Both vanish only
    when `Qx = 0`, which `u² = 1` excludes.

    The addition-formula denominator facts `add_denom_pos` and
    `add_denom_neg` are theorems over this leaf. -/
theorem affine_denom_nonsquare {F : Type*} [Field F] {E : EdwardsParams F}
    (Px Py Qx Qy : F)
    (hP : OnCurveAff E Px Py) (hQ : OnCurveAff E Qx Qy) :
    (E.d * Px * Qx * Py * Qy)^2 ≠ 1 := by
  intro h
  have hP' : E.a * Px^2 + Py^2 = 1 + E.d * Px^2 * Py^2 := hP
  have hQ' : E.a * Qx^2 + Qy^2 = 1 + E.d * Qx^2 * Qy^2 := hQ
  obtain ⟨s, hs⟩ := E.square_a
  have hPx : Px ≠ 0 := by rintro rfl; simp at h
  have hPy : Py ≠ 0 := by rintro rfl; simp at h
  have hQx : Qx ≠ 0 := by rintro rfl; simp at h
  by_cases hc : s * Qx + Qy = 0
  · by_cases hc2 : s * Qx - Qy = 0
    · have hs0 : s ≠ 0 := fun hz => E.a_ne_zero (by rw [← hs, hz]; ring)
      have h2 : (2 : F) * s * Qx = 0 := by linear_combination hc + hc2
      rcases mul_eq_zero.mp h2 with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact E.two_ne_zero h''
        · exact hs0 h''
      · exact hQx h'
    · refine E.nonsquare_d ((s * Px - (E.d * Px * Qx * Py * Qy) * Py)
        / ((s * Qx - Qy) * Px * Py)) ?_
      rw [div_pow, div_eq_iff (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hc2 hPx) hPy))]
      linear_combination (Px^2 - E.d * Px^2 * Py^2 * Qx^2) * hs + (Py^2 - 1) * h
        + (-(E.d * Px^2 * Py^2)) * hQ' + hP'
  · refine E.nonsquare_d ((s * Px + (E.d * Px * Qx * Py * Qy) * Py)
      / ((s * Qx + Qy) * Px * Py)) ?_
    rw [div_pow, div_eq_iff (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hc hPx) hPy))]
    linear_combination (Px^2 - E.d * Px^2 * Py^2 * Qx^2) * hs + (Py^2 - 1) * h
      + (-(E.d * Px^2 * Py^2)) * hQ' + hP'

/-- Completeness, positive form: for `Px, Py, Qx, Qy` on the curve, the
    x-coordinate denominator of `add_xy` is nonzero. -/
theorem add_denom_pos {F : Type*} [Field F] {E : EdwardsParams F} (Px Py Qx Qy : F)
    (hP : OnCurveAff E Px Py) (hQ : OnCurveAff E Qx Qy) :
    (1 : F) + E.d * Px * Qx * Py * Qy ≠ 0 := by
  intro h
  refine affine_denom_nonsquare Px Py Qx Qy hP hQ ?_
  linear_combination (E.d * Px * Qx * Py * Qy - 1) * h

/-- Completeness, negative form: for `Px, Py, Qx, Qy` on the curve, the
    y-coordinate denominator of `add_xy` is nonzero. -/
theorem add_denom_neg {F : Type*} [Field F] {E : EdwardsParams F} (Px Py Qx Qy : F)
    (hP : OnCurveAff E Px Py) (hQ : OnCurveAff E Qx Qy) :
    (1 : F) - E.d * Px * Qx * Py * Qy ≠ 0 := by
  intro h
  refine affine_denom_nonsquare Px Py Qx Qy hP hQ ?_
  linear_combination (-(E.d * Px * Qx * Py * Qy) - 1) * h

/-- Cleared-denominator form of `add_closure`. `set a := E.a` and
    `set d := E.d` bind the record projections to local atoms, so the
    polynomial normalizer treats them as variables. -/
theorem add_closure_polynomial {F : Type*} [Field F] {E : EdwardsParams F}
    (Px Py Qx Qy : F)
    (hP : OnCurveAff E Px Py) (hQ : OnCurveAff E Qx Qy) :
    let a := E.a; let d := E.d
    a * (Px * Qy + Qx * Py)^2 * (1 - d * Px * Qx * Py * Qy)^2 +
      (Py * Qy - a * Px * Qx)^2 * (1 + d * Px * Qx * Py * Qy)^2 =
    (1 + d * Px * Qx * Py * Qy)^2 * (1 - d * Px * Qx * Py * Qy)^2 +
      d * (Px * Qy + Qx * Py)^2 * (Py * Qy - a * Px * Qx)^2 := by
  set a : F := E.a
  set d : F := E.d
  have hP' : a * Px^2 + Py^2 = 1 + d * Px^2 * Py^2 := hP
  have hQ' : a * Qx^2 + Qy^2 = 1 + d * Qx^2 * Qy^2 := hQ
  show a * (Px * Qy + Qx * Py)^2 * (1 - d * Px * Qx * Py * Qy)^2 +
    (Py * Qy - a * Px * Qx)^2 * (1 + d * Px * Qx * Py * Qy)^2 =
    (1 + d * Px * Qx * Py * Qy)^2 * (1 - d * Px * Qx * Py * Qy)^2 +
      d * (Px * Qy + Qx * Py)^2 * (Py * Qy - a * Px * Qx)^2
  -- `grobner` (in-kernel Gröbner-basis ideal membership, oracle-free)
  -- synthesises both closure cofactors from the on-curve constraints
  -- `hP'`, `hQ'`.
  grobner

/-- **Closure of Edwards addition** — `add_xy` of two on-curve points
    is on-curve. Lifts `add_closure_polynomial` over the common
    denominator. Mirrors Rocq's `Pre.v::onCurve_add`. -/
theorem add_closure {F : Type*} [Field F] {E : EdwardsParams F}
    (Px Py Qx Qy : F)
    (hP : OnCurveAff E Px Py) (hQ : OnCurveAff E Qx Qy) :
    OnCurveAff E (add_xy E Px Py Qx Qy).1 (add_xy E Px Py Qx Qy).2 := by
  set a : F := E.a with ha_def
  set d : F := E.d with hd_def
  have hA : (1 : F) + d * Px * Qx * Py * Qy ≠ 0 :=
    add_denom_pos Px Py Qx Qy hP hQ
  have hB : (1 : F) - d * Px * Qx * Py * Qy ≠ 0 :=
    add_denom_neg Px Py Qx Qy hP hQ
  have hAsq : ((1 : F) + d * Px * Qx * Py * Qy)^2 ≠ 0 := pow_ne_zero 2 hA
  have hBsq : ((1 : F) - d * Px * Qx * Py * Qy)^2 ≠ 0 := pow_ne_zero 2 hB
  have key := add_closure_polynomial Px Py Qx Qy hP hQ
  -- `key` is in a/d form; goal (after unfold) is in E.a/E.d form.
  unfold OnCurveAff add_xy
  dsimp only
  -- Lift via calc: write each side as numerator/(D₁²·D₂²) using
  -- div_add_div, then rw using key, then unfold the RHS.
  calc a * ((Px*Qy + Qx*Py) / (1 + d*Px*Qx*Py*Qy))^2 +
        ((Py*Qy - a*Px*Qx) / (1 - d*Px*Qx*Py*Qy))^2
      = (a * (Px*Qy + Qx*Py)^2 * (1 - d*Px*Qx*Py*Qy)^2 +
          (Py*Qy - a*Px*Qx)^2 * (1 + d*Px*Qx*Py*Qy)^2) /
        ((1 + d*Px*Qx*Py*Qy)^2 * (1 - d*Px*Qx*Py*Qy)^2) := by
        rw [div_pow, div_pow, ← mul_div_assoc,
            div_add_div _ _ hAsq hBsq]
        ring_nf
    _ = ((1 + d*Px*Qx*Py*Qy)^2 * (1 - d*Px*Qx*Py*Qy)^2 +
          d * (Px*Qy + Qx*Py)^2 * (Py*Qy - a*Px*Qx)^2) /
        ((1 + d*Px*Qx*Py*Qy)^2 * (1 - d*Px*Qx*Py*Qy)^2) := by
        rw [key]
    _ = 1 + d * ((Px*Qy + Qx*Py) / (1 + d*Px*Qx*Py*Qy))^2 *
            ((Py*Qy - a*Px*Qx) / (1 - d*Px*Qx*Py*Qy))^2 := by
        field_simp [hAsq, hBsq]

/-- Edwards addition formula. Lifted from `add_xy` via `add_closure`.

    For `a = -1`, `d = -121665/121666` (Ed25519): completeness is the
    classical Bernstein–Lange–Niederhagen completeness result. -/
noncomputable def add (P Q : EdwardsPointAff E) : EdwardsPointAff E :=
  let xy := add_xy E P.x P.y Q.x Q.y
  { x := xy.1, y := xy.2
    on_curve := add_closure P.x P.y Q.x Q.y P.on_curve Q.on_curve }

/-! ### Group law (Tier B #4 obligations)

    The Rocq proofs in `AffineProofs.v` use `Field.fsatz` (a
    Gröbner-basis tactic) for these. Mathlib's analogue is `grobner`
    (Lean 4.28's built-in Gröbner-basis tactic), which closes the
    cleared-denominator polynomial identities directly. -/

/-! ### Coordinate-level group-law lemmas

    These work at the `add_xy` level, so they need no on-curve witness.
    The structure-level lemmas below are lifted from them. -/

/-- Extensionality for `EdwardsPointAff` — equal x and y components
    imply equal points. The `on_curve` field is a `Prop` and so
    proof-irrelevant. -/
@[ext] theorem ext_aff {P Q : EdwardsPointAff E}
    (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q := by
  obtain ⟨px, py, _⟩ := P
  obtain ⟨qx, qy, _⟩ := Q
  cases hx; cases hy; rfl

/-- `add_xy` is symmetric in its two operands. -/
lemma add_xy_comm (Px Py Qx Qy : F) :
    add_xy E Px Py Qx Qy = add_xy E Qx Qy Px Py := by
  unfold add_xy; ext <;> simp <;> ring

/-- `add_xy` with `(0, 1)` on the left collapses to the right operand. -/
lemma add_xy_zero_left (Px Py : F) :
    add_xy E 0 1 Px Py = (Px, Py) := by
  unfold add_xy; simp

/-! ### Group-law theorems (lifted via `add_closure`)

    The structure equalities use `add_closure` to construct the on-curve
    witness on both sides. -/

/-- Affine Edwards addition is commutative. From `add_xy_comm` and
    `ext_aff`. -/
theorem add_comm (P Q : EdwardsPointAff E) :
    add P Q = add Q P := by
  apply ext_aff <;> (unfold add; simp [add_xy_comm P.x P.y Q.x Q.y])

/-- `0 + P = P`. From `add_xy_zero_left` and `ext_aff`. -/
theorem zero_add (P : EdwardsPointAff E) :
    add (zero E) P = P := by
  apply ext_aff <;> (unfold add zero; simp [add_xy_zero_left])

/-- `P + 0 = P`. Follows from `add_comm` + `zero_add`. -/
theorem add_zero (P : EdwardsPointAff E) :
    add P (zero E) = P := by
  rw [add_comm]; exact zero_add P

/-- `P + (-P) = 0`. Substituting `-P` for `Q`:
    - x-numerator collapses by symmetry: `Px·Py + (-Px)·Py = 0`.
    - y-numerator: `Py² - a·Px·(-Px) = Py² + a·Px²`. By the curve
      equation `a·Px² + Py² = 1 + d·Px²·Py²`, this equals
      `1 + d·Px²·Py²`.
    - y-denominator: `1 - d·Px·(-Px)·Py·Py = 1 + d·Px²·Py²`.
    - So y' = denom / denom = 1, given denom ≠ 0 (via `add_denom_neg`). -/
theorem add_neg_self (P : EdwardsPointAff E) :
    add P (neg P) = zero E := by
  apply ext_aff
  · -- x-coordinate: numerator collapses to 0
    show (add P (neg P)).x = (zero E).x
    unfold add zero neg add_xy
    dsimp only
    have h_num : P.x * P.y + (-P.x) * P.y = 0 := by ring
    rw [h_num, zero_div]
  · -- y-coordinate: numerator = denominator (both = 1 + d·Px²·Py²)
    show (add P (neg P)).y = (zero E).y
    unfold add zero neg add_xy
    dsimp only
    have h_curve : E.a * P.x^2 + P.y^2 = 1 + E.d * P.x^2 * P.y^2 := P.on_curve
    have h_denom_eq : (1 : F) - E.d * P.x * (-P.x) * P.y * P.y =
                      1 + E.d * P.x^2 * P.y^2 := by ring
    have h_num_eq : P.y * P.y - E.a * P.x * (-P.x) =
                    1 + E.d * P.x^2 * P.y^2 := by linear_combination h_curve
    -- The neg point's on-curve witness, needed by add_denom_neg.
    have h_negP_curve : OnCurveAff E (-P.x) P.y := by
      unfold OnCurveAff
      have := P.on_curve
      unfold OnCurveAff at this
      linear_combination this
    have h_denom_ne : (1 : F) - E.d * P.x * (-P.x) * P.y * P.y ≠ 0 :=
      add_denom_neg P.x P.y (-P.x) P.y P.on_curve h_negP_curve
    rw [h_num_eq, h_denom_eq]
    rw [h_denom_eq] at h_denom_ne
    exact div_self h_denom_ne

/-- **Polynomial form of `add_assoc` x-coordinate identity.** Cleared
    denominator form of `((P+Q)+R).x = (P+(Q+R)).x`. SymPy-computed
    witness; see `scripts/find_add_assoc_witness.py`. -/
theorem add_assoc_x_polynomial {F : Type*} [Field F] {E : EdwardsParams F}
    (Px Py Qx Qy Rx Ry : F)
    (hP : OnCurveAff E Px Py) (hQ : OnCurveAff E Qx Qy) (hR : OnCurveAff E Rx Ry) :
    let a := E.a; let d := E.d
    ((Px*Qy + Qx*Py) * Ry * (1 - d*Px*Qx*Py*Qy) + Rx * (Py*Qy - a*Px*Qx) * (1 + d*Px*Qx*Py*Qy)) * ((1 + d*Qx*Rx*Qy*Ry) * (1 - d*Qx*Rx*Qy*Ry) + d * Px * (Qx*Ry + Rx*Qy) * Py * (Qy*Ry - a*Qx*Rx)) = (Px * (Qy*Ry - a*Qx*Rx) * (1 + d*Qx*Rx*Qy*Ry) + (Qx*Ry + Rx*Qy) * Py * (1 - d*Qx*Rx*Qy*Ry)) * ((1 + d*Px*Qx*Py*Qy) * (1 - d*Px*Qx*Py*Qy) + d * (Px*Qy + Qx*Py) * Rx * (Py*Qy - a*Px*Qx) * Ry) := by
  set a : F := E.a
  set d : F := E.d
  have hP' : a * Px^2 + Py^2 = 1 + d * Px^2 * Py^2 := hP
  have hQ' : a * Qx^2 + Qy^2 = 1 + d * Qx^2 * Qy^2 := hQ
  have hR' : a * Rx^2 + Ry^2 = 1 + d * Rx^2 * Ry^2 := hR
  show ((Px*Qy + Qx*Py) * Ry * (1 - d*Px*Qx*Py*Qy) + Rx * (Py*Qy - a*Px*Qx) * (1 + d*Px*Qx*Py*Qy)) * ((1 + d*Qx*Rx*Qy*Ry) * (1 - d*Qx*Rx*Qy*Ry) + d * Px * (Qx*Ry + Rx*Qy) * Py * (Qy*Ry - a*Qx*Rx)) = (Px * (Qy*Ry - a*Qx*Rx) * (1 + d*Qx*Rx*Qy*Ry) + (Qx*Ry + Rx*Qy) * Py * (1 - d*Qx*Rx*Qy*Ry)) * ((1 + d*Px*Qx*Py*Qy) * (1 - d*Px*Qx*Py*Qy) + d * (Px*Qy + Qx*Py) * Rx * (Py*Qy - a*Px*Qx) * Ry)
  -- `grobner` (in-kernel Gröbner-basis ideal membership, oracle-free)
  -- synthesises the three associativity cofactors from `hP'`, `hQ'`, `hR'`.
  grobner

/-- **Polynomial form of `add_assoc` y-coordinate identity.** -/
theorem add_assoc_y_polynomial {F : Type*} [Field F] {E : EdwardsParams F}
    (Px Py Qx Qy Rx Ry : F)
    (hP : OnCurveAff E Px Py) (hQ : OnCurveAff E Qx Qy) (hR : OnCurveAff E Rx Ry) :
    let a := E.a; let d := E.d
    ((Py*Qy - a*Px*Qx) * Ry * (1 + d*Px*Qx*Py*Qy) - a * (Px*Qy + Qx*Py) * Rx * (1 - d*Px*Qx*Py*Qy)) * ((1 + d*Qx*Rx*Qy*Ry) * (1 - d*Qx*Rx*Qy*Ry) - d * Px * (Qx*Ry + Rx*Qy) * Py * (Qy*Ry - a*Qx*Rx)) = (Py * (Qy*Ry - a*Qx*Rx) * (1 + d*Qx*Rx*Qy*Ry) - a * Px * (Qx*Ry + Rx*Qy) * (1 - d*Qx*Rx*Qy*Ry)) * ((1 + d*Px*Qx*Py*Qy) * (1 - d*Px*Qx*Py*Qy) - d * (Px*Qy + Qx*Py) * Rx * (Py*Qy - a*Px*Qx) * Ry) := by
  set a : F := E.a
  set d : F := E.d
  have hP' : a * Px^2 + Py^2 = 1 + d * Px^2 * Py^2 := hP
  have hQ' : a * Qx^2 + Qy^2 = 1 + d * Qx^2 * Qy^2 := hQ
  have hR' : a * Rx^2 + Ry^2 = 1 + d * Rx^2 * Ry^2 := hR
  show ((Py*Qy - a*Px*Qx) * Ry * (1 + d*Px*Qx*Py*Qy) - a * (Px*Qy + Qx*Py) * Rx * (1 - d*Px*Qx*Py*Qy)) * ((1 + d*Qx*Rx*Qy*Ry) * (1 - d*Qx*Rx*Qy*Ry) - d * Px * (Qx*Ry + Rx*Qy) * Py * (Qy*Ry - a*Qx*Rx)) = (Py * (Qy*Ry - a*Qx*Rx) * (1 + d*Qx*Rx*Qy*Ry) - a * Px * (Qx*Ry + Rx*Qy) * (1 - d*Qx*Rx*Qy*Ry)) * ((1 + d*Px*Qx*Py*Qy) * (1 - d*Px*Qx*Py*Qy) - d * (Px*Qy + Qx*Py) * Rx * (Py*Qy - a*Px*Qx) * Ry)
  -- `grobner` synthesises the three associativity cofactors from `hP'`,
  -- `hQ'`, `hR'`.
  grobner


/-! ### Clearing a ratio-valued left operand

    In `add_assoc` the left operand of the outer `add_xy` is itself a pair of
    ratios `N₁/D₁`, `N₂/D₂`. These four lemmas put the resulting nested
    fraction over the common denominator `D₁·D₂`, which is the form the
    `add_assoc_*_polynomial` identities are stated in. -/

/-- The x-coordinate denominator of `add_xy` at a ratio-valued left operand,
    cleared of `D₁` and `D₂`. -/
private lemma denom_pos_clear {F : Type*} [Field F] {E : EdwardsParams F}
    (N₁ D₁ N₂ D₂ Rx Ry : F) (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (h : (1 : F) + E.d * (N₁ / D₁) * Rx * (N₂ / D₂) * Ry ≠ 0) :
    D₁ * D₂ + E.d * N₁ * Rx * N₂ * Ry ≠ 0 := by
  intro hc
  refine h ?_
  field_simp
  linear_combination hc

/-- The y-coordinate denominator of `add_xy` at a ratio-valued left operand,
    cleared of `D₁` and `D₂`. -/
private lemma denom_neg_clear {F : Type*} [Field F] {E : EdwardsParams F}
    (N₁ D₁ N₂ D₂ Rx Ry : F) (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (h : (1 : F) - E.d * (N₁ / D₁) * Rx * (N₂ / D₂) * Ry ≠ 0) :
    D₁ * D₂ - E.d * N₁ * Rx * N₂ * Ry ≠ 0 := by
  intro hc
  refine h ?_
  field_simp
  linear_combination hc

/-- `add_xy` x-coordinate at a ratio-valued left operand, over `D₁·D₂`. -/
private lemma add_xy_clear_fst {F : Type*} [Field F] {E : EdwardsParams F}
    (N₁ D₁ N₂ D₂ Rx Ry : F) (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (h : (1 : F) + E.d * (N₁ / D₁) * Rx * (N₂ / D₂) * Ry ≠ 0) :
    (add_xy E (N₁ / D₁) (N₂ / D₂) Rx Ry).1 =
      (N₁ * Ry * D₂ + Rx * N₂ * D₁) / (D₁ * D₂ + E.d * N₁ * Rx * N₂ * Ry) := by
  have hc := denom_pos_clear N₁ D₁ N₂ D₂ Rx Ry hD₁ hD₂ h
  unfold add_xy
  dsimp only
  rw [div_eq_div_iff h hc]
  field_simp

/-- `add_xy` y-coordinate at a ratio-valued left operand, over `D₁·D₂`. -/
private lemma add_xy_clear_snd {F : Type*} [Field F] {E : EdwardsParams F}
    (N₁ D₁ N₂ D₂ Rx Ry : F) (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (h : (1 : F) - E.d * (N₁ / D₁) * Rx * (N₂ / D₂) * Ry ≠ 0) :
    (add_xy E (N₁ / D₁) (N₂ / D₂) Rx Ry).2 =
      (N₂ * Ry * D₁ - E.a * N₁ * Rx * D₂) / (D₁ * D₂ - E.d * N₁ * Rx * N₂ * Ry) := by
  have hc := denom_neg_clear N₁ D₁ N₂ D₂ Rx Ry hD₁ hD₂ h
  unfold add_xy
  dsimp only
  rw [div_eq_div_iff h hc]
  field_simp

/-- **Affine Edwards addition is associative.** The Rocq counterpart is
    `fiat-crypto/src/Curves/Edwards/AffineProofs.v::associative_add`.
    `add_assoc_x_polynomial` and `add_assoc_y_polynomial` give the
    cleared-denominator identities; the lift puts each triple-nested ratio
    over its common denominator via `add_xy_clear_fst` / `add_xy_clear_snd`
    and compares numerators by `div_eq_div_iff`. -/
theorem add_assoc (P Q R : EdwardsPointAff E) :
    add (add P Q) R = add P (add Q R) := by
  have hd₁ : (1 : F) + E.d * P.x * Q.x * P.y * Q.y ≠ 0 :=
    add_denom_pos _ _ _ _ P.on_curve Q.on_curve
  have hd₂ : (1 : F) - E.d * P.x * Q.x * P.y * Q.y ≠ 0 :=
    add_denom_neg _ _ _ _ P.on_curve Q.on_curve
  have he₁ : (1 : F) + E.d * Q.x * R.x * Q.y * R.y ≠ 0 :=
    add_denom_pos _ _ _ _ Q.on_curve R.on_curve
  have he₂ : (1 : F) - E.d * Q.x * R.x * Q.y * R.y ≠ 0 :=
    add_denom_neg _ _ _ _ Q.on_curve R.on_curve
  have hPQ : OnCurveAff E
      ((P.x * Q.y + Q.x * P.y) / (1 + E.d * P.x * Q.x * P.y * Q.y))
      ((P.y * Q.y - E.a * P.x * Q.x) / (1 - E.d * P.x * Q.x * P.y * Q.y)) :=
    add_closure P.x P.y Q.x Q.y P.on_curve Q.on_curve
  have hQR : OnCurveAff E
      ((Q.x * R.y + R.x * Q.y) / (1 + E.d * Q.x * R.x * Q.y * R.y))
      ((Q.y * R.y - E.a * Q.x * R.x) / (1 - E.d * Q.x * R.x * Q.y * R.y)) :=
    add_closure Q.x Q.y R.x R.y Q.on_curve R.on_curve
  have hLpos := add_denom_pos _ _ R.x R.y hPQ R.on_curve
  have hLneg := add_denom_neg _ _ R.x R.y hPQ R.on_curve
  have hRpos := add_denom_pos _ _ P.x P.y hQR P.on_curve
  have hRneg := add_denom_neg _ _ P.x P.y hQR P.on_curve
  have hcomm : add_xy E P.x P.y
      ((Q.x * R.y + R.x * Q.y) / (1 + E.d * Q.x * R.x * Q.y * R.y))
      ((Q.y * R.y - E.a * Q.x * R.x) / (1 - E.d * Q.x * R.x * Q.y * R.y)) =
    add_xy E
      ((Q.x * R.y + R.x * Q.y) / (1 + E.d * Q.x * R.x * Q.y * R.y))
      ((Q.y * R.y - E.a * Q.x * R.x) / (1 - E.d * Q.x * R.x * Q.y * R.y))
      P.x P.y := add_xy_comm _ _ _ _
  apply ext_aff
  · show (add_xy E
        ((P.x * Q.y + Q.x * P.y) / (1 + E.d * P.x * Q.x * P.y * Q.y))
        ((P.y * Q.y - E.a * P.x * Q.x) / (1 - E.d * P.x * Q.x * P.y * Q.y))
        R.x R.y).1 =
      (add_xy E P.x P.y
        ((Q.x * R.y + R.x * Q.y) / (1 + E.d * Q.x * R.x * Q.y * R.y))
        ((Q.y * R.y - E.a * Q.x * R.x) / (1 - E.d * Q.x * R.x * Q.y * R.y))).1
    rw [hcomm, add_xy_clear_fst _ _ _ _ _ _ hd₁ hd₂ hLpos,
      add_xy_clear_fst _ _ _ _ _ _ he₁ he₂ hRpos,
      div_eq_div_iff (denom_pos_clear _ _ _ _ _ _ hd₁ hd₂ hLpos)
        (denom_pos_clear _ _ _ _ _ _ he₁ he₂ hRpos)]
    linear_combination add_assoc_x_polynomial P.x P.y Q.x Q.y R.x R.y
      P.on_curve Q.on_curve R.on_curve
  · show (add_xy E
        ((P.x * Q.y + Q.x * P.y) / (1 + E.d * P.x * Q.x * P.y * Q.y))
        ((P.y * Q.y - E.a * P.x * Q.x) / (1 - E.d * P.x * Q.x * P.y * Q.y))
        R.x R.y).2 =
      (add_xy E P.x P.y
        ((Q.x * R.y + R.x * Q.y) / (1 + E.d * Q.x * R.x * Q.y * R.y))
        ((Q.y * R.y - E.a * Q.x * R.x) / (1 - E.d * Q.x * R.x * Q.y * R.y))).2
    rw [hcomm, add_xy_clear_snd _ _ _ _ _ _ hd₁ hd₂ hLneg,
      add_xy_clear_snd _ _ _ _ _ _ he₁ he₂ hRneg,
      div_eq_div_iff (denom_neg_clear _ _ _ _ _ _ hd₁ hd₂ hLneg)
        (denom_neg_clear _ _ _ _ _ _ he₁ he₂ hRneg)]
    linear_combination add_assoc_y_polynomial P.x P.y Q.x Q.y R.x R.y
      P.on_curve Q.on_curve R.on_curve

end EdwardsPointAff

/-! ## 3. Extended (XYZT) coordinates

    Used in implementations because all add/double formulas are
    *complete* and *strongly unified* (same formula for double and
    add). The dalek pipeline uses these. -/

/-- Extended-coords representation: `(X, Y, Z, T)` with `Z ≠ 0` and
    the well-formedness `T·Z = X·Y`. The affine projection is
    `(X/Z, Y/Z)`, and `T = X·Y/Z`. -/
structure EdwardsPointExt (E : EdwardsParams F) where
  /-- Numerator of the x-coordinate. -/
  X : F
  /-- Numerator of the y-coordinate. -/
  Y : F
  /-- Common denominator. -/
  Z : F
  /-- Auxiliary: `T = X·Y/Z`. -/
  T : F
  /-- `Z` is nonzero. -/
  Z_ne_zero : Z ≠ 0
  /-- Well-formedness: `T·Z = X·Y`. -/
  TZ_eq_XY : T * Z = X * Y
  /-- The affine projection is on the curve. -/
  on_curve_aff : OnCurveAff E (X / Z) (Y / Z)

namespace EdwardsPointExt

variable {E : EdwardsParams F}

/-- Projection to affine. -/
def toAff (P : EdwardsPointExt E) : EdwardsPointAff E :=
  { x := P.X / P.Z, y := P.Y / P.Z, on_curve := P.on_curve_aff }

/-- **`F·G ≠ 0` completeness for the m1add formula**, the projective form
    of Bernstein–Lange–Niederhagen completeness at `a = -1`.

    The Rocq counterpart is `m1add`'s subtype obligation in fiat-crypto
    `src/Curves/Edwards/XYZT/Basic.v`, discharged there from
    `to_affine_denom_nonzero` in a section context carrying `char_ge_3`.
    Clearing `Z₁` and `Z₂` rewrites the product as
    `4·Z₁²·Z₂²·(1 - (d·x₁·x₂·y₁·y₂)²)`, so it follows from the affine leaf
    `EdwardsPointAff.affine_denom_nonsquare` together with
    `EdwardsParams.two_ne_zero` and the two `Z ≠ 0` witnesses. -/
theorem m1add_ZneZero (h_a_neg_one : E.a = -1) (P Q : EdwardsPointExt E) :
    (2 * P.Z * Q.Z - P.T * 2 * E.d * Q.T) *
    (2 * P.Z * Q.Z + P.T * 2 * E.d * Q.T) ≠ 0 := by
  intro h
  have hPZ : P.Z ≠ 0 := P.Z_ne_zero
  have hQZ : Q.Z ≠ 0 := Q.Z_ne_zero
  have h2 : (2 : F) ≠ 0 := E.two_ne_zero
  have h4 : (4 : F) ≠ 0 := by
    have h44 : (4 : F) = 2 * 2 := by norm_num
    rw [h44]; exact mul_ne_zero h2 h2
  have hPT : P.T * P.Z = P.X * P.Y := P.TZ_eq_XY
  have hQT : Q.T * Q.Z = Q.X * Q.Y := Q.TZ_eq_XY
  have hkey : P.Z ^ 2 * Q.Z ^ 2 = E.d ^ 2 * P.T ^ 2 * Q.T ^ 2 := by
    have h4' : (4 : F) * (P.Z ^ 2 * Q.Z ^ 2 - E.d ^ 2 * P.T ^ 2 * Q.T ^ 2) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h4' with h' | h'
    · exact absurd h' h4
    · linear_combination h'
  refine EdwardsPointAff.affine_denom_nonsquare (P.X / P.Z) (P.Y / P.Z)
    (Q.X / Q.Z) (Q.Y / Q.Z) P.on_curve_aff Q.on_curve_aff ?_
  field_simp
  linear_combination
    (-(E.d ^ 2 * Q.X ^ 2 * Q.Y ^ 2 * (P.T * P.Z + P.X * P.Y))) * hPT +
      (-(E.d ^ 2 * P.T ^ 2 * P.Z ^ 2 * (Q.T * Q.Z + Q.X * Q.Y))) * hQT +
      (-(P.Z ^ 2 * Q.Z ^ 2)) * hkey

/-! ### `to_affine_m1add` — the key Tier B #4 obligation -/

/-- Polynomial-form x-coord identity for `to_affine_m1add` (a = -1).
    Cleared denominators; uses only TZ_eq_XY constraints, no on-curve. -/
private theorem to_affine_m1add_x_polynomial
    (h_a_neg_one : E.a = -1) (P Q : EdwardsPointExt E) :
    let d := E.d
    ((P.Y + P.X) * (Q.Y + Q.X) - (P.Y - P.X) * (Q.Y - Q.X)) *
      (2 * P.Z * Q.Z - P.T * 2 * d * Q.T) *
      (P.Z^2 * Q.Z^2 + d * P.X * Q.X * P.Y * Q.Y) =
    (P.X * Q.Y + Q.X * P.Y) * P.Z * Q.Z *
      ((2 * P.Z * Q.Z - P.T * 2 * d * Q.T) * (2 * P.Z * Q.Z + P.T * 2 * d * Q.T)) := by
  set d : F := E.d
  have hPT' : P.T * P.Z = P.X * P.Y := P.TZ_eq_XY
  have hQT' : Q.T * Q.Z = Q.X * Q.Y := Q.TZ_eq_XY
  show ((P.Y + P.X) * (Q.Y + Q.X) - (P.Y - P.X) * (Q.Y - Q.X)) *
      (2 * P.Z * Q.Z - P.T * 2 * d * Q.T) *
      (P.Z^2 * Q.Z^2 + d * P.X * Q.X * P.Y * Q.Y) =
    (P.X * Q.Y + Q.X * P.Y) * P.Z * Q.Z *
      ((2 * P.Z * Q.Z - P.T * 2 * d * Q.T) * (2 * P.Z * Q.Z + P.T * 2 * d * Q.T))
  -- `grobner` synthesises the cofactors from `hPT'`, `hQT'` directly.
  grobner

/-- Polynomial-form y-coord identity for `to_affine_m1add` (a = -1). -/
private theorem to_affine_m1add_y_polynomial
    (h_a_neg_one : E.a = -1) (P Q : EdwardsPointExt E) :
    let d := E.d
    (2 * P.Z * Q.Z + P.T * 2 * d * Q.T) *
      ((P.Y + P.X) * (Q.Y + Q.X) + (P.Y - P.X) * (Q.Y - Q.X)) *
      (P.Z^2 * Q.Z^2 - d * P.X * Q.X * P.Y * Q.Y) =
    (P.Y * Q.Y + P.X * Q.X) * P.Z * Q.Z *
      ((2 * P.Z * Q.Z - P.T * 2 * d * Q.T) * (2 * P.Z * Q.Z + P.T * 2 * d * Q.T)) := by
  set d : F := E.d
  have hPT' : P.T * P.Z = P.X * P.Y := P.TZ_eq_XY
  have hQT' : Q.T * Q.Z = Q.X * Q.Y := Q.TZ_eq_XY
  show (2 * P.Z * Q.Z + P.T * 2 * d * Q.T) *
      ((P.Y + P.X) * (Q.Y + Q.X) + (P.Y - P.X) * (Q.Y - Q.X)) *
      (P.Z^2 * Q.Z^2 - d * P.X * Q.X * P.Y * Q.Y) =
    (P.Y * Q.Y + P.X * Q.X) * P.Z * Q.Z *
      ((2 * P.Z * Q.Z - P.T * 2 * d * Q.T) * (2 * P.Z * Q.Z + P.T * 2 * d * Q.T))
  -- `grobner` synthesises the cofactors from `hPT'`, `hQT'` directly.
  grobner

/-- The m1add x-coordinate, as a ratio of the extended coordinates, is the
    x-coordinate of `add_xy` on the affine projections. -/
private theorem m1add_coord_x_eq (h_a_neg_one : E.a = -1) (P Q : EdwardsPointExt E)
    (hZ3 : (2 * P.Z * Q.Z - P.T * 2 * E.d * Q.T) *
      (2 * P.Z * Q.Z + P.T * 2 * E.d * Q.T) ≠ 0) :
    ((P.Y + P.X) * (Q.Y + Q.X) - (P.Y - P.X) * (Q.Y - Q.X)) *
        (2 * P.Z * Q.Z - P.T * 2 * E.d * Q.T) /
        ((2 * P.Z * Q.Z - P.T * 2 * E.d * Q.T) *
          (2 * P.Z * Q.Z + P.T * 2 * E.d * Q.T)) =
      (EdwardsPointAff.add_xy E (P.X / P.Z) (P.Y / P.Z) (Q.X / Q.Z) (Q.Y / Q.Z)).1 := by
  have hPZ : P.Z ≠ 0 := P.Z_ne_zero
  have hQZ : Q.Z ≠ 0 := Q.Z_ne_zero
  have hDx : (1 : F) + E.d * (P.X / P.Z) * (Q.X / Q.Z) * (P.Y / P.Z) * (Q.Y / Q.Z) ≠ 0 :=
    EdwardsPointAff.add_denom_pos _ _ _ _ P.on_curve_aff Q.on_curve_aff
  have keyx := to_affine_m1add_x_polynomial h_a_neg_one P Q
  unfold EdwardsPointAff.add_xy
  dsimp only
  rw [div_eq_div_iff hZ3 hDx]
  field_simp
  linear_combination keyx

/-- The m1add y-coordinate, as a ratio of the extended coordinates, is the
    y-coordinate of `add_xy` on the affine projections. -/
private theorem m1add_coord_y_eq (h_a_neg_one : E.a = -1) (P Q : EdwardsPointExt E)
    (hZ3 : (2 * P.Z * Q.Z - P.T * 2 * E.d * Q.T) *
      (2 * P.Z * Q.Z + P.T * 2 * E.d * Q.T) ≠ 0) :
    ((2 * P.Z * Q.Z + P.T * 2 * E.d * Q.T) *
        ((P.Y + P.X) * (Q.Y + Q.X) + (P.Y - P.X) * (Q.Y - Q.X))) /
        ((2 * P.Z * Q.Z - P.T * 2 * E.d * Q.T) *
          (2 * P.Z * Q.Z + P.T * 2 * E.d * Q.T)) =
      (EdwardsPointAff.add_xy E (P.X / P.Z) (P.Y / P.Z) (Q.X / Q.Z) (Q.Y / Q.Z)).2 := by
  have hPZ : P.Z ≠ 0 := P.Z_ne_zero
  have hQZ : Q.Z ≠ 0 := Q.Z_ne_zero
  have hDy : (1 : F) - E.d * (P.X / P.Z) * (Q.X / Q.Z) * (P.Y / P.Z) * (Q.Y / Q.Z) ≠ 0 :=
    EdwardsPointAff.add_denom_neg _ _ _ _ P.on_curve_aff Q.on_curve_aff
  have keyy := to_affine_m1add_y_polynomial h_a_neg_one P Q
  unfold EdwardsPointAff.add_xy
  dsimp only
  rw [h_a_neg_one, div_eq_div_iff hZ3 hDy]
  field_simp
  linear_combination keyy

/-- The affine projection of the m1add coordinates lies on the curve: those
    coordinates are `add_xy` of two on-curve affine points, so
    `EdwardsPointAff.add_closure` applies. -/
theorem m1add_on_curve_aff (h_a_neg_one : E.a = -1) (P Q : EdwardsPointExt E) :
    OnCurveAff E
      (((P.Y + P.X) * (Q.Y + Q.X) - (P.Y - P.X) * (Q.Y - Q.X)) *
        (2 * P.Z * Q.Z - P.T * 2 * E.d * Q.T) /
        ((2 * P.Z * Q.Z - P.T * 2 * E.d * Q.T) *
          (2 * P.Z * Q.Z + P.T * 2 * E.d * Q.T)))
      (((2 * P.Z * Q.Z + P.T * 2 * E.d * Q.T) *
        ((P.Y + P.X) * (Q.Y + Q.X) + (P.Y - P.X) * (Q.Y - Q.X))) /
        ((2 * P.Z * Q.Z - P.T * 2 * E.d * Q.T) *
          (2 * P.Z * Q.Z + P.T * 2 * E.d * Q.T))) := by
  have hZ3 := m1add_ZneZero h_a_neg_one P Q
  rw [m1add_coord_x_eq h_a_neg_one P Q hZ3, m1add_coord_y_eq h_a_neg_one P Q hZ3]
  exact EdwardsPointAff.add_closure _ _ _ _ P.on_curve_aff Q.on_curve_aff

/-- The dalek `m1`-form addition formula, specialized at `a = -1`.
    Mirrors `bench_ed25519_sign.c::ed25519_add_*`.
    Body: A = (Y₁-X₁)·(Y₂-X₂); B = (Y₁+X₁)·(Y₂+X₂);
          C = T₁·2d·T₂;       D = 2·Z₁·Z₂;
          E_ = B - A; F_ = D - C; G = D + C; H = B + A;
          X₃ = E_·F_; Y₃ = G·H; T₃ = E_·H; Z₃ = F_·G. -/
noncomputable def m1add (h_a_neg_one : E.a = -1) (P Q : EdwardsPointExt E) :
    EdwardsPointExt E :=
  let A := (P.Y - P.X) * (Q.Y - Q.X)
  let B := (P.Y + P.X) * (Q.Y + Q.X)
  let C := P.T * 2 * E.d * Q.T
  let D := 2 * P.Z * Q.Z
  let F_ := D - C
  let G := D + C
  let H := B + A
  let E_ := B - A
  { X := E_ * F_
    Y := G * H
    Z := F_ * G
    T := E_ * H
    Z_ne_zero := m1add_ZneZero h_a_neg_one P Q
    TZ_eq_XY := by ring
    on_curve_aff := m1add_on_curve_aff h_a_neg_one P Q }

/-- **The key correctness theorem.** Adding two extended-coords points
    via `m1add` and projecting to affine is the same as projecting
    each operand to affine and adding via `EdwardsPointAff.add`.

    The Rocq counterpart is `to_affine_m1add` in fiat-crypto
    `src/Curves/Edwards/XYZT/Basic.v`. -/
theorem to_affine_m1add (h_a_neg_one : E.a = -1) (P Q : EdwardsPointExt E) :
    (m1add h_a_neg_one P Q).toAff = EdwardsPointAff.add P.toAff Q.toAff := by
  have hZ3 := m1add_ZneZero h_a_neg_one P Q
  apply EdwardsPointAff.ext_aff
  · show (m1add h_a_neg_one P Q).X / (m1add h_a_neg_one P Q).Z =
      (EdwardsPointAff.add_xy E (P.X / P.Z) (P.Y / P.Z) (Q.X / Q.Z) (Q.Y / Q.Z)).1
    exact m1add_coord_x_eq h_a_neg_one P Q hZ3
  · show (m1add h_a_neg_one P Q).Y / (m1add h_a_neg_one P Q).Z =
      (EdwardsPointAff.add_xy E (P.X / P.Z) (P.Y / P.Z) (Q.X / Q.Z) (Q.Y / Q.Z)).2
    exact m1add_coord_y_eq h_a_neg_one P Q hZ3

end EdwardsPointExt

/-! ## 4. Ed25519 specialization (stub)

    Stand-alone Ed25519 instance for downstream files. Requires:
    - `Fact (Nat.Prime (2^255 - 19))` (already an axiom in
      `Ed25519Spec.lean`'s `fp_is_prime`).
    - The `EdwardsParams` field proofs (immediate after primality is
      settled).

    **Stubbed pending the Lean port — see `Ed25519Spec.lean` for the
    cited Rocq theorems.** Concretely:
    - `Curve25519.v`'s `a_eq_neg_one`, `d_value` give the constants.
    - `AffineProofs.v`'s non-degeneracy hypotheses are the obligations
      (`a ≠ 0`, `d ≠ 0`, `a ≠ d`); all three resolve by direct
      computation on the rational representations of -1, -121665/121666.
    - `(2 : F) ≠ 0` holds since `2^255 - 19` is odd.
    - `square_a` holds because `2^255 - 19 ≡ 1 [MOD 4]`, so `-1` is a
      quadratic residue.
    - `nonsquare_d` is the quadratic-residue character of
      `-121665/121666` at `2^255 - 19`.

    The companion `Ed25519Spec.lean` already uses `EdPoint` (extended
    coords) and `OnCurve` predicates as opaque axioms; once this file's
    Tier B #4 obligations are discharged, those axioms can be either
    transparently defined or re-cited against the proved versions
    here. -/

end CatCrypt.Crypto.Jasmin.EdwardsCurve
