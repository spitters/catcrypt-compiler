/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveLowering
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Twisted-Edwards affine dialect — a curve point is a coordinate pair

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`ecDialect`'s `ECTy.point p` denotes `ECPoint p = Option (ZMod p × ZMod p)`, with
`none` the point at infinity. `fieldDialect` has no such summand, so a total
lowering of the curve type to the field type does not exist there.

This dialect drops the `Option`. Its affine value type `aff p` denotes
`ZMod p × ZMod p`, and its group ops are the twisted-Edwards unified addition law
applied directly to coordinate pairs — total functions, no case split. The
neutral element is the coordinate value `(0, 1)`, so the identity is a point of
the value type rather than an extra constructor. This is the representation
prime-ir's `elliptic_curve` dialect uses (`fractalyze/prime-ir`,
`prime_ir/Dialect/EllipticCurve/`), where the same choice makes the
`elliptic_curve → field` lowering total.

Twisted Edwards is the model where the choice is sound: the unified addition law
is complete, so one formula covers addition, doubling and the identity, and
`EllipticCurveLowering.edPadd_lowers_to_schedule` /
`edPdbl_lowers_to_schedule` carry no side condition (the Weierstrass
`padd_lowers_to_schedule` needs `x₁ ≠ x₂`). The faithfulness theorems below
relate the pair-valued ops to `EdwardsParams.add` on `ECPoint p` with no
hypothesis.

## Main definitions

* `edAddF` / `edDblF` / `edNegF` — the coordinate-pair leaves. `edAddF` is
  `EllipticCurveLowering.EdwardsAddSchedule`; `edDblF` is `edAddF` at equal
  arguments.
* `EdAffTy` / `EdAffOp` / `edAffDialect` — the dialect, its signature and its
  denotation.
* `pointOf` — the embedding `ZMod p × ZMod p → ECPoint p` sending a pair to the
  affine point.
* `ExtPt`, `extAddF` / `extDblF` / `extNegF`, `affToExtF` / `extToAffF` — the
  extended coordinates `(X, Y, Z, T)` (upstream `ed_extended`), the
  `add-2008-hwcd` unified addition, and the two `convert_point_type` directions.
  The type `EdAffTy.ext p` and the ops `extAdd`, `extDbl`, `extNeg`,
  `affToExt`, `extToAff` carry them into the dialect.

## Main results

* `edAdd_faithful` / `edDbl_faithful` — `pointOf` carries the pair-valued ops to
  `EdwardsParams.add` on `ECPoint p`, with no hypothesis on the operands.
* `edAddF_id_right` / `edAddF_id_left` — `(0, 1)` is a two-sided neutral element
  for `edAddF`.
* `pointOf_add_id_right` / `pointOf_add_id_left` — the image of `(0, 1)` is
  neutral for `EdwardsParams.add` on affine points.
* `extAdd_faithful` / `extAdd_point_faithful` — for a prime modulus, well-formed
  extended operands and nonzero affine denominators `1 ± d·x₁x₂y₁y₂`, the
  extended sum projects to `edAddF` and to `EdwardsParams.add`.
* `extToAffF_affToExtF`, `extNeg_faithful` — the conversions and negation
  commute with the projection.
* `edAffDialect_ctSafe_all` — every op of the dialect is data-oblivious.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EcEdwardsAffineDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

/-! ## 1. The coordinate-pair leaves

Every leaf is a total function on `ZMod p × ZMod p`. `edAddF` is the unified
twisted-Edwards addition schedule over the `FieldDialect` leaves; `edDblF` reuses
it at equal arguments rather than running a separate doubling chain. -/

/-- Twisted-Edwards addition on affine coordinate pairs: the unified schedule
    `EdwardsAddSchedule` applied to the two pairs. -/
@[reducible] def edAddF {p : Nat} (C : EdwardsParams p) (P Q : ZMod p × ZMod p) :
    ZMod p × ZMod p :=
  EdwardsAddSchedule C.a C.d P.1 P.2 Q.1 Q.2

/-- Twisted-Edwards doubling on an affine coordinate pair: `edAddF` at equal
    arguments. -/
@[reducible] def edDblF {p : Nat} (C : EdwardsParams p) (P : ZMod p × ZMod p) :
    ZMod p × ZMod p :=
  edAddF C P P

/-- Twisted-Edwards negation on an affine coordinate pair: `(x, y) ↦ (−x, y)`. -/
@[reducible] def edNegF {p : Nat} (P : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (-P.1, P.2)

/-- Negation is an involution. -/
theorem edNegF_edNegF {p : Nat} (P : ZMod p × ZMod p) :
    edNegF (edNegF P) = P := by
  simp [edNegF]

/-! ### Extended coordinates

An extended point is a quadruple `(X, Y, Z, T)` with `Z ≠ 0` and `T·Z = X·Y`,
standing for the affine point `(X/Z, Y/Z)` (upstream
`!elliptic_curve.ed_extended`). Its addition is the unified formula
`add-2008-hwcd` for general `a`; it has no field inversion. -/

/-- An extended coordinate quadruple `(X, Y, Z, T)`. -/
abbrev ExtPt (p : Nat) : Type := ZMod p × ZMod p × ZMod p × ZMod p

/-- Unified twisted-Edwards addition in extended coordinates (`add-2008-hwcd`):
    with `A = X₁X₂`, `B = Y₁Y₂`, `C = d·T₁T₂`, `D = Z₁Z₂`,
    `E = (X₁+Y₁)(X₂+Y₂) − A − B`, `F = D − C`, `G = D + C`, `H = B − a·A`,
    the sum is `(E·F, G·H, F·G, E·H)`. -/
def extAddF {p : Nat} (C : EdwardsParams p) (P Q : ExtPt p) : ExtPt p :=
  let A := P.1 * Q.1
  let B := P.2.1 * Q.2.1
  let Cc := C.d * P.2.2.2 * Q.2.2.2
  let D := P.2.2.1 * Q.2.2.1
  let E := (P.1 + P.2.1) * (Q.1 + Q.2.1) - A - B
  let F := D - Cc
  let G := D + Cc
  let H := B - C.a * A
  (E * F, G * H, F * G, E * H)

/-- Doubling in extended coordinates: `extAddF` at equal arguments. -/
def extDblF {p : Nat} (C : EdwardsParams p) (P : ExtPt p) : ExtPt p :=
  extAddF C P P

/-- Negation in extended coordinates: `(X, Y, Z, T) ↦ (−X, Y, Z, −T)`. -/
def extNegF {p : Nat} (P : ExtPt p) : ExtPt p :=
  (-P.1, P.2.1, P.2.2.1, -P.2.2.2)

/-- The affine pair `(x, y)` as the extended point `(x, y, 1, x·y)`. -/
def affToExtF {p : Nat} (q : ZMod p × ZMod p) : ExtPt p :=
  (q.1, q.2, 1, q.1 * q.2)

/-- The affine pair `(X/Z, Y/Z)` of an extended point. -/
def extToAffF {p : Nat} (P : ExtPt p) : ZMod p × ZMod p :=
  (P.1 * P.2.2.1⁻¹, P.2.1 * P.2.2.1⁻¹)

/-- An extended point is well formed when `Z ≠ 0` and `T·Z = X·Y`. -/
def ExtPt.WF {p : Nat} (P : ExtPt p) : Prop :=
  P.2.2.1 ≠ 0 ∧ P.2.2.2 * P.2.2.1 = P.1 * P.2.1

/-! ## 2. Types -/

/-- The dialect's value-type alphabet: an affine coordinate pair or an extended
    coordinate quadruple over `ZMod p`. The modulus lives in the type, so a
    program mixing two base fields is ill-typed. -/
inductive EdAffTy where
  /-- An affine coordinate pair, `⟦·⟧ = ZMod p × ZMod p`. -/
  | aff (p : Nat)
  /-- An extended coordinate quadruple, `⟦·⟧ = ExtPt p`. -/
  | ext (p : Nat)
  deriving DecidableEq

/-- Total denotation of `EdAffTy`: coordinate tuples, with no infinity
    summand. -/
@[reducible] instance : TyDenote EdAffTy where
  denote
    | .aff p => ZMod p × ZMod p
    | .ext p => ExtPt p

/-! ## 3. Op tags -/

/-- Operation tags. The group-law ops carry the twisted-Edwards curve parameters
    `C : EdwardsParams p`; negation is parameter-free. -/
inductive EdAffOp where
  /-- Point add `P + Q : aff p` (the unified complete addition law). -/
  | edAdd (p : Nat) (C : EdwardsParams p)
  /-- Point double `2·P : aff p` (the same law at `P = Q`). -/
  | edDbl (p : Nat) (C : EdwardsParams p)
  /-- Point negate `−P : aff p`. -/
  | edNeg (p : Nat)
  /-- Point add `P + Q : ext p` in extended coordinates. -/
  | extAdd (p : Nat) (C : EdwardsParams p)
  /-- Point double `2·P : ext p` in extended coordinates. -/
  | extDbl (p : Nat) (C : EdwardsParams p)
  /-- Point negate `−P : ext p` in extended coordinates. -/
  | extNeg (p : Nat)
  /-- `convert_point_type` from `ed_affine` to `ed_extended`. -/
  | affToExt (p : Nat)
  /-- `convert_point_type` from `ed_extended` to `ed_affine`. -/
  | extToAff (p : Nat)
  deriving DecidableEq

/-! ## 4. The dialect -/

/-- The twisted-Edwards affine dialect: `Op` is `EdAffOp`, `Ty` is `EdAffTy`. -/
@[reducible] def edAffDialect : Dialect :=
  { Op := EdAffOp, Ty := EdAffTy }

/-! ## 5. Op signatures -/

instance : DialectSignature edAffDialect where
  sig op := match op with
    | .edAdd p _ => [.aff p, .aff p]
    | .edDbl p _ => [.aff p]
    | .edNeg p => [.aff p]
    | .extAdd p _ => [.ext p, .ext p]
    | .extDbl p _ => [.ext p]
    | .extNeg p => [.ext p]
    | .affToExt p => [.aff p]
    | .extToAff p => [.ext p]
  ret op := match op with
    | .edAdd p _ => .aff p
    | .edDbl p _ => .aff p
    | .edNeg p => .aff p
    | .extAdd p _ => .ext p
    | .extDbl p _ => .ext p
    | .extNeg p => .ext p
    | .affToExt p => .ext p
    | .extToAff p => .aff p

/-! ## 6. Op denotation

Each denotation is a total function on coordinate pairs. `edAdd` is the unified
schedule with no case split; `edDbl` is that schedule at equal arguments. -/

instance edAffDenote : DialectDenote edAffDialect where
  denote op := match op with
    | .edAdd _ C => fun args => edAddF C args.head args.tail.head
    | .edDbl _ C => fun args => edDblF C args.head
    | .edNeg _ => fun args => edNegF args.head
    | .extAdd _ C => fun args => extAddF C args.head args.tail.head
    | .extDbl _ C => fun args => extDblF C args.head
    | .extNeg _ => fun args => extNegF args.head
    | .affToExt _ => fun args => affToExtF args.head
    | .extToAff _ => fun args => extToAffF args.head

/-- `extAdd` denotes the extended-coordinate addition. -/
theorem extAdd_denote {p : Nat} (C : EdwardsParams p) (P Q : ExtPt p) :
    edAffDenote.denote (.extAdd p C) (.cons P (.cons Q .nil)) = extAddF C P Q := rfl

/-- `edAdd` denotes to the coordinate-pair addition leaf. -/
theorem edAdd_denote {p : Nat} (C : EdwardsParams p) (P Q : ZMod p × ZMod p) :
    edAffDenote.denote (.edAdd p C) (.cons P (.cons Q .nil)) = edAddF C P Q := rfl

/-- `edDbl` denotes to the addition leaf at equal arguments. -/
theorem edDbl_denote {p : Nat} (C : EdwardsParams p) (P : ZMod p × ZMod p) :
    edAffDenote.denote (.edDbl p C) (.cons P .nil) = edAddF C P P := rfl

/-- `edNeg` denotes to the coordinate negation `(x, y) ↦ (−x, y)`. -/
theorem edNeg_denote {p : Nat} (P : ZMod p × ZMod p) :
    edAffDenote.denote (.edNeg p) (.cons P .nil) = (-P.1, P.2) := rfl

/-! ## 7. Faithfulness

`pointOf` embeds a coordinate pair as an affine `ECPoint p`. The two group ops
commute with it unconditionally, because the twisted-Edwards law is unified:
`EllipticCurveLowering`'s `edPadd_lowers_to_schedule` and
`edPdbl_lowers_to_schedule` hold for all coordinates. -/

/-- The embedding of a coordinate pair as an affine curve point. -/
def pointOf {p : Nat} (q : ZMod p × ZMod p) : ECPoint p := ECPoint.aff q.1 q.2

/-- **Addition is faithful.** For all coordinate pairs, the pair-valued add
    followed by the embedding equals the `ECPoint` group add of the embedded
    operands. No hypothesis on the operands: the unified law is complete. -/
theorem edAdd_faithful {p : Nat} (C : EdwardsParams p) (a b : ZMod p × ZMod p) :
    pointOf (edAddF C a b) = C.add (pointOf a) (pointOf b) :=
  (edwardsAddSchedule_denote C a.1 a.2 b.1 b.2).symm

/-- **Doubling is faithful.** The pair-valued double followed by the embedding
    equals the `ECPoint` group add of the embedded point with itself. -/
theorem edDbl_faithful {p : Nat} (C : EdwardsParams p) (a : ZMod p × ZMod p) :
    pointOf (edDblF C a) = C.add (pointOf a) (pointOf a) :=
  edAdd_faithful C a a

/-- Faithfulness at the op denotations: the dialect's `edAdd` and the abstract
    group add agree through `pointOf`. -/
theorem edAdd_denote_faithful {p : Nat} (C : EdwardsParams p) (P Q : ZMod p × ZMod p) :
    pointOf (edAffDenote.denote (.edAdd p C) (.cons P (.cons Q .nil)))
      = ecDenote.denote (.edPadd p C) (.cons (pointOf P) (.cons (pointOf Q) .nil)) :=
  edAdd_faithful C P Q

/-- Faithfulness at the op denotations for doubling. -/
theorem edDbl_denote_faithful {p : Nat} (C : EdwardsParams p) (P : ZMod p × ZMod p) :
    pointOf (edAffDenote.denote (.edDbl p C) (.cons P .nil))
      = ecDenote.denote (.edPdbl p C) (.cons (pointOf P) .nil) :=
  edDbl_faithful C P

/-! ### Extended coordinates

`extToAffF` carries the extended ops to the affine ones. Addition needs a prime
modulus (so `ZMod p` is a field), well-formed operands, and the two affine
denominators `1 ± d·x₁x₂y₁y₂` nonzero; the latter hold for every pair of curve
points on a complete curve. -/

/-- `extToAffF` is a left inverse of `affToExtF`. -/
theorem extToAffF_affToExtF {p : Nat} (q : ZMod p × ZMod p) :
    extToAffF (affToExtF q) = q := by
  simp [extToAffF, affToExtF]

/-- `affToExtF` produces well-formed extended points. -/
theorem affToExtF_wf {p : Nat} [Fact p.Prime] (q : ZMod p × ZMod p) :
    (affToExtF q).WF := by
  simp [affToExtF, ExtPt.WF]

/-- Negation commutes with `extToAffF`. -/
theorem extNeg_faithful {p : Nat} (P : ExtPt p) :
    extToAffF (extNegF P) = edNegF (extToAffF P) := by
  simp [extToAffF, extNegF, edNegF, neg_mul]

/-- Extended addition of two points written as scaled affine pairs
    `(x·Z, y·Z, Z, x·y·Z)`: with `k = Z₁Z₂` and `t = d·x₁x₂y₁y₂`, the quantities
    `E, F, G, H` of `extAddF` are `k` times `x₁y₂ + y₁x₂`, `1 − t`, `1 + t` and
    `y₁y₂ − a·x₁x₂`. -/
theorem extAddF_scaled {p : Nat} (C : EdwardsParams p) (x1 y1 x2 y2 Z1 Z2 : ZMod p) :
    extAddF C (x1 * Z1, y1 * Z1, Z1, x1 * y1 * Z1) (x2 * Z2, y2 * Z2, Z2, x2 * y2 * Z2)
      = ((Z1 * Z2) * (x1 * y2 + y1 * x2) * ((Z1 * Z2) * (1 - C.d * x1 * x2 * y1 * y2)),
         (Z1 * Z2) * (1 + C.d * x1 * x2 * y1 * y2) * ((Z1 * Z2) * (y1 * y2 - C.a * (x1 * x2))),
         (Z1 * Z2) * (1 - C.d * x1 * x2 * y1 * y2) * ((Z1 * Z2) * (1 + C.d * x1 * x2 * y1 * y2)),
         (Z1 * Z2) * (x1 * y2 + y1 * x2) * ((Z1 * Z2) * (y1 * y2 - C.a * (x1 * x2)))) := by
  simp only [extAddF, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- **Extended addition is faithful.** For well-formed extended points whose
    affine images have nonzero addition denominators, the extended sum projects
    to the affine sum. -/
theorem extAdd_faithful {p : Nat} [Fact p.Prime] (C : EdwardsParams p) (P Q : ExtPt p)
    (hP : P.WF) (hQ : Q.WF)
    (hpos : 1 + C.d * (extToAffF P).1 * (extToAffF Q).1 * (extToAffF P).2
      * (extToAffF Q).2 ≠ 0)
    (hneg : 1 - C.d * (extToAffF P).1 * (extToAffF Q).1 * (extToAffF P).2
      * (extToAffF Q).2 ≠ 0) :
    extToAffF (extAddF C P Q) = edAddF C (extToAffF P) (extToAffF Q) := by
  obtain ⟨X1, Y1, Z1, T1⟩ := P
  obtain ⟨X2, Y2, Z2, T2⟩ := Q
  obtain ⟨hZ1, hT1⟩ := hP
  obtain ⟨hZ2, hT2⟩ := hQ
  simp only [extToAffF] at *
  have hP' : ((X1, Y1, Z1, T1) : ExtPt p) = (X1 * Z1⁻¹ * Z1, Y1 * Z1⁻¹ * Z1, Z1,
      X1 * Z1⁻¹ * (Y1 * Z1⁻¹) * Z1) := by
    have e1 : T1 = X1 * Y1 * Z1⁻¹ := (eq_mul_inv_iff_mul_eq₀ hZ1).2 hT1
    simp only [e1, Prod.mk.injEq]
    refine ⟨by field_simp, by field_simp, trivial, by field_simp⟩
  have hQ' : ((X2, Y2, Z2, T2) : ExtPt p) = (X2 * Z2⁻¹ * Z2, Y2 * Z2⁻¹ * Z2, Z2,
      X2 * Z2⁻¹ * (Y2 * Z2⁻¹) * Z2) := by
    have e2 : T2 = X2 * Y2 * Z2⁻¹ := (eq_mul_inv_iff_mul_eq₀ hZ2).2 hT2
    simp only [e2, Prod.mk.injEq]
    refine ⟨by field_simp, by field_simp, trivial, by field_simp⟩
  have hk : Z1 * Z2 ≠ 0 := mul_ne_zero hZ1 hZ2
  rw [hP', hQ', extAddF_scaled]
  simp only [edAddF, EdwardsAddSchedule, edTSchedule, edXNumSchedule,
    edYNumSchedule, edRxSchedule, edRySchedule]
  generalize X1 * Z1⁻¹ = x1 at *
  generalize Y1 * Z1⁻¹ = y1 at *
  generalize X2 * Z2⁻¹ = x2 at *
  generalize Y2 * Z2⁻¹ = y2 at *
  generalize Z1 * Z2 = k at *
  refine Prod.ext ?_ ?_
  · show _ = (x1 * y2 + y1 * x2) * (1 + C.d * x1 * x2 * y1 * y2)⁻¹
    generalize 1 - C.d * x1 * x2 * y1 * y2 = f at *
    generalize 1 + C.d * x1 * x2 * y1 * y2 = g at *
    field_simp
  · show _ = (y1 * y2 - C.a * (x1 * x2)) * (1 - C.d * x1 * x2 * y1 * y2)⁻¹
    generalize 1 - C.d * x1 * x2 * y1 * y2 = f at *
    generalize 1 + C.d * x1 * x2 * y1 * y2 = g at *
    field_simp

/-- Extended addition, read through `extToAffF` and `pointOf`, is the group
    addition `EdwardsParams.add` on `ECPoint p`. -/
theorem extAdd_point_faithful {p : Nat} [Fact p.Prime] (C : EdwardsParams p)
    (P Q : ExtPt p) (hP : P.WF) (hQ : Q.WF)
    (hpos : 1 + C.d * (extToAffF P).1 * (extToAffF Q).1 * (extToAffF P).2
      * (extToAffF Q).2 ≠ 0)
    (hneg : 1 - C.d * (extToAffF P).1 * (extToAffF Q).1 * (extToAffF P).2
      * (extToAffF Q).2 ≠ 0) :
    pointOf (extToAffF (extAddF C P Q))
      = C.add (pointOf (extToAffF P)) (pointOf (extToAffF Q)) := by
  rw [extAdd_faithful C P Q hP hQ hpos hneg, edAdd_faithful]

/-! ## 8. The sentinel identity

`(0, 1)` is the neutral element of the coordinate-pair law. Both denominators of
the unified formula are `1` there, so the statement reduces to `(1 : ZMod p)⁻¹`
acting as `1`. -/

/-- **`(0, 1)` is a right identity** for the coordinate-pair addition. -/
theorem edAddF_id_right {p : Nat} (C : EdwardsParams p) (a : ZMod p × ZMod p) :
    edAddF C a ((0, 1) : ZMod p × ZMod p) = a := by
  obtain ⟨x, y⟩ := a
  simp only [edAddF, EdwardsAddSchedule, edTSchedule, edXNumSchedule, edYNumSchedule,
    edRxSchedule, edRySchedule, mul_one, mul_zero, zero_mul, add_zero, sub_zero,
    ZMod.inv_one]

/-- **`(0, 1)` is a left identity** for the coordinate-pair addition. -/
theorem edAddF_id_left {p : Nat} (C : EdwardsParams p) (a : ZMod p × ZMod p) :
    edAddF C ((0, 1) : ZMod p × ZMod p) a = a := by
  obtain ⟨x, y⟩ := a
  simp only [edAddF, EdwardsAddSchedule, edTSchedule, edXNumSchedule, edYNumSchedule,
    edRxSchedule, edRySchedule, one_mul, mul_one, mul_zero, zero_mul, zero_add,
    add_zero, sub_zero, ZMod.inv_one]

/-- The image of the sentinel is a right identity for `EdwardsParams.add` on
    affine points. -/
theorem pointOf_add_id_right {p : Nat} (C : EdwardsParams p) (a : ZMod p × ZMod p) :
    C.add (pointOf a) (pointOf ((0, 1) : ZMod p × ZMod p)) = pointOf a := by
  rw [← edAdd_faithful, edAddF_id_right]

/-- The image of the sentinel is a left identity for `EdwardsParams.add` on
    affine points. -/
theorem pointOf_add_id_left {p : Nat} (C : EdwardsParams p) (a : ZMod p × ZMod p) :
    C.add (pointOf ((0, 1) : ZMod p × ZMod p)) (pointOf a) = pointOf a := by
  rw [← edAdd_faithful, edAddF_id_left]

/-! ## 9. Constant-time predicate

Every op is a fixed straight-line schedule of field operations on its operands,
with no branch on a value, so each is data-oblivious. -/

/-- Per-op CT predicate: every op of this dialect is constant-time. -/
def EdAffOp.ctSafe : EdAffOp → Bool
  | _ => true

@[simp] theorem EdAffOp.ctSafe_all (op : EdAffOp) : op.ctSafe = true := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt edAffDialect} {t : EdAffTy}
    (e : Expr edAffDialect Γ t) : Bool :=
  e.op.ctSafe

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound expression
    is. -/
def ctSafeCom {Γ : Ctxt edAffDialect} {t : EdAffTy} :
    Com edAffDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- Every program of the dialect is constant-time. -/
theorem edAffDialect_ctSafe_all {Γ : Ctxt edAffDialect} {t : EdAffTy}
    (c : Com edAffDialect Γ t) : ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp [ctSafeCom, ctSafeExpr, ih]

/-! ## 10. Smoke test

A one-op program `let R = edAdd P Q; ret R` over the twisted-Edwards curve with
`a = 1`, `d = 2` over `ZMod 7`, evaluated with `Q` the sentinel `(0, 1)`. -/

/-- A tiny twisted-Edwards parameter pair over `ZMod 7`. -/
def smokeCurve : EdwardsParams 7 := ⟨1, 2⟩

/-- One-op smoke program: an `edAdd` over `[aff 7, aff 7]`. -/
def smokeProg : Com edAffDialect [.aff 7, .aff 7] (.aff 7) :=
  .var (.mk (.edAdd 7 smokeCurve) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- Adding the sentinel returns the other operand. -/
example :
    smokeProg.denote (.cons ((2, 3) : ZMod 7 × ZMod 7) (.cons ((0, 1) : ZMod 7 × ZMod 7) .nil))
      = ((2, 3) : ZMod 7 × ZMod 7) :=
  edAddF_id_right smokeCurve (2, 3)

end CatCrypt.Crypto.SecureCompilation.VIR.EcEdwardsAffineDialect
