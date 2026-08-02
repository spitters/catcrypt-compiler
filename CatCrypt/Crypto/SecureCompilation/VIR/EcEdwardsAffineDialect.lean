/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveLowering

/-!
# Twisted-Edwards affine dialect — a curve point is a coordinate pair

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`ecDialect`'s `ECTy.point p` denotes `ECPoint p = Option (ZMod p × ZMod p)`, with
`none` the point at infinity. `fieldDialect` has no such summand, so a total
lowering of the curve type to the field type does not exist there.

This dialect drops the `Option`. Its single value type `aff p` denotes
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

## Main results

* `edAdd_faithful` / `edDbl_faithful` — `pointOf` carries the pair-valued ops to
  `EdwardsParams.add` on `ECPoint p`, with no hypothesis on the operands.
* `edAddF_id_right` / `edAddF_id_left` — `(0, 1)` is a two-sided neutral element
  for `edAddF`.
* `pointOf_add_id_right` / `pointOf_add_id_left` — the image of `(0, 1)` is
  neutral for `EdwardsParams.add` on affine points.
* `edAffDialect_ctSafe_all` — every op of the dialect is data-oblivious.
-/

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

/-! ## 2. Types -/

/-- The dialect's value-type alphabet: an affine coordinate pair over `ZMod p`.
    The modulus lives in the type, so a program mixing two base fields is
    ill-typed. -/
inductive EdAffTy where
  /-- An affine coordinate pair, `⟦·⟧ = ZMod p × ZMod p`. -/
  | aff (p : Nat)
  deriving DecidableEq

/-- Total denotation of `EdAffTy`: the coordinate pair, with no infinity
    summand. -/
@[reducible] instance : TyDenote EdAffTy where
  denote
    | .aff p => ZMod p × ZMod p

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
  ret op := match op with
    | .edAdd p _ => .aff p
    | .edDbl p _ => .aff p
    | .edNeg p => .aff p

/-! ## 6. Op denotation

Each denotation is a total function on coordinate pairs. `edAdd` is the unified
schedule with no case split; `edDbl` is that schedule at equal arguments. -/

instance edAffDenote : DialectDenote edAffDialect where
  denote op := match op with
    | .edAdd _ C => fun args => edAddF C args.head args.tail.head
    | .edDbl _ C => fun args => edDblF C args.head
    | .edNeg _ => fun args => edNegF args.head

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
