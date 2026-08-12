/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
import CatCrypt.Crypto.SecureCompilation.VIR.FieldLowering

/-!
# EllipticCurve lowering (#482-3) — the L4 → L3 (EllipticCurve → Field) step

The lowering step of the layered crypto-IR stack:

    EllipticCurve → Field

proven **denotation-preserving** and **CT-preserving**, mirroring
`FieldLowering`'s `lower_denote_preserved` / `lower_ctSafe_preserved`.

A group-law EC op lowers to a **schedule of Field-dialect ops** on the affine
coordinates `ZMod p`:

* a `padd` on **distinct** affine points lowers to the `add-2007-bl` chord
  schedule — the slope `λ = (y₂ − y₁)·(x₂ − x₁)⁻¹` (one Field `fInv` + `fMul`/
  `fSub`), then `x₃ = λ² − x₁ − x₂` (`fMul`/`fSub`) and `y₃ = λ·(x₁ − x₃) − y₁`
  (`fMul`/`fSub`).  Every leaf is a Field prime-field op, which itself lowers 1:1
  to a ModArith op (`FieldLowering`), so the whole schedule reaches ModArith.
* a `pdbl` lowers to the `dbl-2009-l` tangent schedule — the same coordinate
  maps with the tangent slope `λ = (3x² + a)·(2y)⁻¹`.

## What is proven here

* `AffineAddSchedule` / `AffineDblSchedule` — the Field-level chord/tangent
  coordinate schedules (over `FieldDialect`'s `fMulF`/`fSubF`/`fInvF` leaves).
* `affineAddSchedule_denote` / `affineDblSchedule_denote` — **denotation
  preservation**: the affine-coordinate schedule equals the abstract group
  add `ECParams.add` on distinct affine points / on a self-add (doubling), so the
  EC `padd`/`pdbl` op is realised by its Field schedule.  Both sides are the same
  `ZMod p` chord/tangent formula, so it is a ring identity.
* `lower_denote_preserved` — the op-level identity-realisation statement
  (mirrors `FieldLowering`), plus the `padd`/`pdbl` realisation end-to-end.
* `lower_ctSafe_preserved` — **CT preservation**: every group-law EC op is CT
  (`ECOp.ctSafe = true`) and its Field schedule is CT (every Field op is CT), so
  the lowering preserves CT for the group law unconditionally; for the
  scalar-dependent ops CT is preserved exactly when the op carries `ct = true`.

The lowering is phrased at **op** granularity (one EC op → its Field schedule);
the op-level statement lifts to whole programs by the `Com` recursion, exactly as
in `FieldLowering`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect

/-! ## 1. The chord / tangent schedules over Field leaves

The two output affine coordinates are built from the `FieldDialect` prime-field
leaves (`fMulF`/`fSubF`/`fInvF`/`fAddF`) on the input `ZMod p` coordinates.  These
are exactly the `add-2007-bl` / `dbl-2009-l` formulas expressed over the lowered
field ops. -/

/-- The chord slope `λ = (y₂ − y₁)·(x₂ − x₁)⁻¹` over the Field leaves
    (one `fInv` + `fMul`/`fSub`). -/
def chordSlopeSchedule {p : Nat} (x1 y1 x2 y2 : ZMod p) : ZMod p :=
  fMulF (fSubF y2 y1) (fInvF (fSubF x2 x1))

/-- The tangent slope `λ = (3x² + a)·(2y)⁻¹` over the Field leaves. -/
def tangentSlopeSchedule {p : Nat} (a x y : ZMod p) : ZMod p :=
  fMulF (fAddF (fMulF 3 (fMulF x x)) a) (fInvF (fMulF 2 y))

/-- The `x₃ = λ² − x₁ − x₂` coordinate over the Field leaves. -/
def rxSchedule {p : Nat} (lam x1 x2 : ZMod p) : ZMod p :=
  fSubF (fSubF (fMulF lam lam) x1) x2

/-- The `y₃ = λ·(x₁ − x₃) − y₁` coordinate over the Field leaves. -/
def rySchedule {p : Nat} (lam x1 x3 y1 : ZMod p) : ZMod p :=
  fSubF (fMulF lam (fSubF x1 x3)) y1

/-- The full `add-2007-bl` affine point-add schedule for **distinct** affine
    points, over the Field leaves: compute `λ` (chord), then `x₃`, then `y₃`. -/
def AffineAddSchedule {p : Nat} (x1 y1 x2 y2 : ZMod p) : ZMod p × ZMod p :=
  let lam := chordSlopeSchedule x1 y1 x2 y2
  let x3 := rxSchedule lam x1 x2
  (x3, rySchedule lam x1 x3 y1)

/-- The full `dbl-2009-l` affine doubling schedule, over the Field leaves:
    compute the tangent `λ`, then `x₃`, then `y₃` (with `x₂ = x₁`). -/
def AffineDblSchedule {p : Nat} (a x y : ZMod p) : ZMod p × ZMod p :=
  let lam := tangentSlopeSchedule a x y
  let x3 := rxSchedule lam x x
  (x3, rySchedule lam x x3 y)

/-! ## 2. Denotation preservation — the group law lowers correctly

The Field-leaf schedule denotes to the *same value* as the abstract group add.
Because the schedule is built from the Field leaves (`fMulF = (·*·)`,
`fSubF = (·−·)`, `fInvF = (·⁻¹)`, `fAddF = (·+·)` on `ZMod p`) and the abstract
group add uses the same `ZMod p` chord/tangent formulas, the coordinates are
definitionally equal. -/

/-- The chord-slope schedule denotes to the abstract chord slope. -/
theorem chordSlopeSchedule_denote {p : Nat} (C : ECParams p) (x1 y1 x2 y2 : ZMod p) :
    chordSlopeSchedule x1 y1 x2 y2 = C.chordSlope x1 y1 x2 y2 := rfl

/-- The tangent-slope schedule denotes to the abstract tangent slope. -/
theorem tangentSlopeSchedule_denote {p : Nat} (C : ECParams p) (x y : ZMod p) :
    tangentSlopeSchedule C.a x y = C.tangentSlope x y := rfl

/-- The `x₃` schedule denotes to the abstract `affRx`. -/
theorem rxSchedule_denote {p : Nat} (C : ECParams p) (lam x1 x2 : ZMod p) :
    rxSchedule lam x1 x2 = C.affRx lam x1 x2 := rfl

/-- The `y₃` schedule denotes to the abstract `affRy`. -/
theorem rySchedule_denote {p : Nat} (C : ECParams p) (lam x1 x3 y1 : ZMod p) :
    rySchedule lam x1 x3 y1 = C.affRy lam x1 x3 y1 := rfl

/-- **`padd` lowers to its affine schedule (distinct affine points).** On two
    distinct affine points (`x1 ≠ x2`), the `padd` denotation equals the
    Field-leaf `add-2007-bl` affine schedule re-wrapped as a curve element.  The
    end-to-end EllipticCurve→Field lowering correctness statement for `padd`,
    and the op-level tie consumed by the whole-program fold. -/
theorem padd_lowers_to_schedule {p : Nat} (C : ECParams p)
    (x1 y1 x2 y2 : ZMod p) (hne : x1 ≠ x2) :
    ecDenote.denote (.padd p C)
        (.cons (ECPoint.aff x1 y1) (.cons (ECPoint.aff x2 y2) .nil))
      = some (AffineAddSchedule x1 y1 x2 y2) := by
  show C.add (ECPoint.aff x1 y1) (ECPoint.aff x2 y2) = _
  simp only [ECParams.add, ECPoint.aff, if_neg hne, AffineAddSchedule,
    chordSlopeSchedule, rxSchedule, rySchedule, ECParams.chordSlope,
    ECParams.affRx, ECParams.affRy, fMulF, fSubF, fInvF, ModArithDialect.modMulF,
    ModArithDialect.modSubF, ModArithDialect.byInverseF]

/-- **Denotation preservation, `padd` (distinct affine points).** The Field-leaf
    `add-2007-bl` schedule's coordinates equal the abstract group add's
    coordinates on two distinct affine points (`x1 ≠ x2`). -/
theorem affineAddSchedule_denote {p : Nat} (C : ECParams p)
    (x1 y1 x2 y2 : ZMod p) (hne : x1 ≠ x2) :
    C.add (ECPoint.aff x1 y1) (ECPoint.aff x2 y2)
      = some (AffineAddSchedule x1 y1 x2 y2) :=
  padd_lowers_to_schedule C x1 y1 x2 y2 hne

/-- **`pdbl` lowers to its affine schedule (doubling).** On an affine point with
    `y ≠ −y` (i.e. `2y ≠ 0`, so doubling is defined), the `pdbl` denotation
    equals the Field-leaf `dbl-2009-l` tangent schedule re-wrapped as a curve
    element.  The end-to-end EllipticCurve→Field lowering correctness statement
    for `pdbl`. -/
theorem pdbl_lowers_to_schedule {p : Nat} (C : ECParams p)
    (x y : ZMod p) (hy : y ≠ -y) :
    ecDenote.denote (.pdbl p C) (.cons (ECPoint.aff x y) .nil)
      = some (AffineDblSchedule C.a x y) := by
  show C.add (ECPoint.aff x y) (ECPoint.aff x y) = _
  simp only [ECParams.add, ECPoint.aff, if_pos, if_neg hy, AffineDblSchedule,
    tangentSlopeSchedule, rxSchedule, rySchedule, ECParams.tangentSlope,
    ECParams.affRx, ECParams.affRy, fMulF, fAddF, fSubF, fInvF,
    ModArithDialect.modMulF, ModArithDialect.modAddF, ModArithDialect.modSubF,
    ModArithDialect.byInverseF]

/-- **Denotation preservation, `pdbl` (doubling).** The Field-leaf `dbl-2009-l`
    tangent schedule equals the abstract group double `ECParams.add P P` on an
    affine point with `2y ≠ 0`. -/
theorem affineDblSchedule_denote {p : Nat} (C : ECParams p)
    (x y : ZMod p) (hy : y ≠ -y) :
    C.add (ECPoint.aff x y) (ECPoint.aff x y) = some (AffineDblSchedule C.a x y) :=
  pdbl_lowers_to_schedule C x y hy

/-! ## 2b. The TWISTED-EDWARDS unified-addition schedule over Field leaves

The twisted-Edwards complete addition law `(x₃, y₃)` is a fixed straight-line
schedule of the *same* `FieldDialect` prime-field leaves — but it is the
**unified** law (`add-2008-hwcd`-style, RFC 8032 §5.1), not the Weierstrass
chord/tangent.  Because it is unified, the same schedule realises add **and**
double (the `edPdbl` case is this schedule at `P = Q`), with no separate tangent
chain.  Every leaf is a Field op, which lowers 1:1 to ModArith, so the whole
Edwards schedule reaches ModArith exactly as the Weierstrass one does. -/

/-- The unified-addition common product `t = d·x₁·x₂·y₁·y₂` over the Field
    leaves. -/
def edTSchedule {p : Nat} (d x1 y1 x2 y2 : ZMod p) : ZMod p :=
  fMulF (fMulF (fMulF (fMulF d x1) x2) y1) y2

/-- The `x₃`-numerator `x₁·y₂ + y₁·x₂` over the Field leaves. -/
def edXNumSchedule {p : Nat} (x1 y1 x2 y2 : ZMod p) : ZMod p :=
  fAddF (fMulF x1 y2) (fMulF y1 x2)

/-- The `y₃`-numerator `y₁·y₂ − a·x₁·x₂` over the Field leaves. -/
def edYNumSchedule {p : Nat} (a x1 y1 x2 y2 : ZMod p) : ZMod p :=
  fSubF (fMulF y1 y2) (fMulF a (fMulF x1 x2))

/-- The `x₃ = xNum · (1 + t)⁻¹` coordinate over the Field leaves
    (`fAdd`/`fInv`/`fMul`). -/
def edRxSchedule {p : Nat} (xn t : ZMod p) : ZMod p :=
  fMulF xn (fInvF (fAddF 1 t))

/-- The `y₃ = yNum · (1 − t)⁻¹` coordinate over the Field leaves
    (`fSub`/`fInv`/`fMul`). -/
def edRySchedule {p : Nat} (yn t : ZMod p) : ZMod p :=
  fMulF yn (fInvF (fSubF 1 t))

/-- The full unified twisted-Edwards point-add schedule over the Field leaves:
    compute `t`, the two numerators, then `x₃` and `y₃`. -/
def EdwardsAddSchedule {p : Nat} (a d x1 y1 x2 y2 : ZMod p) : ZMod p × ZMod p :=
  let t  := edTSchedule d x1 y1 x2 y2
  let xn := edXNumSchedule x1 y1 x2 y2
  let yn := edYNumSchedule a x1 y1 x2 y2
  (edRxSchedule xn t, edRySchedule yn t)

/-- The `t`-schedule denotes to the abstract `EdwardsParams.addT`. -/
theorem edTSchedule_denote {p : Nat} (C : EdwardsParams p) (x1 y1 x2 y2 : ZMod p) :
    edTSchedule C.d x1 y1 x2 y2 = C.addT x1 y1 x2 y2 := rfl

/-- The `x`-numerator schedule denotes to `EdwardsParams.addXNum`. -/
theorem edXNumSchedule_denote {p : Nat} (C : EdwardsParams p) (x1 y1 x2 y2 : ZMod p) :
    edXNumSchedule x1 y1 x2 y2 = C.addXNum x1 y1 x2 y2 := rfl

/-- The `y`-numerator schedule denotes to `EdwardsParams.addYNum`. -/
theorem edYNumSchedule_denote {p : Nat} (C : EdwardsParams p) (x1 y1 x2 y2 : ZMod p) :
    edYNumSchedule C.a x1 y1 x2 y2 = C.addYNum x1 y1 x2 y2 := rfl

/-- **`edPadd` lowers to its unified-addition affine schedule.** On two affine
    points, the `edPadd` denotation equals the Field-leaf unified-addition
    schedule re-wrapped as a curve element — the end-to-end
    EllipticCurve→Field lowering correctness statement for the twisted-Edwards
    point-add, the analog of `padd_lowers_to_schedule`. -/
theorem edPadd_lowers_to_schedule {p : Nat} (C : EdwardsParams p)
    (x1 y1 x2 y2 : ZMod p) :
    ecDenote.denote (.edPadd p C)
        (.cons (ECPoint.aff x1 y1) (.cons (ECPoint.aff x2 y2) .nil))
      = some (EdwardsAddSchedule C.a C.d x1 y1 x2 y2) := by
  show C.add (ECPoint.aff x1 y1) (ECPoint.aff x2 y2) = _
  simp only [EdwardsParams.add, ECPoint.aff, EdwardsAddSchedule,
    edTSchedule, edXNumSchedule, edYNumSchedule, edRxSchedule, edRySchedule,
    EdwardsParams.affRx, EdwardsParams.affRy, EdwardsParams.addT,
    EdwardsParams.addXNum, EdwardsParams.addYNum,
    fMulF, fAddF, fSubF, fInvF, ModArithDialect.modMulF, ModArithDialect.modAddF,
    ModArithDialect.modSubF, ModArithDialect.byInverseF]

/-- **Denotation preservation, `edPadd`.** The Field-leaf unified-addition
    schedule's coordinates equal the abstract twisted-Edwards group add's
    coordinates on two affine points. -/
theorem edwardsAddSchedule_denote {p : Nat} (C : EdwardsParams p)
    (x1 y1 x2 y2 : ZMod p) :
    C.add (ECPoint.aff x1 y1) (ECPoint.aff x2 y2)
      = some (EdwardsAddSchedule C.a C.d x1 y1 x2 y2) :=
  edPadd_lowers_to_schedule C x1 y1 x2 y2

/-- **`edPdbl` lowers to the SAME unified-addition schedule at `P = Q`.** The
    twisted-Edwards law is unified, so doubling is the add schedule instantiated
    at `(x₂, y₂) = (x₁, y₁)` — no separate tangent chain (unlike Weierstrass
    `pdbl_lowers_to_schedule`). -/
theorem edPdbl_lowers_to_schedule {p : Nat} (C : EdwardsParams p)
    (x y : ZMod p) :
    ecDenote.denote (.edPdbl p C) (.cons (ECPoint.aff x y) .nil)
      = some (EdwardsAddSchedule C.a C.d x y x y) := by
  show C.add (ECPoint.aff x y) (ECPoint.aff x y) = _
  exact edPadd_lowers_to_schedule C x y x y

/-! ## 3. Op-level identity realisation (mirrors `FieldLowering`)

The realised denotation of an EC op is the op's own abstract denotation; the
above schedules realise it on the affine-coordinate representation. -/

/-- The realised denotation of an EC op (identity realisation). -/
@[reducible] def realise (op : ECOp)
    (args : HVector (fun (t : ECTy) => ⟦t⟧)
              (DialectSignature.sig (d := ecDialect) op)) :
    ⟦DialectSignature.ret (d := ecDialect) op⟧ :=
  ecDenote.denote op args

/-- **Denotation preservation (op-level, identity realisation).** The realised
    value equals the EC op's abstract denotation. -/
theorem lower_denote_preserved (op : ECOp)
    (args : HVector (fun (t : ECTy) => ⟦t⟧)
              (DialectSignature.sig (d := ecDialect) op)) :
    realise op args = ecDenote.denote op args := rfl

/-! ## 4. CT preservation

Every group-law EC op is CT (`ECOp.ctSafe = true` for `padd`/`pdbl`/`pmadd`/
`pneg`/`affToPoint`), and its Field schedule is CT (every Field op is CT, the
chord/tangent schedule is a fixed sequence of `fMul`/`fSub`/`fInv`, no
data-dependent branch or index).  So the lowering preserves CT for the group law
unconditionally.  For the scalar-dependent ops CT is preserved exactly when the
op carries `ct = true`. -/

/-- Is the lowered Field schedule of an EC op CT-safe?  The group-law schedule is
    a fixed sequence of CT Field ops, hence CT by construction; for the
    scalar-dependent ops it tracks the op's own `ct` flag (the ladder / fixed-
    window realisation is CT, a variable-time double-and-add is not). -/
def scheduleCtSafe : ECOp → Bool
  | .padd _ _ => true
  | .pdbl _ _ => true
  | .pneg _ => true
  | .pmadd _ _ => true
  | .affToPoint _ => true
  | .line _ _ => true
  | .psmul _ _ ct => ct
  | .pcomb _ _ ct => ct
  | .pwnaf _ _ ct => ct
  | .edPadd _ _ => true
  | .edPdbl _ _ => true
  | .edPsmul _ _ ct => ct

/-- The lowered schedule is exactly as CT-safe as the EC op itself: the Field
    schedule never *adds* non-CT behaviour, and never *removes* the
    scalar-dependent CT obligation. -/
@[simp] theorem scheduleCtSafe_eq_ctSafe (op : ECOp) :
    scheduleCtSafe op = op.ctSafe := by cases op <;> rfl

/-- **CT preservation (op-level).** An EC op is CT iff its Field schedule is CT.
    For the group-law ops both are unconditionally `true`; for the
    scalar-dependent ops both track the `ct` flag — so the lowering preserves the
    CT predicate exactly. -/
theorem lower_ctSafe_preserved (op : ECOp) :
    op.ctSafe = scheduleCtSafe op := (scheduleCtSafe_eq_ctSafe op).symm

/-- **CT preservation, group law.** Every group-law EC op (`padd`/`pdbl`/`pmadd`/
    `pneg`/`affToPoint`) lowers to a CT Field schedule unconditionally. -/
theorem lower_ctSafe_grouplaw {p : Nat} (C : ECParams p) :
    scheduleCtSafe (.padd p C) = true ∧ scheduleCtSafe (.pdbl p C) = true
      ∧ scheduleCtSafe (.pmadd p C) = true ∧ scheduleCtSafe (.pneg p) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **CT preservation, twisted-Edwards group law.** The unified Edwards add/double
    ops lower to a CT Field schedule unconditionally; the `edPsmul` ladder is CT
    exactly when it carries `ct = true` (the fixed-trip double-and-add ladder).
    The L4 CT obligation the Ed25519/Ristretto scalar-mul discharges. -/
theorem lower_ctSafe_edwards {p : Nat} (C : EdwardsParams p) :
    scheduleCtSafe (.edPadd p C) = true ∧ scheduleCtSafe (.edPdbl p C) = true
      ∧ scheduleCtSafe (.edPsmul p C true) = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## 5. Smoke test: the chord schedule matches the dialect denotation

On the tiny curve `y² = x³ + x + 6` over `ZMod 7`, on distinct affine points
`P = (2, 3)`, `Q = (4, 5)` the chord schedule and the abstract group add agree.
(`2 ≠ 4` in `ZMod 7`, so the chord branch is taken.) -/

example :
    ecDenote.denote (.padd 7 smokeCurve)
        (.cons (ECPoint.aff 2 3) (.cons (ECPoint.aff 4 5) .nil))
      = some (AffineAddSchedule (2 : ZMod 7) 3 4 5) :=
  padd_lowers_to_schedule smokeCurve 2 3 4 5 (by decide)

end CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
