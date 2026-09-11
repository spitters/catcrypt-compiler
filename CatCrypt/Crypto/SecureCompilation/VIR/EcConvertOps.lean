/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

/-!
# EC point-representation conversion ops — first-class `convert_point_type`

A minimal **correspondence** `VIR.Dialect` whose ops are the elliptic-curve
*point-representation conversion* maps of fractalyze/prime-ir: affine → Jacobian
and Jacobian → affine.  It is the CatCrypt counterpart of prime-ir's
`elliptic_curve.convert_point_type` (`EllipticCurveOps.td`).

## Why this dialect exists (the gap it closes)

Per `PRIME_IR_OP_CORRESPONDENCE.md` (repo root, §4), CatCrypt already *moves between*
the affine and Jacobian representations — `affToPoint` embeds an affine wire
point into the abstract group, and the MSM kernels normalise Jacobian
accumulators back to affine via `Pairing/BatchInverse.lean` — but it does **not**
expose `affine ↔ jacobian` as a first-class conversion op.  The gap analysis
classified `elliptic_curve.convert_point_type` **PARTIAL** — "affine↔jacobian via
`affToPoint` + BatchInverse normalize; no generic convert op".  This dialect
**factors the two conversions as standalone ops** over the existing
`EllipticCurveDialect` coordinate carriers (`affine p = ZMod p × ZMod p`,
`jacobian p = ZMod p × ZMod p × ZMod p`), matching prime-ir's
`convert_point_type` one-for-one — WITHOUT modifying `EllipticCurveDialect`'s
`Op` set (additive only).

## The ops (`EcConvertOp`), parametric in the prime `p`

* `affineToJacobian p` — `(x, y) ↦ (x, y, 1)`.  The standard `Z = 1` embedding of
  an affine point into Jacobian coordinates `(X : Y : Z)` with `x = X/Z²`,
  `y = Y/Z³`.  (`elliptic_curve.convert_point_type`, affine → jacobian.)
* `jacobianToAffine p` — `(X, Y, Z) ↦ (X·(Z⁻¹)², Y·(Z⁻¹)³)`.  Normalise a
  Jacobian point back to affine by dividing out `Z` (the affine coordinates of
  `(X : Y : Z)`).  (`elliptic_curve.convert_point_type`, jacobian → affine.)

## Type (`EcConvertTy`)

`EcConvertTy` re-uses the existing `EllipticCurveDialect` coordinate carriers:

* `affine p`   — an affine point `(x, y)`, `⟦·⟧ = ZMod p × ZMod p`.
* `jacobian p` — a Jacobian point `(X, Y, Z)`, `⟦·⟧ = ZMod p × ZMod p × ZMod p`.

These denotations are *exactly* the `EllipticCurveDialect.ECTy.affine` /
`.jacobian` denotations, so the ops convert between the same coordinate tuples
the curve-group kernels consume — the once-for-all tie to that dialect.

## Leaf functions + round-trip agreement

* `affineToJacobianF p P = (P.1, P.2, 1)`.
* `jacobianToAffineF p J = (J.1 · (J.2.2)⁻¹^2, J.2.1 · (J.2.2)⁻¹^3)`.
* `jacobianToAffine_affineToJacobian` : `jacobianToAffine (affineToJacobian P) = P`
  — the section law (Jacobian-then-affine on the `Z = 1` embedding is the
  identity, since `1⁻¹ = 1`).  The reverse direction holds only up to the
  Jacobian equivalence `(X:Y:Z) ~ (λ²X:λ³Y:λZ)` (a Jacobian point has many
  representatives), so the *retraction* is the meaningful one — exactly prime-ir's
  semantics, where `convert_point_type` to affine picks the canonical
  representative.

## What this file supplies

The two conversions as first-class ops with a verified round-trip law. It builds
no lowering and no emit path of its own; `EcConvertToFieldLowering.lean` carries
those coordinate programs, and the batched normalisation the MSM output needs
goes through `BatchInverse` instead, since a single-point op cannot express it.

Lowering status and upstream lineage: `VIR/DIALECTS.md`.

## Pure-only + constant-time

Each conversion is a fixed schedule of field arithmetic (`affineToJacobian` is a
constant store; `jacobianToAffine` is one field inverse plus two multiplies — the
inverse is the data-oblivious `fInv`/`byInverse` schedule, never a
data-dependent branch).  So each op's denotation is a total pure function and it
is constant-time by construction (`ctSafe = true`), exactly the
`EllipticCurveDialect` group-law CT story.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EcConvertOps

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

/-! ## 1. The leaf functions (the denotation targets)

Each is a total function between the `EllipticCurveDialect` coordinate carriers
`ZMod p × ZMod p` (affine) and `ZMod p × ZMod p × ZMod p` (Jacobian). -/

/-- `convert_point_type` affine → Jacobian leaf: the `Z = 1` embedding
    `(x, y) ↦ (x, y, 1)`.  In Jacobian coordinates `(X : Y : Z)` the affine point
    is `(X/Z², Y/Z³)`, so `Z = 1` recovers `(x, y)`. -/
@[reducible] def affineToJacobianF (p : Nat) (P : ZMod p × ZMod p) :
    ZMod p × ZMod p × ZMod p :=
  (P.1, P.2, 1)

/-- `convert_point_type` Jacobian → affine leaf: normalise `(X, Y, Z)` by dividing
    out `Z`, giving the affine point `(X·(Z⁻¹)², Y·(Z⁻¹)³)`. -/
@[reducible] def jacobianToAffineF (p : Nat) (J : ZMod p × ZMod p × ZMod p) :
    ZMod p × ZMod p :=
  (J.1 * (J.2.2)⁻¹ ^ 2, J.2.1 * (J.2.2)⁻¹ ^ 3)

/-! ## 2. Round-trip agreement (the section law)

`jacobianToAffine ∘ affineToJacobian = id`: normalising the `Z = 1` embedding
recovers the affine point (since `1⁻¹ = 1`).  This is the meaningful retraction —
a Jacobian point has many representatives `(λ²X : λ³Y : λZ)`, so only the
affine-canonical direction is a strict identity. -/

/-- **Section law.** Embedding an affine point into Jacobian coordinates
    (`Z = 1`) and normalising back recovers the original affine point. -/
theorem jacobianToAffine_affineToJacobian {p : Nat} (P : ZMod p × ZMod p) :
    jacobianToAffineF p (affineToJacobianF p P) = P := by
  simp [jacobianToAffineF]

/-! ## 3. Type (`EcConvertTy`)

The operand types re-use the existing `EllipticCurveDialect` coordinate
carriers. -/

/-- The conversion dialect's value-type alphabet: the affine and Jacobian
    coordinate carriers of `EllipticCurveDialect`. -/
inductive EcConvertTy where
  /-- An affine point `(x, y)`, `⟦·⟧ = ZMod p × ZMod p`. -/
  | affine (p : Nat)
  /-- A Jacobian point `(X, Y, Z)`, `⟦·⟧ = ZMod p × ZMod p × ZMod p`. -/
  | jacobian (p : Nat)
  deriving DecidableEq

/-- Total denotation of `EcConvertTy`: the affine/Jacobian coordinate tuples,
    matching `EllipticCurveDialect.ECTy.affine` / `.jacobian`. -/
@[reducible] instance : TyDenote EcConvertTy where
  denote
    | .affine p => ZMod p × ZMod p
    | .jacobian p => ZMod p × ZMod p × ZMod p

/-! ## 4. Op tags (`EcConvertOp`) -/

/-- Operation tags for the conversion dialect — prime-ir's
    `elliptic_curve.convert_point_type` in its two directions. -/
inductive EcConvertOp where
  /-- `convert_point_type` affine → Jacobian: `(x, y) ↦ (x, y, 1)`. -/
  | affineToJacobian (p : Nat)
  /-- `convert_point_type` Jacobian → affine: `(X, Y, Z) ↦ (X·(Z⁻¹)², Y·(Z⁻¹)³)`. -/
  | jacobianToAffine (p : Nat)
  deriving DecidableEq

/-! ## 5. The dialect -/

/-- The point-conversion dialect: `Op` is `EcConvertOp`, `Ty` is `EcConvertTy`. -/
@[reducible] def ecConvertDialect : Dialect :=
  { Op := EcConvertOp, Ty := EcConvertTy }

/-! ## 6. Op signatures (arg types + return type) -/

instance : DialectSignature ecConvertDialect where
  sig op := match op with
    | .affineToJacobian p => [.affine p]
    | .jacobianToAffine p => [.jacobian p]
  ret op := match op with
    | .affineToJacobian p => .jacobian p
    | .jacobianToAffine p => .affine p

/-! ## 7. Op denotation (into the coordinate conversions) -/

instance ecConvertDenote : DialectDenote ecConvertDialect where
  denote op := match op with
    | .affineToJacobian p => fun args => affineToJacobianF p args.head
    | .jacobianToAffine p => fun args => jacobianToAffineF p args.head

/-! ## 8. Per-op denotation / agreement facts (the once-per-op ties) -/

/-- `affineToJacobian` denotes to the `Z = 1` embedding `(x, y) ↦ (x, y, 1)`. -/
theorem affineToJacobian_denote {p : Nat} (P : ZMod p × ZMod p) :
    ecConvertDenote.denote (.affineToJacobian p) (.cons P .nil) = (P.1, P.2, 1) := rfl

/-- `jacobianToAffine` denotes to the normalisation `(X·(Z⁻¹)², Y·(Z⁻¹)³)`. -/
theorem jacobianToAffine_denote {p : Nat} (J : ZMod p × ZMod p × ZMod p) :
    ecConvertDenote.denote (.jacobianToAffine p) (.cons J .nil)
      = (J.1 * (J.2.2)⁻¹ ^ 2, J.2.1 * (J.2.2)⁻¹ ^ 3) := rfl

/-- **Round-trip at the op level.** Converting an affine point to Jacobian and
    back recovers it — the op-level lift of `jacobianToAffine_affineToJacobian`. -/
theorem convert_roundtrip {p : Nat} (P : ZMod p × ZMod p) :
    ecConvertDenote.denote (.jacobianToAffine p)
        (.cons (ecConvertDenote.denote (.affineToJacobian p) (.cons P .nil)) .nil)
      = P := by
  show jacobianToAffineF p (affineToJacobianF p P) = P
  exact jacobianToAffine_affineToJacobian P

/-! ## 9. Constant-time predicate (the dialect's CT instance)

Each conversion is a fixed schedule of field arithmetic — `affineToJacobian` is a
constant store, `jacobianToAffine` is one field inverse plus multiplies — with no
`ite` on data and no data-dependent memory index, so `ctSafe` is `true` for every
op, exactly the `EllipticCurveDialect` group-law CT story. -/

/-- Per-op CT predicate: every point-conversion op is constant-time. -/
def EcConvertOp.ctSafe : EcConvertOp → Bool
  | _ => true

@[simp] theorem EcConvertOp.ctSafe_all (op : EcConvertOp) : op.ctSafe = true := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt ecConvertDialect} {t : EcConvertTy}
    (e : Expr ecConvertDialect Γ t) : Bool :=
  e.op.ctSafe

@[simp] theorem ctSafeExpr_true {Γ : Ctxt ecConvertDialect} {t : EcConvertTy}
    (e : Expr ecConvertDialect Γ t) : ctSafeExpr e = true := rfl

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound expression
    is.  Since every op is CT, this is identically `true`. -/
def ctSafeCom {Γ : Ctxt ecConvertDialect} {t : EcConvertTy} :
    Com ecConvertDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- **CT by construction.** Every point-conversion program is constant-time. -/
theorem ctSafeCom_all {Γ : Ctxt ecConvertDialect} {t : EcConvertTy}
    (c : Com ecConvertDialect Γ t) : ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp [ctSafeCom, ctSafeExpr_true, ih]

/-! ## 10. Smoke test

A one-op `Com ecConvertDialect`: `let J = affineToJacobian P; ret J` over
`ZMod 7`.  On `P = (2, 3)` it returns `(2, 3, 1)` (the `Z = 1` embedding). -/

/-- One-op smoke program: an `affineToJacobian` over `[affine 7]`. -/
def smokeProg : Com ecConvertDialect [.affine 7] (.jacobian 7) :=
  .var (.mk (.affineToJacobian 7) rfl (.cons .here .nil))
    (.ret .here)

/-- The smoke program denotes to the `Z = 1` embedding; on `P = (2, 3)` that is
    `(2, 3, 1)`. -/
example :
    smokeProg.denote (.cons ((2, 3) : ZMod 7 × ZMod 7) .nil)
      = ((2, 3, 1) : ZMod 7 × ZMod 7 × ZMod 7) := by
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.EcConvertOps
