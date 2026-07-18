/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
import Mathlib.Data.ZMod.Basic

/-!
# EllipticCurve VIR dialect (#482-3 — the L4 algebraic layer, over Field)

The **L4** level of the PrimeIR-style layered crypto-IR stack
(`docs/dialect-restructure-plan.md`), sitting above the `Field` dialect and the
prime-field base it lowers onto:

    **EllipticCurve(L4)** → Field(L3) → ModArith(L2) → {Vector | LowCT} → {jasmin | x86}

Today every curve re-derives its group law and its MSM separately — Pasta,
Ristretto, BLS, BN254, secp256k1, P-256, Ed25519 each carry their own
chord-tangent formulas and Straus/Pippenger bucketing.  This dialect gives the
**abstract elliptic-curve group layer** one verified home, mirroring the way
`ModArithDialect` gives the residue-ring layer one home and `FieldDialect` gives
the field/extension-tower layer one home.

## The curve and its group (`ECParams`, `ECPoint`)

A short-Weierstrass curve `y² = x³ + a·x + b` over the prime field `F_p = ZMod p`
is fixed by its parameters `a b : ZMod p` (the dialect is **parametric** over the
curve via `ECParams p`).  Its group of points is

    ECPoint p := Option (ZMod p × ZMod p)

with `none` the point at infinity `O` (the identity), and `some (x, y)` an affine
point.  This is the standard model of `WeierstrassCurve.Affine`'s point set
(`mathlib`'s `WeierstrassCurve.Affine.Point`) stripped to the carrier we need for
the emitted-kernel ties; the on-curve predicate is `ECParams.onCurve`.

## Types (`ECTy`)

* `point p`    — an abstract curve-group element, `⟦·⟧ = ECPoint p`.  This is the
                 denotation target of every group op (the once-per-dialect tie).
* `affine p`   — an on-wire affine point `(x, y)`, `⟦·⟧ = ZMod p × ZMod p`
                 (no infinity; the representation the field-leaf kernels consume).
* `jacobian p` — a Jacobian projective point `(X, Y, Z)`, `⟦·⟧ =
                 ZMod p × ZMod p × ZMod p` (the inversion-free in-loop MSM
                 representation; `Z = 0` is `O`).
* `scalar p`   — a scalar `k : ZMod p` (the scalar-mul / MSM coefficient layer).

## Ops (`ECOp`)

* `padd`    — point add (the `add-2007-bl` distinct-point chord formula);
* `pdbl`    — point double (the `dbl-2009-l` tangent formula);
* `pmadd`   — mixed add (affine `Q` into Jacobian `P`, the MSM inner op);
* `psmul`   — scalar multiply `k · P`;
* `pmsm`    — multi-scalar multiply `∑ kᵢ·Pᵢ` (Straus/Pippenger);
* `pcomb`   — fixed-base comb scalar-mul (precomputed-table windows);
* `pwnaf`   — windowed-NAF scalar-mul.

Each op **denotes to the abstract group operation** on `ECPoint p` — group add,
the `n`-fold group sum, `∑ kᵢ·Pᵢ` — so the schedule (`add-2007-bl`, Pippenger
bucketing, comb tables, wNAF) is an *optimization realisation* of the abstract
spec, attached at lowering (`EllipticCurveLowering.lean`), exactly as the
Karatsuba/CIOS schedules are at `Field`/`ModArith`.

## Lowering (`EllipticCurveLowering.lean`)

A `padd`/`pdbl` lowers to a **schedule of Field-dialect ops** — the
chord-tangent slope (one `fInv` + `fMul`s) and the coordinate maps `x₃`, `y₃`
(`fMul`/`fSub`).  That lowering is proven denotation- and CT-preserving there,
mirroring `FieldLowering`'s `lower_denote_preserved` / `lower_ctSafe_preserved`.

## Pure-only + constant-time

Like `ModArithDialect` / `FieldDialect`, every EC-op denotation is a total pure
function (no memory/sampling effect).  The group-law ops (`padd`, `pdbl`,
`pmadd`) are data-oblivious — a fixed schedule of field ops — so `ctSafe` is
`true` for them.  The scalar-dependent ops (`psmul`, `pmsm`, `pcomb`, `pwnaf`)
are CT **only** when realised by a constant-time ladder / fixed-window schedule
(Montgomery ladder, fixed-window with conditional select); the dialect carries a
per-op `ctSafe` flag so a variable-time double-and-add realisation is *flagged*,
not silently accepted.  This is the L4 instance of the VIR `ctSafe` story.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-! ## 1. The abstract curve group (the denotation target)

A short-Weierstrass curve over `F_p = ZMod p` and its point group.  We model the
point set as `Option (ZMod p × ZMod p)` (`none = O`), parametric over `a b`. -/

/-- Short-Weierstrass curve parameters `y² = x³ + a·x + b` over `ZMod p`. -/
@[ext]
structure ECParams (p : Nat) where
  /-- The curve coefficient `a`. -/
  a : ZMod p
  /-- The curve coefficient `b`. -/
  b : ZMod p
  deriving DecidableEq

/-- An abstract curve-group element: `none` is the point at infinity `O`, and
    `some (x, y)` is an affine point. -/
abbrev ECPoint (p : Nat) : Type := Option (ZMod p × ZMod p)

namespace ECPoint

variable {p : Nat}

/-- The identity (point at infinity `O`). -/
def zero : ECPoint p := none

/-- The affine point `(x, y)`. -/
def aff (x y : ZMod p) : ECPoint p := some (x, y)

/-- Point negation: `−(x, y) = (x, −y)`, `−O = O`. -/
def neg (P : ECPoint p) : ECPoint p :=
  P.map (fun q => (q.1, -q.2))

@[simp] theorem neg_none : neg (none : ECPoint p) = none := rfl
@[simp] theorem neg_some (x y : ZMod p) : neg (aff x y) = aff x (-y) := rfl

end ECPoint

namespace ECParams

variable {p : Nat}

/-- The on-curve predicate `y² = x³ + a·x + b`. -/
def onCurve (C : ECParams p) (x y : ZMod p) : Prop :=
  y * y = x * x * x + C.a * x + C.b

/-- The distinct-point chord slope `λ = (y₂ − y₁)/(x₂ − x₁)`. -/
def chordSlope (_ : ECParams p) (x1 y1 x2 y2 : ZMod p) : ZMod p :=
  (y2 - y1) * (x2 - x1)⁻¹

/-- The tangent slope at `(x, y)` for doubling: `λ = (3x² + a)/(2y)`. -/
def tangentSlope (C : ECParams p) (x y : ZMod p) : ZMod p :=
  (3 * (x * x) + C.a) * (2 * y)⁻¹

/-- The short-Weierstrass affine `x₃` map: `x₃ = λ² − x₁ − x₂`. -/
def affRx (_ : ECParams p) (lam x1 x2 : ZMod p) : ZMod p := lam * lam - x1 - x2

/-- The short-Weierstrass affine `y₃` map: `y₃ = λ·(x₁ − x₃) − y₁`. -/
def affRy (_ : ECParams p) (lam x1 x3 y1 : ZMod p) : ZMod p := lam * (x1 - x3) - y1

/-- The **Miller-loop line-function value** `ℓ` (the pairing's per-step line
    through an anchor `(xA, yA)` with slope `λ`, evaluated at `(x, y)`):
    `ℓ_{λ,(xA,yA)}(x, y) = (y − yA) − λ·(x − xA)`.

    This is the affine *line* (not a coordinate map): the chord/tangent line at
    the accumulator point, evaluated at the other pairing input.  It is **pure
    base-field arithmetic over `ZMod p`** — the same `fSub`/`fMul` fragment the
    `affRx`/`affRy` coordinate maps use — so it fits the EllipticCurve→Field
    lowering exactly like the coordinate maps do.  The slope `λ` is the same
    base-field slope the group law computes (`chordSlope` at an add step,
    `tangentSlope` at a doubling step), taken as a parameter so no field inverse
    appears in the line algebra (mirroring `affRx`/`affRy`).  This is the
    abstract spec the `ECOp.line` op denotes to and the field-Com line schedule
    (`EcLineFieldEmit`) realises. -/
def lineEval (_ : ECParams p) (lam xA yA x y : ZMod p) : ZMod p :=
  (y - yA) - lam * (x - xA)

/-- **The line through `(xA, yA)` vanishes at `(xA, yA)`** (the defining algebraic
    property of a pairing line function): both coordinate differences are `0`, so
    `ℓ_{λ,(xA,yA)}(xA, yA) = (yA − yA) − λ·(xA − xA) = 0`.  The structural sanity
    check that `lineEval` is the right object. -/
@[simp] theorem lineEval_vanishes_at_anchor (C : ECParams p) (lam xA yA : ZMod p) :
    C.lineEval lam xA yA xA yA = 0 := by
  simp [lineEval]

/-- The full short-Weierstrass group add on `ECPoint`.  `O` is the identity; for
    two distinct affine points it is the chord formula; for `P = Q` the tangent
    (doubling) formula; for `Q = −P` the result is `O`.  This is the **abstract
    group operation** every EC group op denotes to. -/
def add (C : ECParams p) (P Q : ECPoint p) : ECPoint p :=
  match P, Q with
  | none, _ => Q
  | _, none => P
  | some (x1, y1), some (x2, y2) =>
    if x1 = x2 then
      -- vertical line: either doubling (y1 = y2 ≠ 0) or P = −Q (→ O).
      if y1 = -y2 then none
      else
        let lam := C.tangentSlope x1 y1
        let x3 := C.affRx lam x1 x2
        some (x3, C.affRy lam x1 x3 y1)
    else
      let lam := C.chordSlope x1 y1 x2 y2
      let x3 := C.affRx lam x1 x2
      some (x3, C.affRy lam x1 x3 y1)

/-- The `n`-fold group sum of a list of points (`scalar-mul` is the special case
    of a single repeated point; `MSM` is the sum of `kᵢ·Pᵢ`). -/
def sum (C : ECParams p) (Ps : List (ECPoint p)) : ECPoint p :=
  Ps.foldl (C.add) ECPoint.zero

/-- Scalar multiply `k · P` (abstract): the `k`-fold group sum of `P` with
    itself.  This is the spec the double-and-add / ladder / comb / wNAF
    schedules all realise. -/
def smul (C : ECParams p) (k : Nat) (P : ECPoint p) : ECPoint p :=
  (List.replicate k P).foldl (C.add) ECPoint.zero

/-- Multi-scalar multiply `∑ᵢ kᵢ·Pᵢ` (abstract): the group sum of the
    per-term scalar multiples.  Straus/Pippenger bucketing realises exactly
    this value. -/
def msm (C : ECParams p) (terms : List (Nat × ECPoint p)) : ECPoint p :=
  C.sum (terms.map (fun t => C.smul t.1 t.2))

@[simp] theorem add_none_left (C : ECParams p) (Q : ECPoint p) : C.add none Q = Q := rfl
@[simp] theorem add_none_right (C : ECParams p) (P : ECPoint p) : C.add P none = P := by
  cases P <;> rfl

@[simp] theorem smul_zero (C : ECParams p) (P : ECPoint p) : C.smul 0 P = ECPoint.zero := rfl

@[simp] theorem sum_nil (C : ECParams p) : C.sum [] = ECPoint.zero := rfl

end ECParams

/-! ## 1b. The abstract TWISTED-EDWARDS curve group (the second denotation target)

Short-Weierstrass is not the only curve model the L4 layer must cover:
Ed25519/Ristretto/zkgroup live on a **twisted-Edwards** curve
`a·x² + y² = 1 + d·x²·y²` over `F_p`, whose group law is the *unified complete
addition law* — **not** the Weierstrass chord/tangent.  We add it as a parallel
parameter+group-law alongside `ECParams`, reusing the *same* `ECPoint p` carrier
(`some (x, y)`, the affine point; the Edwards identity is `(0, 1)`), so the
existing `point p` type and all the dialect plumbing are shared. -/

/-- Twisted-Edwards curve parameters `a·x² + y² = 1 + d·x²·y²` over `ZMod p`. -/
@[ext]
structure EdwardsParams (p : Nat) where
  /-- The curve coefficient `a` (`a = −1` for Ed25519). -/
  a : ZMod p
  /-- The curve coefficient `d` (`d = −121665/121666` for Ed25519). -/
  d : ZMod p
  deriving DecidableEq

namespace EdwardsParams

variable {p : Nat}

/-- The twisted-Edwards on-curve predicate `a·x² + y² = 1 + d·x²·y²`. -/
def onCurve (C : EdwardsParams p) (x y : ZMod p) : Prop :=
  C.a * (x * x) + y * y = 1 + C.d * (x * x) * (y * y)

/-- The unified-addition common product `t = d·x₁·x₂·y₁·y₂` (the two
    denominators are `1 ± t`). -/
def addT (C : EdwardsParams p) (x1 y1 x2 y2 : ZMod p) : ZMod p :=
  C.d * x1 * x2 * y1 * y2

/-- The `x₃`-numerator `x₁·y₂ + y₁·x₂`. -/
def addXNum (_ : EdwardsParams p) (x1 y1 x2 y2 : ZMod p) : ZMod p :=
  x1 * y2 + y1 * x2

/-- The `y₃`-numerator `y₁·y₂ − a·x₁·x₂`. -/
def addYNum (C : EdwardsParams p) (x1 y1 x2 y2 : ZMod p) : ZMod p :=
  y1 * y2 - C.a * (x1 * x2)

/-- The unified-addition `x₃` coordinate map:
    `x₃ = (x₁·y₂ + y₁·x₂) · (1 + t)⁻¹`, `t = d·x₁·x₂·y₁·y₂`. -/
def affRx (C : EdwardsParams p) (x1 y1 x2 y2 : ZMod p) : ZMod p :=
  C.addXNum x1 y1 x2 y2 * (1 + C.addT x1 y1 x2 y2)⁻¹

/-- The unified-addition `y₃` coordinate map:
    `y₃ = (y₁·y₂ − a·x₁·x₂) · (1 − t)⁻¹`, `t = d·x₁·x₂·y₁·y₂`. -/
def affRy (C : EdwardsParams p) (x1 y1 x2 y2 : ZMod p) : ZMod p :=
  C.addYNum x1 y1 x2 y2 * (1 - C.addT x1 y1 x2 y2)⁻¹

/-- The complete twisted-Edwards affine group add on `ECPoint`.  The Edwards law
    is **unified** — the same formula adds, doubles, and handles the identity
    `(0, 1)` — so there is no branch (unlike the Weierstrass `ECParams.add`).
    `none` (`O`) is kept as a formal identity element so the carrier matches the
    Weierstrass one.  This is the **abstract group operation** every twisted-
    Edwards group op denotes to. -/
def add (C : EdwardsParams p) (P Q : ECPoint p) : ECPoint p :=
  match P, Q with
  | none, _ => Q
  | _, none => P
  | some (x1, y1), some (x2, y2) =>
    some (C.affRx x1 y1 x2 y2, C.affRy x1 y1 x2 y2)

/-- Scalar multiply `k · P` (abstract): the `k`-fold group sum.  Realised by the
    Ed25519 double-and-add ladder. -/
def smul (C : EdwardsParams p) (k : Nat) (P : ECPoint p) : ECPoint p :=
  (List.replicate k P).foldl (C.add) ECPoint.zero

@[simp] theorem add_none_left (C : EdwardsParams p) (Q : ECPoint p) : C.add none Q = Q := rfl
@[simp] theorem add_none_right (C : EdwardsParams p) (P : ECPoint p) : C.add P none = P := by
  cases P <;> rfl

@[simp] theorem smul_zero (C : EdwardsParams p) (P : ECPoint p) :
    C.smul 0 P = ECPoint.zero := rfl

/-- The Edwards add on two affine points is the coordinate-wise unified law. -/
@[simp] theorem add_aff (C : EdwardsParams p) (x1 y1 x2 y2 : ZMod p) :
    C.add (ECPoint.aff x1 y1) (ECPoint.aff x2 y2)
      = ECPoint.aff (C.affRx x1 y1 x2 y2) (C.affRy x1 y1 x2 y2) := rfl

end EdwardsParams

/-! ## 2. Types (`ECTy`) -/

/-- The EllipticCurve dialect's value-type alphabet.  The modulus `p` lives in
    every type, so a pass mixing two curves' base fields is ill-typed.  The
    curve parameters `a b` are carried at the *ops*, not the types (a single
    `point p` type carries every short-Weierstrass curve over `F_p`). -/
inductive ECTy where
  /-- An abstract curve-group element, `⟦·⟧ = ECPoint p`. -/
  | point (p : Nat)
  /-- An on-wire affine point `(x, y)`, `⟦·⟧ = ZMod p × ZMod p`. -/
  | affine (p : Nat)
  /-- A Jacobian projective point `(X, Y, Z)`, `⟦·⟧ = ZMod p × ZMod p × ZMod p`. -/
  | jacobian (p : Nat)
  /-- A scalar `k : ZMod p` (the scalar-mul / MSM coefficient). -/
  | scalar (p : Nat)
  deriving DecidableEq

/-- Total denotation of `ECTy`: the abstract group element, the affine/Jacobian
    coordinate tuples, and the scalar. -/
@[reducible] instance : TyDenote ECTy where
  denote
    | .point p => ECPoint p
    | .affine p => ZMod p × ZMod p
    | .jacobian p => ZMod p × ZMod p × ZMod p
    | .scalar p => ZMod p

/-! ## 3. Concrete leaf functions

The group leaves are the abstract `ECParams` operations (so a `padd` *is* the
abstract group add, the lowering tie is a direct equality).  The coordinate-
conversion leaves move between the abstract `point` and the on-wire
`affine`/`jacobian` representations. -/

/-- Group add `P + Q` (the abstract `ECParams.add`). -/
@[reducible] def paddF {p : Nat} (C : ECParams p) (P Q : ECPoint p) : ECPoint p :=
  C.add P Q

/-- Group double `2·P` (the abstract group add of `P` with itself). -/
@[reducible] def pdblF {p : Nat} (C : ECParams p) (P : ECPoint p) : ECPoint p :=
  C.add P P

/-- Group negate `−P`. -/
@[reducible] def pnegF {p : Nat} (P : ECPoint p) : ECPoint p := ECPoint.neg P

/-- Mixed add: an affine point `Q = (x, y)` into the curve element `P`
    (`P + (x, y)`). -/
@[reducible] def pmaddF {p : Nat} (C : ECParams p) (P : ECPoint p) (Q : ZMod p × ZMod p) :
    ECPoint p :=
  C.add P (ECPoint.aff Q.1 Q.2)

/-- Scalar multiply `k · P` (abstract; `k` read as a `Nat` representative). -/
@[reducible] def psmulF {p : Nat} (C : ECParams p) (k : ZMod p) (P : ECPoint p) :
    ECPoint p :=
  C.smul k.val P

/-- Embed an affine point into the abstract group. -/
@[reducible] def affToPointF {p : Nat} (Q : ZMod p × ZMod p) : ECPoint p :=
  ECPoint.aff Q.1 Q.2

/-- The Miller-loop **line-function value** `ℓ_{λ,(xA,yA)}(x, y)` (the abstract
    `ECParams.lineEval`): the chord/tangent line at the accumulator anchor,
    evaluated at the other pairing input.  Pure base-field arithmetic; the
    pairing per-step value the Miller loop accumulates. -/
@[reducible] def lineF {p : Nat} (C : ECParams p)
    (lam xA yA x y : ZMod p) : ZMod p :=
  C.lineEval lam xA yA x y

/-- Twisted-Edwards group add `P + Q` (the abstract `EdwardsParams.add`, the
    unified complete addition law). -/
@[reducible] def edPaddF {p : Nat} (C : EdwardsParams p) (P Q : ECPoint p) : ECPoint p :=
  C.add P Q

/-- Twisted-Edwards group double `2·P = P + P` (the unified law at `P = Q`). -/
@[reducible] def edPdblF {p : Nat} (C : EdwardsParams p) (P : ECPoint p) : ECPoint p :=
  C.add P P

/-- Twisted-Edwards scalar multiply `k · P` (abstract; `k` read as a `Nat`
    representative). -/
@[reducible] def edPsmulF {p : Nat} (C : EdwardsParams p) (k : ZMod p) (P : ECPoint p) :
    ECPoint p :=
  C.smul k.val P

/-! ## 4. Op tags -/

/-- Operation tags for the EllipticCurve dialect.  The group-law ops (`padd`,
    `pdbl`, `pmadd`, `pneg`) carry the curve parameters `C : ECParams p`; the
    scalar-dependent ops (`psmul`, `pmsm`, `pcomb`, `pwnaf`) additionally carry a
    `ct : Bool` flag recording whether their realisation is a constant-time
    ladder/fixed-window schedule. -/
inductive ECOp where
  /-- Point add `P + Q : point p` (the `add-2007-bl` distinct-point chord). -/
  | padd (p : Nat) (C : ECParams p)
  /-- Point double `2·P : point p` (the `dbl-2009-l` tangent). -/
  | pdbl (p : Nat) (C : ECParams p)
  /-- Point negate `−P : point p`. -/
  | pneg (p : Nat)
  /-- Mixed add: affine `Q` into `P`, `P + Q : point p`. -/
  | pmadd (p : Nat) (C : ECParams p)
  /-- Embed an affine wire point into the abstract group. -/
  | affToPoint (p : Nat)
  /-- The Miller-loop **line function** `ℓ_{λ,(xA,yA)}(x, y) : scalar p`
      (the pairing per-step line value, `ECParams.lineEval`).  Inputs (all
      `scalar p`): the precomputed slope `λ`, the anchor `(xA, yA)`, and the
      evaluation point `(x, y)`.  Data-oblivious pure field arithmetic (the
      `add-2007-bl`/`dbl-2009-l` line of the doubling-and-add Miller loop), so
      always CT.  This is the abstract group/pairing op that lowers to the
      field-Com line schedule (`EcLineFieldEmit`), exactly as `padd`/`pdbl`
      lower to their coordinate schedules. -/
  | line (p : Nat) (C : ECParams p)
  /-- Scalar multiply `k · P : point p`.  `ct = true` records a CT ladder /
      fixed-window realisation. -/
  | psmul (p : Nat) (C : ECParams p) (ct : Bool)
  /-- Fixed-base comb scalar-mul `k · G : point p` (precomputed-table windows;
      `ct = true` for the constant-time conditional-select variant). -/
  | pcomb (p : Nat) (C : ECParams p) (ct : Bool)
  /-- Windowed-NAF scalar-mul `k · P : point p`. -/
  | pwnaf (p : Nat) (C : ECParams p) (ct : Bool)
  /-- **Twisted-Edwards** point add `P + Q : point p` (the unified complete
      addition law over `EdwardsParams`, NOT the Weierstrass chord). -/
  | edPadd (p : Nat) (C : EdwardsParams p)
  /-- **Twisted-Edwards** point double `2·P : point p` (the unified law at
      `P = Q`; no separate tangent chain). -/
  | edPdbl (p : Nat) (C : EdwardsParams p)
  /-- **Twisted-Edwards** scalar multiply `k · P : point p`.  `ct = true` records
      a fixed-trip double-and-add ladder realisation. -/
  | edPsmul (p : Nat) (C : EdwardsParams p) (ct : Bool)
  deriving DecidableEq

/-! ## 5. The dialect -/

/-- The EllipticCurve dialect: `Op` is `ECOp`, `Ty` is `ECTy`. -/
@[reducible] def ecDialect : Dialect :=
  { Op := ECOp, Ty := ECTy }

/-! ## 6. Op signatures (arg types + return type) -/

instance : DialectSignature ecDialect where
  sig op := match op with
    | .padd p _ => [.point p, .point p]
    | .pdbl p _ => [.point p]
    | .pneg p => [.point p]
    | .pmadd p _ => [.point p, .affine p]
    | .affToPoint p => [.affine p]
    | .line p _ => [.scalar p, .scalar p, .scalar p, .scalar p, .scalar p]
    | .psmul p _ _ => [.scalar p, .point p]
    | .pcomb p _ _ => [.scalar p, .point p]
    | .pwnaf p _ _ => [.scalar p, .point p]
    | .edPadd p _ => [.point p, .point p]
    | .edPdbl p _ => [.point p]
    | .edPsmul p _ _ => [.scalar p, .point p]
  ret op := match op with
    | .padd p _ => .point p
    | .pdbl p _ => .point p
    | .pneg p => .point p
    | .pmadd p _ => .point p
    | .affToPoint p => .point p
    | .line p _ => .scalar p
    | .psmul p _ _ => .point p
    | .pcomb p _ _ => .point p
    | .pwnaf p _ _ => .point p
    | .edPadd p _ => .point p
    | .edPdbl p _ => .point p
    | .edPsmul p _ _ => .point p

/-! ## 7. Op denotation — every group op into the abstract `ECPoint` group -/

instance ecDenote : DialectDenote ecDialect where
  denote op := match op with
    | .padd _ C => fun args => paddF C args.head args.tail.head
    | .pdbl _ C => fun args => pdblF C args.head
    | .pneg _ => fun args => pnegF args.head
    | .pmadd _ C => fun args => pmaddF C args.head args.tail.head
    | .affToPoint _ => fun args => affToPointF args.head
    | .line _ C => fun args =>
        lineF C args.head args.tail.head args.tail.tail.head
          args.tail.tail.tail.head args.tail.tail.tail.tail.head
    | .psmul _ C _ => fun args => psmulF C args.head args.tail.head
    | .pcomb _ C _ => fun args => psmulF C args.head args.tail.head
    | .pwnaf _ C _ => fun args => psmulF C args.head args.tail.head
    | .edPadd _ C => fun args => edPaddF C args.head args.tail.head
    | .edPdbl _ C => fun args => edPdblF C args.head
    | .edPsmul _ C _ => fun args => edPsmulF C args.head args.tail.head

/-! ## 8. Constant-time predicate (L4 instance of `CTPredicate.lean`)

The group-law ops (`padd`, `pdbl`, `pmadd`, `pneg`, `affToPoint`) are
data-oblivious — a fixed schedule of field ops, no data-dependent branch — so
they are CT by construction.  The scalar-dependent ops (`psmul`, `pcomb`,
`pwnaf`) are CT **iff** their `ct` flag is set (a Montgomery-ladder /
fixed-window realisation with conditional select); a variable-time
double-and-add (`ct = false`) is flagged, not silently accepted.  This is the L4
contribution: the dialect makes the scalar-mul CT obligation *explicit* in the
op alphabet. -/

/-- Per-op CT predicate.  Group-law ops are always CT; scalar-dependent ops are
    CT iff their `ct` flag is set. -/
def ECOp.ctSafe : ECOp → Bool
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

@[simp] theorem ECOp.ctSafe_padd {p : Nat} (C : ECParams p) : (ECOp.padd p C).ctSafe = true := rfl
@[simp] theorem ECOp.ctSafe_pdbl {p : Nat} (C : ECParams p) : (ECOp.pdbl p C).ctSafe = true := rfl
@[simp] theorem ECOp.ctSafe_pmadd {p : Nat} (C : ECParams p) : (ECOp.pmadd p C).ctSafe = true := rfl
@[simp] theorem ECOp.ctSafe_line {p : Nat} (C : ECParams p) : (ECOp.line p C).ctSafe = true := rfl
@[simp] theorem ECOp.ctSafe_edPadd {p : Nat} (C : EdwardsParams p) :
    (ECOp.edPadd p C).ctSafe = true := rfl
@[simp] theorem ECOp.ctSafe_edPdbl {p : Nat} (C : EdwardsParams p) :
    (ECOp.edPdbl p C).ctSafe = true := rfl
/-- **CT inheritance: the twisted-Edwards fixed-trip ladder is CT.** A CT-flagged
    `edPsmul` (the fixed-trip double-and-add ladder) is admitted as CT — the L4
    obligation the Ed25519/Ristretto scalar-mul discharges. -/
@[simp] theorem ECOp.ctSafe_edPsmul {p : Nat} (C : EdwardsParams p) :
    (ECOp.edPsmul p C true).ctSafe = true := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt ecDialect} {t : ECTy}
    (e : Expr ecDialect Γ t) : Bool :=
  e.op.ctSafe

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound expression
    is.  A program built only of group-law ops (and CT-flagged scalar ops) is
    CT-safe. -/
def ctSafeCom {Γ : Ctxt ecDialect} {t : ECTy} :
    Com ecDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- A group-law program (only `padd`/`pdbl`/`pmadd`/`pneg`/`affToPoint` lets) is
    CT-safe.  The scalar-dependent ops must carry `ct = true` to be admitted; the
    `ctSafeCom` predicate enforces exactly that. -/
theorem ctSafeCom_grouplaw {Γ : Ctxt ecDialect} {t : ECTy}
    (c : Com ecDialect Γ t)
    (h : ∀ {Γ' : Ctxt ecDialect} {t' : ECTy} (e : Expr ecDialect Γ' t'),
          e.op.ctSafe = true) :
    ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp only [ctSafeCom, ctSafeExpr, h e, ih, Bool.and_self]

/-- Propositional form, decidable. -/
def ctSafePropCom {Γ : Ctxt ecDialect} {t : ECTy}
    (c : Com ecDialect Γ t) : Prop :=
  ctSafeCom c = true

instance {Γ : Ctxt ecDialect} {t : ECTy}
    (c : Com ecDialect Γ t) : Decidable (ctSafePropCom c) := by
  unfold ctSafePropCom; infer_instance

/-! ## 9. Algebraic denotation facts (the once-per-dialect ties)

These hold **definitionally** because the op denotations are the abstract
`ECParams` group operations.  Stated once at the dialect, not re-proved per
migrated curve. -/

/-- `padd` denotes to the abstract group add `P + Q`. -/
theorem padd_denote {p : Nat} (C : ECParams p) (P Q : ECPoint p) :
    ecDenote.denote (.padd p C) (.cons P (.cons Q .nil)) = C.add P Q := rfl

/-- `pdbl` denotes to the abstract group double `P + P`. -/
theorem pdbl_denote {p : Nat} (C : ECParams p) (P : ECPoint p) :
    ecDenote.denote (.pdbl p C) (.cons P .nil) = C.add P P := rfl

/-- `pneg` denotes to the abstract group negate `−P`. -/
theorem pneg_denote {p : Nat} (P : ECPoint p) :
    ecDenote.denote (.pneg p) (.cons P .nil) = ECPoint.neg P := rfl

/-- `pmadd` denotes to the abstract group add of `P` with the embedded affine
    point `Q`. -/
theorem pmadd_denote {p : Nat} (C : ECParams p) (P : ECPoint p) (Q : ZMod p × ZMod p) :
    ecDenote.denote (.pmadd p C) (.cons P (.cons Q .nil))
      = C.add P (ECPoint.aff Q.1 Q.2) := rfl

/-- `line` denotes to the abstract Miller-loop line-function value
    `ℓ_{λ,(xA,yA)}(x, y) = (y − yA) − λ·(x − xA)` (`ECParams.lineEval`). -/
theorem line_denote {p : Nat} (C : ECParams p) (lam xA yA x y : ZMod p) :
    ecDenote.denote (.line p C)
        (.cons lam (.cons xA (.cons yA (.cons x (.cons y .nil)))))
      = C.lineEval lam xA yA x y := rfl

/-- `psmul` denotes to the abstract scalar multiply `k · P`. -/
theorem psmul_denote {p : Nat} (C : ECParams p) (ct : Bool) (k : ZMod p) (P : ECPoint p) :
    ecDenote.denote (.psmul p C ct) (.cons k (.cons P .nil)) = C.smul k.val P := rfl

/-- `pwnaf` denotes to the abstract scalar multiply `k · P` — the wNAF/GLV
    schedule is an optimization realisation of this spec (the secp256k1
    realisation is `EcPwnafGlvRealization.pwnaf_ct_realized_glvWnaf`, backed by
    the verified `GlvWnafScalarMul` schedule). -/
theorem pwnaf_denote {p : Nat} (C : ECParams p) (ct : Bool) (k : ZMod p) (P : ECPoint p) :
    ecDenote.denote (.pwnaf p C ct) (.cons k (.cons P .nil)) = C.smul k.val P := rfl

/-- `pcomb` denotes to the abstract scalar multiply `k · P` — the fixed-base
    comb table schedule is an optimization realisation of this spec. -/
theorem pcomb_denote {p : Nat} (C : ECParams p) (ct : Bool) (k : ZMod p) (P : ECPoint p) :
    ecDenote.denote (.pcomb p C ct) (.cons k (.cons P .nil)) = C.smul k.val P := rfl

/-- `edPadd` denotes to the abstract twisted-Edwards group add `P + Q`. -/
theorem edPadd_denote {p : Nat} (C : EdwardsParams p) (P Q : ECPoint p) :
    ecDenote.denote (.edPadd p C) (.cons P (.cons Q .nil)) = C.add P Q := rfl

/-- `edPdbl` denotes to the abstract twisted-Edwards group double `P + P`. -/
theorem edPdbl_denote {p : Nat} (C : EdwardsParams p) (P : ECPoint p) :
    ecDenote.denote (.edPdbl p C) (.cons P .nil) = C.add P P := rfl

/-- `edPsmul` denotes to the abstract twisted-Edwards scalar multiply `k · P`. -/
theorem edPsmul_denote {p : Nat} (C : EdwardsParams p) (ct : Bool) (k : ZMod p) (P : ECPoint p) :
    ecDenote.denote (.edPsmul p C ct) (.cons k (.cons P .nil)) = C.smul k.val P := rfl

/-! ## 10. Smoke test

A two-op `Com ecDialect` over a tiny curve `y² = x³ + x + 6` over `ZMod 7`:
`let R = padd P Q; ret R`.  We check `padd O P = P` (the identity law) — purely
structural, no modulus arithmetic. -/

/-- The tiny test curve `y² = x³ + x + 6` over `ZMod 7` (`a = 1`, `b = 6`). -/
def smokeCurve : ECParams 7 := ⟨1, 6⟩

/-- Two-op smoke program: one `padd` over `[point 7, point 7]`. -/
def smokeProg : Com ecDialect [.point 7, .point 7] (.point 7) :=
  .var (.mk (.padd 7 smokeCurve) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The smoke program denotes to the group add; on `P = O, Q = (2, 3)` the
    identity law gives `O + (2,3) = (2,3)`. -/
example :
    smokeProg.denote
        (.cons (ECPoint.zero : ECPoint 7) (.cons (ECPoint.aff 2 3) .nil))
      = ECPoint.aff 2 3 := by
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
