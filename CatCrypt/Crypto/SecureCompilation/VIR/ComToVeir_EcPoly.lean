/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Veir.IR.Basic
import all Veir.IR.Attribute
public import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeir_ModArithField
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldEcCmpOps
public import CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.TensorExtDialect

/-!
# `ecDialect`, `cmpDialect`, `polyDialect` and `tensorExtDialect` → VeIR's prime-ir forms

The lowering of our elliptic-curve, comparison, polynomial and tensor dialects to
VeIR's prime-ir `elliptic_curve`, `field`, `ring` and `tensor_ext` dialects.

A point type prints as `!elliptic_curve.<repr><#elliptic_curve.sw<a, b, (Gx, Gy)> : F>`
(or `#elliptic_curve.te<a, d, (Gx, Gy)>`), with the curve, the base-field
representation and the point representation read from an `ECReprMap`. The side
conditions, checked over the whole program before lowering, reject a modulus without
a curve, a curve without a generator (the attribute requires one), a generator off
its curve, a point representation of the other curve form, and an op whose curve
differs from the one the map fixes. The Miller line has no VeIR operation and is
rejected.

A polynomial type prints as `!ring.rq<[q], n : i32, iW>`, with `, eval` in the
evaluation domain. `ring.mul` is defined on the evaluation domain only, so the
coefficient-domain product `nttMul` lowers as the transform of both operands, the
pointwise `ring.mul` and the inverse transform. prime-ir has no NTT operation; the
transforms and the scalar action lower to `catcrypt.unknown` carrying the discardable
attribute `catcrypt.ntt`, `catcrypt.intt` or `catcrypt.poly_smul = c : iW`, and the
scalar action by `−1` is `ring.negate`.

The constant-time flag of a scalar multiplication and the public-data flag of a
comparison print as the discardable attributes `catcrypt.ct` and
`catcrypt.public_data`.

## Main definitions

* `AlgebraicPrintCtx.withCurves`: the print context with the base-field
  representations of the curves of an `ECReprMap`.
* `curveAttr`, `pointTyOf`: the curve attribute and the point type of a descriptor.
* `generatorOnCurveB`, `checkCurveAt`: the decidable side conditions on a curve.
* `ecToVeirOp`, `ecToVeirTy`, `cmpToVeirOp`, `cmpToVeirTy`, `polyToVeirOp`,
  `polyToVeirTy`, `tensorExtToVeirOp`, `tensorExtToVeirTy`: the lowerings.
* `ecModule`, `ecModuleAt`, `cmpModule`, `polyModule`, `tensorExtModule`: the checked
  `builtin.module` of a program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComToVeirAlgebraic

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldEcCmpOps
open CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TensorExtDialect

/-- The discardable unit attribute `key`. -/
def unitAttrEntry (key : String) : ByteArray × Veir.Attribute :=
  (key.toUTF8, .unitAttr Veir.UnitAttr.mk)

/-! ## Curves and point types -/

/-- The base-field representation of the curve `σ` fixes over each modulus, and the
    unfixed representation where `σ` fixes no curve. -/
def ecBaseRepr (σ : ECReprMap) : ModArithDialect.ModArithReprMap :=
  fun p => ((σ p).curve.map (·.baseRepr)).getD {}

/-- The print context with the base-field widths and Montgomery flags of the curves
    of `σ`, and those of `pc` for the moduli without a curve. -/
def AlgebraicPrintCtx.withCurves (pc : AlgebraicPrintCtx) (σ : ECReprMap) :
    AlgebraicPrintCtx :=
  pc.withRepr (ecBaseRepr σ)

/-- VeIR's curve form. -/
def CurveForm.toVeir : CurveForm → Veir.EllipticCurveForm
  | .sw => .sw
  | .te => .te

/-- VeIR's point representation. -/
def PointRepr.toVeir : PointRepr → Veir.EllipticCurvePointRepr
  | .affine => .affine
  | .jacobian => .jacobian
  | .xyzz => .xyzz
  | .edAffine => .edAffine
  | .edExtended => .edExtended

/-- The field attribute `x : iw` of a base-field element, in standard form. -/
def fieldElemAttr {p : Nat} (w : Nat) (x : ZMod p) : Veir.Attribute :=
  .integerAttr (intAttr x.val w)

/-- The attribute `#elliptic_curve.sw<a, b, (Gx, Gy)> : !field.pf<p : iW>` of a
    short-Weierstrass descriptor, `#elliptic_curve.te<a, d, (Gx, Gy)> : …` of a
    twisted-Edwards one. A descriptor without a generator prints `(0, 0)`; the side
    condition `checkCurveAt` rejects it before lowering. -/
def curveAttr (pc : AlgebraicPrintCtx) {p : Nat} (D : CurveDesc p) : Veir.Attribute :=
  let w := pc.width p
  let g := D.generator.getD (0, 0)
  .ellipticCurveAttr
    { form := CurveForm.toVeir D.form
      baseField := (primeFieldTy p w (pc.mont p)).val
      a := fieldElemAttr w D.a
      b := fieldElemAttr w D.b
      gx := fieldElemAttr w g.1
      gy := fieldElemAttr w g.2 }

/-- The point type `!elliptic_curve.<q><#curve>` over the curve of `r`. Where `r` fixes
    no curve the curve attribute is `i0`; `checkCurveAt` rejects that case. -/
def pointTyOf (pc : AlgebraicPrintCtx) {p : Nat} (r : ECRepr p) (q : PointRepr) :
    Veir.TypeAttr :=
  ({ repr := PointRepr.toVeir q
     curve :=
       match r.curve with
       | some D => curveAttr pc D
       | none => .integerType (Veir.IntegerType.signless 0) } : Veir.EllipticCurvePointType)

/-! ## Side conditions on curves -/

/-- Whether the generator of `D`, where it has one, satisfies the curve equation of its
    form. -/
def generatorOnCurveB {p : Nat} (D : CurveDesc p) : Bool :=
  match D.generator with
  | none => true
  | some (x, y) =>
    match D.form with
    | .sw => decide (y * y = x * x * x + D.a * x + D.b)
    | .te => decide (D.a * (x * x) + y * y = 1 + D.b * (x * x) * (y * y))

/-- The Boolean check decides `CurveDesc.GeneratorOnCurve`. -/
theorem generatorOnCurve_of_generatorOnCurveB {p : Nat} (D : CurveDesc p)
    (h : generatorOnCurveB D = true) : D.GeneratorOnCurve := by
  obtain ⟨form, a, b, r, gen⟩ := D
  intro g hg
  cases hg
  obtain ⟨x, y⟩ := g
  cases form <;>
    simpa [generatorOnCurveB, CurveDesc.toECParams, CurveDesc.toEdwardsParams,
      ECParams.onCurve, EdwardsParams.onCurve] using h

/-- The curve over `p` is printable: `σ` fixes a curve over `p` with a generator on the
    curve, and the point representation of `point p` belongs to the curve's form. -/
def curvePrintable (σ : ECReprMap) (p : Nat) : Bool :=
  match (σ p).curve with
  | none => false
  | some D =>
      D.generator.isSome && generatorOnCurveB D && ((σ p).pointRepr.form == D.form)

/-- The curve `σ` fixes over `p`, when the width of the print context holds `p`, the
    curve has a generator on it, and the point representation belongs to its form. -/
def checkCurveAt (pc : AlgebraicPrintCtx) (σ : ECReprMap) (p : Nat) :
    Except String (CurveDesc p) :=
  match (σ p).curve with
  | none => .error s!"the representation map fixes no curve over {p}"
  | some D => do
      pc.checkModulus p
      require D.generator.isSome
        (s!"the curve over {p} has no generator, which " ++
          s!"#elliptic_curve.{(CurveForm.toVeir D.form).mnemonic} requires")
      require (generatorOnCurveB D) s!"the generator of the curve over {p} is not on the curve"
      require ((σ p).pointRepr.form == D.form)
        (s!"the point representation {(σ p).pointRepr.primeIrName} does not belong to " ++
          s!"the curve over {p}")
      pure D

/-- The check that `σ` fixes the short-Weierstrass curve `C` over `p`, printable. -/
def checkSwCurve (pc : AlgebraicPrintCtx) (σ : ECReprMap) (p : Nat) (C : ECParams p) :
    Except String Unit := do
  let D ← checkCurveAt pc σ p
  require (D.form == .sw && D.a == C.a && D.b == C.b)
    s!"the op's short-Weierstrass curve over {p} is not the curve of the representation map"

/-- The check that `σ` fixes the twisted-Edwards curve `C` over `p`, printable. -/
def checkTeCurve (pc : AlgebraicPrintCtx) (σ : ECReprMap) (p : Nat) (C : EdwardsParams p) :
    Except String Unit := do
  let D ← checkCurveAt pc σ p
  require (D.form == .te && D.a == C.a && D.b == C.d)
    s!"the op's twisted-Edwards curve over {p} is not the curve of the representation map"

/-! ## `ecDialect` -/

/-- The VeIR type of an `ECTy` under the print context and the representation map:
    `point p` in the representation `σ p` gives, `affine p` and `jacobian p` in theirs,
    and a scalar as the base field `!field.pf<p : iW>`. -/
def ECTy.toVeirTyIn (pc : AlgebraicPrintCtx) (σ : ECReprMap) : ECTy → Veir.TypeAttr
  | .point p => pointTyOf pc (σ p) (σ p).pointRepr
  | .affine p => pointTyOf pc (σ p) .affine
  | .jacobian p => pointTyOf pc (σ p) .jacobian
  | .scalar p => primeFieldTy p (pc.width p) (pc.mont p)

/-- The check of an `ECTy`: a point type needs a printable curve, `affine` and
    `jacobian` a short-Weierstrass one, and a scalar a modulus the width holds. -/
def ECTy.checkIn (pc : AlgebraicPrintCtx) (σ : ECReprMap) : ECTy → Except String Unit
  | .point p => discard (checkCurveAt pc σ p)
  | .affine p | .jacobian p => do
      let D ← checkCurveAt pc σ p
      require (D.form == .sw)
        s!"affine and Jacobian points over {p} need a short-Weierstrass curve"
  | .scalar p => pc.checkModulus p

/-- The VeIR op-code of an `ECOp`. The Miller line, rejected by `ECOp.checkIn`, maps
    to `catcrypt.unknown`. -/
def ECOp.toVeirOpCode : ECOp → Veir.OpCode
  | .padd _ _ | .pmadd _ _ | .edPadd _ _ => .elliptic_curve .add
  | .pdbl _ _ | .edPdbl _ _ => .elliptic_curve .double
  | .pneg _ => .elliptic_curve .negate
  | .affToPoint _ => .elliptic_curve .convert_point_type
  | .psmul _ _ _ | .pcomb _ _ _ | .pwnaf _ _ _ | .edPsmul _ _ _ => .elliptic_curve .scalar_mul
  | .line _ _ => .catcrypt .unknown

/-- The properties of the operation of an `ECOp`: the default ones. -/
def ECOp.propsIn (o : ECOp) : Veir.propertiesOf (ECOp.toVeirOpCode o) := default

/-- The discardable attributes of an `ECOp`: `catcrypt.ct` on a scalar multiplication
    whose constant-time flag is set. -/
def ECOp.attrsIn : ECOp → Array (ByteArray × Veir.Attribute)
  | .psmul _ _ true | .pcomb _ _ true | .pwnaf _ _ true | .edPsmul _ _ true =>
      #[unitAttrEntry "catcrypt.ct"]
  | _ => #[]

/-- The expansions of `ecDialect`: `affToPoint p` is an alias where `point p` is
    represented in affine coordinates. -/
def ECOp.expandIn (σ : ECReprMap) : ECOp → Option (VeirExpansion Veir.OpCode)
  | .affToPoint p =>
      if (σ p).pointRepr = .affine then some { steps := [], value := .arg 0 } else none
  | _ => none

/-- The side conditions of an `ECOp`: the curve it carries is the printable curve `σ`
    fixes over its modulus, and the op has a VeIR form. -/
def ECOp.checkIn (pc : AlgebraicPrintCtx) (σ : ECReprMap) : ECOp → Except String Unit
  | .padd p C | .pdbl p C | .pmadd p C => checkSwCurve pc σ p C
  | .psmul p C _ | .pcomb p C _ | .pwnaf p C _ => checkSwCurve pc σ p C
  | .edPadd p C | .edPdbl p C => checkTeCurve pc σ p C
  | .edPsmul p C _ => checkTeCurve pc σ p C
  | .pneg p | .affToPoint p => discard (checkCurveAt pc σ p)
  | .line _ _ => .error "the Miller line has no VeIR operation"

/-- The lowering of `ecDialect` under the representation map `σ`. -/
@[reducible] def ecToVeirOp (σ : ECReprMap) : ToVeirOp ecDialect where
  Op := Veir.OpCode
  hasOpInfo := inferInstance
  toOp := ECOp.toVeirOpCode
  defaultProps := ECOp.propsIn
  attrsOf := ECOp.attrsIn
  expand? := ECOp.expandIn σ

/-- The types of `ecDialect` under a print context and the representation map `σ`. -/
@[reducible] def ecToVeirTy (pc : AlgebraicPrintCtx) (σ : ECReprMap) : ToVeirTy ecDialect where
  toTy := ECTy.toVeirTyIn pc σ

/-! ## `cmpDialect` -/

/-- The predicate `eq`, `0 : i64`, of `field.cmp` and `elliptic_curve.cmp`. -/
def eqPredicate : Veir.CmpPredicateProperties := { predicate := intAttr 0 64 }

/-- The VeIR type of a `CmpTy`: the base field, the point type `σ p` gives, and `i1`. -/
def CmpTy.toVeirTyIn (pc : AlgebraicPrintCtx) (σ : ECReprMap) : CmpTy → Veir.TypeAttr
  | .fp p => primeFieldTy p (pc.width p) (pc.mont p)
  | .point p => pointTyOf pc (σ p) (σ p).pointRepr
  | .bool => intTy 1

/-- The check of a `CmpTy` against the print context and the representation map. -/
def CmpTy.checkIn (pc : AlgebraicPrintCtx) (σ : ECReprMap) : CmpTy → Except String Unit
  | .fp p => pc.checkModulus p
  | .point p => discard (checkCurveAt pc σ p)
  | .bool => .ok ()

/-- The VeIR op-code of a `CmpOp`; `fieldIsZero` lowers through an expansion. -/
def CmpOp.toVeirOpCode : CmpOp → Veir.OpCode
  | .fieldEq _ _ => .field .cmp
  | .fieldIsZero _ _ => .field .cmp
  | .ecIsZero _ _ => .elliptic_curve .is_zero
  | .ecEq _ _ => .elliptic_curve .cmp

/-- The properties of the operation of a `CmpOp`: the predicate `eq` of the
    comparisons. -/
def CmpOp.propsIn (o : CmpOp) : Veir.propertiesOf (CmpOp.toVeirOpCode o) :=
  match o with
  | .fieldEq _ _ => eqPredicate
  | .fieldIsZero _ _ => eqPredicate
  | .ecIsZero _ _ => default
  | .ecEq _ _ => eqPredicate

/-- The discardable attributes of a `CmpOp`: `catcrypt.public_data` where its operands
    are public. -/
def CmpOp.attrsIn : CmpOp → Array (ByteArray × Veir.Attribute)
  | .fieldEq _ true | .fieldIsZero _ true | .ecIsZero _ true | .ecEq _ true =>
      #[unitAttrEntry "catcrypt.public_data"]
  | _ => #[]

/-- The expansions of `cmpDialect`: `fieldIsZero` is `field.constant 0` and
    `field.cmp eq`. -/
def CmpOp.expandIn (pc : AlgebraicPrintCtx) : CmpOp → Option (VeirExpansion Veir.OpCode)
  | .fieldIsZero p pd =>
      let w := pc.width p
      some
        { steps :=
            [ { op := .field .constant,
                props := ({ value := .integerAttr (intAttr 0 w) } : Veir.FieldConstantProperties),
                operands := [], results := [some (primeFieldTy p w (pc.mont p))] },
              { op := .field .cmp, props := eqPredicate,
                attrs := CmpOp.attrsIn (.fieldIsZero p pd),
                operands := [.arg 0, .res 0 0], results := [none] } ]
          value := .res 1 0 }
  | _ => none

/-- The side conditions of a `CmpOp`: the modulus fits the width, and a point
    comparison has a printable curve. -/
def CmpOp.checkIn (pc : AlgebraicPrintCtx) (σ : ECReprMap) : CmpOp → Except String Unit
  | .fieldEq p _ | .fieldIsZero p _ => pc.checkModulus p
  | .ecIsZero p _ | .ecEq p _ => discard (checkCurveAt pc σ p)

/-- The lowering of `cmpDialect` under a print context. -/
@[reducible] def cmpToVeirOp (pc : AlgebraicPrintCtx) : ToVeirOp cmpDialect where
  Op := Veir.OpCode
  hasOpInfo := inferInstance
  toOp := CmpOp.toVeirOpCode
  defaultProps := CmpOp.propsIn
  attrsOf := CmpOp.attrsIn
  expand? := CmpOp.expandIn pc

/-- The types of `cmpDialect` under a print context and the representation map `σ`. -/
@[reducible] def cmpToVeirTy (pc : AlgebraicPrintCtx) (σ : ECReprMap) :
    ToVeirTy cmpDialect where
  toTy := CmpTy.toVeirTyIn pc σ

/-! ## `polyDialect` -/

/-- `!ring.rq<[q], n : i32, iw>`, with `, eval` in the evaluation domain. -/
def rqTy (q n w : Nat) (eval : Bool) : Veir.TypeAttr :=
  ({ moduli := #[(q : Int)], ringDegree := intAttr n 32, storageType := Veir.IntegerType.signless w,
     domain := if eval then .eval else .coeff } : Veir.RqType)

/-- The VeIR type of a `PolyTy`: the coefficient or evaluation domain of `!ring.rq`. -/
def PolyTy.toVeirTyIn (pc : AlgebraicPrintCtx) : PolyTy → Veir.TypeAttr
  | .polyC q n => rqTy q n (pc.width q) false
  | .polyN q n => rqTy q n (pc.width q) true

/-- The check of a `PolyTy`: the width holds the modulus and the degree is positive. -/
def PolyTy.checkIn (pc : AlgebraicPrintCtx) : PolyTy → Except String Unit
  | .polyC q n | .polyN q n => do
      pc.checkModulus q
      require (0 < n) "zero ring degree"

/-- The VeIR op-code of a `PolyOp`. The transforms, the coefficient-domain product and
    a scalar action other than `−1` map to `catcrypt.unknown`; the product lowers
    through an expansion. -/
def PolyOp.toVeirOpCode : PolyOp → Veir.OpCode
  | .polyAdd _ _ => .ring .add
  | .polySub _ _ => .ring .sub
  | .basemul _ _ => .ring .mul
  | .polySMul _ _ c => if c = -1 then .ring .negate else .catcrypt .unknown
  | .ntt _ _ => .catcrypt .unknown
  | .intt _ _ => .catcrypt .unknown
  | .nttMul _ _ => .catcrypt .unknown

/-- The properties of the operation of a `PolyOp`: the default ones. -/
def PolyOp.propsIn (o : PolyOp) : Veir.propertiesOf (PolyOp.toVeirOpCode o) := default

/-- The discardable attributes of a `PolyOp`: the name of a transform, and the scalar
    `c : iW` of a scalar action other than `−1`. -/
def PolyOp.attrsIn (pc : AlgebraicPrintCtx) : PolyOp → Array (ByteArray × Veir.Attribute)
  | .ntt _ _ => #[unitAttrEntry "catcrypt.ntt"]
  | .intt _ _ => #[unitAttrEntry "catcrypt.intt"]
  | .polySMul q _ c =>
      if c = -1 then #[]
      else #[("catcrypt.poly_smul".toUTF8, .integerAttr (intAttr c.val (pc.width q)))]
  | _ => #[]

/-- The expansions of `polyDialect`: `nttMul` is the transform of both operands, the
    pointwise `ring.mul` in the evaluation domain and the inverse transform. -/
def PolyOp.expandIn (pc : AlgebraicPrintCtx) : PolyOp → Option (VeirExpansion Veir.OpCode)
  | .nttMul q n =>
      let ev := rqTy q n (pc.width q) true
      some
        { steps :=
            [ { op := .catcrypt .unknown, props := (), attrs := #[unitAttrEntry "catcrypt.ntt"],
                operands := [.arg 0], results := [some ev] },
              { op := .catcrypt .unknown, props := (), attrs := #[unitAttrEntry "catcrypt.ntt"],
                operands := [.arg 1], results := [some ev] },
              { op := .ring .mul, props := (), operands := [.res 0 0, .res 1 0],
                results := [some ev] },
              { op := .catcrypt .unknown, props := (),
                attrs := #[unitAttrEntry "catcrypt.intt"],
                operands := [.res 2 0], results := [none] } ]
          value := .res 3 0 }
  | _ => none

/-- The side conditions of a `PolyOp`: the width holds the modulus. -/
def PolyOp.checkIn (pc : AlgebraicPrintCtx) : PolyOp → Except String Unit
  | .ntt q _ | .intt q _ | .basemul q _ | .polyAdd q _ | .polySub q _ | .nttMul q _ =>
      pc.checkModulus q
  | .polySMul q _ _ => pc.checkModulus q

/-- The lowering of `polyDialect` under a print context. -/
@[reducible] def polyToVeirOp (pc : AlgebraicPrintCtx) : ToVeirOp polyDialect where
  Op := Veir.OpCode
  hasOpInfo := inferInstance
  toOp := PolyOp.toVeirOpCode
  defaultProps := PolyOp.propsIn
  attrsOf := PolyOp.attrsIn pc
  expand? := PolyOp.expandIn pc

/-- The types of `polyDialect` under a print context. -/
@[reducible] def polyToVeirTy (pc : AlgebraicPrintCtx) : ToVeirTy polyDialect where
  toTy := PolyTy.toVeirTyIn pc

/-! ## `tensorExtDialect` -/

/-- The VeIR type of a `TensorExtTy`: `tensor<2^k x i64>`. -/
def TensorExtTy.toVeirTy : TensorExtTy → Veir.TypeAttr
  | .tensor k => tensorTy (2 ^ k) (intTy 64)

/-- The dimension `0 : i64` of `tensor_ext.bit_reverse`. -/
def bitReverseDim0 : Veir.TensorExtBitReverseProperties := { dimension := intAttr 0 64 }

/-- The VeIR op-code of a `TensorExtOp`. -/
def TensorExtOp.toVeirOpCode : TensorExtOp → Veir.OpCode
  | .bitReverse _ => .tensor_ext .bit_reverse

/-- The properties of the operation of a `TensorExtOp`: dimension `0`. -/
def TensorExtOp.propsIn (o : TensorExtOp) : Veir.propertiesOf (TensorExtOp.toVeirOpCode o) :=
  match o with
  | .bitReverse _ => bitReverseDim0

/-- The expansion of `bitReverse k`: `tensor_ext.bit_reverse(x, x)`, the source doubling
    as the destination. -/
def TensorExtOp.expand : TensorExtOp → Option (VeirExpansion Veir.OpCode)
  | .bitReverse _ =>
      some
        { steps :=
            [ { op := .tensor_ext .bit_reverse, props := bitReverseDim0,
                operands := [.arg 0, .arg 0], results := [none] } ]
          value := .res 0 0 }

/-- The lowering of `tensorExtDialect`. -/
@[reducible] def tensorExtToVeirOp : ToVeirOp tensorExtDialect where
  Op := Veir.OpCode
  hasOpInfo := inferInstance
  toOp := TensorExtOp.toVeirOpCode
  defaultProps := TensorExtOp.propsIn
  expand? := TensorExtOp.expand

/-- The types of `tensorExtDialect`. -/
@[reducible] def tensorExtToVeirTy : ToVeirTy tensorExtDialect where
  toTy := TensorExtTy.toVeirTy

/-! ## Modules -/

/-- The `builtin.module` holding `func.func @name` lowered from an `ecDialect` program
    over the curves of `σ`, when its side conditions pass. -/
def ecModule (pc : AlgebraicPrintCtx) (σ : ECReprMap) {Γ : Ctxt ecDialect} {t : ECTy}
    (com : Com ecDialect Γ t) (name : String) :
    Except String (Veir.IRContext Veir.OpCode × Veir.OperationPtr) := do
  let pc := pc.withCurves σ
  checkCom (ECOp.checkIn pc σ) (ECTy.checkIn pc σ) com
  letI := ecToVeirOp σ
  letI := ecToVeirTy pc σ
  pure (lowerClosedComToModuleWithExterns (d := ecDialect) com []
    (Veir.OpCode.builtin .module) default
    (Veir.OpCode.func .func) VeirPrinterShim.funcFuncProps
    (Veir.OpCode.func .return) default name)

/-- The `builtin.module` of a program of `ecDialectAt σ`: `ecModule` over the curves
    and point representations of `σ`. -/
def ecModuleAt (pc : AlgebraicPrintCtx) {σ : ECReprMap} {Γ : Ctxt (ecDialectAt σ)}
    {t : ECTyAt σ} (com : Com (ecDialectAt σ) Γ t) (name : String) :
    Except String (Veir.IRContext Veir.OpCode × Veir.OperationPtr) :=
  ecModule pc σ (unannotateEcCom com) name

/-- The `builtin.module` of a `cmpDialect` program whose point operands lie on the
    curves of `σ`, when its side conditions pass. -/
def cmpModule (pc : AlgebraicPrintCtx) (σ : ECReprMap) {Γ : Ctxt cmpDialect} {t : CmpTy}
    (com : Com cmpDialect Γ t) (name : String) :
    Except String (Veir.IRContext Veir.OpCode × Veir.OperationPtr) := do
  let pc := pc.withCurves σ
  checkCom (CmpOp.checkIn pc σ) (CmpTy.checkIn pc σ) com
  letI := cmpToVeirOp pc
  letI := cmpToVeirTy pc σ
  pure (lowerClosedComToModuleWithExterns (d := cmpDialect) com []
    (Veir.OpCode.builtin .module) default
    (Veir.OpCode.func .func) VeirPrinterShim.funcFuncProps
    (Veir.OpCode.func .return) default name)

/-- The `builtin.module` of a `polyDialect` program, when its side conditions pass. -/
def polyModule (pc : AlgebraicPrintCtx) {Γ : Ctxt polyDialect} {t : PolyTy}
    (com : Com polyDialect Γ t) (name : String) :
    Except String (Veir.IRContext Veir.OpCode × Veir.OperationPtr) := do
  checkCom (PolyOp.checkIn pc) (PolyTy.checkIn pc) com
  letI := polyToVeirOp pc
  letI := polyToVeirTy pc
  pure (lowerClosedComToModuleWithExterns (d := polyDialect) com []
    (Veir.OpCode.builtin .module) default
    (Veir.OpCode.func .func) VeirPrinterShim.funcFuncProps
    (Veir.OpCode.func .return) default name)

/-- The `builtin.module` of a `tensorExtDialect` program. -/
def tensorExtModule {Γ : Ctxt tensorExtDialect} {t : TensorExtTy}
    (com : Com tensorExtDialect Γ t) (name : String) :
    Except String (Veir.IRContext Veir.OpCode × Veir.OperationPtr) := do
  letI := tensorExtToVeirOp
  letI := tensorExtToVeirTy
  pure (lowerClosedComToModuleWithExterns (d := tensorExtDialect) com []
    (Veir.OpCode.builtin .module) default
    (Veir.OpCode.func .func) VeirPrinterShim.funcFuncProps
    (Veir.OpCode.func .return) default name)

end CatCrypt.Crypto.SecureCompilation.VIR.ComToVeirAlgebraic
