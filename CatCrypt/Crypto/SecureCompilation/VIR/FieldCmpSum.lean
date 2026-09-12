/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldEcCmpOps
public import CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport

/-!
# Shared-`Ty` combination of `fieldDialect` and `cmpDialect`

`fieldDialect` (`VIR/FieldDialect.lean`) denotes into `ZMod p` and the pairing
extension tower; `cmpDialect` (`VIR/FieldEcCmpOps.lean`) takes a field element or
a curve point and denotes into `Bool`. A comparison's operand is produced by a
field operation, so the two dialects exchange values, and the disjoint-`Ty`
coproduct `Dialect.sum` (`VIR/DialectCoproduct.lean`) cannot host the exchange: a
`fMul` result would carry the type `.inl (FieldTy.fp p)` while `fieldEq` demands
`.inr (CmpTy.fp p)`.

This file follows `VIR/MlirArithScfSum.lean`: the combined dialect tags `Op`
alone, over a type alphabet the two summands share. `mlirArith` and `mlirScf`
already share `CryptoTy`; `fieldDialect` and `cmpDialect` do not, so the shared
alphabet is built here as `FieldCmpTy` — the `FieldTy` alphabet, the curve-point
type, and a boolean — with `FieldTy.fp p` and `CmpTy.fp p` mapped to the same
`FieldCmpTy.fld (.fp p)`. That identification is what lets a field value flow
into a comparison.

`CryptoTy` carries a boolean (`CryptoTy.bit`) but no field or curve type, so it
does not serve as the shared alphabet here.

## Main definitions

* `FieldCmpTy`, `instFieldCmpTyDenote`: the shared type alphabet and its
  denotation.
* `embedCmpTy`, `transCmpVal`, `untransCmpVal`: the `CmpTy` type embedding and
  the value transports along it.
* `fieldCmpDialect`, `instFieldCmpSignature`, `fieldCmpDenote`: the combined
  dialect, with `Op = FieldOp ⊕ CmpOp` and `Ty = FieldCmpTy`, its signature and
  its denotation, each a case-split delegating to the summand.
* `fieldLowering` / `cmpLowering`: the two inclusions as
  `ComParametricityTransport.LoweringData`.
* `opCtSafe`, `ctSafeExprSum`, `ctSafeComSum`: the constant-time predicate of the
  combined dialect, reading each summand's per-op flag.

## Main results

* `field_denote` / `cmp_denote`: whole-program denotation preservation for the
  two inclusions, from `ComParametricityTransport.fundamental` applied to the
  three leaf coherences.
* `ctSafeComSum_lowerCom_cmp`: the `cmpDialect` inclusion carries each op's
  `publicData` flag, whole-program.
* `Witness.cmpAfterFieldProg_denote`: a four-binding program in which a field
  multiply's result is an operand of a `fieldEq`, with its denotation.
* `Witness.boolAcrossFieldProg_denote_zero` / `_nonzero`: a comparison result
  read across an intervening field binding.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldCmpSum

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
  (ECPoint)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
  (FieldTy FieldOp fieldDialect fieldDenote)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldEcCmpOps
  (CmpTy CmpOp cmpDialect cmpDenote)
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)

/-! ## 1. The shared type alphabet -/

/-- The type alphabet shared by the field and comparison operations: a `FieldTy`,
    a curve point, or a boolean. -/
inductive FieldCmpTy where
  /-- A `fieldDialect` type, denoting as it does there. -/
  | fld (t : FieldTy)
  /-- The curve group at modulus `p`, `⟦·⟧ = ECPoint p`. -/
  | pt (p : Nat)
  /-- The comparison result, `⟦·⟧ = Bool`. -/
  | bool
  deriving DecidableEq

/-- Denotation of the shared alphabet: a wrapped `FieldTy` denotes as in
    `fieldDialect`, `pt p` to the curve group, `bool` to `Bool`. -/
@[reducible] instance instFieldCmpTyDenote : TyDenote FieldCmpTy where
  denote
    | .fld t => ⟦t⟧
    | .pt p => ECPoint p
    | .bool => Bool

/-- The `CmpTy` alphabet inside the shared one: the field operand lands on the
    wrapped `FieldTy.fp`, the point operand on `pt`, the result on `bool`. -/
def embedCmpTy : CmpTy → FieldCmpTy
  | .fp p => .fld (.fp p)
  | .point p => .pt p
  | .bool => .bool

/-- The value transport along `embedCmpTy`. -/
def transCmpVal : {t : CmpTy} → ⟦t⟧ → ⟦embedCmpTy t⟧
  | .fp _, x => x
  | .point _, x => x
  | .bool, x => x

/-- The inverse value transport along `embedCmpTy`. -/
def untransCmpVal : {t : CmpTy} → ⟦embedCmpTy t⟧ → ⟦t⟧
  | .fp _, x => x
  | .point _, x => x
  | .bool, x => x

/-- The two value transports along `embedCmpTy` compose to the identity. -/
theorem untransCmpVal_transCmpVal : ∀ {t : CmpTy} (x : ⟦t⟧),
    untransCmpVal (transCmpVal x) = x
  | .fp _, _ => rfl
  | .point _, _ => rfl
  | .bool, _ => rfl

/-! ## 2. The combined dialect -/

/-- The combined dialect: `Op` is the tagged sum of the field and comparison
    operation alphabets, `Ty` is the shared alphabet. -/
@[reducible] def fieldCmpDialect : Dialect :=
  { Op := Sum FieldOp CmpOp, Ty := FieldCmpTy }

/-- Argument vectors of a field operation, re-indexed out of the shared
    alphabet: `⟦.fld t⟧` and `⟦t⟧` are the same type. -/
def unmapFld : {ts : List FieldTy} →
    HVector (fun t => ⟦t⟧) (ts.map FieldCmpTy.fld) →
    HVector (fun t => ⟦t⟧) ts
  | [], _ => .nil
  | _ :: _, .cons x xs => .cons x (unmapFld xs)

/-- Argument vectors of a comparison operation, re-indexed out of the shared
    alphabet by `untransCmpVal`. -/
def unmapCmp : {ts : List CmpTy} →
    HVector (fun t => ⟦t⟧) (ts.map embedCmpTy) →
    HVector (fun t => ⟦t⟧) ts
  | [], _ => .nil
  | t :: _, .cons x xs => .cons (untransCmpVal (t := t) x) (unmapCmp xs)

/-- Signatures in the combined dialect: the summand's argument list and return
    type, carried into the shared alphabet. -/
@[reducible] instance instFieldCmpSignature : DialectSignature fieldCmpDialect where
  sig
    | .inl o => (DialectSignature.sig (d := fieldDialect) o).map FieldCmpTy.fld
    | .inr o => (DialectSignature.sig (d := cmpDialect) o).map embedCmpTy
  ret
    | .inl o => .fld (DialectSignature.ret (d := fieldDialect) o)
    | .inr o => embedCmpTy (DialectSignature.ret (d := cmpDialect) o)

/-- Operation denotation in the combined dialect: re-index the arguments into the
    summand's alphabet and apply the summand's denotation. -/
instance fieldCmpDenote : DialectDenote fieldCmpDialect where
  denote
    | .inl o => fun args => DialectDenote.denote (d := fieldDialect) o (unmapFld args)
    | .inr o => fun args => transCmpVal (DialectDenote.denote (d := cmpDialect) o (unmapCmp args))

/-! ## 3. Per-summand denotation

The combined denotation at a tagged operation is the summand's denotation of the
re-indexed arguments. -/

/-- A field operation in the combined dialect denotes as in `fieldDialect`. -/
theorem field_op_denote (o : FieldOp)
    (args : HVector (fun t => ⟦t⟧)
      (DialectSignature.sig (d := fieldCmpDialect) (.inl o))) :
    DialectDenote.denote (d := fieldCmpDialect) (.inl o) args
      = fieldDenote.denote o (unmapFld args) := rfl

/-- A comparison operation in the combined dialect denotes as in `cmpDialect`,
    transported along `embedCmpTy`. -/
theorem cmp_op_denote (o : CmpOp)
    (args : HVector (fun t => ⟦t⟧)
      (DialectSignature.sig (d := fieldCmpDialect) (.inr o))) :
    DialectDenote.denote (d := fieldCmpDialect) (.inr o) args
      = transCmpVal (cmpDenote.denote o (unmapCmp args)) := rfl

/-- A `fieldEq` in the combined dialect denotes to the field-equality test on its
    two operands. -/
theorem fieldEq_denote {p : Nat} (pub : Bool) (a b : ZMod p) :
    DialectDenote.denote (d := fieldCmpDialect) (.inr (.fieldEq p pub))
        (.cons a (.cons b .nil)) = decide (a = b) := rfl

/-- A `fieldIsZero` in the combined dialect denotes to the field zero-test. -/
theorem fieldIsZero_denote {p : Nat} (pub : Bool) (a : ZMod p) :
    DialectDenote.denote (d := fieldCmpDialect) (.inr (.fieldIsZero p pub))
        (.cons a .nil) = decide (a = 0) := rfl

/-- An `fMul` in the combined dialect denotes to `ZMod p` multiplication. -/
theorem fMul_denote {p : Nat} (a b : ZMod p) :
    DialectDenote.denote (d := fieldCmpDialect) (.inl (.fMul p))
        (.cons a (.cons b .nil)) = a * b := rfl

/-! ## 4. Syntactic transport along the two embeddings -/

/-- Transport a `fieldDialect` variable into the shared context. -/
def mapVarFld : {Γ : Ctxt fieldDialect} → {t : FieldTy} →
    Var Γ t → Var (d := fieldCmpDialect) (Γ.map FieldCmpTy.fld) (FieldCmpTy.fld t)
  | _, _, .here => .here
  | _, _, .there v => .there (mapVarFld v)

/-- Transport a `fieldDialect` argument vector into the shared context. -/
def mapArgsFld {Γ : Ctxt fieldDialect} : {ts : List FieldTy} →
    HVector (fun t => Var Γ t) ts →
    HVector (fun t => Var (d := fieldCmpDialect) (Γ.map FieldCmpTy.fld) t)
      (ts.map FieldCmpTy.fld)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (mapVarFld v) (mapArgsFld vs)

/-- Transport a `cmpDialect` variable into the shared context. -/
def mapVarCmp : {Γ : Ctxt cmpDialect} → {t : CmpTy} →
    Var Γ t → Var (d := fieldCmpDialect) (Γ.map embedCmpTy) (embedCmpTy t)
  | _, _, .here => .here
  | _, _, .there v => .there (mapVarCmp v)

/-- Transport a `cmpDialect` argument vector into the shared context. -/
def mapArgsCmp {Γ : Ctxt cmpDialect} : {ts : List CmpTy} →
    HVector (fun t => Var Γ t) ts →
    HVector (fun t => Var (d := fieldCmpDialect) (Γ.map embedCmpTy) t)
      (ts.map embedCmpTy)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (mapVarCmp v) (mapArgsCmp vs)

/-! ## 5. The two inclusions as structural lowerings -/

/-- The inclusion of `fieldDialect` into the combined dialect: types and contexts
    are wrapped by `FieldCmpTy.fld`, each operation is tagged `.inl`. -/
def fieldLowering : LoweringData fieldDialect fieldCmpDialect where
  mapTy := FieldCmpTy.fld
  mapCtx := List.map FieldCmpTy.fld
  mapCtx_cons := fun _ _ => rfl
  mapVar := mapVarFld
  lowerExpr := fun ex =>
    { op := .inl ex.op
      retTy_eq := congrArg FieldCmpTy.fld ex.retTy_eq
      args := mapArgsFld ex.args }

/-- The inclusion of `cmpDialect` into the combined dialect: types and contexts
    are carried by `embedCmpTy`, each operation is tagged `.inr`. -/
def cmpLowering : LoweringData cmpDialect fieldCmpDialect where
  mapTy := embedCmpTy
  mapCtx := List.map embedCmpTy
  mapCtx_cons := fun _ _ => rfl
  mapVar := mapVarCmp
  lowerExpr := fun ex =>
    { op := .inr ex.op
      retTy_eq := congrArg embedCmpTy ex.retTy_eq
      args := mapArgsCmp ex.args }

/-! ## 6. The leaf coherences -/

/-- Re-index a `fieldDialect` valuation into the shared context. -/
def mapValFld : {Γ : Ctxt fieldDialect} →
    Valuation Γ → Valuation (d := fieldCmpDialect) (Γ.map FieldCmpTy.fld)
  | [], _ => .nil
  | _ :: _, .cons x xs => .cons x (mapValFld xs)

/-- Re-index a `cmpDialect` valuation into the shared context. -/
def mapValCmp : {Γ : Ctxt cmpDialect} →
    Valuation Γ → Valuation (d := fieldCmpDialect) (Γ.map embedCmpTy)
  | [], _ => .nil
  | _ :: _, .cons x xs => .cons (transCmpVal x) (mapValCmp xs)

/-- Looking up a transported field variable in a transported valuation gives the
    source lookup. -/
theorem lookup_mapVarFld :
    ∀ {Γ : Ctxt fieldDialect} {t : FieldTy} (v : Var Γ t) (V : Valuation Γ),
      (mapVarFld v).lookup (mapValFld V) = v.lookup V
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ xs => lookup_mapVarFld v xs

/-- Looking up a transported comparison variable in a transported valuation gives
    the transport of the source lookup. -/
theorem lookup_mapVarCmp :
    ∀ {Γ : Ctxt cmpDialect} {t : CmpTy} (v : Var Γ t) (V : Valuation Γ),
      (mapVarCmp v).lookup (mapValCmp V) = transCmpVal (v.lookup V)
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ xs => lookup_mapVarCmp v xs

/-- Resolving transported field arguments against a transported valuation and
    re-indexing gives the source argument values. -/
theorem lookupArgs_mapArgsFld {Γ : Ctxt fieldDialect} :
    ∀ {ts : List FieldTy} (args : HVector (fun t => Var Γ t) ts) (V : Valuation Γ),
      unmapFld (Expr.lookupArgs (mapArgsFld args) (mapValFld V))
        = Expr.lookupArgs args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v vs, V => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookup_mapVarFld v V, lookupArgs_mapArgsFld vs V]

/-- Resolving transported comparison arguments against a transported valuation
    and re-indexing gives the source argument values. -/
theorem lookupArgs_mapArgsCmp {Γ : Ctxt cmpDialect} :
    ∀ {ts : List CmpTy} (args : HVector (fun t => Var Γ t) ts) (V : Valuation Γ),
      unmapCmp (Expr.lookupArgs (mapArgsCmp args) (mapValCmp V))
        = Expr.lookupArgs args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v vs, V => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookup_mapVarCmp v V, untransCmpVal_transCmpVal, lookupArgs_mapArgsCmp vs V]

/-- The field inclusion's value transport. -/
def fieldTransTy : TransTy fieldLowering := fun x => x

/-- The field inclusion's valuation transport. -/
def fieldMapVal : MapVal fieldLowering := fun V => mapValFld V

/-- The comparison inclusion's value transport. -/
def cmpTransTy : TransTy cmpLowering := fun x => transCmpVal x

/-- The comparison inclusion's valuation transport. -/
def cmpMapVal : MapVal cmpLowering := fun V => mapValCmp V

/-- Variable-transport coherence for the field inclusion. -/
theorem field_varTransports :
    VarTransports fieldLowering fieldTransTy fieldMapVal :=
  fun v V => lookup_mapVarFld v V

/-- Variable-transport coherence for the comparison inclusion. -/
theorem cmp_varTransports :
    VarTransports cmpLowering cmpTransTy cmpMapVal :=
  fun v V => lookup_mapVarCmp v V

/-- Binding-threading coherence for the field inclusion. -/
theorem field_mapValExtends :
    MapValExtends fieldLowering fieldTransTy fieldMapVal := fun _ _ => rfl

/-- Binding-threading coherence for the comparison inclusion. -/
theorem cmp_mapValExtends :
    MapValExtends cmpLowering cmpTransTy cmpMapVal := fun _ _ => rfl

/-- Per-operation leaf transport for the field inclusion. -/
theorem field_opTransports :
    OpLowerTransports fieldLowering fieldTransTy fieldMapVal := by
  intro Γ t ex V
  obtain ⟨op, rfl, args⟩ := ex
  show DialectDenote.denote (d := fieldDialect) op
      (unmapFld (Expr.lookupArgs (mapArgsFld args) (mapValFld V))) = _
  rw [lookupArgs_mapArgsFld args V]
  rfl

/-- Per-operation leaf transport for the comparison inclusion. -/
theorem cmp_opTransports :
    OpLowerTransports cmpLowering cmpTransTy cmpMapVal := by
  intro Γ t ex V
  obtain ⟨op, rfl, args⟩ := ex
  show transCmpVal (DialectDenote.denote (d := cmpDialect) op
      (unmapCmp (Expr.lookupArgs (mapArgsCmp args) (mapValCmp V)))) = _
  rw [lookupArgs_mapArgsCmp args V]
  rfl

/-! ## 7. Denotation preservation -/

/-- Whole-program denotation preservation for the field inclusion: every
    `Com fieldDialect`, included into the combined dialect, denotes under the
    transported valuation to the value it denotes over `fieldDialect`. -/
theorem field_denote {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    ComLowerTransports fieldLowering fieldTransTy fieldMapVal c :=
  fundamental fieldLowering fieldTransTy fieldMapVal
    field_varTransports field_opTransports field_mapValExtends c

/-- Whole-program denotation preservation for the comparison inclusion. -/
theorem cmp_denote {Γ : Ctxt cmpDialect} {t : CmpTy} (c : Com cmpDialect Γ t) :
    ComLowerTransports cmpLowering cmpTransTy cmpMapVal c :=
  fundamental cmpLowering cmpTransTy cmpMapVal
    cmp_varTransports cmp_opTransports cmp_mapValExtends c

/-! ## 8. The constant-time flag

Every `FieldOp` is data-oblivious; a `CmpOp` carries a `publicData` flag and is
admitted only when that flag is set. The combined dialect's operation *is* the
summand's operation under a tag, so the flag is read off it directly. -/

/-- Per-operation constant-time predicate of the combined dialect: a field
    operation is data-oblivious, a comparison is admitted exactly when its
    `publicData` flag is set. -/
def opCtSafe : fieldCmpDialect.Op → Bool
  | .inl o => o.ctSafe
  | .inr o => o.ctSafe

/-- A tagged field operation carries `FieldOp.ctSafe`. -/
@[simp] theorem opCtSafe_inl (o : FieldOp) : opCtSafe (.inl o) = o.ctSafe := rfl

/-- A tagged comparison operation carries `CmpOp.ctSafe`, hence its
    `publicData` flag. -/
@[simp] theorem opCtSafe_inr (o : CmpOp) : opCtSafe (.inr o) = o.ctSafe := rfl

/-- A public-data `fieldEq` is admitted in the combined dialect. -/
theorem opCtSafe_fieldEq_public {p : Nat} :
    opCtSafe (.inr (.fieldEq p true)) = true := rfl

/-- A secret-operand `fieldEq` is flagged in the combined dialect. -/
theorem opCtSafe_fieldEq_secret {p : Nat} :
    opCtSafe (.inr (.fieldEq p false)) = false := rfl

/-- Per-expression constant-time predicate of the combined dialect. -/
def ctSafeExprSum {Γ : Ctxt fieldCmpDialect} {t : FieldCmpTy}
    (e : Expr fieldCmpDialect Γ t) : Bool :=
  opCtSafe e.op

/-- Per-program constant-time predicate of the combined dialect: every let-bound
    operation is admitted. -/
def ctSafeComSum {Γ : Ctxt fieldCmpDialect} {t : FieldCmpTy} :
    Com fieldCmpDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExprSum e && ctSafeComSum body

/-- The comparison inclusion carries each operation's `publicData` flag: a
    lowered expression is admitted in the combined dialect exactly when the
    source expression is admitted in `cmpDialect`. -/
theorem ctSafeExprSum_lowerExpr_cmp {Γ : Ctxt cmpDialect} {t : CmpTy}
    (e : Expr cmpDialect Γ t) :
    ctSafeExprSum (cmpLowering.lowerExpr e) = FieldEcCmpOps.ctSafeExpr e := rfl

/-- The comparison inclusion carries the `publicData` flags whole-program: an
    included `Com cmpDialect` is admitted in the combined dialect exactly when it
    is admitted in `cmpDialect`. -/
theorem ctSafeComSum_lowerCom_cmp :
    ∀ {Γ : Ctxt cmpDialect} {t : CmpTy} (c : Com cmpDialect Γ t),
      ctSafeComSum (cmpLowering.lowerCom c) = FieldEcCmpOps.ctSafeCom c
  | _, _, .ret _ => rfl
  | _, _, .var e body => by
      show (ctSafeExprSum (cmpLowering.lowerExpr e)
              && ctSafeComSum (cmpLowering.lowerCom body))
            = (FieldEcCmpOps.ctSafeExpr e && FieldEcCmpOps.ctSafeCom body)
      rw [ctSafeExprSum_lowerExpr_cmp e, ctSafeComSum_lowerCom_cmp body]

/-- Every included field expression is admitted in the combined dialect. -/
theorem ctSafeExprSum_lowerExpr_field {Γ : Ctxt fieldDialect} {t : FieldTy}
    (e : Expr fieldDialect Γ t) :
    ctSafeExprSum (fieldLowering.lowerExpr e) = true := rfl

/-- Every included `Com fieldDialect` is admitted in the combined dialect. -/
theorem ctSafeComSum_lowerCom_field :
    ∀ {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t),
      ctSafeComSum (fieldLowering.lowerCom c) = true
  | _, _, .ret _ => rfl
  | _, _, .var e body => by
      show (ctSafeExprSum (fieldLowering.lowerExpr e)
              && ctSafeComSum (fieldLowering.lowerCom body)) = true
      rw [ctSafeExprSum_lowerExpr_field e, ctSafeComSum_lowerCom_field body]
      rfl

/-! ## 9. Programs that exchange values between the summands

A comparison operand produced by a field operation, and a comparison result
carried across a later field binding. Neither shape is expressible over
`fieldDialect ⊕ cmpDialect` or over either summand alone. -/

namespace Witness

/-- The prime field `F_7` inside the shared alphabet. -/
abbrev fpT : FieldCmpTy := .fld (.fp 7)

/-- A four-binding program over the combined dialect:

    ```
    let a : fld (fp 7) = inl (fConst 7 3)
    let b : fld (fp 7) = inl (fMul 7) a a
    let z : fld (fp 7) = inl (fConst 7 2)
    let r : bool       = inr (fieldEq 7 true) b z
    ret r
    ```

    The `fieldEq` operand `b` is the result of a field multiply, and is read
    across the intervening `z` binding. -/
def cmpAfterFieldProg : Com fieldCmpDialect [] .bool :=
  .var (t := fpT) ⟨.inl (.fConst 7 3), rfl, .nil⟩
    (.var (t := fpT) ⟨.inl (.fMul 7), rfl, .cons .here (.cons .here .nil)⟩
      (.var (t := fpT) ⟨.inl (.fConst 7 2), rfl, .nil⟩
        (.var (t := FieldCmpTy.bool)
            ⟨.inr (.fieldEq 7 true), rfl, .cons (.there .here) (.cons .here .nil)⟩
          (.ret .here))))

/-- `cmpAfterFieldProg` denotes to `true`: `3 * 3 = 2` in `ZMod 7`. -/
theorem cmpAfterFieldProg_denote : cmpAfterFieldProg.denote .nil = true := by rfl

/-- `cmpAfterFieldProg` is admitted by the combined dialect's constant-time
    predicate: its comparison carries `publicData = true`. -/
theorem cmpAfterFieldProg_ctSafe : ctSafeComSum cmpAfterFieldProg = true := rfl

/-- `cmpAfterFieldProg` with the comparison's `publicData` flag cleared. -/
def cmpAfterFieldProgSecret : Com fieldCmpDialect [] .bool :=
  .var (t := fpT) ⟨.inl (.fConst 7 3), rfl, .nil⟩
    (.var (t := fpT) ⟨.inl (.fMul 7), rfl, .cons .here (.cons .here .nil)⟩
      (.var (t := fpT) ⟨.inl (.fConst 7 2), rfl, .nil⟩
        (.var (t := FieldCmpTy.bool)
            ⟨.inr (.fieldEq 7 false), rfl, .cons (.there .here) (.cons .here .nil)⟩
          (.ret .here))))

/-- `cmpAfterFieldProgSecret` denotes to the same value as
    `cmpAfterFieldProg`. -/
theorem cmpAfterFieldProgSecret_denote :
    cmpAfterFieldProgSecret.denote .nil = true := by rfl

/-- `cmpAfterFieldProgSecret` is flagged by the combined dialect's constant-time
    predicate: the flag is carried on the operation, independently of the
    denotation. -/
theorem cmpAfterFieldProgSecret_ctSafe :
    ctSafeComSum cmpAfterFieldProgSecret = false := rfl

/-- A three-binding program over the combined dialect:

    ```
    let r : bool       = inr (fieldIsZero 7 true) x
    let c : fld (fp 7) = inl (fConst 7 5)
    ret r
    ```

    The comparison result `r` is read across the intervening field binding `c`,
    so a boolean and a field value share one context. -/
def boolAcrossFieldProg : Com fieldCmpDialect [fpT] .bool :=
  .var (t := FieldCmpTy.bool)
      ⟨.inr (.fieldIsZero 7 true), rfl, .cons .here .nil⟩
    (.var (t := fpT) ⟨.inl (.fConst 7 5), rfl, .nil⟩
      (.ret (.there .here)))

/-- `boolAcrossFieldProg` denotes to `true` on a zero input. -/
theorem boolAcrossFieldProg_denote_zero :
    boolAcrossFieldProg.denote (.cons (0 : ZMod 7) .nil) = true := by rfl

/-- `boolAcrossFieldProg` denotes to `false` on a non-zero input. -/
theorem boolAcrossFieldProg_denote_nonzero :
    boolAcrossFieldProg.denote (.cons (3 : ZMod 7) .nil) = false := by rfl

/-! ### The inclusions at concrete source programs -/

/-- The comparison inclusion's transport square at `FieldEcCmpOps.smokeProg`. -/
theorem cmp_smokeProg_transports :
    ComLowerTransports cmpLowering cmpTransTy cmpMapVal FieldEcCmpOps.smokeProg :=
  cmp_denote FieldEcCmpOps.smokeProg

/-- `FieldEcCmpOps.smokeProg` denotes to `true` on a zero input. -/
theorem smokeProg_denote_zero :
    FieldEcCmpOps.smokeProg.denote (.cons (0 : ZMod 7) .nil) = true := by rfl

/-- `FieldEcCmpOps.smokeProg` included into the combined dialect denotes to
    `true` on a zero input, read off the transport square. -/
theorem cmp_smokeProg_denote :
    (cmpLowering.lowerCom FieldEcCmpOps.smokeProg).denote
      (cmpMapVal (.cons (0 : ZMod 7) .nil)) = true := by
  rw [cmp_smokeProg_transports (.cons (0 : ZMod 7) .nil)]
  exact smokeProg_denote_zero

/-- The field inclusion's transport square at `FieldDialect.smokeProg`. -/
theorem field_smokeProg_transports :
    ComLowerTransports fieldLowering fieldTransTy fieldMapVal
      FieldDialect.smokeProg :=
  field_denote FieldDialect.smokeProg

end Witness

end CatCrypt.Crypto.SecureCompilation.VIR.FieldCmpSum
