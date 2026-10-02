/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum

/-!
# Extending a block lowering by the identity on a second dialect

A block lowering `L : BlockLoweringData d d'` (`VIR/FieldDialectBlockDescent.lean`)
is written for programs over `d`. `BlockLoweringData.extendId L` is the block
lowering of the operation sum `Dialect.opSum d e` (`VIR/DialectOpSum.lean`) to
`Dialect.opSum d' e` that lowers each operation of `d` by `L` and maps each
operation of `e` to itself, so a pass written for one dialect applies to programs
that also use the operations of another. This is MLIR's partial dialect
conversion, in which the operations of `e` are legal.

The source sum has the type alphabet `T` of `d` and the target sum the alphabet
`T'` of `d'`; the dialect `e` carries a signature over each. Mapping an operation
of `e` to itself needs two conditions, the weakest under which the image of an
operation is again a well-typed operation with the same denotation:

* `SigMaps`: the type map of `L` carries the signature of each operation of `e`
  over `T` to its signature over `T'`. When `T' = T` and the type map is the
  identity this holds by `List.map_id`.
* `OpsCommute`: the denotation of each operation of `e` commutes with the value
  transport of `L`, for the operations satisfying a predicate `GoodE`. When the
  transport is the identity this is the agreement of the two denotations.

A conversion driver `LowerChain D D'` is a list of block-lowering steps between
bundled dialects (`SemDialect`); `LowerChain.run` applies them in order with the
continuation-passing lowering `blockLowerComK`, and `LowerChain.run_denote`
proves preservation by induction on the list.

## Main definitions

* `SigMaps`, `OpsCommute`: the two conditions on the identity part.
* `BlockLoweringData.extendId`: the extended block lowering.
* `liftGood`: the coverage predicate of the extended lowering.
* `SemDialect`, `LowerStep`, `LowerChain`, `LowerChain.run`: the conversion driver.

## Main results

* `extendId_varTransports`, `extendId_mapValExtends`,
  `extendId_blockOpTransports_on`: the three leaf obligations of `L.extendId`, from
  those of `L`.
* `extendId_fundamental_on`: whole-program preservation for covered programs,
  from `blockFundamental_on`.
* `extendId_fundamental`: whole-program preservation for every program, from
  `blockFundamental`.
* `LowerChain.run_denote`: the driver preserves denotation.

An instance over the derived field operations and the prime-field arithmetic
dialect is in `VIR/BlockLoweringExtendWitness.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum
  (castVar castArgs lookup_castVar lookupArgs_castArgs)

/-! ## 1. Casts along equalities of type lists -/

section Casts

variable {T : Type} [TyDenote T] {O : Type}

/-- Resolving an argument vector cast along an equality of type lists is the cast
    of the resolution. -/
theorem lookupArgs_eqRec {Γ : List T} {ts ts' : List T} (h : ts = ts')
    (args : HVector (fun t => Var (d := ⟨O, T⟩) Γ t) ts)
    (V : Valuation (d := ⟨O, T⟩) Γ) :
    Expr.lookupArgs (h ▸ args) V = h ▸ Expr.lookupArgs args V := by
  subst h
  rfl

/-- A value cast along an equality and back is the value. -/
theorem eqRec_symm_eqRec {a b : T} (p : a = b) (x : ⟦a⟧) :
    (p.symm ▸ (p ▸ x : ⟦b⟧) : ⟦a⟧) = x := by
  subst p
  rfl

end Casts

/-- An argument vector of values carried along a type map by a value transport. -/
def transArgs {T T' : Type} [TyDenote T] [TyDenote T'] (m : T → T')
    (tr : ∀ {t : T}, ⟦t⟧ → ⟦m t⟧) :
    {ts : List T} → HVector (fun t => ⟦t⟧) ts → HVector (fun t => ⟦t⟧) (ts.map m)
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons (tr x) (transArgs m tr xs)

/-! ## 2. The conditions on the identity part -/

/-- The type map `m` carries the signature of each operation of `O₂` over `T` to
    its signature over `T'`. -/
structure SigMaps (O₂ : Type) {T T' : Type} [DialectSignature (⟨O₂, T⟩ : Dialect)]
    [DialectSignature (⟨O₂, T'⟩ : Dialect)] (m : T → T') : Prop where
  /-- The argument types of an operation over `T'` are the mapped argument types
      over `T`. -/
  sig_eq : ∀ o : O₂, DialectSignature.sig (d := ⟨O₂, T'⟩) o
    = (DialectSignature.sig (d := ⟨O₂, T⟩) o).map m
  /-- The return type of an operation over `T'` is the mapped return type over
      `T`. -/
  ret_eq : ∀ o : O₂, DialectSignature.ret (d := ⟨O₂, T'⟩) o
    = m (DialectSignature.ret (d := ⟨O₂, T⟩) o)

/-- The denotation of each operation of `O₂` satisfying `GoodE` commutes with the
    value transport `tr` along `m`: the operation over `T'` applied to the
    transported arguments is the transport of the operation over `T`. -/
def OpsCommute {O₂ : Type} {T T' : Type} [TyDenote T] [TyDenote T']
    [DialectSignature (⟨O₂, T⟩ : Dialect)] [DialectDenote (⟨O₂, T⟩ : Dialect)]
    [DialectSignature (⟨O₂, T'⟩ : Dialect)] [DialectDenote (⟨O₂, T'⟩ : Dialect)]
    (m : T → T') (hS : SigMaps O₂ m) (tr : ∀ {t : T}, ⟦t⟧ → ⟦m t⟧)
    (GoodE : O₂ → Prop) : Prop :=
  ∀ o : O₂, GoodE o →
    ∀ xs : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := ⟨O₂, T⟩) o),
      DialectDenote.denote (d := ⟨O₂, T'⟩) o ((hS.sig_eq o).symm ▸ transArgs m tr xs)
        = (hS.ret_eq o).symm ▸ tr (DialectDenote.denote (d := ⟨O₂, T⟩) o xs)

/-! ## 3. The extended lowering -/

section Extend

variable {O₁ O₁' O₂ : Type} {T T' : Type}
  [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)]
  [DialectSignature (⟨O₁', T'⟩ : Dialect)] [DialectSignature (⟨O₂, T'⟩ : Dialect)]

/-- The variable map of the extended lowering: the variable map of `L`, read in
    the two operation sums. -/
def sumMapVar (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩) {Γ : List T} {t : T}
    (v : Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t) :
    Var (d := Dialect.opSum ⟨O₁', T'⟩ ⟨O₂, T'⟩) (L.mapCtx Γ) (L.mapTy t) :=
  castVar (L.mapVar (castVar v))

/-- An argument vector of variables carried by `sumMapVar`. -/
def sumMapArgs (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩) {Γ : List T} :
    {ts : List T} → HVector (fun t => Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t) ts →
    HVector (fun t => Var (d := Dialect.opSum ⟨O₁', T'⟩ ⟨O₂, T'⟩) (L.mapCtx Γ) t)
      (ts.map L.mapTy)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (sumMapVar L v) (sumMapArgs L vs)

/-- The block of an operation of the source sum: an operation of `d` becomes the
    block `L` gives it, included into the target sum; an operation of `e` becomes
    the one-binding block applying the same operation to the mapped arguments. -/
def sumOpBlock (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩) (hS : SigMaps O₂ L.mapTy)
    {Γ : List T} {t : T} : (op : O₁ ⊕ O₂) →
    DialectSignature.ret (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) op = t →
    HVector (fun t => Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t)
      (DialectSignature.sig (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) op) →
    Com (Dialect.opSum ⟨O₁', T'⟩ ⟨O₂, T'⟩) (L.mapCtx Γ) (L.mapTy t)
  | .inl o, h, args =>
      (DialectOpSum.inl (O₂ := O₂)).lowerCom (L.lowerExprBlock ⟨o, h, castArgs args⟩)
  | .inr o, h, args =>
      .var ⟨.inr o, (hS.ret_eq o).trans (congrArg L.mapTy h),
          (hS.sig_eq o).symm ▸ sumMapArgs L args⟩ (.ret .here)

/-- **The extension of a block lowering by the identity.** From a block lowering
    `L` of `d` to `d'`, the block lowering of `Dialect.opSum d e` to
    `Dialect.opSum d' e` that lowers the operations of `d` by `L` and maps each
    operation of `e` to itself. Types, contexts and variables are mapped as by
    `L`. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent.BlockLoweringData.extendId
    (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩) (hS : SigMaps O₂ L.mapTy) :
    BlockLoweringData (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (Dialect.opSum ⟨O₁', T'⟩ ⟨O₂, T'⟩) where
  mapTy := L.mapTy
  mapCtx := L.mapCtx
  mapCtx_cons := L.mapCtx_cons
  mapVar := sumMapVar L
  lowerExprBlock := fun e => sumOpBlock L hS e.op e.retTy_eq e.args

/-- The coverage predicate on an operation of the source sum: `Good` on the
    expression of `d` it carries for an operation of `d`, `GoodE` for an operation
    of `e`. -/
def liftGoodOp (Good : ∀ {Γ : Ctxt (⟨O₁, T⟩ : Dialect)} {t : T}, Expr ⟨O₁, T⟩ Γ t → Prop)
    (GoodE : O₂ → Prop) {Γ : List T} {t : T} : (op : O₁ ⊕ O₂) →
    DialectSignature.ret (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) op = t →
    HVector (fun t => Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t)
      (DialectSignature.sig (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) op) → Prop
  | .inl o, h, args => Good ⟨o, h, castArgs args⟩
  | .inr o, _, _ => GoodE o

/-- The coverage predicate of the extended lowering on expressions. -/
def liftGood (Good : ∀ {Γ : Ctxt (⟨O₁, T⟩ : Dialect)} {t : T}, Expr ⟨O₁, T⟩ Γ t → Prop)
    (GoodE : O₂ → Prop) {Γ : List T} {t : T}
    (e : Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t) : Prop :=
  liftGoodOp Good GoodE e.op e.retTy_eq e.args

variable [TyDenote T] [TyDenote T']

omit [DialectSignature (⟨O₂, T⟩ : Dialect)] [DialectSignature (⟨O₂, T'⟩ : Dialect)] in
/-- Looking up a variable mapped by `sumMapVar` in the transported valuation gives
    the transported lookup. -/
theorem lookup_sumMapVar (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩)
    (transTy : TransTy L) (mapVal : MapVal L) (hVar : VarTransports L transTy mapVal)
    {Γ : List T} {t : T} (v : Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t)
    (V : Valuation (d := ⟨O₁, T⟩) Γ) :
    (sumMapVar L v).lookup (d := Dialect.opSum ⟨O₁', T'⟩ ⟨O₂, T'⟩) (mapVal V)
      = transTy (v.lookup V) := by
  unfold sumMapVar
  rw [lookup_castVar (O := O₁') (O' := O₁' ⊕ O₂) (L.mapVar (castVar v)) (mapVal V),
    hVar (castVar v) V, lookup_castVar (O := O₁ ⊕ O₂) (O' := O₁) v V]

/-- The variable leaf of `L.extendId hS`, from that of `L`. -/
theorem extendId_varTransports (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩)
    (hS : SigMaps O₂ L.mapTy) (transTy : TransTy L) (mapVal : MapVal L)
    (hVar : VarTransports L transTy mapVal) :
    VarTransports (L.extendId hS) transTy mapVal := by
  intro Γ t v V
  exact lookup_sumMapVar L transTy mapVal hVar v V

/-- The binding-threading leaf of `L.extendId hS` is that of `L`. -/
theorem extendId_mapValExtends (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩)
    (hS : SigMaps O₂ L.mapTy) (transTy : TransTy L) (mapVal : MapVal L)
    (hExt : MapValExtends L transTy mapVal) :
    MapValExtends (L.extendId hS) transTy mapVal :=
  fun V x => hExt V x

omit [DialectSignature (⟨O₂, T⟩ : Dialect)] [DialectSignature (⟨O₂, T'⟩ : Dialect)] in
/-- Resolving the mapped arguments against the transported valuation gives the
    transported argument values. -/
theorem lookupArgs_sumMapArgs (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩)
    (transTy : TransTy L) (mapVal : MapVal L) (hVar : VarTransports L transTy mapVal)
    {Γ : List T} :
    ∀ {ts : List T} (args : HVector (fun t => Var (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t) ts)
      (V : Valuation (d := ⟨O₁, T⟩) Γ),
      Expr.lookupArgs (d := Dialect.opSum ⟨O₁', T'⟩ ⟨O₂, T'⟩) (sumMapArgs L args) (mapVal V)
        = transArgs L.mapTy transTy
            (Expr.lookupArgs (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) args V)
  | [], .nil, _ => rfl
  | _ :: _, .cons v vs, V => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookupArgs_sumMapArgs L transTy mapVal hVar vs V]
      congr 1
      exact lookup_sumMapVar L transTy mapVal hVar v V

variable [DialectDenote (⟨O₁, T⟩ : Dialect)] [DialectDenote (⟨O₂, T⟩ : Dialect)]
  [DialectDenote (⟨O₁', T'⟩ : Dialect)] [DialectDenote (⟨O₂, T'⟩ : Dialect)]

/-- **The block leaf of `L.extendId hS` on covered expressions.** An operation of
    `d` uses the block leaf of `L` and the preservation of the left inclusion
    (`DialectOpSum.inl_fundamental`); an operation of `e` uses `OpsCommute`. -/
theorem extendId_blockOpTransports_on (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩)
    (hS : SigMaps O₂ L.mapTy) (transTy : TransTy L) (mapVal : MapVal L)
    (Good : ∀ {Γ : Ctxt (⟨O₁, T⟩ : Dialect)} {t : T}, Expr ⟨O₁, T⟩ Γ t → Prop)
    (GoodE : O₂ → Prop)
    (hVar : VarTransports L transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt (⟨O₁, T⟩ : Dialect)} {t : T} (e : Expr ⟨O₁, T⟩ Γ t), Good e →
      ∀ V : Valuation Γ, (L.lowerExprBlock e).denote (mapVal V) = transTy (e.denote V))
    (hE : OpsCommute L.mapTy hS transTy GoodE) :
    ∀ {Γ : List T} {t : T} (e : Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t),
      liftGood Good GoodE e → ∀ V : Valuation (d := ⟨O₁, T⟩) Γ,
      ((L.extendId hS).lowerExprBlock e).denote (mapVal V) = transTy (e.denote V) := by
  intro Γ t e hg V
  rcases e with ⟨op, h, args⟩
  cases op with
  | inl o =>
      have hinl := DialectOpSum.inl_fundamental (O₂ := O₂)
        (L.lowerExprBlock ⟨o, h, castArgs args⟩) (mapVal V)
      refine hinl.trans ?_
      refine (hBlk ⟨o, h, castArgs args⟩ hg V).trans ?_
      congr 1
      show h ▸ DialectDenote.denote (d := ⟨O₁, T⟩) o
          (Expr.lookupArgs (d := ⟨O₁, T⟩) (castArgs args) V) = h ▸ _
      rw [lookupArgs_castArgs args V]
      rfl
  | inr o =>
      cases h
      show ((hS.ret_eq o).trans rfl ▸ DialectDenote.denote (d := ⟨O₂, T'⟩) o
          (Expr.lookupArgs (d := Dialect.opSum ⟨O₁', T'⟩ ⟨O₂, T'⟩)
            ((hS.sig_eq o).symm ▸ sumMapArgs L args) (mapVal V)))
        = transTy (DialectDenote.denote (d := ⟨O₂, T⟩) o
            (Expr.lookupArgs (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) args V))
      rw [lookupArgs_eqRec, lookupArgs_sumMapArgs L transTy mapVal hVar args V,
        hE o hg]
      exact eqRec_symm_eqRec (hS.ret_eq o).symm _

/-- **Fundamental lemma of the extended lowering, on covered programs.** If `L`
    satisfies the variable, `Good`-gated block and binding-threading leaves and the
    operations of `e` satisfying `GoodE` commute with the value transport, every
    program over `Dialect.opSum d e` covered by `liftGood Good GoodE` lowers by
    `L.extendId hS` to a program denoting the transport of its denotation. -/
theorem extendId_fundamental_on (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩)
    (hS : SigMaps O₂ L.mapTy) (transTy : TransTy L) (mapVal : MapVal L)
    (Good : ∀ {Γ : Ctxt (⟨O₁, T⟩ : Dialect)} {t : T}, Expr ⟨O₁, T⟩ Γ t → Prop)
    (GoodE : O₂ → Prop)
    (hVar : VarTransports L transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt (⟨O₁, T⟩ : Dialect)} {t : T} (e : Expr ⟨O₁, T⟩ Γ t), Good e →
      ∀ V : Valuation Γ, (L.lowerExprBlock e).denote (mapVal V) = transTy (e.denote V))
    (hExt : MapValExtends L transTy mapVal)
    (hE : OpsCommute L.mapTy hS transTy GoodE)
    {Γ : List T} {t : T} (c : Com (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t)
    (hc : CoveredCom (liftGood Good GoodE) c) (V : Valuation (d := ⟨O₁, T⟩) Γ) :
    ((L.extendId hS).blockLowerCom c).denote (mapVal V) = transTy (c.denote V) :=
  blockFundamental_on (L.extendId hS) transTy mapVal (liftGood Good GoodE)
    (extendId_varTransports L hS transTy mapVal hVar)
    (fun e hg V => extendId_blockOpTransports_on L hS transTy mapVal Good GoodE hVar hBlk
      hE e hg V)
    (extendId_mapValExtends L hS transTy mapVal hExt) c hc V

/-- The block leaf of `L.extendId hS` for every expression, from the block leaf of
    `L` and `OpsCommute` for every operation of `e`. -/
theorem extendId_blockOpTransports (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩)
    (hS : SigMaps O₂ L.mapTy) (transTy : TransTy L) (mapVal : MapVal L)
    (hVar : VarTransports L transTy mapVal)
    (hOp : BlockOpTransports L transTy mapVal)
    (hE : OpsCommute L.mapTy hS transTy (fun _ => True)) :
    BlockOpTransports (L.extendId hS) transTy mapVal := by
  intro Γ t e V
  refine extendId_blockOpTransports_on L hS transTy mapVal (fun _ => True)
    (fun _ => True) hVar (fun e _ V => hOp e V) hE e ?_ V
  rcases e with ⟨op, h, args⟩
  cases op <;> trivial

/-- **Fundamental lemma of the extended lowering.** If `L` satisfies its three
    leaves for every expression and every operation of `e` commutes with the value
    transport, every program over `Dialect.opSum d e` lowers by `L.extendId hS` to a
    program denoting the transport of its denotation. -/
theorem extendId_fundamental (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩)
    (hS : SigMaps O₂ L.mapTy) (transTy : TransTy L) (mapVal : MapVal L)
    (hVar : VarTransports L transTy mapVal)
    (hOp : BlockOpTransports L transTy mapVal)
    (hExt : MapValExtends L transTy mapVal)
    (hE : OpsCommute L.mapTy hS transTy (fun _ => True))
    {Γ : List T} {t : T} (c : Com (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Γ t)
    (V : Valuation (d := ⟨O₁, T⟩) Γ) :
    ((L.extendId hS).blockLowerCom c).denote (mapVal V) = transTy (c.denote V) :=
  blockFundamental (L.extendId hS) transTy mapVal
    (extendId_varTransports L hS transTy mapVal hVar)
    (extendId_blockOpTransports L hS transTy mapVal hVar hOp hE)
    (extendId_mapValExtends L hS transTy mapVal hExt) c V

end Extend

/-! ## 4. The conversion driver -/

/-- A dialect bundled with its type denotation, signature and denotation. -/
structure SemDialect where
  /-- The dialect. -/
  dia : Dialect.{0, 0}
  /-- The denotation of its types. -/
  [tyDenote : TyDenote dia.Ty]
  /-- Its signature. -/
  [sig : DialectSignature dia]
  /-- Its denotation. -/
  [den : DialectDenote dia]

attribute [instance] SemDialect.tyDenote SemDialect.sig SemDialect.den

/-- One step of the driver: a block lowering with its value and valuation
    transports and its three leaf obligations. -/
structure LowerStep (D D' : SemDialect) where
  /-- The block lowering. -/
  L : BlockLoweringData D.dia D'.dia
  /-- The value transport. -/
  transTy : TransTy L
  /-- The valuation transport. -/
  mapVal : MapVal L
  /-- The variable leaf. -/
  hVar : VarTransports L transTy mapVal
  /-- The block leaf. -/
  hOp : BlockOpTransports L transTy mapVal
  /-- The binding-threading leaf. -/
  hExt : MapValExtends L transTy mapVal

/-- **The conversion driver**: a list of block-lowering steps, each from the
    target dialect of the previous one. -/
inductive LowerChain : SemDialect → SemDialect → Type 1 where
  /-- The empty list. -/
  | nil (D : SemDialect) : LowerChain D D
  /-- A step followed by a list. -/
  | cons {D D' D'' : SemDialect} (s : LowerStep D D') (rest : LowerChain D' D'') :
      LowerChain D D''

namespace LowerChain

/-- The composite type map. -/
def mapTy : {D D' : SemDialect} → LowerChain D D' → D.dia.Ty → D'.dia.Ty
  | _, _, .nil _ => fun t => t
  | _, _, .cons s rest => fun t => rest.mapTy (s.L.mapTy t)

/-- The composite context map. -/
def mapCtx : {D D' : SemDialect} → LowerChain D D' → Ctxt D.dia → Ctxt D'.dia
  | _, _, .nil _ => fun Γ => Γ
  | _, _, .cons s rest => fun Γ => rest.mapCtx (s.L.mapCtx Γ)

/-- The composite value transport. -/
def transTy : {D D' : SemDialect} → (P : LowerChain D D') →
    ∀ {t : D.dia.Ty}, ⟦t⟧ → ⟦P.mapTy t⟧
  | _, _, .nil _ => fun x => x
  | _, _, .cons s rest => fun x => rest.transTy (s.transTy x)

/-- The composite valuation transport. -/
def mapVal : {D D' : SemDialect} → (P : LowerChain D D') →
    ∀ {Γ : Ctxt D.dia}, Valuation Γ → Valuation (P.mapCtx Γ)
  | _, _, .nil _ => fun V => V
  | _, _, .cons s rest => fun V => rest.mapVal (s.mapVal V)

/-- **Run the driver**: apply the steps in order, each by the
    continuation-passing lowering `blockLowerComK`. -/
def run : {D D' : SemDialect} → (P : LowerChain D D') →
    ∀ {Γ : Ctxt D.dia} {t : D.dia.Ty}, Com D.dia Γ t → Com D'.dia (P.mapCtx Γ) (P.mapTy t)
  | _, _, .nil _ => fun c => c
  | _, _, .cons s rest => fun c => rest.run (s.L.blockLowerComK c)

/-- **The driver preserves denotation**: the program the steps produce denotes,
    under the composite valuation transport, the composite transport of the
    source denotation. By induction on the list of steps. -/
theorem run_denote : {D D' : SemDialect} → (P : LowerChain D D') →
    ∀ {Γ : Ctxt D.dia} {t : D.dia.Ty} (c : Com D.dia Γ t) (V : Valuation Γ),
      (P.run c).denote (P.mapVal V) = P.transTy (c.denote V)
  | _, _, .nil _, _, _, _, _ => rfl
  | _, _, .cons s rest, _, _, c, V => by
      show (rest.run (s.L.blockLowerComK c)).denote (rest.mapVal (s.mapVal V))
        = rest.transTy (s.transTy (c.denote V))
      rw [run_denote rest (s.L.blockLowerComK c) (s.mapVal V)]
      congr 1
      exact s.L.blockLowerComK_denote_on s.transTy s.mapVal (fun _ => True) s.hVar
        (fun e _ V => s.hOp e V) s.hExt c (coveredCom_of_forall _ (fun _ => trivial) c) V

end LowerChain

/-- The driver step of the extended lowering `L.extendId hS`. -/
def LowerStep.extendId {O₁ O₁' O₂ : Type} {T T' : Type} [TyDenote T] [TyDenote T']
    [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectDenote (⟨O₁, T⟩ : Dialect)]
    [DialectSignature (⟨O₂, T⟩ : Dialect)] [DialectDenote (⟨O₂, T⟩ : Dialect)]
    [DialectSignature (⟨O₁', T'⟩ : Dialect)] [DialectDenote (⟨O₁', T'⟩ : Dialect)]
    [DialectSignature (⟨O₂, T'⟩ : Dialect)] [DialectDenote (⟨O₂, T'⟩ : Dialect)]
    (L : BlockLoweringData ⟨O₁, T⟩ ⟨O₁', T'⟩) (hS : SigMaps O₂ L.mapTy)
    (transTy : TransTy L) (mapVal : MapVal L)
    (hVar : VarTransports L transTy mapVal) (hOp : BlockOpTransports L transTy mapVal)
    (hExt : MapValExtends L transTy mapVal)
    (hE : OpsCommute L.mapTy hS transTy (fun _ => True)) :
    LowerStep ⟨Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩⟩ ⟨Dialect.opSum ⟨O₁', T'⟩ ⟨O₂, T'⟩⟩ where
  L := L.extendId hS
  transTy := transTy
  mapVal := mapVal
  hVar := extendId_varTransports L hS transTy mapVal hVar
  hOp := extendId_blockOpTransports L hS transTy mapVal hVar hOp hE
  hExt := extendId_mapValExtends L hS transTy mapVal hExt

end CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend
