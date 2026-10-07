/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproductLeak
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFMapLeak

/-!
# Elimination of a coproduct summand by a partial block lowering

For dialects `d` and `e` and a partial block lowering `Q : PartialBlockLowering e d`,
`Q.sumElimId : PartialBlockLowering (Dialect.sum d e) d` lowers the coproduct to its left
summand: a type of `d` is kept and a type of `e` is mapped by `Q.mapTy`; an operation of `d`
becomes the same operation on the mapped variables; an operation `o` of `e` becomes the block
`Q` gives the expression of `o` on its own argument context, under the renaming that sends
that context to the argument variables. The lowering refuses an operation of `e` when `Q`
refuses that expression or when `Q.mapCtx []` is not the empty context.

## Main definitions

* `PartialBlockLowering.sumTy`, `sumVar` — the type and variable maps.
* `PartialBlockLowering.opExpr` — the expression of an operation on its argument context.
* `PartialBlockLowering.sumElimId` — the lowering.
* `PartialBlockLowering.sumTransTy`, `sumMapVal` — the value and valuation transports over
  a value transport of `Q`.

## Main results

* `sumElimId_varTransports`, `sumElimId_mapValExtends` — the variable and binding leaves.
* `sumElimId_block` — a block of `sumElimId` denotes the transport of the value of its
  expression, given the block leaf of `Q`.
* `sumElimId_blockLeak` — a block of `sumElimId` emits the events of its expression in the
  coproduct model, given the block leak leaf of `Q`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open FieldDialectBlockDescent
open BlockLoweringCPS (consHom castHom valuation_ext lookup_pullV)
open BlockLoweringExtend (transArgs)
open DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel Expr.ctLeak Com.ctLeak opLeak)

namespace PartialBlockLowering

/-! ## 1. The lowering -/

section Defs

variable {d e : Dialect.{0, 0}} [DialectSignature d] [DialectSignature e]

/-- The type map: a type of `d` is kept, a type of `e` is mapped by `Q`. -/
def sumTy (Q : PartialBlockLowering e d) : (Dialect.sum d e).Ty → d.Ty
  | .inl t => t
  | .inr t => Q.mapTy t

/-- The variable map along `sumTy`. -/
def sumVar (Q : PartialBlockLowering e d) : {Γ : Ctxt (Dialect.sum d e)} →
    {t : (Dialect.sum d e).Ty} → Var Γ t → Var (d := d) (Γ.map Q.sumTy) (Q.sumTy t)
  | _, _, .here => .here
  | _, _, .there v => .there (sumVar Q v)

/-- The mapped argument variables of an operation of `d`. -/
def sumArgsInl (Q : PartialBlockLowering e d) {Γ : Ctxt (Dialect.sum d e)} :
    {ts : List d.Ty} → HVector (fun t => Var Γ t) (ts.map (Sum.inl (β := e.Ty))) →
    HVector (fun t => Var (d := d) (Γ.map Q.sumTy) t) ts
  | [], _ => .nil
  | _ :: _, .cons v vs => .cons (Q.sumVar v) (sumArgsInl Q vs)

/-- The renaming of the mapped argument context of an operation of `e` to its mapped
    argument variables. -/
def sumArgHom (Q : PartialBlockLowering e d) (hnil : Q.mapCtx [] = [])
    {Γ : Ctxt (Dialect.sum d e)} :
    (ts : List e.Ty) → HVector (fun t => Var Γ t) (ts.map (Sum.inr (α := d.Ty))) →
    Ctxt.Hom (Q.mapCtx ts) (Γ.map Q.sumTy)
  | [], _ => fun v => nomatch castHom hnil v
  | t :: ts, .cons a as => fun v =>
      consHom (sumArgHom Q hnil ts as) (Q.sumVar a) (castHom (Q.mapCtx_cons t ts) v)

/-- The variables of a context `ts`, renamed by `f`, as an argument vector. -/
def varsOf {Γ : Ctxt e} : (ts : List e.Ty) → Ctxt.Hom ts Γ → HVector (fun t => Var Γ t) ts
  | [], _ => .nil
  | _ :: ts, f => .cons (f .here) (varsOf ts (fun v => f (.there v)))

/-- The expression of the operation `o` on its own argument context. -/
def opExpr (o : e.Op) : Expr e (DialectSignature.sig o) (DialectSignature.ret o) :=
  ⟨o, rfl, varsOf _ (fun v => v)⟩

/-- A proof that a context is empty, when it is. -/
def nilEq? (Δ : Ctxt d) : Option (PLift (Δ = [])) :=
  match Δ with
  | [] => some ⟨rfl⟩
  | _ :: _ => none

/-- The block of an expression of the coproduct. -/
def sumBlock? (Q : PartialBlockLowering e d) : {Γ : Ctxt (Dialect.sum d e)} →
    {t : (Dialect.sum d e).Ty} → Expr (Dialect.sum d e) Γ t →
    Option (Com d (Γ.map Q.sumTy) (Q.sumTy t))
  | _, _, ⟨.inl o, h, args⟩ =>
      some (congrArg Q.sumTy h ▸
        Com.var ⟨o, rfl, Q.sumArgsInl (ts := DialectSignature.sig o) args⟩ (.ret .here))
  | _, _, ⟨.inr o, h, args⟩ =>
      (nilEq? (Q.mapCtx [])).bind fun hn =>
        (Q.lowerExprBlock? (opExpr o)).map fun blk =>
          congrArg Q.sumTy h ▸ Com.rename (Q.sumArgHom hn.down (DialectSignature.sig o) args) blk

/-- **Elimination of the right summand.** The partial block lowering of
    `Dialect.sum d e` to `d` that keeps the operations of `d` and lowers the operations of
    `e` by `Q`. -/
def sumElimId (Q : PartialBlockLowering e d) : PartialBlockLowering (Dialect.sum d e) d where
  mapTy := Q.sumTy
  mapCtx := List.map Q.sumTy
  mapCtx_cons := fun _ _ => rfl
  mapVar := Q.sumVar
  lowerExprBlock? := Q.sumBlock?

end Defs

/-! ## 2. The transports -/

section Transport

variable {d e : Dialect.{0, 0}} [DialectSignature d] [DialectSignature e] [TyDenote d.Ty]
  [TyDenote e.Ty]

/-- The value transport: the identity on a value of `d`, the transport `tr` of `Q` on a
    value of `e`. -/
def sumTransTy (Q : PartialBlockLowering e d) (tr : Q.TransTy) :
    {t : (Dialect.sum d e).Ty} → ⟦t⟧ → ⟦Q.sumTy t⟧
  | .inl _, x => x
  | .inr _, x => tr x

/-- The valuation transport: `sumTransTy` at every variable. -/
def sumMapVal (Q : PartialBlockLowering e d) (tr : Q.TransTy) {Γ : Ctxt (Dialect.sum d e)}
    (V : Valuation Γ) : Valuation (d := d) (Γ.map Q.sumTy) :=
  transArgs Q.sumTy (Q.sumTransTy tr) V

/-- A mapped variable reads the transported value. -/
theorem lookup_sumVar (Q : PartialBlockLowering e d) (tr : Q.TransTy) :
    ∀ {Γ : Ctxt (Dialect.sum d e)} {t : (Dialect.sum d e).Ty} (v : Var Γ t) (V : Valuation Γ),
      (Q.sumVar v).lookup (Q.sumMapVal tr V) = Q.sumTransTy tr (v.lookup V)
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ xs => lookup_sumVar Q tr v xs

/-- The variable leaf of `sumElimId`. -/
theorem sumElimId_varTransports (Q : PartialBlockLowering e d) (tr : Q.TransTy) :
    Q.sumElimId.VarTransports (Q.sumTransTy tr) (Q.sumMapVal tr) :=
  fun v V => lookup_sumVar Q tr v V

/-- The binding leaf of `sumElimId`. -/
theorem sumElimId_mapValExtends (Q : PartialBlockLowering e d) (tr : Q.TransTy) :
    Q.sumElimId.MapValExtends (Q.sumTransTy tr) (Q.sumMapVal tr) :=
  fun _ _ => rfl

/-- The mapped argument variables of an operation of `d` read the argument values. -/
theorem lookupArgs_sumArgsInl (Q : PartialBlockLowering e d) (tr : Q.TransTy)
    {Γ : Ctxt (Dialect.sum d e)} (V : Valuation Γ) :
    {ts : List d.Ty} → (args : HVector (fun t => Var Γ t) (ts.map (Sum.inl (β := e.Ty)))) →
    Expr.lookupArgs (Q.sumArgsInl args) (Q.sumMapVal tr V) =
      unmapInl (e := e) (Expr.lookupArgs args V)
  | [], _ => rfl
  | _ :: _, .cons v vs =>
      congrArg₂ HVector.cons (lookup_sumVar Q tr v V) (lookupArgs_sumArgsInl Q tr V vs)

omit [DialectSignature d] [DialectSignature e] [TyDenote d.Ty] in
/-- The variables of a context renamed by `f` read the valuation pulled back along `f`. -/
theorem lookupArgs_varsOf [DialectSignature e] [DialectDenote e] {Γ : Ctxt e} :
    (ts : List e.Ty) → (f : Ctxt.Hom ts Γ) → (V : Valuation Γ) →
    Expr.lookupArgs (varsOf ts f) V = pullV f V
  | [], _, _ => rfl
  | _ :: ts, f, V =>
      congrArg (HVector.cons _) (lookupArgs_varsOf ts (fun v => f (.there v)) V)

end Transport

/-! ## 3. The block leaves -/

section Blocks

variable {d e : Dialect.{0, 0}} [DialectSignature d] [DialectSignature e] [TyDenote d.Ty]
  [TyDenote e.Ty] [DialectDenote d] [DialectDenote e]

/-- The expression of an operation on its argument context denotes the operation. -/
theorem opExpr_denote (o : e.Op) (V : Valuation (d := e) (DialectSignature.sig o)) :
    (opExpr o).denote V = DialectDenote.denote o V := by
  show DialectDenote.denote o (Expr.lookupArgs (varsOf _ (fun v => v)) V) = _
  rw [lookupArgs_varsOf, pullV_id]

omit [DialectDenote e] in
/-- The renaming of `sumArgHom` pulls the transported valuation back to the transport by
    `Q` of the argument values. -/
theorem pullV_sumArgHom (Q : PartialBlockLowering e d) (tr : Q.TransTy) (mv : Q.MapVal)
    (hExt : Q.MapValExtends tr mv) (hnil : Q.mapCtx [] = [])
    {Γ : Ctxt (Dialect.sum d e)} (V : Valuation Γ) :
    (ts : List e.Ty) → (args : HVector (fun t => Var Γ t) (ts.map (Sum.inr (α := d.Ty)))) →
    pullV (Q.sumArgHom hnil ts args) (Q.sumMapVal tr V) =
      mv (unmapInr (d := d) (Expr.lookupArgs args V))
  | [], _ => valuation_ext _ _ (fun v => nomatch castHom hnil v)
  | t :: ts, .cons a as => by
      refine Eq.trans ?_
        (hExt (unmapInr (d := d) (Expr.lookupArgs as V)) (a.lookup V)).symm
      refine NFProg.eq_cast_of_lookup (Q.mapCtx_cons t ts) _ _ (fun v => ?_)
      rw [lookup_pullV]
      show (consHom (Q.sumArgHom hnil ts as) (Q.sumVar a)
        (castHom (Q.mapCtx_cons t ts) v)).lookup _ = _
      generalize castHom (Q.mapCtx_cons t ts) v = w
      cases w with
      | here => exact lookup_sumVar Q tr a V
      | there w =>
          show (Q.sumArgHom hnil ts as w).lookup (Q.sumMapVal tr V) = _
          rw [← lookup_pullV, pullV_sumArgHom Q tr mv hExt hnil V ts as]
          rfl

/-- **The block leaf of `sumElimId`.** Given the binding leaf and the block leaf of `Q` at
    the transports `tr` and `mv`, a block of `Q.sumElimId` denotes, on the transported
    valuation, the transport of the value of its expression. -/
theorem sumElimId_block (Q : PartialBlockLowering e d) (tr : Q.TransTy) (mv : Q.MapVal)
    (hExt : Q.MapValExtends tr mv)
    (hBlk : ∀ {Γ : Ctxt e} {t : e.Ty} (ex : Expr e Γ t) blk, Q.lowerExprBlock? ex = some blk →
      ∀ V : Valuation Γ, blk.denote (mv V) = tr (ex.denote V))
    {Γ : Ctxt (Dialect.sum d e)} {t : (Dialect.sum d e).Ty} (ex : Expr (Dialect.sum d e) Γ t)
    (blk : Com d (Q.sumElimId.mapCtx Γ) (Q.sumElimId.mapTy t))
    (hb : Q.sumElimId.lowerExprBlock? ex = some blk) (V : Valuation Γ) :
    blk.denote (Q.sumMapVal tr V) = Q.sumTransTy tr (ex.denote V) := by
  obtain ⟨op, rfl, args⟩ := ex
  cases op with
  | inl o =>
      cases hb
      show DialectDenote.denote o (Expr.lookupArgs (Q.sumArgsInl args) (Q.sumMapVal tr V)) =
        DialectDenote.denote o (unmapInl (e := e) (Expr.lookupArgs args V))
      rw [lookupArgs_sumArgsInl]
  | inr o =>
      obtain ⟨hn, _, hb⟩ := Option.bind_eq_some_iff.mp hb
      obtain ⟨blk0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
      show (Com.rename (Q.sumArgHom hn.down _ args) blk0).denote (Q.sumMapVal tr V) =
        tr (DialectDenote.denote o (unmapInr (d := d) (Expr.lookupArgs args V)))
      rw [Com.denote_rename, pullV_sumArgHom Q tr mv hExt]
      exact (hBlk (opExpr o) blk0 h0 _).trans (congrArg (fun x => tr x) (opExpr_denote o _))

/-- **The block leak leaf of `sumElimId`.** Given the binding leaf and the block leak leaf
    of `Q` from the model `N` of `e` to the model `M` of `d`, a block of `Q.sumElimId` emits
    in `M`, on the transported valuation, the events of its expression in `sumLeak M N`. -/
theorem sumElimId_blockLeak (M : LeakModel d) (N : LeakModel e)
    (Q : PartialBlockLowering e d) (tr : Q.TransTy) (mv : Q.MapVal)
    (hExt : Q.MapValExtends tr mv)
    (hLeak : ∀ {Γ : Ctxt e} {t : e.Ty} (ex : Expr e Γ t) blk,
      Q.lowerExprBlock? ex = some blk →
      ∀ V : Valuation Γ, Com.ctLeak M blk (mv V) = Expr.ctLeak N ex V)
    {Γ : Ctxt (Dialect.sum d e)} {t : (Dialect.sum d e).Ty} (ex : Expr (Dialect.sum d e) Γ t)
    (blk : Com d (Q.sumElimId.mapCtx Γ) (Q.sumElimId.mapTy t))
    (hb : Q.sumElimId.lowerExprBlock? ex = some blk) (V : Valuation Γ) :
    Com.ctLeak M blk (Q.sumMapVal tr V) = Expr.ctLeak (sumLeak M N) ex V := by
  obtain ⟨op, rfl, args⟩ := ex
  cases op with
  | inl o =>
      cases hb
      show opLeak M o (Expr.lookupArgs (Q.sumArgsInl args) (Q.sumMapVal tr V)) ++ [] =
        opLeak (sumLeak M N) (.inl o) (Expr.lookupArgs args V)
      rw [lookupArgs_sumArgsInl, opLeak_inl, List.append_nil]
  | inr o =>
      obtain ⟨hn, _, hb⟩ := Option.bind_eq_some_iff.mp hb
      obtain ⟨blk0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
      show Com.ctLeak M (Com.rename (Q.sumArgHom hn.down _ args) blk0) (Q.sumMapVal tr V) =
        opLeak (sumLeak M N) (.inr o) (Expr.lookupArgs args V)
      rw [NFProg.Com.ctLeak_rename_pullV, pullV_sumArgHom Q tr mv hExt, opLeak_inr]
      refine (hLeak (opExpr o) blk0 h0 _).trans ?_
      show opLeak N o (Expr.lookupArgs (varsOf _ (fun v => v)) _) = _
      rw [lookupArgs_varsOf, pullV_id]

end Blocks

end PartialBlockLowering

end CatCrypt.Crypto.SecureCompilation.VIR
