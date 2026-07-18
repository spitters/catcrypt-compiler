/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.KernelSyntax

/-!
# `kernel%` DELABORATOR — the inverse of the typed symbol-table elaborator

`VIR/KernelSyntax.lean` elaborates the named-variable `kernel%` surface into an
intrinsically-typed `Com` leaf: it resolves each named use to its de-Bruijn
`Ctxt.Var` (`.there^i .here`) against a compile-time scope. This file builds the
**inverse**: a `@[delab]` handler that renders a `Com d Γ t` back as `kernel%`
concrete syntax, so an existing leaf **displays** as the reviewable surface.

Names are erased when the elaborator runs — a `Com` term carries only de-Bruijn
indices, not the source identifiers. The delaborator therefore recovers
**positional** names: it re-seeds a scope from the leaf's formal context `Γ`
(formal `i` ↦ `v{i}`, matching the elaborator's "`formals[i]` is de-Bruijn index
`i`"), and each `Com.var` binding gets a fresh `x{k}`. Because the elaborator
resolves names *by position*, any internally-consistent renaming reconstructs the
identical `Com`; positional names round-trip exactly (`elab (delab t) = t`).
Recovering the *original* identifiers would require them to be stored in the term
(an annotation / name side-table the `Com` framework does not carry) — see the
report. §2 pins faithfulness with `#guard_msgs` render checks + `rfl` round-trips.

## How the recovery mirrors the elaborator's scope

`Com.var (e : Expr d Γ t) (body : Com d (t :: Γ) s)` binds its result at the
front of the context, so de-Bruijn `0` (`.here`) is always the most-recent name.
Walking the `Com`:

* the outer node's `Γ` seeds `scope = #[v0, …, v_{n-1}]` (position `i` = index `i`);
* each `Com.var` **prepends** a fresh `x{k}` (it becomes index `0`);
* a `Ctxt.Var` argument resolves by counting `.there`s to an index, then reading
  `scope[index]` — the exact reverse of `resolveVar`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KernelDelab

open Lean Lean.PrettyPrinter Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.KernelSyntax

/-! ## 1. The delaborator -/

/-- De-Bruijn index of a `Ctxt.Var` Expr: count the `.there` wrappers around the
    innermost `.here`. `none` if the Expr is not a `Ctxt.Var` literal. -/
private partial def varIndex? (e : Lean.Expr) : Option Nat :=
  match e.getAppFn.constName? with
  | some ``Ctxt.Var.here  => some 0
  | some ``Ctxt.Var.there => (varIndex? e.appArg!).map (· + 1)
  | _                     => none

/-- Flatten an `HVector.cons … .nil` Expr spine into its head Exprs (in order). -/
private partial def hvArgs (e : Lean.Expr) : List Lean.Expr :=
  match e.getAppFn.constName? with
  | some ``HVector.cons =>
      -- @HVector.cons α f t ts head tail
      let a := e.getAppArgs
      a[4]! :: hvArgs a[5]!
  | _ => []

/-- Flatten a `List.cons … List.nil` Expr spine into its element Exprs (in order). -/
private partial def listArgs (e : Lean.Expr) : List Lean.Expr :=
  match e.getAppFn.constName? with
  | some ``List.cons =>
      -- @List.cons α head tail
      let a := e.getAppArgs
      a[1]! :: listArgs a[2]!
  | _ => []

/-- Fold the `Com.var … (Com.ret …)` chain into a `kstmt` list, threading the
    positional scope (`scope[i]` = the ident currently at de-Bruijn index `i`). -/
private partial def buildStmts (scope : Array Ident) (depth : Nat) (e : Lean.Expr) :
    DelabM (Array (TSyntax `kstmt)) := do
  match e.getAppFn.constName? with
  | some ``Com.ret =>
      -- @Com.ret d inst Γ t v
      let v := e.getAppArgs[4]!
      let some i := varIndex? v | failure
      let some nm := scope[i]? | failure
      return #[← `(kstmt| ret $nm)]
  | some ``Com.var =>
      -- @Com.var d inst Γ t s e body
      let args := e.getAppArgs
      let exprE := args[5]!
      let body  := args[6]!
      -- @Expr.mk d inst Γ t op retTy_eq args
      let eArgs := exprE.getAppArgs
      let opE   := eArgs[4]!
      let argsE := eArgs[6]!
      let opStx ← Lean.PrettyPrinter.delab opE
      let argVars := hvArgs argsE
      let argIdents ← argVars.mapM fun v => do
        let some i := varIndex? v | failure
        let some nm := scope[i]? | failure
        pure nm
      let nm : Ident := mkIdent (Name.mkSimple s!"x{depth}")
      let argArr := argIdents.toArray
      let stmt ← `(kstmt| $nm:ident := ($opStx) [$argArr,*])
      let rest ← buildStmts (#[nm] ++ scope) (depth + 1) body
      return #[stmt] ++ rest
  | _ => failure

/-- Render a `Com d Γ t` Expr as `kernel%` surface. Registered for both entry
    constructors so any top-level `Com` fires it; inner nodes are consumed by
    the manual walk, not re-dispatched. -/
private def delabKernelCom : Delab := do
  let e ← getExpr
  let cn := e.getAppFn.constName?
  unless cn == some ``Com.var || cn == some ``Com.ret do failure
  -- Γ is arg index 2 of both Com.var and Com.ret.
  let γE := e.getAppArgs[2]!
  let tys := listArgs γE
  -- Seed scope: formal i ↦ v{i} at de-Bruijn index i.
  let formalIdents : Array Ident := (Array.range tys.length).map (fun i => mkIdent (Name.mkSimple s!"v{i}"))
  let formals ← (tys.toArray.zip formalIdents).mapM fun (tyE, nm) => do
    let tyStx ← Lean.PrettyPrinter.delab tyE
    `(kformal| ($nm : $tyStx))
  let stmts ← buildStmts formalIdents 0 e
  `(kernel% $[$formals]* { $[$stmts];* })

attribute [delab app.CatCrypt.Crypto.SecureCompilation.VIR.Com.var] delabKernelCom
attribute [delab app.CatCrypt.Crypto.SecureCompilation.VIR.Com.ret] delabKernelCom

/-! ## 2. Faithfulness — render pins + `elab (delab t) = t` round-trips

`macColHand` / `addLimbHand` (hand-written `Com` leaves, imported from
`KernelSyntax`) now **display** as `kernel%` via the delaborator above. The
`#guard_msgs` blocks pin that rendered surface; the round-trip defs copy that
surface back and prove it re-elaborates to the same `Com` (`:= rfl`). Positional
names (`v0…`, `x0…`) round-trip exactly. -/

section Roundtrip
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/--
info: def CatCrypt.Crypto.SecureCompilation.VIR.KernelSyntax.macColHand : Com jasminDialect
  [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64] (JasminTy.reg 64) :=
kernel%
  (v0 :
    JasminTy.reg
      64)(v1 :
    JasminTy.reg
      64)(v2 :
    JasminTy.reg
      64)(v3 :
    JasminTy.reg
      64){x0 := (JasminOp.regArith JasminBinOp.mul 64)[v2,
    v3];x1 := (JasminOp.regArith JasminBinOp.add 64)[v0, x0];ret x1}
-/
#guard_msgs (whitespace := lax) in
#print macColHand

/-- The delaborated surface of `macColHand`, re-elaborated: `elab (delab t) = t`. -/
def macColRoundtrip : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  kernel% (v0 : .reg 64) (v1 : .reg 64) (v2 : .reg 64) (v3 : .reg 64) {
    x0 := (JasminOp.regArith .mul 64) [v2, v3];
    x1 := (JasminOp.regArith .add 64) [v0, x0];
    ret x1
  }

/-- **Round-trip (shape 1).** Re-elaborating the delaborated `kernel%` surface of
    `macColHand` yields `macColHand` back — `rfl`. -/
theorem macColRoundtrip_eq : macColRoundtrip = macColHand := rfl

/-- The delaborated surface of `addLimbHand`, re-elaborated. -/
def addLimbRoundtrip : Com jasminDialect [.stackArr 64 5, .stackArr 64 5, .reg 64] (.reg 64) :=
  kernel% (v0 : .stackArr 64 5) (v1 : .stackArr 64 5) (v2 : .reg 64) {
    x0 := (JasminOp.stackLoad 64 5) [v0, v2];
    x1 := (JasminOp.stackLoad 64 5) [v1, v2];
    x2 := (JasminOp.regArith .add 64) [x0, x1];
    ret x2
  }

/-- **Round-trip (shape 2).** A mixed `stackArr`/`reg` context round-trips too. -/
theorem addLimbRoundtrip_eq : addLimbRoundtrip = addLimbHand := rfl

end Roundtrip

end CatCrypt.Crypto.SecureCompilation.VIR.KernelDelab
