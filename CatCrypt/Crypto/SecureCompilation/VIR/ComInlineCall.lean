/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.ComInline
public import CatCrypt.Crypto.SecureCompilation.VIR.ComInline
public meta import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

/-!
# `func.call` / `.Lcall` inlining for the A-normal `Com` export path

The A-normal `Com` export-faithfulness theorems (`loopMem_export_faithful` and the
straight-line faithfulness it composes with) are **call-free**: they linearize a `Com`
whose body is a straight-line chain of `Lopn`s (`straightOpsMem_isLopn`). A deployed EC
ladder body instead `call`s a linked leaf — the loop body is a sibling
`.Lcall x25519_mono_step`, and the field ops call `fe25519_{mul,sqr}` — lowered to a real
`LinstrR.Lcall`. Faithfulness at that layer needs the inter-procedural region-call machine
model (`calleeLeaf_export_com_denote`).

Crypto call graphs are **shallow and static** (non-recursive leaves): so rather than
inter-procedural denotation, we **inline** the call. This module supplies the `func.call`
capability as a `Com → Com` transform: replace a `.var (extCall f args) body` — the
`Com`-level node the ABI lowers to a linked `.Lcall f` — by the callee's whole body
spliced in at the call site, yielding a **call-free** `Com` whose denotation is unchanged,
which the existing call-free export path handles directly.

## Relation to `ComInline`

`ComInline.inline` already eliminates `extCall` nodes denote-preservingly
(`ComInline.inline_preserves_denote`), but only for **single-expression** callee bodies
(`SingleExprBody = .var defExpr (.ret .here)` — one op). A real ladder step callee
(`x25519_mono_step`, a whole block of `fe25519` word ops) is a **multi-binding** `Com`.
`ComInline`'s docstring places this case outside its scope ("general inlining … requires
Com-level splicing through `Com.foldVar`"). This module supplies it, reusing the
dialect-generic block-splice primitive
`FieldDialectBlockDescent.spliceCom` (the `Com` let-composition, `spliceCom_denote`) and
`ComInline.argHom` (the call's args → formal substitution).

## What is proved (all goals closed)

* `inlineCallCom` — splice a statically-known callee `Com` (renamed through the call's
  args) ahead of the continuation.
* `inlineCallCom_denote` — the inlined program denotes to `let r := callee(args) in body`.
* `callExpr_denote` — an `extCall` node denotes to `jasminExtSem` on the looked-up args.
* `inlineLcall_denote` — **the headline.** For a callee `Com` consistent with the external
  leaf `name` (`CalleeConsistent`), the inlined **call-free** program denotes identically
  to the original `.var (extCall name …) body` (the with-call program). Any
  statically-known non-recursive callee; multi-binding body.
* `inlineCalls` / `inlineCalls_preserves_denote` — the whole-`Com` single pass inlining
  every registered head call; on a body whose registered callees are themselves call-free
  it produces a call-free `Com` denote-equivalent to the original.
* `denoteSubst` / `inlineCalls_denote_eq_denoteSubst` — the leaf-agnostic whole-`Com`
  law: the inlined program denotes to `Com.denote` with each registered head `extCall`
  node interpreted by the registry's callee `Com` value rather than by `jasminExtSem`.
  Carries no registry-consistency hypothesis, so it holds for the `.reg 64` leaves whose
  `jasminExtSem` arm is the opaque default (where `inlineCalls_preserves_denote` is
  vacuous).

All proofs are structural. No open goals, no `native_decide`, no new axioms.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComInlineCall

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.ComInline (argHom argsLookup)

/-! ## 1. `pullV` along the args-substitution hom

`FieldDialectBlockDescent.Com.denote_rename` is stated over `FieldDialectBlockDescent.pullV`
(the dialect-generic pullback). We need its value on `argHom args`: the formals' valuation
`Expr.lookupArgs args V`. This is the generic-`pullV` analogue of `ComInline.pullV_argHom`. -/

/-- The pullback of `V` along `argHom args` is the looked-up args valuation. -/
theorem pullV_argHom {Γ : Ctxt jasminDialect} {argTys : List JasminTy}
    (args : HVector (fun ty => Ctxt.Var Γ ty) argTys) (V : Ctxt.Valuation Γ) :
    FieldDialectBlockDescent.pullV (argHom args) V = Expr.lookupArgs args V := by
  induction args with
  | nil => rfl
  | @cons t ts v rest ih =>
    show HVector.cons _ _ = HVector.cons _ _
    congr 1

/-! ## 2. Multi-binding callee bodies and the call-inline transform -/

/-- A statically-known callee: its whole body is a `Com` over the formal parameter types. -/
structure FunBodyN where
  /-- Formal parameter types. -/
  argTys : List JasminTy
  /-- Return type. -/
  retTy  : JasminTy
  /-- The callee body: a whole `Com` over the formals (multi-binding allowed). -/
  body   : Com jasminDialect argTys retTy

/-- **The call inline.** Inline a statically-known callee at a call site: rename the
    callee's whole body into the caller context via the args (`argHom`), then splice it
    ahead of the continuation `body`, binding the callee's result at the head. The result
    is call-free whenever the callee body is. -/
def inlineCallCom {Γ : Ctxt jasminDialect} {argTys : List JasminTy}
    {retTy t : JasminTy}
    (cCallee : Com jasminDialect argTys retTy)
    (args : HVector (fun ty => Ctxt.Var Γ ty) argTys)
    (body : Com jasminDialect (retTy :: Γ) t) :
    Com jasminDialect Γ t :=
  spliceCom (Com.rename (argHom args) cCallee) body

/-- **Call-inline denotation.** The inlined program equals `let r := callee(args) in body`:
    `body` evaluated with the callee's result (on the looked-up args) bound at the head. -/
theorem inlineCallCom_denote {Γ : Ctxt jasminDialect} {argTys : List JasminTy}
    {retTy t : JasminTy}
    (cCallee : Com jasminDialect argTys retTy)
    (args : HVector (fun ty => Ctxt.Var Γ ty) argTys)
    (body : Com jasminDialect (retTy :: Γ) t)
    (V : Ctxt.Valuation Γ) :
    (inlineCallCom cCallee args body).denote V
      = body.denote (Ctxt.Valuation.extend V
          (cCallee.denote (Expr.lookupArgs args V))) := by
  unfold inlineCallCom
  rw [spliceCom_denote, Com.denote_rename, pullV_argHom]

/-! ## 3. The `extCall` node it eliminates -/

/-- The `Com`-level call node: an `extCall name` on the given args. This is the node the
    ABI export lowers to a linked `LinstrR.Lcall name` for a deployed leaf. -/
def callExpr {Γ : Ctxt jasminDialect} {argTys : List JasminTy} {retTy : JasminTy}
    (name : String) (args : HVector (fun ty => Ctxt.Var Γ ty) argTys) :
    Expr jasminDialect Γ retTy :=
  ⟨JasminOp.extCall name argTys retTy, rfl, args⟩

/-- An `extCall` node denotes to the external leaf semantics on the looked-up args. -/
theorem callExpr_denote {Γ : Ctxt jasminDialect} {argTys : List JasminTy}
    {retTy : JasminTy}
    (name : String) (args : HVector (fun ty => Ctxt.Var Γ ty) argTys)
    (V : Ctxt.Valuation Γ) :
    (callExpr name args).denote V
      = jasminExtSem name argTys retTy (Expr.lookupArgs args V) := rfl

/-! ## 4. The headline: eliminating a statically-known call preserves denotation -/

/-- Callee consistency: the callee `Com` computes the external leaf semantics `name` on
    any valuation of the formals. This is the multi-binding analogue of
    `ComInline.RegistryConsistent`; for a deployed leaf it is the leaf's own KAT
    (`fb.body.denote = jasminExtSem name …`), carried alongside the emit. -/
def CalleeConsistent (name : String) (fb : FunBodyN) : Prop :=
  ∀ V : Ctxt.Valuation (d := jasminDialect) fb.argTys,
    fb.body.denote V = jasminExtSem name fb.argTys fb.retTy V

/-- **`inlineLcall_denote`.** For a callee `fb` consistent with the external leaf `name`,
    the inlined **call-free** program (`inlineCallCom fb.body args body`) denotes identically
    to the original with-call program `.var (extCall name …) body`. Any statically-known
    non-recursive callee; the callee body may be multi-binding. This is the `func.call`
    capability: a `.var (extCall)`/`.Lcall` node is replaced by a call-free `Com` with the
    same denotation, feeding the (call-free) export-faithfulness path. -/
theorem inlineLcall_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (name : String) (fb : FunBodyN) (hcon : CalleeConsistent name fb)
    (args : HVector (fun ty => Ctxt.Var Γ ty) fb.argTys)
    (body : Com jasminDialect (fb.retTy :: Γ) t)
    (V : Ctxt.Valuation Γ) :
    (inlineCallCom fb.body args body).denote V
      = (Com.var (callExpr name args) body).denote V := by
  rw [inlineCallCom_denote, hcon (Expr.lookupArgs args V)]
  rfl

/-! ## 5. Whole-`Com` single-pass inlining of every registered head call

The registry maps a call name to its callee body. `inlineCalls` walks the `Com` and, at
each `.var (extCall name argTys retTy) body` whose `name` is registered with matching
types, splices in the callee (via `inlineCallCom`) and recurses into `body`; otherwise it
keeps the node and recurses. On a caller whose registered callees are themselves call-free
(the shallow, static crypto call graph), one pass yields a call-free `Com`. -/

/-- The multi-binding function registry. -/
abbrev FuncRegistryN := String → Option FunBodyN

/-- Name of an `extCall` op (any other op maps to a reserved sentinel never registered). -/
def extCallName : JasminOp → String
  | .extCall name _ _ => name
  | _ => ""

/-- Whole-`Com` single pass: inline every registered head call. -/
def inlineCalls (R : FuncRegistryN) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Com jasminDialect Γ t
  | _, _, .ret v => .ret v
  | Γ, t, .var (t := bs) e body =>
    match e_op : e.op, R (extCallName e.op) with
    | .extCall name eArgTys eRetTy, some fb =>
      if hArg : fb.argTys = eArgTys then
        if hRet : fb.retTy = bs then
          -- View `e.args` as `HVector (Var Γ) fb.argTys` and splice the callee.
          let argsV : HVector (fun ty => Ctxt.Var Γ ty) fb.argTys :=
            hArg ▸ (show HVector (fun ty => Ctxt.Var Γ ty)
                        (DialectSignature.sig (.extCall name eArgTys eRetTy))
                    from e_op ▸ e.args)
          let bodyV : Com jasminDialect (fb.retTy :: Γ) t := hRet ▸ inlineCalls R body
          inlineCallCom fb.body argsV bodyV
        else .var e (inlineCalls R body)
      else .var e (inlineCalls R body)
    | _, _ => .var e (inlineCalls R body)

/-- Registry consistency: every registered callee computes its external leaf. -/
def RegistryConsistentN (R : FuncRegistryN) : Prop :=
  ∀ (name : String) (fb : FunBodyN), R name = some fb → CalleeConsistent name fb

/-- **Whole-`Com` inlining preserves denotation.** Under registry consistency, the
    single pass `inlineCalls R` — which replaces every registered head `extCall` node
    (the `.Lcall` the ABI would emit) with the callee's spliced-in body — denotes
    identically to the original `Com`. Composed at every call node, this turns a
    `.Lcall`-containing body into a call-free `Com` (when the registered callees are
    themselves call-free) with the same denotation, feeding the call-free export path. -/
theorem inlineCalls_preserves_denote (R : FuncRegistryN)
    (hR : RegistryConsistentN R) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
    (V : Ctxt.Valuation Γ) →
    (inlineCalls R c).denote V = c.denote V
  | _, _, .ret v, _ => rfl
  | Γ, t, .var (t := bs) e body, V => by
    obtain ⟨op, retTy_eq, args⟩ := e
    have ih := inlineCalls_preserves_denote R hR body
    cases op
    case extCall name eArgTys eRetTy =>
      cases hRname : R name with
      | none =>
        simp only [inlineCalls, extCallName, hRname, Com.denote, ih]
      | some fb =>
        by_cases hArg : fb.argTys = eArgTys
        · by_cases hRet : fb.retTy = bs
          · -- The inline branch fires: splice the callee, then use its consistency.
            simp only [inlineCalls, extCallName, hRname]
            rw [dite_eq_left hArg, dite_eq_left hRet]
            subst hArg; subst hRet
            have hre : eRetTy = fb.retTy := retTy_eq
            subst hre
            rw [inlineCallCom_denote, ih, hR name fb hRname (Expr.lookupArgs args V)]
            rfl
          · simp only [inlineCalls, extCallName, hRname, dite_eq_left hArg, dite_eq_right hRet,
              Com.denote, ih]
        · simp only [inlineCalls, extCallName, hRname, dite_eq_right hArg, Com.denote, ih]
    all_goals (simp only [inlineCalls, Com.denote, ih])

/-! ## 6. Leaf-agnostic whole-`Com` denotation of the inlined program

`inlineCalls_preserves_denote` is gated on `RegistryConsistentN`, which for a
`.reg 64` leaf demands `fb.body.denote V = jasminExtSem name … V`; the
`jasminExtSem` return arm for `.reg 64` is the catch-all `JasminTy.default`, so
that side condition is refutable and the theorem is vacuous for such leaves. The
result below carries no consistency hypothesis: it characterizes the fused `Com`'s
denotation directly in terms of the registry's callee `Com` values.

`denoteSubst R c V` interprets `c` exactly as `Com.denote`, except at each
registered head `extCall name` node — where `inlineCalls` splices the callee — it
binds the callee `Com`'s own value `fb.body.denote (lookupArgs args V)` in place of
the opaque `jasminExtSem name … value`. `inlineCalls_denote_eq_denoteSubst` shows
the inlined program denotes to this substituted interpreter, unconditionally. -/

/-- `Com.denote` with each registered head `extCall` node interpreted by the
    registry's callee `Com` value (`fb.body.denote` on the looked-up args) rather
    than by `jasminExtSem`. Mirrors `inlineCalls`: at a registered call node with
    matching argument and return types it binds the callee value; every other node
    (unregistered, type-mismatched, or non-`extCall`) denotes as in `Com.denote`. -/
def denoteSubst (R : FuncRegistryN) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Ctxt.Valuation Γ → ⟦t⟧
  | _, _, .ret v, V => v.lookup V
  | Γ, _t, .var (t := bs) e body, V =>
    match e_op : e.op, R (extCallName e.op) with
    | .extCall name eArgTys eRetTy, some fb =>
      if hArg : fb.argTys = eArgTys then
        if hRet : fb.retTy = bs then
          let argsV : HVector (fun ty => Ctxt.Var Γ ty) fb.argTys :=
            hArg ▸ (show HVector (fun ty => Ctxt.Var Γ ty)
                        (DialectSignature.sig (.extCall name eArgTys eRetTy))
                    from e_op ▸ e.args)
          denoteSubst R body
            (Ctxt.Valuation.extend V (hRet ▸ fb.body.denote (Expr.lookupArgs argsV V)))
        else denoteSubst R body (Ctxt.Valuation.extend V (e.denote V))
      else denoteSubst R body (Ctxt.Valuation.extend V (e.denote V))
    | _, _ => denoteSubst R body (Ctxt.Valuation.extend V (e.denote V))

/-- **Leaf-agnostic whole-`Com` inlining law.** The single pass `inlineCalls R` — which
    splices in the callee body at every registered head `extCall` node — denotes to the
    substituted interpreter `denoteSubst R`, which binds each such callee's own `Com`
    value. No registry-consistency side condition: unlike `inlineCalls_preserves_denote`
    it does not equate the callee value with `jasminExtSem`, so it holds for the width-64
    (`.reg 64`) leaves whose `jasminExtSem` arm is the opaque default. -/
theorem inlineCalls_denote_eq_denoteSubst (R : FuncRegistryN) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
    (V : Ctxt.Valuation Γ) →
    (inlineCalls R c).denote V = denoteSubst R c V
  | _, _, .ret v, _ => rfl
  | Γ, t, .var (t := bs) e body, V => by
    obtain ⟨op, retTy_eq, args⟩ := e
    have ih := inlineCalls_denote_eq_denoteSubst R body
    cases op
    case extCall name eArgTys eRetTy =>
      cases hRname : R name with
      | none =>
        simp only [inlineCalls, denoteSubst, extCallName, hRname, Com.denote, ih]
      | some fb =>
        by_cases hArg : fb.argTys = eArgTys
        · by_cases hRet : fb.retTy = bs
          · simp only [inlineCalls, denoteSubst, extCallName, hRname,
              dite_eq_left hArg, dite_eq_left hRet]
            subst hArg; subst hRet
            have hre : eRetTy = fb.retTy := retTy_eq
            subst hre
            rw [inlineCallCom_denote, ih]
          · simp only [inlineCalls, denoteSubst, extCallName, hRname, dite_eq_left hArg,
              dite_eq_right hRet, Com.denote, ih]
        · simp only [inlineCalls, denoteSubst, extCallName, hRname, dite_eq_right hArg,
            Com.denote, ih]
    all_goals (simp only [inlineCalls, denoteSubst, Com.denote, ih])

/-- The substituted denotation of a single registered leaf call followed by the return
    of its result: the leaf `Com`'s own value on the call args. The `callExpr` return
    type is the callee's `retTy`, so the registered inline branch of `denoteSubst`
    fires. Discharges the concrete whole-`Com` fusion consequence for a one-call
    orchestration loop-body without reducing the registry lookup by hand. -/
theorem denoteSubst_matchedCall {Γ : Ctxt jasminDialect}
    (R : FuncRegistryN) (name : String) (fb : FunBodyN)
    (args : HVector (fun ty => Ctxt.Var Γ ty) fb.argTys)
    (hR : R name = some fb) (V : Ctxt.Valuation Γ) :
    denoteSubst R (Com.var (callExpr (retTy := fb.retTy) name args) (Com.ret .here)) V
      = fb.body.denote (Expr.lookupArgs args V) := by
  simp only [denoteSubst, callExpr, extCallName, hR, dite_eq_left]
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.ComInlineCall
