/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety
public import CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety

/-!
# Programs with a hole on `Com`: linking, denotation and the label checker

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

On CatCrypt's ANF `Com` substrate (`VIR/Core.lean`) a program is a chain of
`var` let-bindings ending in a `ret`. A *linking context* is therefore a
**let-prefix with a typed hole** at the tail: the context binds some variables
(extending the de Bruijn context), then the hole expects a sub-`Com` as the
continuation. In ANF the tail's result type is the whole program's result type,
so the hole and the outer interface share the result type `th`.

* `ComCtx d Γh th Γ` is a context whose hole expects a `Com d Γh th` and which,
  once plugged, yields a `Com d Γ th`;
* `ComCtx.hole` is the trivial context;
* `ComCtx.var e C` binds `e : Expr d Γ tb` and continues with `C` in the
  extended context `tb :: Γ`.

`plug C p : Com d Γ th` performs the linking.

The label checker `JasminCTPredicate.ctSafeJasmin` flags only a `stackLoad` /
`stackStore` whose index register is labelled secret; every other op passes its
catch-all case. The compositionality lemmas below are facts about that checker,
not constant-time statements about a leakage semantics.

## Main results

* `ComCtx.plug_denote` — the denotation of `plug C p` is `p.denote` in the
  valuation the prefix `C` accumulates (`ComCtx.propagate`).
* `ctSafeCtxJasmin` lifts `ctSafeJasmin` to contexts, and `ctSafeJasmin_plug`
  shows `ctSafeJasmin (plug C p) L = ctSafeCtxJasmin C L && ctSafeJasmin p
  (propagateLabel C L)`; `ctSafeJasmin_plug_of` is the implication form.
* `lowerCtx` — the lowering of a lattice context to a Jasmin context, in lockstep
  with `lowerLatticeToJasmin`.
* `hostileCtx_not_ctSafe` — a context with a secret-indexed `stackLoad` fails
  `ctSafeCtxJasmin`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyContext

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. The context model: a `Com` with a typed hole

A `ComCtx d Γh th Γ` is a program *with a hole*: given any `Com d Γh th` it
produces a `Com d Γ th`. We take the faithful ANF shape — a let-prefix that binds
fresh variables (extending the de Bruijn context) and then defers to the hole as
its continuation. Because in ANF the tail's result type *is* the whole program's
result type, the hole and the output share the result type `th`. `hole` is the
trivial (identity) context; `var e C` is "bind `e`, then continue with context
`C` in the extended context". -/

/-- A typed program-with-a-hole over a dialect `d`. The hole expects a sub-program
    `Com d Γh th`; the context wraps it as a let-prefix to yield a `Com d Γ th`.
    `Γh` is the hole's input context, `Γ` the outer input context, and `th` the
    result type shared by the hole and the output (the hole is the ANF tail). -/
inductive ComCtx (d : Dialect) [DialectSignature d] :
    Ctxt d → d.Ty → Ctxt d → Type _ where
  /-- The trivial context: the hole is the whole program. The outer input context
      coincides with the hole input context. -/
  | hole {Γh : Ctxt d} {th : d.Ty} : ComCtx d Γh th Γh
  /-- Bind an expression `e`, then continue with the context `C` in the de Bruijn
      context extended by `e`'s result. The prefix supplies a fresh variable that
      the plugged program may consume. -/
  | var {Γh : Ctxt d} {th : d.Ty} {Γ : Ctxt d} {tb : d.Ty}
      (e : Expr d Γ tb) (C : ComCtx d Γh th (tb :: Γ)) :
      ComCtx d Γh th Γ

namespace ComCtx

/-- **Linking (plug).** Plug a program `p : Com d Γh th` into the hole of a
    context `C : ComCtx d Γh th Γ`, yielding the linked whole program
    `Com d Γ th`. `hole` returns `p` unchanged; `var e C` prepends the let-binding
    `e` to the linked tail. -/
def plug {d : Dialect} [DialectSignature d] :
    {Γh : Ctxt d} → {th : d.Ty} → {Γ : Ctxt d} →
    ComCtx d Γh th Γ → Com d Γh th → Com d Γ th
  | _, _, _, .hole, p => p
  | _, _, _, .var e C, p => .var e (plug C p)

@[simp]
theorem plug_hole {d : Dialect} [DialectSignature d]
    {Γh : Ctxt d} {th : d.Ty} (p : Com d Γh th) :
    plug (ComCtx.hole) p = p := by simp only [plug]

@[simp]
theorem plug_var {d : Dialect} [DialectSignature d]
    {Γh : Ctxt d} {th : d.Ty} {Γ : Ctxt d} {tb : d.Ty}
    (e : Expr d Γ tb) (C : ComCtx d Γh th (tb :: Γ)) (p : Com d Γh th) :
    plug (ComCtx.var e C) p = .var e (plug C p) := by simp only [plug]

/-! ## 2. Denotational compositionality

The denotation of a plugged program factors through the plugged program's own
denotation, evaluated in the valuation the prefix accumulates from the outer
valuation. We express the accumulated valuation by the same recursion as `plug`:
`hole` leaves the valuation unchanged; `var e C` extends it with `e.denote`. -/

/-- The valuation the context's let-prefix accumulates: starting from the outer
    valuation `V : Valuation Γ`, run the prefix's bindings to reach a valuation of
    the hole's context `Γh`. -/
def propagate {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] :
    {Γh : Ctxt d} → {th : d.Ty} → {Γ : Ctxt d} →
    (C : ComCtx d Γh th Γ) → Ctxt.Valuation Γ → Ctxt.Valuation Γh
  | _, _, _, .hole, V => V
  | _, _, _, .var e C, V => propagate C (V.extend (e.denote V))

/-- **Denotational compositionality.** The denotation of the linked program is
    the denotation of the plugged program in the valuation the prefix propagates
    from the outer valuation. This is the `Com` analogue of "evaluate the prefix,
    then run the plugged continuation". -/
theorem plug_denote {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] :
    {Γh : Ctxt d} → {th : d.Ty} → {Γ : Ctxt d} →
    (C : ComCtx d Γh th Γ) → (p : Com d Γh th) → (V : Ctxt.Valuation Γ) →
    (plug C p).denote V = p.denote (propagate C V)
  | _, _, _, .hole, _, _ => by simp only [plug_hole, propagate]
  | _, _, _, .var e C, p, V => by
      rw [plug_var, Com.denote, show propagate (ComCtx.var e C) V
            = propagate C (V.extend (e.denote V)) from by simp only [propagate]]
      exact plug_denote C p (V.extend (e.denote V))

end ComCtx

/-! ## 3. The label checker on contexts and its compositionality over linking

We lift `ctSafeJasmin` to contexts. A context passes iff every op in its
let-prefix passes, labelling each binding with the join of its argument levels
(`exprLevel`), as `ctSafeJasmin` does on `Com`. The hole imposes no constraint of
its own. `ctSafeJasmin_plug` then shows the checker is compositional over
linking. -/

/-- The label context a Jasmin context's prefix propagates: starting from a
    labelling `L` of the outer context `Γ`, label each binding with the join of
    its argument levels (as `ctSafeJasmin` does), reaching a labelling of the
    hole's context `Γh`. -/
def propagateLabel :
    {Γh : Ctxt jasminDialect} → {th : JasminTy} → {Γ : Ctxt jasminDialect} →
    (C : ComCtx jasminDialect Γh th Γ) → LabelCtxt Γ → LabelCtxt Γh
  | _, _, _, .hole, L => L
  | _, _, _, .var e C, L => propagateLabel C (L.extend (exprLevel e L))

/-- **The label checker on a context.** A Jasmin context passes under a labelling
    `L` iff every op in its let-prefix passes `ctSafeExprJasmin`, each binding
    labelled with the join of its argument levels. The hole contributes nothing.
    Mirrors `ctSafeJasmin` on `Com`, dropping the `ret` case. -/
def ctSafeCtxJasmin :
    {Γh : Ctxt jasminDialect} → {th : JasminTy} → {Γ : Ctxt jasminDialect} →
    ComCtx jasminDialect Γh th Γ → LabelCtxt Γ → Bool
  | _, _, _, .hole, _ => true
  | _, _, _, .var e C, L =>
      ctSafeExprJasmin e L && ctSafeCtxJasmin C (L.extend (exprLevel e L))

@[simp]
theorem ctSafeCtxJasmin_hole {Γh : Ctxt jasminDialect} {th : JasminTy}
    (L : LabelCtxt Γh) :
    ctSafeCtxJasmin (ComCtx.hole : ComCtx jasminDialect Γh th Γh) L = true := by
  simp only [ctSafeCtxJasmin]

@[simp]
theorem ctSafeCtxJasmin_var {Γh : Ctxt jasminDialect} {th : JasminTy}
    {Γ : Ctxt jasminDialect} {tb : JasminTy}
    (e : Expr jasminDialect Γ tb) (C : ComCtx jasminDialect Γh th (tb :: Γ))
    (L : LabelCtxt Γ) :
    ctSafeCtxJasmin (ComCtx.var e C) L
      = (ctSafeExprJasmin e L
          && ctSafeCtxJasmin C (L.extend (exprLevel e L))) := by
  simp only [ctSafeCtxJasmin]

/-- **Compositionality of the label checker over linking.** The linked program
    `plug C p` passes `ctSafeJasmin` under `L` iff the context prefix `C` passes
    under `L` and the plugged program `p` passes under the labelling `C`
    propagates. Proved by induction on `C`. -/
theorem ctSafeJasmin_plug :
    {Γh : Ctxt jasminDialect} → {th : JasminTy} → {Γ : Ctxt jasminDialect} →
    (C : ComCtx jasminDialect Γh th Γ) → (p : Com jasminDialect Γh th) →
    (L : LabelCtxt Γ) →
    ctSafeJasmin (ComCtx.plug C p) L
      = (ctSafeCtxJasmin C L && ctSafeJasmin p (propagateLabel C L))
  | _, _, _, .hole, _, L => by
      simp only [ComCtx.plug_hole, ctSafeCtxJasmin_hole, Bool.true_and, propagateLabel]
  | _, _, _, .var e C, p, L => by
      simp only [ComCtx.plug_var, ctSafeJasmin_var, ctSafeCtxJasmin_var,
        ctSafeJasmin_plug C p (L.extend (exprLevel e L)), propagateLabel, Bool.and_assoc]

/-- The implication form of `ctSafeJasmin_plug`: if the context passes and the
    plugged program passes in the propagated labelling, the linked program
    passes. -/
theorem ctSafeJasmin_plug_of {Γh : Ctxt jasminDialect} {th : JasminTy}
    {Γ : Ctxt jasminDialect}
    (C : ComCtx jasminDialect Γh th Γ) (p : Com jasminDialect Γh th)
    (L : LabelCtxt Γ)
    (hC : ctSafeCtxJasmin C L = true)
    (hp : ctSafeJasmin p (propagateLabel C L) = true) :
    ctSafeJasmin (ComCtx.plug C p) L = true := by
  simp [ctSafeJasmin_plug, hC, hp]

/-! ## 4. The lowering of lattice contexts -/

/-- Lower a lattice context to a Jasmin context along the lowering, in lockstep
    with `lowerLatticeToJasmin` on `Com`. -/
def lowerCtx {Γh : Ctxt latticeDialect} {th : LatticeTy} :
    {Γ : Ctxt latticeDialect} →
    ComCtx latticeDialect Γh th Γ →
    ComCtx jasminDialect (Γh.map tau) (tau th) (Γ.map tau)
  | _, .hole => .hole
  | _, .var e C => .var (lowerExpr e) (lowerCtx C)

/-! ## 5. A context the label checker rejects

A context that itself performs a secret-indexed `stackLoad` fails
`ctSafeCtxJasmin`. We reuse `JasminCTPredicate.loadProg`'s secret-index load as
the prefix. -/

/-- A context: a let-prefix performing a secret-indexed `stackLoad`, with a hole
    expecting the loaded value as the continuation. -/
def hostileCtx :
    ComCtx jasminDialect (.reg 16 :: JasminCTPredicate.loadCtxt) (.reg 16)
      JasminCTPredicate.loadCtxt :=
  .var (.mk (.stackLoad 16 8) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (ComCtx.hole)

/-- The context `hostileCtx` fails the label checker under the secret-index
    labelling: its prefix's `stackLoad` index register is labelled secret. -/
theorem hostileCtx_not_ctSafe :
    ctSafeCtxJasmin hostileCtx JasminCTPredicate.secretIdxLabels = false := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyContext
