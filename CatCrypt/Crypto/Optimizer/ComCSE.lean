/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.CopyProp

/-!
# Verified common-subexpression elimination for `Com` — a denotation-preserving rewrite

A **structural `Com → Com` common-subexpression-elimination pass** over the
typed VIR `jasminDialect`. It performs the `Com`-level rewrite for the
analysis-only `SecureCompilation/VIR/CommonSubexprElim.lean`: that file *decides* which binders recompute an
already-bound expression but applies the identity transform at the `Com` level
(the CSE decisions are consumed downstream as a labelling). Here the rewrite
actually rewires the body's references away from a redundant binder, with a real
denotation-preservation proof (an induction over the let-chain, reusing the de
Bruijn substitution machinery of `CopyProp`/`MergeCom`, **not** `rfl`).

## The De Bruijn obstruction and our sound scope

`Com d Γ t` is intrinsically typed: a binder introduces a fresh type at the head
of the context, and every variable below it is a `Ctxt.Var` De Bruijn index.
*Deleting* an interior redundant binder would change the intrinsic type of the
body — every subsequent `.there` index would have to shift, and references to the
deleted binder must be re-aimed at the canonical earlier binder (a full
context-permutation layer).

We take the sound scope that needs only a single, **total** redirect — the same
shape `CopyProp` uses for register copies: an **adjacent redundant binder**

    let v0 = e          let v0 = e
    let v1 = e'    ↦     let v1 = e'              (binding kept; a later DCE drops it)
    body                body[v1 := v0]

where `e' : Expr (t :: Γ) t` is `e : Expr Γ t` shifted one binding deeper
(`e' = shiftExpr e`). Because `Com` is single-static-assignment, the outer binder
`v0` always denotes the value `e.denote V`; a shifted `e'` reads exactly the same
arguments, so the inner binder `v1` denotes the **same** value as `v0`. Hence
inside `body` the inner binding (`Ctxt.Var.here`) and the shifted outer binding
(`Ctxt.Var.there .here`) look up the same valuation entry — redirecting every use
of `v1` to `v0` is denotation-preserving. This is exactly the `copyHom`/
`pullV_copyHom` redirect of `CopyProp`, instantiated at the source variable
`Ctxt.Var.there .here`.

We *keep* the redundant binder in place (so the surrounding chain's De Bruijn
shape, cost and CT facts are undisturbed); the binder is dead — every use is
redirected to `v0` — and a later dead-code pass (`ComDCE`) removes it.

## Contents

* `shiftVar` / `shiftArgs` / `shiftExpr` — push a variable / expression one
  binding deeper; the duplicate `e'` of an earlier binder `e` is `shiftExpr e`.
* `shiftExpr_denote` — a shifted expression denotes the value the original binder
  carries: `(shiftExpr e).denote (V.extend y) = e.denote V`.
* `decEqVar` / `decEqArgs` / `decEqExpr` — structural decidable equality on
  variables, argument vectors and expressions (the syntactic CSE test).
* `comCSE` — the adjacent-redundant-binder redirect, reusing `CopyProp.copyHom`.
* `comCSE_denote` — **denotation preservation**
  (`(comCSE c).denote V = c.denote V`), by induction over the let-chain, reusing
  `CopyProp.Com.denote_rename` / `pullV_copyHom`. **Not `rfl`.**
* Self-contained validation: a program with an adjacent redundant binder has its
  later uses redirected, denotation preserved.

All goals closed. No `sorry`. Axiom set inherited from `CopyProp` (the standard
Lean/Mathlib `propext` / `Quot.sound` / `Classical.choice` trio).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ComCSE

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.CopyProp

/-! ## 1. Variable shifting (build the shifted duplicate `e'`)

`shiftVar` / `shiftExpr` push a variable / expression from context `Γ` into the
extended context `s :: Γ` by adding one De Bruijn `.there`. This is how the
"adjacent duplicate" `e'` of an earlier binder `e` is constructed: `e'` reads the
same originating slots as `e`, one binding deeper. A shifted expression therefore
denotes exactly the value the earlier binder carries. -/

/-- Shift a variable into the extended context `s :: Γ`. -/
def shiftVar {Γ : Ctxt jasminDialect} {s t : JasminTy} (v : Ctxt.Var Γ t) :
    Ctxt.Var (s :: Γ) t := .there v

/-- Shift an `HVector` of argument variables into the extended context. -/
def shiftArgs {Γ : Ctxt jasminDialect} {s : JasminTy} :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys →
    HVector (fun ty => Ctxt.Var (s :: Γ) ty) tys
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (shiftVar v) (shiftArgs rest)

/-- Shift an `Expr` into the extended context `s :: Γ` (the duplicate of an
earlier binder, read one binding deeper). -/
def shiftExpr {Γ : Ctxt jasminDialect} {s t : JasminTy}
    (e : Expr jasminDialect Γ t) : Expr jasminDialect (s :: Γ) t :=
  { op := e.op, retTy_eq := e.retTy_eq, args := shiftArgs e.args }

/-- Looking up a shifted variable in an extended valuation ignores the fresh
entry. -/
theorem shiftVar_lookup {Γ : Ctxt jasminDialect} {s t : JasminTy}
    (v : Ctxt.Var Γ t) (V : Ctxt.Valuation Γ) (y : ⟦s⟧) :
    (shiftVar (s := s) v).lookup (V.extend y) = v.lookup V := rfl

/-- Looking up shifted arguments in an extended valuation equals looking up the
originals. -/
theorem shiftArgs_lookupArgs {Γ : Ctxt jasminDialect} {s : JasminTy}
    (V : Ctxt.Valuation Γ) (y : ⟦s⟧) :
    ∀ {tys : List JasminTy} (args : HVector (fun ty => Ctxt.Var Γ ty) tys),
      Expr.lookupArgs (shiftArgs (s := s) args) (V.extend y) =
      Expr.lookupArgs args V
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show Expr.lookupArgs (.cons (shiftVar v) (shiftArgs rest)) (V.extend y) = _
      rw [Expr.lookupArgs, Expr.lookupArgs, shiftVar_lookup v V y,
        shiftArgs_lookupArgs V y rest]

/-- **A shifted expression denotes the earlier binder's value.**
`(shiftExpr e).denote (V.extend y) = e.denote V` — the shift reads the same
arguments, one binding deeper, so the fresh entry `y` is never observed. -/
theorem shiftExpr_denote {Γ : Ctxt jasminDialect} {s t : JasminTy}
    (e : Expr jasminDialect Γ t) (V : Ctxt.Valuation Γ) (y : ⟦s⟧) :
    (shiftExpr (s := s) e).denote (V.extend y) = e.denote V := by
  simp only [Expr.denote, shiftExpr]
  rw [shiftArgs_lookupArgs V y e.args]

/-! ## 2. Structural decidable equality on expressions

The CSE test compares two same-type expressions for syntactic identity (same op,
same argument indices). We build it bottom-up: variables, then argument vectors,
then expressions. -/

/-- Decidable equality on De Bruijn variables of the same type. -/
instance decEqVar {Γ : Ctxt jasminDialect} {t : JasminTy} :
    (a b : Ctxt.Var Γ t) → Decidable (a = b)
  | .here, .here => isTrue rfl
  | .here, .there _ => isFalse (by intro h; cases h)
  | .there _, .here => isFalse (by intro h; cases h)
  | .there x, .there y =>
      match decEqVar x y with
      | isTrue hx => isTrue (by rw [hx])
      | isFalse hx => isFalse (by intro h; cases h; exact hx rfl)

/-- Decidable equality on `HVector`s of variables (same length, pointwise-equal
indices). -/
instance decEqArgs {Γ : Ctxt jasminDialect} :
    {tys : List JasminTy} → (a b : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    Decidable (a = b)
  | [], .nil, .nil => isTrue rfl
  | _ :: _, .cons x xs, .cons y ys =>
      match decEqVar x y with
      | isTrue hx =>
          match decEqArgs xs ys with
          | isTrue hxs => isTrue (by rw [hx, hxs])
          | isFalse hxs => isFalse (by intro h; cases h; exact hxs rfl)
      | isFalse hx => isFalse (by intro h; cases h; exact hx rfl)

/-- Decide whether two same-type expressions in the same context are
syntactically identical (same op and same argument indices). -/
instance decEqExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (a b : Expr jasminDialect Γ t) : Decidable (a = b) :=
  if hop : a.op = b.op then
    match decEqArgs a.args (hop ▸ b.args) with
    | isTrue hargs => isTrue (by
        cases a with
        | mk aop ahq aargs =>
        cases b with
        | mk bop bhq bargs =>
        cases hop
        simp only [] at hargs
        subst hargs
        rfl)
    | isFalse hargs => isFalse (by
        intro h; cases h; exact hargs (by cases hop; rfl))
  else
    isFalse (by intro h; cases h; exact hop rfl)

/-! ## 3. The CSE pass: redirect an adjacent redundant binder

`comCSE` walks the let-chain. At `.var e (.var e' body)`:

* if `e'` is the shifted duplicate of `e` (`e' = shiftExpr e`, decided by
  `decEqExpr`), the inner binder `v1` (`Ctxt.Var.here` in the body's context) is
  redundant — it denotes the same value as the outer binder `v0`
  (`Ctxt.Var.there .here`). We redirect every use of `v1` in `body` to `v0` via
  `CopyProp.copyHom (.there .here)`, leaving the binding in place (a later DCE
  drops it), and recurse;
* otherwise we recurse into the body unchanged.

Reusing `CopyProp.copyHom` / `Com.denote_rename` / `pullV_copyHom` keeps the
denotation proof a short reduction to the already-verified redirect law. -/

/-- **One adjacent-CSE step at the head.** Given a head binder `e : Expr Γ r` and
an already-processed continuation `c : Com (r :: Γ) t`, if `c` begins with a
binder `e'` that is the shifted duplicate of `e` (`e' = shiftExpr e`), redirect
that inner binder's uses to the outer binder (`copyHom .here`) and keep the
binding; otherwise re-attach `e` unchanged. Non-recursive — the recursion lives
in `comCSE`. -/
def cseHead {Γ : Ctxt jasminDialect} {r t : JasminTy}
    (e : Expr jasminDialect Γ r) (c : Com jasminDialect (r :: Γ) t) :
    Com jasminDialect Γ t :=
  match c with
  | .var (t := r') e' body2 =>
      if h : r' = r then
        let e'c : Expr jasminDialect (r :: Γ) r := h ▸ e'
        let body2c : Com jasminDialect (r :: r :: Γ) t := h ▸ body2
        if (decEqExpr e'c (shiftExpr (s := r) e)).decide then
          -- Redundant: redirect uses of the inner binder (`.here`) to the outer
          -- binder (`.there .here`); keep the binding for a later DCE pass.
          .var e (.var e'c (body2c.rename (copyHom Ctxt.Var.here)))
        else
          .var e c
      else
        .var e c
  | _ => .var e c

/-- **Adjacent common-subexpression elimination.** Bottom-up: clean the body,
then apply one adjacent-CSE step (`cseHead`) at this binder. Collapses every
adjacent redundant binder along the let-chain. -/
def comCSE {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Com jasminDialect Γ t
  | .ret v => .ret v
  | .var e body => cseHead e (comCSE body)

/-! ## 4. Denotation preservation (not `rfl`) -/

/-- **One CSE step preserves denotation.** `cseHead e c` denotes exactly the
`.var e c` it replaces: `(cseHead e c).denote V = c.denote (V.extend (e.denote V))`.
The firing case discharges via:
* `shiftExpr_denote` — the inner binder denotes the outer binder's value, so the
  two adjacent slots hold equal values;
* `Com.denote_rename` + `pullV_copyHom` — redirecting the inner binder to the
  outer one is a no-op on the (equal-valued) doubled valuation.
**Not `rfl`.** -/
theorem cseHead_denote {Γ : Ctxt jasminDialect} {r t : JasminTy}
    (e : Expr jasminDialect Γ r) (c : Com jasminDialect (r :: Γ) t)
    (V : Ctxt.Valuation Γ) :
    (cseHead e c).denote V = c.denote (V.extend (e.denote V)) := by
  cases c with
  | ret v => rfl
  | var e' body2 =>
      rename_i r'
      by_cases h : r' = r
      · subst h
        by_cases hd : (decEqExpr e' (shiftExpr (s := r') e)).decide
        · -- Firing case: `e' = shiftExpr e`.
          have heq : e' = shiftExpr (s := r') e := of_decide_eq_true hd
          have hx : e'.denote (V.extend (e.denote V)) = e.denote V := by
            rw [heq]; exact shiftExpr_denote e V (e.denote V)
          simp only [cseHead, dif_pos, hd, if_true, Com.denote]
          -- Goal: `(body2.rename copyHom).denote ((V.extend x0).extend x1)`
          --       `= body2.denote ((V.extend x0).extend x1)`, where `x1 = x0`.
          rw [Com.denote_rename (copyHom Ctxt.Var.here) body2
                ((V.extend (e.denote V)).extend (e'.denote (V.extend (e.denote V))))]
          rw [hx]
          -- Both valuations are now `(V.extend x0).extend x0`; the pullback along
          -- `copyHom .here` is the identity (`pullV_copyHom`).
          congr 1
          exact pullV_copyHom Ctxt.Var.here (V.extend (e.denote V))
        · -- Non-firing: types match but expressions differ.
          have hd' : (decEqExpr e' (shiftExpr (s := r') e)).decide = false := by
            simp only [Bool.not_eq_true] at hd; exact hd
          simp only [cseHead, dif_pos, hd', Bool.false_eq_true, if_false,
            Com.denote]
      · -- Non-firing: inner binder type differs.
        simp only [cseHead, dif_neg h, Com.denote]

/-- **Denotation preservation for `comCSE`.** `comCSE c` denotes the same function
as `c`, by induction over the `Com` let-chain (each binder discharges via
`cseHead_denote`). **Not `rfl`.** -/
theorem comCSE_denote {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ),
      (comCSE c).denote V = c.denote V
  | .ret _, _ => rfl
  | .var e body, V => by
      show (cseHead e (comCSE body)).denote V = _
      rw [cseHead_denote e (comCSE body) V, comCSE_denote body (V.extend (e.denote V))]
      rfl

/-! ## 5. Self-contained validation

A `Com jasminDialect [reg 32] (reg 32)` with an **adjacent redundant binder**:

    let v0 = x + x      -- x is `.here`
    let v1 = x + x      -- x is now `.there .here` (shifted past v0) — duplicate!
    ret v1              -- reads the duplicate v1 (`.here`)

`v1`'s expression is `shiftExpr` of `v0`'s, so the analysis fires: the use of
`v1` in `ret v1` is redirected to `v0` (`.there .here`), the binding kept. Both
programs map `x` to `x + x`; the rewrite shifts the returned variable's index. -/

/-- A `reg 32` binary `regArith` helper for the demo. -/
def binR32 {Γ : Ctxt jasminDialect} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg 32)) : Expr jasminDialect Γ (.reg 32) :=
  { op := .regArith op 32, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- The demo: `v0 = x + x; v1 = x + x; ret v1`. The inner binder `v1` recomputes
`v0` (its `Expr` is `shiftExpr` of `v0`'s). -/
def demoAdjacentCSE : Com jasminDialect [.reg 32] (.reg 32) :=
  -- v0 = x + x.  Context [v0, x]; x is `.here`.
  .var (binR32 .add .here .here)
    -- v1 = x + x.  Context [v1, v0, x]; x is `.there .here` (shifted past v0).
    (.var (binR32 .add (.there .here) (.there .here))
      -- ret v1.  v1 is `.here`.
      (.ret .here))

/-- **The pass fires**: the redundant `v1` use in `ret v1` is redirected to `v0`
(`.there .here`); the binding is kept (a later DCE drops it). -/
example : comCSE demoAdjacentCSE =
    Com.var (binR32 .add .here .here)
      (.var (binR32 .add (.there .here) (.there .here)) (.ret (.there .here))) := by
  rfl

/-- **Denotation preserved** for the demo, via the general theorem. Both map
`x` to `x + x`. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (comCSE demoAdjacentCSE).denote V = demoAdjacentCSE.denote V :=
  comCSE_denote demoAdjacentCSE V

/-- Concretely, on `x = 21`, both denote `42` (`= 21 + 21`). -/
example : demoAdjacentCSE.denote (.cons (21 : BitVec 32) .nil) = (42 : BitVec 32) :=
  rfl

example :
    (comCSE demoAdjacentCSE).denote (.cons (21 : BitVec 32) .nil) = (42 : BitVec 32) :=
  rfl

/-- A program whose adjacent binders are **not** duplicates is left structurally
unchanged: `v0 = x + x; v1 = v0 + v0; ret v1` — `v1`'s args read `v0` (`.here`),
not the shifted `x`, so `e' ≠ shiftExpr e` and the pass does not fire. -/
def demoNoFire : Com jasminDialect [.reg 32] (.reg 32) :=
  .var (binR32 .add .here .here)          -- v0 = x + x
    (.var (binR32 .add .here .here)       -- v1 = v0 + v0  (reads v0, not x)
      (.ret .here))

example : comCSE demoNoFire = demoNoFire := rfl

/-- A bare `ret` program is unchanged. -/
example : comCSE (Com.ret (Γ := [JasminTy.reg 8]) (t := JasminTy.reg 8) .here)
    = Com.ret .here := rfl

end CatCrypt.Crypto.Optimizer.ComCSE
