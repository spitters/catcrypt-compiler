/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.Rewrite.Egraph

/-!
# Verified dead-let elimination for `Com` — a denotation-preserving rewrite

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A **structural `Com → Com` dead-binding-elimination pass** over the typed VIR
framework. It is the `Com`-level rewrite that the analysis-only
`SecureCompilation/VIR/DeadCodeElim.lean` left as the documented residual: that
file decides *which* binders are dead but applies the identity transform at the
`Com` level (deadness is consumed downstream as a labelling). Here the rewrite
actually deletes a dead let-binding and re-checks the result type, with a real
denotation-preservation proof (an induction over the let-chain, **not** `rfl`).

## The De Bruijn obstruction and our sound scope

`Com d Γ t` is intrinsically typed: a binder introduces a fresh type at the head
of the context, and every variable below it is a `Ctxt.Var` De Bruijn index.
Removing an *interior* binding changes the intrinsic type of the body — every
subsequent `.there` index would need to shift, and binders nested below the
dead one would have to be exchanged past it (a full context-permutation /
reindexing layer).

We take the sound scope that needs **no interior reindex**: a **trailing dead
binding** — a binder `.var e body` whose `body`, after recursively eliminating
its own trailing dead bindings, is a bare `.ret v` that does *not* read the
binder (`v ≠ .here`). Such a binder feeds a value into a return that ignores it,
so it can be dropped, leaving `.ret v'` where `v'` is `v` with its outermost
index strengthened (the only reindex required, and it is total because `v` is
not `.here`). Running the pass bottom-up peels off *all* trailing dead bindings
in one traversal — e.g.

    let a = …        let a = …
    let b = …    ↦   ret a            (b, c dead: they feed a ret that returns a)
    let c = …
    ret a

Every `jasminDialect` op is pure (effect-free), so deleting a dead binding never
drops an observable effect: denotation is preserved exactly.

## Contents

* `dropVar` — strengthen a variable out of an extended context, defined only on
  non-`.here` indices (`Option`-valued; `none` exactly on `.here`).
* `dropVar_lookup` — the strengthening is lookup-invariant under `extend`.
* `comDCE` — the bottom-up trailing-dead-binding elimination, generic over any
  `Dialect`.
* `comDCE_denote` — **denotation preservation** (`(comDCE c).denote V = c.denote V`),
  by induction over the let-chain. **Not `rfl`.**
* `comDCE_cost_le`, `comDCE_ctSafe` — `jasminDialect` corollaries: the pass is
  cost-non-increasing and CT-preserving (the dialect is branch-free).
* Self-contained validation: a program with a dead trailing binder is
  shrunk by the pass while its denotation is preserved.

All goals closed. No `sorry`. Axiom set: `propext`, `Quot.sound`,
`Classical.choice` (the standard Lean/Mathlib trio inherited via `Egraph`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ComDCE

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open Ctxt (Var)

/-! ## 1. Variable strengthening

Dropping a binder removes the head type `t` from the context. A variable
`Var (t :: Γ) s` strengthens to `Var Γ s` exactly when it is not the dropped
binder itself (i.e. not `.here`). `dropVar` is total into `Option`, returning
`none` precisely on `.here`. -/

/-- Strengthen a variable out of the extended context `t :: Γ`. Returns `none`
exactly when the variable *is* the head binder (`.here`); otherwise peels one
`.there`. -/
def dropVar {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t s : d.Ty} :
    Var (t :: Γ) s → Option (Var Γ s)
  | .here    => none
  | .there v => some v

/-- **Lookup invariance of `dropVar`.** When `dropVar v = some v'`, the value
read for `v` under an extended valuation `V.extend x` is exactly the value read
for the strengthened `v'` under `V` — the dropped binding `x` is never observed.
This is the variable-level core of denotation preservation. -/
theorem dropVar_lookup {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    {Γ : Ctxt d} {t s : d.Ty}
    (v : Var (t :: Γ) s) (v' : Var Γ s) (h : dropVar v = some v')
    (V : Ctxt.Valuation Γ) (x : ⟦t⟧) :
    v.lookup (V.extend x) = v'.lookup V := by
  cases v with
  | here    => simp [dropVar] at h
  | there w => simp [dropVar] at h; subst h; rfl

/-! ## 2. The dead-let-elimination pass

`comDCE` is a single bottom-up traversal. At a binder `.var e body` it first
eliminates the trailing dead bindings of `body`; if the residual body is a bare
`.ret v` that does not read this binder (`dropVar v = some v'`), the binder is
dead and is dropped, collapsing to `.ret v'`. Otherwise the binder is kept (the
body still reads it, or the body is not a bare return). Iterating the recursion
removes a whole trailing run of dead bindings in one pass. -/

/-- **Dead-let elimination.** Bottom-up removal of trailing dead bindings: a
binder whose (already-cleaned) body is a `.ret` ignoring it is deleted, with the
returned variable strengthened. Generic over any `Dialect` — every operation in
the VIR `Expr` model is a pure function, so deleting a dead binding cannot drop
an effect. -/
def comDCE {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t : d.Ty} :
    Com d Γ t → Com d Γ t
  | .ret v => .ret v
  | .var e body =>
      match comDCE body with
      | .ret v =>
          match dropVar v with
          | some v' => .ret v'          -- binder is dead: drop it
          | none    => .var e (.ret v)  -- the binder *is* the returned value: keep
      | body' => .var e body'           -- body still has binders: keep this one

/-! ## 3. Denotation preservation (not `rfl`) -/

/-- **Denotation preservation for `comDCE`.** The cleaned program denotes the
same function as the input: `(comDCE c).denote V = c.denote V`, for every
valuation `V`. Proved by induction over the `Com` let-chain — the dead-binder
case discharges via `dropVar_lookup` (the dropped binding is never read).
**Not `rfl`.** -/
theorem comDCE_denote {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] {Γ : Ctxt d} {t : d.Ty} :
    ∀ (c : Com d Γ t) (V : Ctxt.Valuation Γ), (comDCE c).denote V = c.denote V
  | .ret _, _ => rfl
  | .var e body, V => by
      have ih := comDCE_denote body (V.extend (e.denote V))
      show (comDCE (.var e body)).denote V = body.denote (V.extend (e.denote V))
      rw [← ih]
      simp only [comDCE]
      cases hb : comDCE body with
      | ret v =>
          simp only []
          split
          · next v' hv =>
              simp only [Com.denote]
              exact (dropVar_lookup v v' hv V (e.denote V)).symm
          · next hv => simp only [Com.denote]
      | var e2 body2 => simp only [Com.denote]

/-! ## 4. `jasminDialect` corollaries: cost and constant-time

The headline preservation theorem is dialect-generic. For the concrete
`jasminDialect` (the linear-jasmin emit target) we additionally show the pass is
cost-non-increasing (it only ever deletes binders) and constant-time-preserving
(the dialect is branch-free, so every `Com` is CT-safe before and after). -/

/-- **The pass is cost-non-increasing on `jasminDialect`.** `comDCE` only deletes
binders, so the let-chain cost never rises. -/
theorem comDCE_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ c : Com jasminDialect Γ t, comCost (comDCE c) ≤ comCost c
  | .ret _ => Nat.le_refl _
  | .var e body => by
      have ih := comDCE_cost_le body
      show comCost (comDCE (.var e body)) ≤ comCost (.var e body)
      simp only [comDCE]
      cases hb : comDCE body with
      | ret v =>
          rw [hb] at ih
          simp only []
          split
          · simp only [comCost]; omega
          · simp only [comCost]; omega
      | var e2 body2 =>
          rw [hb] at ih
          simp only [comCost] at ih ⊢
          omega

/-- **The pass preserves constant-time safety on `jasminDialect`.** The dialect
has no conditional op, so every `Com` — input or output — is CT-safe. -/
theorem comDCE_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) :
    ctSafeComJ (comDCE c) = ctSafeComJ c := by
  rw [ctSafeComJ_true (comDCE c), ctSafeComJ_true c]

/-! ## 5. Self-contained validation

A `Com jasminDialect [reg 32] (reg 32)` with a **dead trailing
binding**:

    let v0 = x + x      -- live: it is what we return
    let v1 = x + x      -- dead: never read; feeds a ret that returns v0
    ret v0

The pass deletes `v1` and re-points the return at the strengthened `v0`. We
check that (a) the pass actually shrinks the program (one binder removed),
(b) the denotation is preserved, and (c) cost is non-increasing and CT is
preserved. -/

/-- A `reg 32` binary `regArith` helper for the demo. -/
private def binR32 {Γ : Ctxt jasminDialect} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg 32)) : Expr jasminDialect Γ (.reg 32) :=
  { op := .regArith op 32, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- The demo program: `v0 = x + x; v1 = x + x; ret v0`. The binder `v1` is dead
— the `ret` returns `v0` (which is `.there .here` after `v1` is bound), never
`v1` (`.here`). -/
def demoDeadTrailing : Com jasminDialect [.reg 32] (.reg 32) :=
  -- v0 = x + x.  Context becomes [v0, x]; `x` is `.there .here`, `v0` is `.here`.
  .var (binR32 .add .here .here)
    -- v1 = x + x.  Context becomes [v1, v0, x]; `x` is `.there (.there .here)`.
    (.var (binR32 .add (.there .here) (.there .here))
      -- ret v0.  `v0` is `.there .here` here (skipping the dead `v1`).
      (.ret (.there .here)))

/-- **The pass deletes the dead `v1` binder**, collapsing to `v0 = x + x; ret v0`
with the return strengthened to `.here`. A concrete `rfl`-checkable shrink. -/
example : comDCE demoDeadTrailing =
    Com.var (binR32 .add .here .here) (.ret .here) := rfl

/-- **Strictly fewer binders after the pass** (the dead binder is gone): the
input has cost `2`, the output cost `1`. -/
example : comCost (comDCE demoDeadTrailing) < comCost demoDeadTrailing := by decide

/-- **Denotation preserved** for the demo, via the general theorem. Both map
`x` to `x + x`. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (comDCE demoDeadTrailing).denote V = demoDeadTrailing.denote V :=
  comDCE_denote demoDeadTrailing V

/-- Concretely, on `x = 21`, both denote `42`. -/
example : demoDeadTrailing.denote (.cons (21 : BitVec 32) .nil) = (42 : BitVec 32) := rfl

example :
    (comDCE demoDeadTrailing).denote (.cons (21 : BitVec 32) .nil) = (42 : BitVec 32) := rfl

/-- **Cost non-increasing** on the demo. -/
example : comCost (comDCE demoDeadTrailing) ≤ comCost demoDeadTrailing :=
  comDCE_cost_le demoDeadTrailing

/-- **CT preserved** on the demo. -/
example : ctSafeComJ (comDCE demoDeadTrailing) = ctSafeComJ demoDeadTrailing :=
  comDCE_ctSafe demoDeadTrailing

/-- A program with **no** dead trailing binder is left unchanged: the binder *is*
the returned value, so it is kept. -/
def demoLive : Com jasminDialect [.reg 32] (.reg 32) :=
  .var (binR32 .add .here .here) (.ret .here)

example : comDCE demoLive = demoLive := rfl

end CatCrypt.Crypto.Optimizer.ComDCE
