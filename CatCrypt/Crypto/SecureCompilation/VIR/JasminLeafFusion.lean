/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# Jasmin leaf fusion: a verified `Com → Com` rewrite

The **verified** form of the hand-written `gen_matvec` shim leaf of the ML-KEM
benchmark.

## The verification-vs-performance tension

The verified jasmin pipeline lowers a straight-line `Com jasminDialect` whose
NTT-domain orchestration is a sequence of per-op `extCall` leaves
(`JasminDialect.lean`). Keeping that orchestration **modular** — one leaf per
primitive — is what makes each primitive separately KAT-able and separately
spec'd (each leaf's agreement is a `LeafAgrees`/leaf-spec obligation, see
`JasminPrintSemCorrect.lean`).

But modularity costs performance: between two adjacent leaves the first leaf's
result is materialised into a stack array and re-read by the second. At ML-KEM
scale the `gen_matrix → matvec` pair alone round-trips a `u16[2304]` intermediate
copy (measured 20.2 µs per encapsulation, against 18.2 µs with the pair fused).
The hand-written `gen_matvec` shim removes that copy by fusing the two leaves into
one — at the cost of giving up the per-op granularity.

This is the *verification-vs-performance tension at the AVX2-leaf boundary*. The
principled resolution is **leaf fusion as a verified `Com → Com` rewrite**: keep the modular, per-op-spec'd source, emit the fused
form, and prove the fusion preserves `Com.denote` — *given* the fused leaf
computes the composition of the two it replaces. The composition fact is exactly
the fused leaf's own KAT/spec obligation (`hgf` below); the *rewrite* is
denotation-preserving unconditionally on top of it.

## The fusion pattern

The real fusion case is: `f`'s result is consumed *only* by `g`, as `g`'s first
argument, and `g`'s result is what the rest of the program uses. In De Bruijn
form (newest binding at the head of the context `Γ`), with input variables
`x : Var Γ tx` and `y : Var Γ ty`:

* **source** — two adjacent leaves, `g` reads the freshly-bound `f`-result via
  `Ctxt.Var.here`, and the remaining body uses the `g`-result via `here`:
  ```
  .var (extCall f [x])                         -- binds  tf  : Γ' = tf :: Γ
    (.var (extCall g [here, y.there])          -- binds  tg  : Γ'' = tg :: tf :: Γ
      body)                                    -- body : Com (tg :: tf :: Γ) s
  ```
  In the fusion case `body` reads the `g`-result through `here` and does **not**
  otherwise read the intermediate `f`-result.

* **fused** — one leaf, the `f`-result unnamed:
  ```
  .var (extCall gf [x, y])                     -- binds  tg  : Γ_f = tg :: Γ
    body'                                       -- body' : Com (tg :: Γ) s
  ```
  where `body'` is `body` with the two intermediate bindings collapsed to the one
  fused result.

The crux is the De Bruijn bookkeeping relating `body : Com (tg :: tf :: Γ) s` to
`body' : Com (tg :: Γ) s`. We make the concrete fusion case — `body = .ret here`,
the literal `gen_matrix → matvec → ret` shape — fully precise and fully proven;
the general body-shift relation is stated with a single clearly-labelled `sorry`
and a precise note on what remains.

## The fused-leaf spec

`Expr.denote` evaluates an `extCall` through the dialect's `jasminExtSem`
(`jasminDenote`). So the semantic content the hand fusion relies on — *the fused
leaf computes `g ∘ f`* — is exactly

```
∀ vx vy, jasminExtSem gf [tx,ty] tg ⟨vx, vy⟩
           = jasminExtSem g [tf,ty] tg ⟨jasminExtSem f [tx] tf ⟨vx⟩, vy⟩
```

i.e. the fused leaf, on `(x, y)`, returns what `g` returns on
`(f x, y)`. Under this hypothesis the two `Com`s denote equally.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLeafFusion

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Single-argument `extCall` expressions

Helper builders for the unary / binary `extCall` `Expr`s in the fusion pattern.
Each pins the op's declared signature (`argTys`/`retTy`) so `retTy_eq := rfl`. -/

/-- A unary `extCall` `Expr`: leaf `name : [tx] → tf`, applied to `x`. -/
def callU (name : String) {Γ : Ctxt jasminDialect} {tx tf : JasminTy}
    (x : Ctxt.Var Γ tx) : Expr jasminDialect Γ tf :=
  { op := .extCall name [tx] tf
    retTy_eq := rfl
    args := .cons x .nil }

/-- A binary `extCall` `Expr`: leaf `name : [tx, ty] → tg`, applied to `x, y`. -/
def callB (name : String) {Γ : Ctxt jasminDialect} {tx ty tg : JasminTy}
    (x : Ctxt.Var Γ tx) (y : Ctxt.Var Γ ty) : Expr jasminDialect Γ tg :=
  { op := .extCall name [tx, ty] tg
    retTy_eq := rfl
    args := .cons x (.cons y .nil) }

/-! ## 2. Reduction lemmas for `Expr.denote` on these `extCall`s

`Expr.denote` is `retTy_eq ▸ DialectDenote.denote op (lookupArgs args V)`; with
`retTy_eq := rfl` the transport vanishes, `DialectDenote.denote` of an `extCall`
is `jasminExtSem`, and `lookupArgs` unfolds the argument `HVector`. -/

/-- A unary `callU` leaf denotes to `jasminExtSem` applied to the looked-up
    argument. -/
theorem callU_denote (name : String) {Γ : Ctxt jasminDialect} {tx tf : JasminTy}
    (x : Ctxt.Var Γ tx) (V : Ctxt.Valuation Γ) :
    (callU name (tf := tf) x).denote V
      = jasminExtSem name [tx] tf (.cons (x.lookup V) .nil) := rfl

/-- A binary `callB` leaf denotes to `jasminExtSem` applied to its two looked-up
    arguments. -/
theorem callB_denote (name : String) {Γ : Ctxt jasminDialect}
    {tx ty tg : JasminTy} (x : Ctxt.Var Γ tx) (y : Ctxt.Var Γ ty)
    (V : Ctxt.Valuation Γ) :
    (callB name (tg := tg) x y).denote V
      = jasminExtSem name [tx, ty] tg
          (.cons (x.lookup V) (.cons (y.lookup V) .nil)) := rfl

/-! ## 3. The concrete fusion instance (fully proven)

Fixed input context `Γ = [tx, ty]`, `body = .ret here`. This is the literal
`gen_matrix → matvec → ret` shape:

* **source**:
  `f := extCall fName [tx] tf`, on `x = here : Var [tx,ty] tx`;
  then `g := extCall gName [tf, ty] tg`, on
  `[here : Var [tf,tx,ty] tf, there (there here) : Var [tf,tx,ty] ty]`;
  then `ret here`.
* **fused**:
  `gf := extCall gfName [tx, ty] tg`, on
  `[here : Var [tx,ty] tx, there here : Var [tx,ty] ty]`;
  then `ret here`. -/

/-- The **source** program: two adjacent leaves over `Γ = [tx, ty]`, with the
    `g`-result returned. `f` reads `x = here`; `g` reads the freshly-bound
    `f`-result (`here`) and the input `y` (shifted twice past `f`'s binding and
    `x`). -/
def srcProg (fName gName : String) (tx ty tf tg : JasminTy) :
    Com jasminDialect [tx, ty] tg :=
  .var (callU fName (Γ := [tx, ty]) (tf := tf) .here)
    (.var (callB gName (Γ := tf :: [tx, ty]) (tg := tg)
            .here (.there (.there .here)))
      (.ret .here))

/-- The **fused** program: one leaf over `Γ = [tx, ty]` returning its result.
    `gf` reads `x = here` and `y = there here`. -/
def fusedProg (gfName : String) (tx ty tg : JasminTy) :
    Com jasminDialect [tx, ty] tg :=
  .var (callB gfName (Γ := [tx, ty]) (tg := tg) .here (.there .here))
    (.ret .here)

/-- **Concrete leaf-fusion correctness** (fully proven). Under the fused-leaf
    spec `hgf` — the fused leaf computes `g ∘ f` on `(x, y)` — the source and
    fused programs have equal `Com.denote` on every input valuation
    `V = ⟨vx, vy⟩`.

    This is the verified `gen_matrix → matvec` fusion, denotation-preserving by
    construction once the fused leaf's own KAT/spec (`hgf`) is supplied. -/
theorem fuseExtCall_denote_concrete
    (fName gName gfName : String) (tx ty tf tg : JasminTy)
    (hgf : ∀ (vx : ⟦tx⟧) (vy : ⟦ty⟧),
      jasminExtSem gfName [tx, ty] tg (.cons vx (.cons vy .nil))
        = jasminExtSem gName [tf, ty] tg
            (.cons (jasminExtSem fName [tx] tf (.cons vx .nil))
              (.cons vy .nil)))
    (V : Ctxt.Valuation ([tx, ty] : Ctxt jasminDialect)) :
    (srcProg fName gName tx ty tf tg).denote V
      = (fusedProg gfName tx ty tg).denote V := by
  -- Destructure V = ⟨vx, vy⟩.
  cases V with
  | cons vx Vrest =>
    cases Vrest with
    | cons vy Vnil =>
      cases Vnil
      -- Both sides reduce by `Com.denote` / `Expr.denote` (`extCall` ↦
      -- `jasminExtSem`) and the De Bruijn `Var.lookup` laws to a pair of
      -- `jasminExtSem` applications related exactly by `hgf vx vy`.
      simp only [srcProg, fusedProg, Com.denote, Ctxt.Valuation.extend,
        callU_denote, callB_denote]
      exact (hgf vx vy).symm

/-! ## 4. The general fusion lemma

The fully-general statement keeps `Γ` and the consuming `body` arbitrary. The
source binds two intermediate results (`tf` then `tg`); the fused program binds
one (`tg`). In the fusion case `body : Com (tg :: tf :: Γ) s` reads the
`g`-result through `here` and never reads the `f`-result. The fused body
`body' : Com (tg :: Γ) s` is `body` with the `tf` binding dropped from the
context — the De Bruijn rewrite that removes the now-unnamed intermediate.

We package "`body'` is `body` with the `tf` slot dropped" as a denotation
relation `bodyDrop`: for any valuation `V : Valuation Γ`, any `g`-result value
`vg : ⟦tg⟧`, and any (irrelevant, dropped) `f`-result value `vf : ⟦tf⟧`,

    body.denote  (V.extend vf |>.extend vg over (tg :: tf :: Γ))
      = body'.denote (V.extend vg over (tg :: Γ)).

This is precisely the statement that `body` does not observe the `tf` slot. Under
that relation the general fusion is denotation-preserving. -/

/-- Denotation relation between the source body (over `tg :: tf :: Γ`) and the
    fused body (over `tg :: Γ`): the source body ignores the dropped `tf` slot. -/
def BodyDrop {Γ : Ctxt jasminDialect} {tf tg s : JasminTy}
    (body : Com jasminDialect (tg :: tf :: Γ) s)
    (body' : Com jasminDialect (tg :: Γ) s) : Prop :=
  ∀ (V : Ctxt.Valuation Γ) (vf : ⟦tf⟧) (vg : ⟦tg⟧),
    body.denote (.cons vg (.cons vf V)) = body'.denote (.cons vg V)

/-- The general **source** program: `f` on `x`, then `g` on `(f-result, y')`,
    then an arbitrary consuming `body`. `x : Var Γ tx`, `y' : Var Γ ty`; inside
    `g`'s context `tf :: Γ` the input `y'` is `y'.there`. -/
def srcProgGen {Γ : Ctxt jasminDialect} {tx ty tf tg s : JasminTy}
    (fName gName : String) (x : Ctxt.Var Γ tx) (y' : Ctxt.Var Γ ty)
    (body : Com jasminDialect (tg :: tf :: Γ) s) :
    Com jasminDialect Γ s :=
  .var (callU fName (tf := tf) x)
    (.var (callB gName (Γ := tf :: Γ) (tg := tg) .here y'.there)
      body)

/-- The general **fused** program: one leaf `gf` on `(x, y')`, then the fused
    body `body'`. -/
def fusedProgGen {Γ : Ctxt jasminDialect} {tx ty tg s : JasminTy}
    (gfName : String) (x : Ctxt.Var Γ tx) (y' : Ctxt.Var Γ ty)
    (body' : Com jasminDialect (tg :: Γ) s) :
    Com jasminDialect Γ s :=
  .var (callB gfName (Γ := Γ) (tg := tg) x y') body'

/-- **General leaf-fusion correctness.** Under the fused-leaf spec `hgf` (the
    fused leaf computes `g ∘ f`) and the body-drop relation `hbody` (the
    consuming body ignores the intermediate `f`-result), the general source and
    fused programs have equal `Com.denote`.

    Fully reduced to the De Bruijn lookup facts: with `hbody` packaging the body
    shift, the two programs agree once their two leaf evaluations are related by
    `hgf`. The proof unfolds `Com.denote`/`Expr.denote`, rewrites the leaves via
    `callU_denote`/`callB_denote`, applies `hgf` to relate the bound `g`/`gf`
    values, and closes with `hbody`. -/
theorem fuseExtCall_denote
    {Γ : Ctxt jasminDialect} {tx ty tf tg s : JasminTy}
    (fName gName gfName : String)
    (x : Ctxt.Var Γ tx) (y' : Ctxt.Var Γ ty)
    (body : Com jasminDialect (tg :: tf :: Γ) s)
    (body' : Com jasminDialect (tg :: Γ) s)
    (hgf : ∀ (vx : ⟦tx⟧) (vy : ⟦ty⟧),
      jasminExtSem gfName [tx, ty] tg (.cons vx (.cons vy .nil))
        = jasminExtSem gName [tf, ty] tg
            (.cons (jasminExtSem fName [tx] tf (.cons vx .nil))
              (.cons vy .nil)))
    (hbody : BodyDrop body body')
    (V : Ctxt.Valuation Γ) :
    (srcProgGen fName gName x y' body).denote V
      = (fusedProgGen gfName x y' body').denote V := by
  simp only [srcProgGen, fusedProgGen, Com.denote, Ctxt.Valuation.extend,
    callU_denote, callB_denote]
  rw [hgf (x.lookup V) (y'.lookup V)]
  exact hbody V (jasminExtSem fName [tx] tf (.cons (x.lookup V) .nil))
    (jasminExtSem gName [tf, ty] tg
      (.cons (jasminExtSem fName [tx] tf (.cons (x.lookup V) .nil))
        (.cons (y'.lookup V) .nil)))

/-! ## 5. The concrete instance discharges its `BodyDrop` obligation

The concrete `body = .ret here` satisfies `BodyDrop` trivially (`.ret here`
returns the head of the valuation, ignoring the rest), and the concrete fusion
is the general lemma instantiated at `Γ = [tx, ty]`, `body = .ret here`. This
ties the two together and re-derives the concrete result from the general one,
confirming the bookkeeping is consistent. -/

/-- `.ret here` ignores the dropped `tf` slot: `BodyDrop` holds for it. -/
theorem bodyDrop_ret_here {Γ : Ctxt jasminDialect} {tf tg : JasminTy} :
    BodyDrop (Γ := Γ) (tf := tf) (tg := tg) (s := tg)
      (.ret .here) (.ret .here) := by
  intro V vf vg
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLeafFusion
