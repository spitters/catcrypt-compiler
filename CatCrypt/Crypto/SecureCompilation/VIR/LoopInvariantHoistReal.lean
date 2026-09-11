/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# A hoisting loop-invariant code motion (LICM) pass for `Com` (real transform)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`LoopInvariantHoist.lean` ships an *analysis-as-labelling* LICM whose
`Com → Com` rewrite is the identity (`applyLicm = fun p _ => p`), so its
preservation theorems are `rfl` and verify nothing about an actual hoist.
This file supplies what that one avoids: a **structural** transform that
*moves* a loop-invariant binding from inside a bounded loop to a
once-per-call prelude, together with a **non-`rfl`** denotation-preservation
proof by induction over the loop trip count.

## The loop model (mirrors `JForProg`)

A bounded loop over a single accumulator is

  `acc := init; for _ in 0..n { acc := body(acc) }; ret acc`

with the total denotation `loopDenote n step init = (List.range n).foldl
(fun a _ => step a) init`, where `step acc = update.denote (.cons acc .nil)`
for a body `update : Com d [accTy] accTy`. This is exactly
`JasminPrint.JForProg.denote`'s shape, kept dialect-general here.

## The transform

The cleanest invariant binding is the head of the loop body:

  `update = .var e body`  with  `e : Expr d [accTy] t`  **loop-invariant**.

The body context is the singleton `[accTy]`, so the only variable an
argument of `e` could read is `acc` itself (de Bruijn `.here`). Hence
`e` is loop-invariant **iff it reads no argument** — `e.args = .nil`. A
nullary `e` denotes a constant `c := e.denote (.cons acc .nil)` that is the
*same value for every `acc`* (its denotation never inspects the valuation).

`hoist` restructures the program: it pulls `e` out of the loop. The hoisted
program is a `HoistedLoop`: a precomputed constant `c : ⟦t⟧` (the
once-computed invariant) plus the residual `body : Com d [t, accTy] accTy`.
Its denotation runs a loop whose step is `acc ↦ body.denote (.cons c (.cons
acc .nil))` — the invariant value `c` is supplied **once**, not recomputed
each iteration. This is a real structural change: the binding has left the
loop.

## The proof (not `rfl`)

The original loop computes, each iteration, `e.denote (.cons acc .nil)` and
feeds it to `body`; the hoisted loop feeds the *precomputed* `c`. They agree
because `e` is nullary, so `e.denote (.cons acc .nil) = c` for every `acc`
— *this is the loop-invariance content*. The central lemma

  `hoist_denote : (hoist update h).denote n init = loopDenote n update init`

is proved by:

* `nullaryExpr_denote_const` — a nullary `Expr` denotes the same value in any
  valuation (so the per-iteration recomputation equals the prelude `c`);
* `loopDenote_step_congr` — two loops with pointwise-equal step functions
  fold to the same result (a `List.foldl` congruence, by induction on the
  trip count / the range list).

The two sides denote at *different program structures* (a binding inside vs.
outside the loop) and agree only because of the invariance hypothesis. The
proof is **not** `rfl`: it inducts on the loop and rewrites each iteration's
recomputed value to the hoisted constant.

## What is general vs. scoped

* **General:** the loop model (`loopDenote`), the loop congruence
  (`loopDenote_step_congr`), and the nullary-constant law
  (`nullaryExpr_denote_const`) are dialect-generic.
* **Scoped to the cleanest case:** `hoist` / `hoist_denote` move the
  *outermost*, *nullary* (hence provably invariant) head binding of the loop
  body. A general hoist of a deeper invariant binding whose args read only
  earlier-invariant binders needs the de Bruijn renumbering layer
  (`strengthen*` in `DeadCodeElimReal.lean`); the nullary head case needs
  none, which is why it carries the non-`rfl` proof cleanly.
-/

@[expose] public section

set_option autoImplicit false
-- Equation/lookup lemmas legitimately do not use every ambient typeclass
-- section variable; silence the section-variable linter rather than thread
-- per-theorem `omit` clauses.
set_option linter.unusedSectionVars false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LICMReal

open CatCrypt.Crypto.SecureCompilation.VIR

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-! ## 1. The dialect-general bounded-loop denotation (mirrors `JForProg.denote`)

One iteration runs the body `update : Com d [accTy] accTy` on the singleton
valuation `[acc]`; the loop folds `n` iterations from `init`. This is the
ground-truth functional semantics that `JForProg.denote` also uses. -/

/-- One iteration: run the body on the singleton accumulator valuation. -/
def stepOf {accTy : d.Ty} (update : Com d [accTy] accTy) (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  update.denote (.cons acc .nil)

/-- `n`-fold loop denotation: fold `step` `n` times from `init`. -/
def loopDenote {accTy : d.Ty} (n : Nat) (update : Com d [accTy] accTy)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range n).foldl (fun acc _ => stepOf update acc) init

/-! ## 2. A `List.foldl` congruence over loop steps

Two loops whose step functions agree on every accumulator value fold to the
same result. The inductive lemma underlying the hoist: hoisting only
changes *how* each step's invariant value is obtained, never the step's
result, so the folds coincide. -/

/-- **Step congruence (general).** If `f` and `g` agree on every accumulator
value, then folding either over the same list yields the same result. Proven
by induction on the list (hence on the trip count when the list is
`List.range n`). -/
theorem foldl_step_congr {α : Type _} {β : Type _} (f g : α → β → α)
    (h : ∀ a b, f a b = g a b) :
    ∀ (l : List β) (init : α), l.foldl f init = l.foldl g init
  | [],      init => rfl
  | b :: bs, init => by
      simp only [List.foldl_cons]
      rw [h init b]
      exact foldl_step_congr f g h bs (g init b)

/-- **Loop step congruence.** Two `loopDenote`s with pointwise-equal step
functions denote the same loop. (Specialises `foldl_step_congr` to the
range-fold shape; the step closures ignore the list element.) -/
theorem loopDenote_step_congr {accTy : d.Ty}
    (n : Nat) (u₁ u₂ : Com d [accTy] accTy)
    (hstep : ∀ acc, stepOf u₁ acc = stepOf u₂ acc) (init : ⟦accTy⟧) :
    loopDenote n u₁ init = loopDenote n u₂ init := by
  unfold loopDenote
  exact foldl_step_congr _ _ (fun a _ => hstep a) (List.range n) init

/-! ## 3. Loop-invariance of an expression, and nullary expressions

The expression `e` at the head of a loop body is **loop-invariant** exactly
when its denotation does not depend on the accumulator valuation. We take this
denotational predicate as the invariance criterion — it is precisely what the
hoist needs. The canonical instance is a *nullary* `e` (`sig e.op = []`): it
reads no arguments, so its denotation never inspects the valuation. -/

/-- **Loop-invariance of an expression.** `e` denotes the same value in any two
valuations of its context — its result does not depend on the accumulator. -/
def LoopInvariant {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) : Prop :=
  ∀ V₁ V₂ : Ctxt.Valuation Γ, e.denote V₁ = e.denote V₂

/-- **Empty-arity arg lookup is valuation-independent.** When the argument-type
list is empty, the only `HVector` over it is `.nil`, and `lookupArgs` returns
`.nil` for any valuation. Stated over a *general* `tys` so the `tys = []`
substitution is clean (no dependent-cast trouble). -/
theorem lookupArgs_nil_const {Γ : Ctxt d} :
    {tys : List d.Ty} → (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    tys = [] → (V₁ V₂ : Ctxt.Valuation Γ) →
    Expr.lookupArgs args V₁ = Expr.lookupArgs args V₂
  | [], .nil, _, _, _ => rfl

/-- **Nullary ⇒ loop-invariant.** An `Expr` whose op has empty signature reads
no arguments (`lookupArgs` of an empty `HVector` ignores the valuation), so it
denotes the same value in any valuation. This is the canonical loop-invariant
head binding (the textbook "round constant" / `const` hoist target). -/
theorem nullary_loopInvariant {Γ : Ctxt d} {t : d.Ty}
    (e : Expr d Γ t) (hnil : DialectSignature.sig e.op = []) :
    LoopInvariant e := by
  intro V₁ V₂
  unfold Expr.denote
  -- The `retTy_eq ▸` cast is identical on both sides; `congr 1` peels it,
  -- leaving the args-lookup equality, which is valuation-independent because
  -- `sig e.op = []`.
  congr 2
  exact lookupArgs_nil_const e.args hnil V₁ V₂

/-! ## 4. The hoisted program and the real transform

A `HoistedLoop` carries the *precomputed* invariant value `c` (computed once,
in the prelude) and the residual loop body `body : Com d [t, accTy] accTy`,
which reads the invariant at the freshly-bound `t` slot. Its denotation
supplies `c` to every iteration without recomputing it. -/

/-- The hoisted program: a once-computed invariant `c` and a residual loop
body over the extended context `[t, accTy]`. The loop trip count `n` is
carried along. -/
structure HoistedLoop (d : Dialect) [TyDenote d.Ty] [DialectSignature d]
    (accTy : d.Ty) where
  /-- Trip count (static). -/
  n : Nat
  /-- The hoisted-out invariant's value type. -/
  t : d.Ty
  /-- The once-computed invariant value (would be materialised in the prelude). -/
  c : ⟦t⟧
  /-- The residual loop body, reading the invariant at the head slot. -/
  body : Com d [t, accTy] accTy

/-- One iteration of the hoisted loop: feed the *precomputed* invariant `c`
and the current `acc` to `body`. No recomputation of the invariant. -/
def HoistedLoop.step {accTy : d.Ty} (p : HoistedLoop d accTy)
    (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  p.body.denote (.cons p.c (.cons acc .nil))

/-- Hoisted loop denotation: fold the hoisted step `n` times. The invariant
`c` lives in the structure and is supplied once for the whole loop. -/
def HoistedLoop.denote {accTy : d.Ty} (p : HoistedLoop d accTy)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range p.n).foldl (fun acc _ => p.step acc) init

/-- **The real hoisting transform.** Given a loop with trip count `n` and body
`update = .var e body` whose head expression `e` is nullary (hence
loop-invariant), pull `e` out of the loop: precompute its constant value once
and return a `HoistedLoop` whose residual body is `body`.

This restructures the program — the binding `e` is removed from the
per-iteration body and materialised in the prelude (the `c` field). It is
**not** the identity: the result is a different structure (`HoistedLoop`) over
a body in a *different* (extended) context. -/
def hoist {accTy t : d.Ty} (n : Nat) (dummyAcc : ⟦accTy⟧)
    (e : Expr d [accTy] t) (body : Com d [t, accTy] accTy)
    (_hinv : LoopInvariant e) : HoistedLoop d accTy where
  n := n
  t := t
  -- Compute the invariant ONCE. Any valuation works (invariance); the supplied
  -- `dummyAcc` is a witness, and `hoist_denote` proves the choice is irrelevant.
  c := e.denote (.cons dummyAcc .nil)
  body := body

/-! ## 5. Denotation preservation (NON-`rfl`)

The hoisted loop denotes exactly the original loop. The two programs are
structurally different (invariant inside vs. outside the loop) and agree only
because the head binding is loop-invariant — its per-iteration recomputation
equals the once-computed prelude constant. The proof rewrites each iteration's
recomputed invariant to the hoisted constant (via the invariance hypothesis)
and concludes by the loop step congruence. -/

/-- **Hoisting preservation (NON-`rfl`).** For a loop-invariant head expression
`e`, the hoisted loop denotes the same function as the original loop: the
once-computed invariant equals what the loop recomputes every iteration.

The proof is not `rfl`: the original loop's step recomputes
`e.denote (.cons acc .nil)` each iteration, while the hoisted loop's step uses
the prelude constant `c`; equating them is the loop-invariance reasoning
(`hinv`), threaded through the loop fold (`foldl_step_congr`). -/
theorem hoist_denote {accTy t : d.Ty} (n : Nat) (dummyAcc : ⟦accTy⟧)
    (e : Expr d [accTy] t) (body : Com d [t, accTy] accTy)
    (hinv : LoopInvariant e) (init : ⟦accTy⟧) :
    (hoist n dummyAcc e body hinv).denote init = loopDenote n (.var e body) init := by
  -- Unfold the hoisted denotation to a range-fold over `HoistedLoop.step`.
  show (List.range n).foldl
        (fun acc _ => (hoist n dummyAcc e body hinv).step acc) init
      = loopDenote n (.var e body) init
  -- Rewrite the original loop as a range-fold over `stepOf (.var e body)`,
  -- then close by step congruence: the two steps agree at every `acc`.
  unfold loopDenote
  apply foldl_step_congr
  intro acc _
  -- Hoisted step: feed precomputed `c`. Original step: recompute `e` then run.
  show (hoist n dummyAcc e body hinv).step acc = stepOf (.var e body) acc
  unfold HoistedLoop.step stepOf hoist
  -- Original `.var e body` denotation peels to `body.denote (extend (e.denote …))`.
  show body.denote (.cons (e.denote (.cons dummyAcc .nil)) (.cons acc .nil))
      = (Com.var e body).denote (.cons acc .nil)
  rw [Com.denote]
  -- Now reduce to the invariance fact: the prelude `c` equals the
  -- per-iteration recomputed value, because `e` is loop-invariant.
  show body.denote (.cons (e.denote (.cons dummyAcc .nil)) (.cons acc .nil))
      = body.denote ((Ctxt.Valuation.extend (.cons acc .nil) (e.denote (.cons acc .nil))))
  unfold Ctxt.Valuation.extend
  rw [hinv (.cons dummyAcc .nil) (.cons acc .nil)]

/-! ## 6. A concrete worked example (the binding really leaves the loop)

A self-contained one-type, two-op toy dialect over `Nat`, on which we exhibit
a loop whose head binding is a nullary `const` (loop-invariant) and show that
`hoist` removes it from the body and the hoisted loop denotes the same value.
-/

namespace Demo

/-- A toy dialect: a single value type, a `const` op (nullary) and an `add`
op (binary, adds its two arguments). -/
inductive ToyOp where
  | const (n : Nat)
  | add
  deriving DecidableEq

def toyDialect : Dialect where
  Op := ToyOp
  Ty := Unit

instance : TyDenote toyDialect.Ty where
  denote _ := Nat

instance : DialectSignature toyDialect where
  sig | .const _ => [] | .add => [(), ()]
  ret _ := ()

instance : DialectDenote toyDialect where
  denote
    | .const n, _                              => n
    | .add,     .cons (a : Nat) (.cons b .nil) => a + b

/-- A loop body whose **head** binding is a nullary `const 10` (loop-invariant)
followed by `acc + const`:

```
-- context here is `acc :: []`
let k   = const 10      -- nullary  → loop-invariant
let acc' = add acc k    -- uses acc (.there .here) and k (.here)
ret acc'
```

`update : Com toy [()] ()`. One iteration adds `10` to the accumulator. -/
def invHeadExpr : Expr toyDialect [()] () :=
  { op := .const 10, retTy_eq := rfl, args := .nil }

/-- The residual body (after the head `const`): `acc' = add acc k; ret acc'`,
over the extended context `[k, acc]`. `k` is `.here`, `acc` is `.there .here`. -/
def residualBody : Com toyDialect [(), ()] () :=
  .var { op := .add, retTy_eq := rfl, args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)

/-- The full loop body: `let k = const 10; <residualBody>`. -/
def loopBody : Com toyDialect [()] () :=
  .var invHeadExpr residualBody

/-- The head expression is nullary, hence loop-invariant. -/
theorem invHeadExpr_inv : LoopInvariant invHeadExpr :=
  nullary_loopInvariant invHeadExpr rfl

/-- One original loop iteration adds 10 to the accumulator: `step acc = acc + 10`. -/
example (acc : Nat) : stepOf loopBody acc = acc + 10 := rfl

/-- **The transform moves the binding out of the loop.** The hoisted
program's prelude constant is `10` — the `const` binding now lives outside the
loop. (`dummyAcc = 0`; invariance makes the choice irrelevant.) -/
example : (hoist 5 (0 : Nat) invHeadExpr residualBody invHeadExpr_inv).c = (10 : Nat) := rfl

/-- The hoisted residual body is `residualBody` itself — the `const` binding is
gone from the loop body (one fewer binding inside the loop). -/
example : (hoist 5 (0 : Nat) invHeadExpr residualBody invHeadExpr_inv).body = residualBody := rfl

/-- **Denotation preservation on this concrete loop (5 iterations from 0):**
the hoisted loop and the original loop agree. The hoisted loop computes the
constant `10` once; the original recomputes it 5 times. Both yield `0 + 50`. -/
example :
    (hoist 5 (0 : Nat) invHeadExpr residualBody invHeadExpr_inv).denote (0 : Nat)
      = loopDenote 5 loopBody (0 : Nat) :=
  hoist_denote 5 (0 : Nat) invHeadExpr residualBody invHeadExpr_inv (0 : Nat)

-- `#eval`: both loops denote `50` (= 5 × 10) from `init = 0`.
#eval (hoist 5 (0 : Nat) invHeadExpr residualBody invHeadExpr_inv).denote (0 : Nat)  -- 50
#eval loopDenote 5 loopBody (0 : Nat)                                                -- 50

end Demo

end CatCrypt.Crypto.SecureCompilation.VIR.LICMReal
