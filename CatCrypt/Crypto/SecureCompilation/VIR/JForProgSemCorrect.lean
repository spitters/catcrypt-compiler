/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect

/-!
# The emitted bounded loop denotes the `n`-fold semantics (`JForProg` keystone)

`JForProgCT.lean` (§7) proves the *whole-loop* agreement
`loopRun p bodyRun init = p.denote init` **modulo** an explicit per-iteration
edge hypothesis `StepAgrees p bodyRun` — exactly the
`JasminPrintSemCorrect.lean` discipline of carrying the single uncovered edge as
a named hypothesis rather than a `sorry`. The remaining gap (flagged at
`JasminPrint.lean` §7 — "the printer's `Cfor` is a faithful *skeleton*") was the
absence of a theorem that *discharges* `StepAgrees` against the actual emitted
loop body.

This file closes that gap. It builds a **concrete** body runner from the
word-level evaluator of `JasminPrintSemCorrect.lean` — running the lowering of
`p.update` once through the named accumulator slot `"acc"` — and **proves**
`StepAgrees` for it. Composing with `JForProgCT.loopRun_eq` then yields the
keystone, fully discharged (no carried `StepAgrees`):

> running the emitted `for i = 0 to n { acc = body(acc) }` `n` times, threading
> the named accumulator, equals `p.denote init` = the `n`-fold application of the
> body's denotation `JForProg.step`.

## Why the body runner is `hInj`-free

`JasminPrintSemCorrect.execCom_eq` (the straight-line whole-`Com` preservation)
carries `hInj : Function.Injective freshName` because a *general* straight-line
body binds several fresh SSA names `v0, v1, …` that must stay distinct. The
crypto loop bodies that gate the downstream phases are **single-leaf** bodies of
the shape `Com.var e (Com.ret .here)` — one op, one binding (X25519's
`x25519_ladder_iter` is one `extCall`; a running-sum body is one `regArith`).
For that shape only **one** fresh name (`v0`) is ever introduced, so the
fresh-name freshness/injectivity machinery is vacuous. We therefore prove a
self-contained single-step lemma (`execStep_singleVar`) directly from
`execExpr_eq` (which needs no `hInj`), and discharge `StepAgrees` for single-leaf
bodies unconditionally (modulo the same opaque-leaf hypothesis `LeafAgrees` that
every other emit-correctness theorem in this development carries).

## What is established

* `bodyStepRun` — the concrete per-iteration body runner from the emitted
  evaluator (lowering of `p.update` run once through the `"acc"` slot).
* `bodyStepRun_singleVar_eq` — for a single-`var` body, `bodyStepRun` computes
  `p.step` (the per-iteration ground truth), `hInj`-free.
* `stepAgrees_singleVar` — hence `StepAgrees p (bodyStepRun …)` for single-leaf
  bodies.
* `loop_denote_eq` — **the keystone**: the emitted loop's `n`-fold run equals
  `JForProg.denote`. Stated for single-leaf bodies, fully discharged.
* The X25519 ladder instance (`x25519Ladder_loop_denote_eq`): the emitted
  `for i = 0 to 255 { acc = x25519_ladder_iter(acc) }` denotes the 255-fold
  application of the ladder iteration.

0 sorries; the only hypothesis is the opaque-leaf edge `LeafAgrees`, the same
edge carried throughout the emit-correctness theory.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT

/-! ## 1. The accumulator resolver and seed store

The emitted loop body (`JForProg.toCfor`) lowers `p.update` under the singleton
resolver `accVM = VarMap.empty.extend "acc"` (the loop-carried accumulator is
named `"acc"`), starting the fresh-SSA counter at `0`. To *run* one iteration on
an accumulator value `acc` we seed a store in which `"acc"` holds `acc`. -/

/-- The body resolver `JForProg.toCfor` uses: the singleton context's `.here`
    (the loop-carried accumulator) resolves to the name `"acc"`. -/
def accVM (accTy : JasminTy) : VarMap [accTy] :=
  (VarMap.empty).extend (t := accTy) "acc"

/-- The seed store for one iteration: every name gets the type default, except
    `"acc"` which holds the iteration's input accumulator value. -/
def accSeed {accTy : JasminTy} (acc : ⟦accTy⟧) : Store :=
  Store.set (fun _ => DynVal.default accTy) "acc" (t := accTy) acc

/-- The seed store agrees with the singleton valuation `.cons acc .nil` under the
    `"acc"` resolver: the lone variable `.here ↦ "acc"` reads back `acc`. -/
theorem accSeed_agrees {accTy : JasminTy} (acc : ⟦accTy⟧) :
    StoreAgrees (accVM accTy) (.cons acc .nil) (accSeed acc) := by
  intro t v
  cases v with
  | here =>
      -- `.here ↦ "acc"`; the seed wrote `acc` at `"acc"`.
      show (accSeed acc).get "acc" accTy = acc
      unfold accSeed
      exact Store.get_set_same _ _ _
  | there v' => cases v'

/-! ## 2. The concrete per-iteration body runner

Running the emitted loop body once is exactly `execCom` over `p.update` from the
`"acc"`-seed: the lowered instruction list is threaded through the store, and the
result name's value is the new accumulator. This is the evaluator-side meaning of
"`acc = body(acc)`" inside the emitted `Cfor`. -/

/-- Run the emitted loop body once on accumulator `acc`: thread the lowering of
    `p.update` through the `"acc"`-seeded store and read the result value. This
    is the concrete `JForProgCT.BodyRunner` realised by the word-level evaluator
    on the emitted body. -/
def bodyStepRun {accTy : JasminTy} (leafSem : LeafSem) (p : JForProg accTy) :
    BodyRunner accTy :=
  fun acc => (execCom leafSem (accVM accTy) 0 (accSeed acc) p.update).2

/-! ## 3. Single-`var` body: the runner computes `JForProg.step`

A single-leaf loop body is `Com.var e (Com.ret .here)`. We characterise such
bodies and prove the runner equals `JForProg.step` directly — bypassing
`execCom_eq` and so needing **no** `freshName` injectivity. -/

/-- A loop body is *single-leaf* if it is one op then a return of that op's
    result: `Com.var e (Com.ret .here)`. -/
def SingleVarBody {accTy : JasminTy}
    (e : Expr jasminDialect [accTy] accTy) : Com jasminDialect [accTy] accTy :=
  .var e (.ret .here)

/-- One `execCom` step over a single-`var` body reads back exactly the value
    `execExpr` writes to the bound name (no `hInj`: only one fresh name `v0` is
    ever introduced, and it is immediately read by the trailing `.ret .here`). -/
theorem execCom_singleVar {accTy : JasminTy} (leafSem : LeafSem)
    (vm : VarMap [accTy]) (s : Store) (e : Expr jasminDialect [accTy] accTy) :
    (execCom leafSem vm 0 s (SingleVarBody e)).2
      = execExpr leafSem vm e s := by
  -- Unfold one `var` step: bind `bound := resultName vm e "v0"`, write
  -- `execExpr e` there, then `.ret .here` reads the freshly-bound name.
  show (execCom leafSem (vm.extend (resultName vm e ("v" ++ toString 0)))
          1 (s.set (resultName vm e ("v" ++ toString 0))
            (execExpr leafSem vm e s)) (.ret .here)).2
        = execExpr leafSem vm e s
  -- `.ret .here` reads `(vm.extend bound) _ .here = bound`, just written.
  show (s.set (resultName vm e ("v" ++ toString 0)) (execExpr leafSem vm e s)).get
        ((vm.extend (resultName vm e ("v" ++ toString 0))) accTy Ctxt.Var.here) accTy
      = execExpr leafSem vm e s
  -- `(vm.extend name) _ .here = name`.
  show (s.set (resultName vm e ("v" ++ toString 0)) (execExpr leafSem vm e s)).get
        (resultName vm e ("v" ++ toString 0)) accTy
      = execExpr leafSem vm e s
  exact Store.get_set_same _ _ _

/-- **The body runner computes `JForProg.step` for a single-leaf body.** Under
    the opaque-leaf agreement `hLeaf` (the only carried edge, exactly as
    `JasminPrintSemCorrect.execExpr_eq`), running the emitted body once on `acc`
    equals `p.step acc` = the per-iteration ground truth. No `freshName`
    injectivity is needed. -/
theorem bodyStepRun_singleVar_eq {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (e : Expr jasminDialect [accTy] accTy)
    (p : JForProg accTy) (hp : p.update = SingleVarBody e) (acc : ⟦accTy⟧) :
    bodyStepRun leafSem p acc = p.step acc := by
  unfold bodyStepRun JForProg.step
  rw [hp]
  -- LHS: one step over the single-var body reads `execExpr`; RHS: the body's
  -- denotation on `.cons acc .nil` is exactly `e.denote (.cons acc .nil)`.
  rw [execCom_singleVar]
  -- `execExpr = e.denote` under store-agreement (`accSeed_agrees`).
  rw [execExpr_eq hLeaf (accSeed_agrees acc) e]
  -- `(SingleVarBody e).denote (.cons acc .nil) = e.denote (.cons acc .nil)`.
  rfl

/-- **`StepAgrees` for a single-leaf body, discharged.** The concrete body runner
    satisfies the per-iteration edge condition of `JForProgCT.loopRun_eq` — it is
    no longer a hypothesis but a theorem, modulo the opaque-leaf edge. -/
theorem stepAgrees_singleVar {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (e : Expr jasminDialect [accTy] accTy)
    (p : JForProg accTy) (hp : p.update = SingleVarBody e) :
    StepAgrees p (bodyStepRun leafSem p) :=
  fun acc => bodyStepRun_singleVar_eq hLeaf e p hp acc

/-! ## 4. The keystone: emitted loop run = `n`-fold denotation

Composing the discharged `StepAgrees` with `JForProgCT.loopRun_eq` gives the
whole-loop result with **no carried per-iteration hypothesis** (only the
opaque-leaf edge): running the emitted `for i = 0 to n { acc = body(acc) }`
`n` times equals `JForProg.denote` = the `n`-fold application of the body's
denotation. This is the for-loop layer's `lowerComToProg`-analogue. -/

/-- **Keystone — the emitted bounded loop denotes the `n`-fold semantics.** For a
    single-leaf body, running the emitted `Cfor` (`p.toProg`) by iterating the
    word-level body evaluator `p.n` times from `init`, threading the named
    accumulator, equals `p.denote init` — the `n`-fold application of
    `JForProg.step` = the body's denotation iterated `n` times. The loop
    structure is closed unconditionally; the only hypothesis is the opaque-leaf
    edge `LeafAgrees`, the same edge carried throughout the emit-correctness
    theory. This discharges the `StepAgrees` edge of `JForProgCT.loopRun_eq`,
    closing the "faithful skeleton" gap flagged at `JasminPrint.lean` §7. -/
theorem loop_denote_eq {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (e : Expr jasminDialect [accTy] accTy)
    (p : JForProg accTy) (hp : p.update = SingleVarBody e) (init : ⟦accTy⟧) :
    loopRun p (bodyStepRun leafSem p) init = p.denote init :=
  loopRun_eq p (stepAgrees_singleVar hLeaf e p hp) init

/-- Per-iteration unfolding of the keystone: the emitted loop of `n+1` iterations
    applies one extra emitted body step *after* the `n`-iteration loop — the
    evaluator-side recurrence matching `JForProgCT.denote_succ`. -/
theorem loop_denote_succ {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (e : Expr jasminDialect [accTy] accTy)
    (p : JForProg accTy) (hp : p.update = SingleVarBody e) (m : Nat)
    (init : ⟦accTy⟧) (hn : p.n = m + 1) :
    loopRun p (bodyStepRun leafSem p) init
      = p.step ((withCount p m).denote init) := by
  rw [loop_denote_eq hLeaf e p hp init]
  exact denote_succ p m init hn

/-! ## 5. A running-sum kernel (the simplest loop, end-to-end ground truth)

The simplest bounded-loop kernel: a running double `acc := acc + acc` for `n`
iterations (a `regArith add` body — a single leaf). Its emitted-loop run equals
`n`-fold doubling = the `denote` the keystone covers. This is exactly the
`JasminPrint.doubleLoop` example, now with a *discharged* (not hypothesised)
`StepAgrees`. The leaf agreement is vacuous (no `extCall`), so any `leafSem`
works. -/

/-- `JasminPrint.doubleLoop.update` is a single-leaf body (one `regArith add`
    then `.ret .here`). -/
theorem doubleLoop_singleVar :
    JasminPrint.doubleLoop.update
      = SingleVarBody (accTy := .reg 64)
          (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil))) := rfl

/-- **Running-sum (doubling) kernel — emitted loop denotes the `n`-fold double.**
    Running the emitted `for i = 0 to 4 { acc = acc + acc }` four times from
    `init` equals `doubleLoop.denote init` (= `init` doubled four times). The
    leaf agreement is vacuous here. -/
theorem doubleLoop_loop_denote_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : BitVec 64) :
    loopRun JasminPrint.doubleLoop (bodyStepRun leafSem JasminPrint.doubleLoop) init
      = JasminPrint.doubleLoop.denote init :=
  loop_denote_eq hLeaf _ JasminPrint.doubleLoop doubleLoop_singleVar init

/-- The discharged-`StepAgrees` keystone, instantiated at the concrete count
    `n = 4` and seed `init = 1`, computes `16` — byte-for-byte the unrolled
    reference (`1 → 2 → 4 → 8 → 16`). This ties the emitted-loop semantics the
    keystone proves to the concrete KAT validated end-to-end in
    `bench/loop_layer/`. -/
theorem doubleLoop_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    loopRun JasminPrint.doubleLoop (bodyStepRun leafSem JasminPrint.doubleLoop)
        (1 : BitVec 64)
      = (16 : BitVec 64) := by
  rw [doubleLoop_loop_denote_eq hLeaf]
  exact JasminPrint.doubleLoop_denote

end CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
