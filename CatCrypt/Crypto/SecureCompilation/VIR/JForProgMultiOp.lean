/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgNested
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgTreehash
public import CatCrypt.Crypto.SecureCompilation.VIR.FreshNameInjective

/-!
# The bounded-loop keystone for arbitrary multi-op straight-line bodies

`JForProgSemCorrect.loop_denote_eq` (task #60) proves the bounded-loop keystone —
"the emitted `for i = 0 to n { acc = body(acc) }` denotes the `n`-fold
semantics" — **only** for `SingleVarBody e = Com.var e (Com.ret .here)`: one op,
one binding. Its proof (`execCom_singleVar` / `bodyStepRun_singleVar_eq`)
sidesteps the whole-`Com` preservation theorem `JasminPrintSemCorrect.execCom_eq`
and so needs no fresh-name injectivity.

Real hash-leaf inner bodies (a Merkle compression, a Keccak round) bind several
fresh SSA names `v0, v1, …` and so need the full `execCom_eq` path, which carries
`hInj : Function.Injective freshName`. That hypothesis is now a **theorem**
(`FreshNameInjective.freshName_injective`, task #R1a), so this file lifts the
keystone to **arbitrary straight-line multi-op `Com` bodies**:

* `accVM_FreshFor` — the accumulator resolver `accVM` is `FreshFor … 0`: its only
  name `"acc"` begins with `'a'`, while every `freshName k = "v…"` begins with
  `'v'` (a single-character comparison, mirroring `paramsAndMap_FreshFor`).
* `bodyStepRun_multiOp_eq` — for **any** body with `StraightLine`, the concrete
  body runner `bodyStepRun` computes `JForProg.step`, via `execCom_eq` supplied
  with `hInj := freshName_injective`. **No carried injectivity hypothesis
  remains.**
* `stepAgrees_multiOp` / `loop_denote_eq_multiOp` — hence `StepAgrees` and the
  whole-loop keystone for multi-op bodies (composing with
  `JForProgCT.loopRun_eq` exactly as the single-var version does).
* `outerBodyRun_eq_multiOp` / `nested_loop_denote_eq_multiOp` and
  `levelRun_eq_multiOp` / `treehash_loop_denote_eq_multiOp` — the nested and
  treehash keystones lifted to multi-op inner / level bodies, mirroring
  `JForProgNested.nested_loop_denote_eq` and
  `JForProgTreehash.treehash_loop_denote_eq` but using the multi-op body runner.

The only carried hypothesis is the opaque-leaf edge `LeafAgrees`, exactly as the
single-var keystone — no `sorry`, axiom-clean.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.FreshNameInjective

/-! ## 1. The accumulator resolver is fresh for counter `0`

`accVM accTy = VarMap.empty.extend "acc"` has a single name `"acc"` (the
loop-carried accumulator), whose first character is `'a'`. Every fresh name
`freshName k = "v" ++ toString k` begins with `'v'`. So `"acc"` never equals any
`freshName k` — a one-character comparison, mirroring
`JasminPrintSemCorrect.paramsAndMap_FreshFor` (which separates `"p…"` from
`"v…"`). No Nat-string injectivity is needed for *this* step. -/

/-- The accumulator resolver `accVM` is `FreshFor … 0`: its only name `"acc"`
    (first char `'a'`) never equals a `freshName k = "v…"` name (first char
    `'v'`). -/
theorem accVM_FreshFor {accTy : JasminTy} : FreshFor (accVM accTy) 0 := by
  intro k t v _
  -- The only variable is `.here ↦ "acc"`; the empty tail has no `.there`.
  cases v with
  | here =>
      show ("acc" : String) ≠ freshName k
      intro heq
      -- `"acc"`'s first char is 'a'; `freshName k`'s is 'v'.
      have hacc : ("acc" : String).toList.head? = some 'a' := rfl
      have hv : (freshName k).toList.head? = some 'v' := by
        show (("v" ++ toString k : String)).toList.head? = some 'v'
        rw [String.toList_append, show ("v" : String).toList = ['v'] from rfl]
        rfl
      rw [heq, hv] at hacc
      exact absurd hacc (by decide)
  | there v' => cases v'

/-! ## 2. The body runner computes `JForProg.step` for any multi-op body

For any body with `StraightLine`, the concrete body runner `bodyStepRun` computes
`JForProg.step` — the per-iteration ground truth — via the whole-`Com`
preservation theorem `JasminPrintSemCorrect.execCom_eq`, supplied with
`hInj := freshName_injective` (now a theorem). Unlike `bodyStepRun_singleVar_eq`,
the body may bind several fresh SSA names `v0, v1, …`; the freshness machinery
(`FreshFor.extend_v`, under `freshName` injectivity) keeps them distinct from the
accumulator `"acc"` and from each other. **No carried injectivity hypothesis
remains.** -/

/-- **The body runner computes `JForProg.step` for an arbitrary multi-op
    straight-line body.** Under the opaque-leaf agreement `hLeaf` and the
    straight-line discipline `hSL` (every binder is non-`stackStore`), running the
    emitted body once on `acc` equals `p.step acc`. This is the multi-op analogue
    of `JForProgSemCorrect.bodyStepRun_singleVar_eq`, routed through
    `execCom_eq` with `hInj := freshName_injective` — so it carries no injectivity
    hypothesis. -/
theorem bodyStepRun_multiOp_eq {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (p : JForProg accTy)
    (hSL : StraightLine p.update) (acc : ⟦accTy⟧) :
    bodyStepRun leafSem p acc = p.step acc := by
  unfold bodyStepRun JForProg.step
  -- Whole-`Com` preservation on the body, with `hInj` discharged.
  exact execCom_eq hLeaf freshName_injective p.update hSL
    (accSeed_agrees acc) accVM_FreshFor

/-- **`StepAgrees` for an arbitrary multi-op straight-line body, discharged.** The
    concrete body runner satisfies the per-iteration edge condition of
    `JForProgCT.loopRun_eq` — a theorem (not a hypothesis), modulo the opaque-leaf
    edge `LeafAgrees`. Multi-op analogue of
    `JForProgSemCorrect.stepAgrees_singleVar`. -/
theorem stepAgrees_multiOp {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (p : JForProg accTy)
    (hSL : StraightLine p.update) :
    StepAgrees p (bodyStepRun leafSem p) :=
  fun acc => bodyStepRun_multiOp_eq hLeaf p hSL acc

/-! ## 3. The keystone, lifted to multi-op bodies

Composing the discharged multi-op `StepAgrees` with `JForProgCT.loopRun_eq` gives
the whole-loop result for **arbitrary straight-line bodies**, with no carried
per-iteration hypothesis (only the opaque-leaf edge). This is the core unlock for
real hash-leaf inner bodies. -/

/-- **Keystone (multi-op) — the emitted bounded loop denotes the `n`-fold
    semantics, for ANY straight-line body.** Running the emitted
    `for i = 0 to n { acc = body(acc) }` `n` times from `init`, threading the
    named accumulator, equals `p.denote init` — the `n`-fold application of
    `JForProg.step` = the body's denotation iterated `n` times. Unlike
    `JForProgSemCorrect.loop_denote_eq` (single-leaf only), the body may bind
    several fresh SSA names (a Merkle compression, a Keccak round). The only
    hypothesis is the opaque-leaf edge `LeafAgrees`; fresh-name injectivity is
    discharged by `FreshNameInjective.freshName_injective`. -/
theorem loop_denote_eq_multiOp {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (p : JForProg accTy)
    (hSL : StraightLine p.update) (init : ⟦accTy⟧) :
    loopRun p (bodyStepRun leafSem p) init = p.denote init :=
  loopRun_eq p (stepAgrees_multiOp hLeaf p hSL) init

/-- A `SingleVarBody e` is `StraightLine` exactly when `e` is non-`stackStore`
    (the single binder's freshness obligation). This bridges the single-var
    keystone's `SingleVarBody` shape into the multi-op keystone's `StraightLine`
    hypothesis. -/
theorem straightLine_singleVar {accTy : JasminTy}
    {e : Expr jasminDialect [accTy] accTy} (he : ExprNotStackStore e) :
    StraightLine (SingleVarBody e) :=
  ⟨he, trivial⟩

/-! ## 4. The nested keystone, lifted to multi-op inner bodies

The nested layer (`JForProgNested.nested_loop_denote_eq`) bakes in a single-leaf
inner body (`hInner : p.inner.update = SingleVarBody e`). We mirror it with the
multi-op inner-body runner: the outer body runner is the emitted inner loop run,
which equals `inner.denote` by the multi-op single-level keystone above. The
outer level closes by the same `foldl` congruence the single-var version uses. -/

/-- A `foldl` of two functions that agree everywhere over the same list and seed
    coincide. (Local mirror of `JForProgCT.foldl_congr_fun`, which is `private`.) -/
theorem foldl_congr_fun {accTy : JasminTy} {β : Type}
    (f g : ⟦accTy⟧ → β → ⟦accTy⟧)
    (hfg : ∀ acc u, f acc u = g acc u) :
    ∀ (l : List β) (init : ⟦accTy⟧), l.foldl f init = l.foldl g init
  | [], _ => rfl
  | _ :: l, init => by
      rw [List.foldl_cons, List.foldl_cons, hfg]
      exact foldl_congr_fun f g hfg l _

/-- **The outer body runner computes `outerStep` (= `inner.denote`), for a
    multi-op inner body.** Multi-op analogue of `JForProgNested.outerBodyRun_eq`:
    the inner straight-line body may bind several fresh names; the inner loop run
    still equals `inner.denote` by `loop_denote_eq_multiOp`. -/
theorem outerBodyRun_eq_multiOp {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (p : JForProgNested.NestedForProg accTy)
    (hInner : StraightLine p.inner.update) (acc : ⟦accTy⟧) :
    JForProgNested.outerBodyRun leafSem p acc = p.outerStep acc := by
  unfold JForProgNested.outerBodyRun JForProgNested.NestedForProg.outerStep
  exact loop_denote_eq_multiOp hLeaf p.inner hInner acc

/-- **Nested keystone (multi-op inner body).** Running the emitted nested loop
    (outer `for` over inner `for`) by iterating the outer body runner `outerN`
    times — each outer step running the emitted inner loop in full — equals
    `NestedForProg.denote init`, for an arbitrary straight-line inner body. The
    inner level reuses `loop_denote_eq_multiOp`; the outer level is closed by the
    `foldl` congruence. Multi-op analogue of
    `JForProgNested.nested_loop_denote_eq`. -/
theorem nested_loop_denote_eq_multiOp {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (p : JForProgNested.NestedForProg accTy)
    (hInner : StraightLine p.inner.update) (init : ⟦accTy⟧) :
    JForProgNested.nestedLoopRun leafSem p init = p.denote init := by
  unfold JForProgNested.nestedLoopRun JForProgNested.NestedForProg.denote
  exact foldl_congr_fun
    (fun acc _ => JForProgNested.outerBodyRun leafSem p acc)
    (fun acc _ => p.outerStep acc)
    (fun acc _ => outerBodyRun_eq_multiOp hLeaf p hInner acc)
    (List.range p.outerN) init

/-! ## 5. The treehash keystone, lifted to multi-op level bodies

The treehash layer (`JForProgTreehash.treehash_loop_denote_eq`) bakes in
`AllSingleVar` (every level body is `SingleVarBody`). We mirror it with the
multi-op level-body runner: each level's emitted loop run equals `level.denote`
by `loop_denote_eq_multiOp`, and the level dimension closes by induction. -/

/-- The per-level straight-line hypothesis for a treehash: every level's body is
    `StraightLine`. Multi-op analogue of `JForProgTreehash.AllSingleVar` (which
    requires each level body to be `SingleVarBody`). -/
def AllStraightLine {accTy : JasminTy}
    (levels : JForProgTreehash.TreehashProg accTy) : Prop :=
  ∀ lvl ∈ levels, StraightLine lvl.update

/-- **The per-level runner computes `levelStep` (= `lvl.denote`), for a multi-op
    level body.** Multi-op analogue of `JForProgTreehash.levelRun_eq`. -/
theorem levelRun_eq_multiOp {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (lvl : JForProg accTy)
    (hLvl : StraightLine lvl.update) (acc : ⟦accTy⟧) :
    JForProgTreehash.levelRun leafSem lvl acc = JForProgTreehash.levelStep lvl acc := by
  unfold JForProgTreehash.levelRun JForProgTreehash.levelStep
  exact loop_denote_eq_multiOp hLeaf lvl hLvl acc

/-- **Treehash keystone (multi-op level bodies).** Running the emitted
    `h`-`Cfor` sequence (each level a real `for`) by composing the per-level
    emitted single-level loop runners serially equals `TreehashProg.denote init`,
    for arbitrary straight-line level bodies. Each level reuses
    `loop_denote_eq_multiOp`; the level dimension is closed by induction. Multi-op
    analogue of `JForProgTreehash.treehash_loop_denote_eq`. -/
theorem treehash_loop_denote_eq_multiOp {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (levels : JForProgTreehash.TreehashProg accTy)
    (hAll : AllStraightLine levels) (init : ⟦accTy⟧) :
    JForProgTreehash.treehashLoopRun leafSem levels init
      = JForProgTreehash.TreehashProg.denote levels init := by
  induction levels generalizing init with
  | nil => rfl
  | cons lvl rest ih =>
      have hHead : StraightLine lvl.update := hAll lvl List.mem_cons_self
      have hTail : AllStraightLine rest :=
        fun l hl => hAll l (List.mem_cons_of_mem _ hl)
      unfold JForProgTreehash.treehashLoopRun JForProgTreehash.TreehashProg.denote
      rw [List.foldl_cons, List.foldl_cons, levelRun_eq_multiOp hLeaf lvl hHead init]
      exact ih hTail (JForProgTreehash.levelStep lvl init)

end CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
