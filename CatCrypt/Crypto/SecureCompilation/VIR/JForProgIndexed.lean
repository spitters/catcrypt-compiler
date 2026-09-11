/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp

/-!
# Index-parameterized bounded loops (`JForProgIdx`) — per-round constants as a theorem

`JForProgMultiOp.loop_denote_eq_multiOp` (task #R1) proves the bounded-loop
keystone for an arbitrary **straight-line multi-op** body — but the body is
**uniform**: it is a single `Com jasminDialect [accTy] accTy` whose only free
variable is the loop-carried accumulator. The loop counter `i` does **not**
appear in the body, so a uniform body cannot fold in a *different* constant each
iteration. That is exactly why the emitted Keccak ι (`RC[round]`), SHA-2 `K[t]` /
fixed σ shift amounts, and Poseidon2 per-round constants could, until now, only
be certified by the FULLY-UNROLLED emission (validated against the FIPS / Plonky3
KAT) — **not** by the loop denotation theorem, whose uniform skeleton folded in a
*fixed* constant (e.g. `RC[0]`).

This file closes that hole. It generalizes the loop layer so the body can see the
loop counter `i`:

* `JForProgIdx accTy` — like `JForProg` but its body is an **indexed family**
  `update : Nat → Com jasminDialect [accTy] accTy`. Iteration `i` runs the body
  `update i`, so each iteration may carry its own per-round constant. The
  per-round constant is materialized at `Com`-construction time as a literal
  immediate inside `update i` (the EXISTING immediate machinery the unrolled
  emission already uses — e.g. `KeccakEmit.emitIota bs immV i` reads `RC[i]` as a
  literal operand). **No new dialect op is needed:** the index selects *which*
  `Com` body is emitted, and each body carries its own constant via the immediate
  resolver. (Part B: least-invasive mechanism — no `JasminOp` constructor added,
  no exhaustive-match cascade.)

* `JForProgIdx.stepI` / `denoteI` — the **index-dependent** `n`-fold semantics:
  `denoteI init = (List.range n).foldl (fun acc i => stepI i acc) init`. Unlike
  `JForProg.denote` (which folds `fun acc _ => …`, ignoring the index), this folds
  `fun acc i => …`, so the index genuinely threads through.

* `bodyStepRunI` / `loopRunI` — the concrete index-parameterized evaluator: at
  iteration `i`, run the emitted body `update i` once on the accumulator through
  the named `"acc"` slot.

* `loopRunI_eq_denoteI` — **the index-parameterized analogue of
  `loop_denote_eq_multiOp`**: under the (per-index) straight-line discipline and
  the opaque-leaf edge `LeafAgrees`, the emitted indexed loop
  `for i = 0 to n { acc = update(i)(acc) }` denotes the `n`-fold application of the
  index-dependent step. Routed through the SAME `freshName_injective` discharge
  (each per-index body reuses `JForProgMultiOp.bodyStepRun_multiOp_eq`), then the
  index dimension closes by a fold congruence that threads `i`.

The only carried hypothesis is the opaque-leaf edge `LeafAgrees`, exactly as the
uniform multi-op keystone — no `sorry`, axiom-clean.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JForProgIndexed

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
open CatCrypt.Crypto.SecureCompilation.VIR.FreshNameInjective

/-! ## 1. The index-parameterized bounded loop -/

/-- A bounded for-loop whose body is an **indexed family** of accumulator
    transforms. Like `JForProg`, but the body `update i` may depend on the loop
    counter `i` — letting each iteration carry its own per-round constant
    (`RC[i]`, `K[i]`, a fixed σ shift) materialized as a literal immediate inside
    the `Com` body `update i`. -/
structure JForProgIdx (accTy : JasminTy) where
  /-- Static iteration count. -/
  n : Nat
  /-- The index-parameterized accumulator-update body family: at iteration `i`,
      `acc ↦ (update i)(acc)`. The per-round constant for round `i` lives inside
      `update i` as a literal immediate. -/
  update : Nat → Com jasminDialect [accTy] accTy

/-- One iteration at index `i`: run the body `update i` on the singleton
    valuation `[acc]`. The index-dependent analogue of `JForProg.step`. -/
def JForProgIdx.stepI {accTy : JasminTy} (p : JForProgIdx accTy)
    (i : Nat) (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  (p.update i).denote (.cons acc .nil)

/-- The **index-dependent** `n`-fold denotation: fold the index-dependent step
    over `List.range n`, threading the counter `i`. Contrast `JForProg.denote`,
    which folds `fun acc _ => …` and so ignores the index. -/
def JForProgIdx.denoteI {accTy : JasminTy} (p : JForProgIdx accTy)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range p.n).foldl (fun acc i => p.stepI i acc) init

/-- The fixed-index `JForProg` for iteration `i`: the uniform multi-op loop with
    body `p.update i`. Used to reuse the uniform multi-op keystone per index. -/
def JForProgIdx.atIndex {accTy : JasminTy} (p : JForProgIdx accTy) (i : Nat) :
    JForProg accTy :=
  { n := p.n, update := p.update i }

@[simp] theorem JForProgIdx.atIndex_update {accTy : JasminTy}
    (p : JForProgIdx accTy) (i : Nat) :
    (p.atIndex i).update = p.update i := rfl

@[simp] theorem JForProgIdx.atIndex_step {accTy : JasminTy}
    (p : JForProgIdx accTy) (i : Nat) (acc : ⟦accTy⟧) :
    (p.atIndex i).step acc = p.stepI i acc := rfl

/-! ## 2. The concrete index-parameterized body runner

At iteration `i`, run the emitted body `update i` once on accumulator `acc`,
threading the named `"acc"` slot — exactly `JForProgSemCorrect.bodyStepRun` of
the fixed-index `JForProg` `p.atIndex i`. -/

/-- Run the emitted indexed loop body once at index `i` on accumulator `acc`:
    thread the lowering of `update i` through the `"acc"`-seeded store and read
    the result value. The index-parameterized analogue of
    `JForProgSemCorrect.bodyStepRun`. -/
def bodyStepRunI {accTy : JasminTy} (leafSem : LeafSem) (p : JForProgIdx accTy)
    (i : Nat) (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  (execCom leafSem (accVM accTy) 0 (accSeed acc) (p.update i)).2

/-- `bodyStepRunI` at index `i` is exactly `bodyStepRun` of the fixed-index
    `JForProg` `p.atIndex i`. -/
theorem bodyStepRunI_eq_bodyStepRun {accTy : JasminTy} (leafSem : LeafSem)
    (p : JForProgIdx accTy) (i : Nat) (acc : ⟦accTy⟧) :
    bodyStepRunI leafSem p i acc = bodyStepRun leafSem (p.atIndex i) acc := rfl

/-- Run the emitted indexed loop abstractly: iterate the index-parameterized body
    runner `n` times, threading the counter `i` into each step. This is the
    evaluator-side `n`-fold iteration the emitted `Cfor` performs — the index `i`
    selecting body `update i` at iteration `i`. -/
def loopRunI {accTy : JasminTy} (leafSem : LeafSem) (p : JForProgIdx accTy)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range p.n).foldl (fun acc i => bodyStepRunI leafSem p i acc) init

/-! ## 3. Per-index step agreement, via the uniform multi-op keystone

For each fixed index `i`, the body `update i` is a straight-line multi-op `Com`,
so `JForProgMultiOp.bodyStepRun_multiOp_eq` (routed through `execCom_eq` with
`hInj := freshName_injective`) gives `bodyStepRun (p.atIndex i) acc =
(p.atIndex i).step acc = p.stepI i acc`. No `freshName` injectivity is carried;
it is discharged inside R1. -/

/-- The per-index straight-line discipline: every body `update i` is
    `StraightLine` (each binder non-`stackStore`). The natural per-round constant
    materialization (a literal immediate) keeps every binder a `regArith`, so this
    holds by construction for the crypto bodies (Keccak ι, SHA-2 `K[t]`, …). -/
def AllStraightLineIdx {accTy : JasminTy} (p : JForProgIdx accTy) : Prop :=
  ∀ i : Nat, StraightLine (p.update i)

/-- **Per-index step agreement.** At any index `i`, the concrete indexed body
    runner computes the index-dependent step `p.stepI i`, via the uniform multi-op
    body runner agreement `JForProgMultiOp.bodyStepRun_multiOp_eq`. The only
    carried edge is the opaque-leaf `LeafAgrees`; fresh-name injectivity is
    discharged inside R1. -/
theorem bodyStepRunI_eq_stepI {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (p : JForProgIdx accTy)
    (hSL : AllStraightLineIdx p) (i : Nat) (acc : ⟦accTy⟧) :
    bodyStepRunI leafSem p i acc = p.stepI i acc := by
  rw [bodyStepRunI_eq_bodyStepRun]
  -- The fixed-index uniform multi-op keystone, with `hInj` discharged inside R1.
  rw [bodyStepRun_multiOp_eq hLeaf (p.atIndex i) (hSL i) acc]
  rfl

/-! ## 4. The keystone: emitted indexed loop run = index-dependent `n`-fold
       denotation

A `foldl` of two index-threading functions that agree on every `(acc, i)` over
the same list and seed coincide. With per-index agreement (§3) this closes the
index-parameterized analogue of `loop_denote_eq_multiOp`: the emitted indexed
loop denotes the index-dependent semantics. -/

/-- A `foldl` of two index-threading functions that agree everywhere over the
    same list and seed coincide. (Index-threading mirror of
    `JForProgMultiOp.foldl_congr_fun`, which threads no index.) -/
theorem foldl_congr_idx {accTy : JasminTy}
    (f g : ⟦accTy⟧ → Nat → ⟦accTy⟧)
    (hfg : ∀ acc i, f acc i = g acc i) :
    ∀ (l : List Nat) (init : ⟦accTy⟧), l.foldl f init = l.foldl g init
  | [], _ => rfl
  | i :: l, init => by
      rw [List.foldl_cons, List.foldl_cons, hfg]
      exact foldl_congr_idx f g hfg l _

/-- **Keystone (index-parameterized) — the emitted indexed bounded loop denotes
    the index-dependent `n`-fold semantics.** Running the emitted
    `for i = 0 to n { acc = update(i)(acc) }` `n` times from `init`, threading the
    named accumulator AND the loop counter `i` (each iteration running the
    per-index body `update i`, which carries its own per-round constant as a
    literal immediate), equals `p.denoteI init` — the `n`-fold application of the
    index-dependent step `JForProgIdx.stepI`.

    This is the index-parameterized analogue of
    `JForProgMultiOp.loop_denote_eq_multiOp` (which covers only a UNIFORM body):
    the body may now depend on the loop counter, so a per-round-varying constant
    `RC[i]` / `K[i]` / a fixed σ shift is a genuine input to the certified
    denotation — closing the "uniform skeleton" hole. The per-index bodies route
    through the SAME `freshName_injective` discharge (via R1's
    `bodyStepRun_multiOp_eq`); the only hypothesis is the opaque-leaf edge
    `LeafAgrees`. -/
theorem loopRunI_eq_denoteI {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (p : JForProgIdx accTy)
    (hSL : AllStraightLineIdx p) (init : ⟦accTy⟧) :
    loopRunI leafSem p init = p.denoteI init := by
  unfold loopRunI JForProgIdx.denoteI
  exact foldl_congr_idx
    (fun acc i => bodyStepRunI leafSem p i acc)
    (fun acc i => p.stepI i acc)
    (fun acc i => bodyStepRunI_eq_stepI hLeaf p hSL i acc)
    (List.range p.n) init

/-! ## 5. Recovering the uniform loop as the constant-index special case

A `JForProgIdx` whose body family is constant (`update i = body` for all `i`) is
exactly the uniform `JForProg` of `JForProgMultiOp`. So the index-parameterized
keystone strictly generalizes the uniform one: instantiating at a constant family
recovers `loop_denote_eq_multiOp`. -/

/-- The constant-index family: every iteration runs the same uniform body. -/
def ofUniform {accTy : JasminTy} (p : JForProg accTy) : JForProgIdx accTy :=
  { n := p.n, update := fun _ => p.update }

@[simp] theorem ofUniform_update {accTy : JasminTy} (p : JForProg accTy) (i : Nat) :
    (ofUniform p).update i = p.update := rfl

/-- For a uniform body, the index-dependent denotation collapses to the uniform
    `JForProg.denote`. -/
theorem denoteI_ofUniform {accTy : JasminTy} (p : JForProg accTy) (init : ⟦accTy⟧) :
    (ofUniform p).denoteI init = p.denote init := by
  unfold JForProgIdx.denoteI JForProg.denote
  rfl

/-- The index-parameterized keystone, instantiated at a constant family, recovers
    the uniform multi-op keystone `loop_denote_eq_multiOp`: the emitted indexed
    loop over a uniform body denotes `JForProg.denote`. -/
theorem loopRunI_ofUniform_eq {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (p : JForProg accTy)
    (hSL : StraightLine p.update) (init : ⟦accTy⟧) :
    loopRunI leafSem (ofUniform p) init = p.denote init := by
  rw [loopRunI_eq_denoteI hLeaf (ofUniform p) (fun _ => hSL) init,
      denoteI_ofUniform]

/-! ## 6. The index register in the body context (the stackLoad-by-index path)

§1–5 let the body *family* `update i` differ per iteration — but where does the
per-round constant `RC[i]` actually enter a single `regArith` body over the lone
accumulator `[accTy]`? It cannot: with a single-accumulator `[accTy]` body and
the straight-line (no `stackStore`, and for a leaf-free kernel no `extCall`)
discipline, there is no in-body literal op to synthesise a fixed nonzero
constant, and the only `stackArr`-returning ops are exactly `stackStore` /
`extCall` (so a `stackArr`-accumulator update is not straight-line / not
leaf-free). **This is why the stackLoad-by-index path needs the body context to
carry the index register and a (loop-invariant) constant table** — the least
invasive mechanism that adds *no* `JasminOp` constructor (so no exhaustive-match
cascade across emit / printer / CT predicate / psem-alignment).

We model this directly. The body lives over the **three-slot** context
`tabCtxt accTy = [accTy, .reg 64, .stackArr 64 nRC]`:

* `.here`              — the loop-carried accumulator (name `"acc"`);
* `.there .here`       — the loop **index register** `i` (name `"idx"`), bound by
  the loop counter at each iteration;
* `.there (.there .here)` — the loop-invariant **constant table** (name `"rc"`),
  a `stackArr 64 nRC` holding `RC[0..nRC-1]`.

A round body reads `RC[i]` by `stackLoad rc idx` (a `regArith`-free, but
`StraightLine`, op — it binds a fresh name), then folds it in by `regArith`. The
constant is genuinely per-round (it is `table[i]`, and the loop threads the real
`i`), so the certified denotation now carries the actual per-round-varying input.
-/

/-- The three-slot body context: accumulator, loop index register, constant table.
    The table width is fixed at 64 bits; `nRC` is the number of round constants. -/
abbrev tabCtxt (accTy : JasminTy) (nRC : Nat) : Ctxt jasminDialect :=
  [accTy, .reg 64, .stackArr 64 nRC]

/-- Names for the three slots: the accumulator `"acc"`, the index register
    `"idx"`, the constant table `"rc"`. First chars `'a'`, `'i'`, `'r'` — all
    distinct from the `'v'` of every `freshName k`, so the resolver is `FreshFor`
    for counter `0` by a one-character comparison (no Nat-string injectivity). -/
def tabVM (accTy : JasminTy) (nRC : Nat) : VarMap (tabCtxt accTy nRC) :=
  fun _ v =>
    match v with
    | .here => "acc"
    | .there .here => "idx"
    | .there (.there .here) => "rc"

/-- The seed store for one indexed iteration: `"acc"` holds the accumulator,
    `"idx"` holds the loop index `i` (as a `reg 64`), `"rc"` holds the constant
    table; every other name gets the type default. -/
def tabSeed {accTy : JasminTy} {nRC : Nat} (acc : ⟦accTy⟧) (i : Nat)
    (table : Fin nRC → BitVec 64) : Store :=
  ((Store.set (Store.set (Store.set (fun _ => DynVal.default accTy)
      "acc" (t := accTy) acc)
      "idx" (t := .reg 64) (BitVec.ofNat 64 i))
      "rc" (t := .stackArr 64 nRC) table))

/-- The three-slot resolver is `FreshFor … 0`: each name `"acc"`/`"idx"`/`"rc"`
    has first char `'a'`/`'i'`/`'r'`, never the `'v'` of `freshName k`. Mirrors
    `JForProgMultiOp.accVM_FreshFor`. -/
theorem tabVM_FreshFor {accTy : JasminTy} {nRC : Nat} :
    FreshFor (tabVM accTy nRC) 0 := by
  -- `freshName k = "v…"` has first char `'v'`; the names `"acc"/"idx"/"rc"` have
  -- first chars `'a'/'i'/'r'`. A name with first char `c ≠ 'v'` is never a
  -- `freshName k` (a one-character comparison, mirroring `accVM_FreshFor`).
  have hv : ∀ k, (freshName k).toList.head? = some 'v' := by
    intro k
    show (("v" ++ toString k : String)).toList.head? = some 'v'
    rw [String.toList_append, show ("v" : String).toList = ['v'] from rfl]; rfl
  have hne : ∀ (nm : String) (c : Char), nm.toList.head? = some c → c ≠ 'v' →
      ∀ k, nm ≠ freshName k := by
    intro nm c hc hcv k heq
    rw [heq, hv k] at hc
    exact hcv (Option.some.inj hc).symm
  intro k t v _
  match v with
  | .here => exact hne "acc" 'a' rfl (by decide) k
  | .there .here => exact hne "idx" 'i' rfl (by decide) k
  | .there (.there .here) => exact hne "rc" 'r' rfl (by decide) k

/-- The seed store agrees with the three-slot valuation `[acc, ofNat i, table]`
    under the `tabVM` resolver: each slot reads back its seeded value. Mirrors
    `JForProgSemCorrect.accSeed_agrees`. -/
theorem tabSeed_agrees {accTy : JasminTy} {nRC : Nat} (acc : ⟦accTy⟧) (i : Nat)
    (table : Fin nRC → BitVec 64) :
    StoreAgrees (tabVM accTy nRC)
      (.cons acc (.cons (BitVec.ofNat 64 i) (.cons table .nil)))
      (tabSeed acc i table) := by
  intro t v
  match v with
  | .here =>
      show (tabSeed acc i table).get "acc" accTy = acc
      unfold tabSeed
      rw [Store.get_set_other _ (by decide), Store.get_set_other _ (by decide),
          Store.get_set_same]
  | .there .here =>
      show (tabSeed acc i table).get "idx" (.reg 64) = BitVec.ofNat 64 i
      unfold tabSeed
      rw [Store.get_set_other _ (by decide), Store.get_set_same]
  | .there (.there .here) =>
      show (tabSeed acc i table).get "rc" (.stackArr 64 nRC) = table
      unfold tabSeed
      rw [Store.get_set_same]

/-- An **index-parameterized loop with the index register and a constant table in
    its body context.** `body` is a single straight-line `Com` over
    `tabCtxt accTy nRC`; iteration `i` runs it on the valuation
    `[acc, ofNat 64 i, table]`, so the body may read `RC[i]` (= `table[i]`) by a
    `stackLoad rc idx`. The table is loop-invariant; the index register threads
    the real counter. -/
structure JForProgTab (accTy : JasminTy) (nRC : Nat) where
  /-- Static iteration count. -/
  n : Nat
  /-- The loop-invariant constant table `RC[0..nRC-1]`. -/
  table : Fin nRC → BitVec 64
  /-- The (uniform-shaped) body over `[acc, idx, rc]`; the per-round variation is
      entirely the value read from `rc` at `idx`. -/
  body : Com jasminDialect (tabCtxt accTy nRC) accTy

/-- One iteration at index `i`: run `body` on `[acc, ofNat 64 i, table]`. The
    index-and-table-dependent analogue of `JForProg.step`. -/
def JForProgTab.stepT {accTy : JasminTy} {nRC : Nat} (p : JForProgTab accTy nRC)
    (i : Nat) (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  p.body.denote (.cons acc (.cons (BitVec.ofNat 64 i) (.cons p.table .nil)))

/-- The index-dependent `n`-fold denotation: fold `stepT` over `List.range n`,
    threading the counter `i` (which selects `table[i]`). -/
def JForProgTab.denoteT {accTy : JasminTy} {nRC : Nat} (p : JForProgTab accTy nRC)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range p.n).foldl (fun acc i => p.stepT i acc) init

/-- The concrete index-and-table body runner: at iteration `i`, run the emitted
    `body` once on `acc` through the three-slot seed store (with `"idx"` holding
    `i` and `"rc"` holding the table). -/
def bodyStepRunT {accTy : JasminTy} {nRC : Nat} (leafSem : LeafSem)
    (p : JForProgTab accTy nRC) (i : Nat) (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  (execCom leafSem (tabVM accTy nRC) 0 (tabSeed acc i p.table) p.body).2

/-- The abstract indexed loop run with index register + table: iterate the
    table-and-index body runner `n` times, threading the counter `i`. -/
def loopRunT {accTy : JasminTy} {nRC : Nat} (leafSem : LeafSem)
    (p : JForProgTab accTy nRC) (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range p.n).foldl (fun acc i => bodyStepRunT leafSem p i acc) init

/-- **Per-index step agreement (table form).** At any index `i`, the concrete
    table-and-index body runner computes `p.stepT i` — via the whole-`Com`
    preservation `JasminPrintSemCorrect.execCom_eq` on the three-slot context,
    with fresh-name injectivity discharged by `freshName_injective` and the
    resolver freshness / store agreement by `tabVM_FreshFor` / `tabSeed_agrees`.
    The only carried edge is the opaque-leaf `LeafAgrees`. -/
theorem bodyStepRunT_eq_stepT {accTy : JasminTy} {nRC : Nat} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (p : JForProgTab accTy nRC)
    (hSL : StraightLine p.body) (i : Nat) (acc : ⟦accTy⟧) :
    bodyStepRunT leafSem p i acc = p.stepT i acc := by
  unfold bodyStepRunT JForProgTab.stepT
  exact execCom_eq hLeaf freshName_injective p.body hSL
    (tabSeed_agrees acc i p.table) tabVM_FreshFor

/-- **Keystone (index register + constant table) — the emitted indexed loop
    denotes the index-dependent `n`-fold semantics.** Running the emitted
    `for i = 0 to n { acc = body(acc, i, table)(acc) }` `n` times from `init`,
    threading the named accumulator, the loop index register `"idx"` and the
    loop-invariant constant table `"rc"`, equals `p.denoteT init` — the `n`-fold
    application of the table-and-index step `JForProgTab.stepT`, where iteration
    `i` reads the **actual** per-round constant `table[i]`. This is the genuine
    per-round-constant analogue of `loop_denote_eq_multiOp`: the constant is a
    real input to the certified denotation, not a fixed `RC[0]` skeleton. Routed
    through the SAME `freshName_injective` discharge (via `execCom_eq`); the only
    hypothesis is the opaque-leaf edge `LeafAgrees`. -/
theorem loopRunT_eq_denoteT {accTy : JasminTy} {nRC : Nat} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (p : JForProgTab accTy nRC)
    (hSL : StraightLine p.body) (init : ⟦accTy⟧) :
    loopRunT leafSem p init = p.denoteT init := by
  unfold loopRunT JForProgTab.denoteT
  exact foldl_congr_idx
    (fun acc i => bodyStepRunT leafSem p i acc)
    (fun acc i => p.stepT i acc)
    (fun acc i => bodyStepRunT_eq_stepT hLeaf p hSL i acc)
    (List.range p.n) init

end CatCrypt.Crypto.SecureCompilation.VIR.JForProgIndexed
