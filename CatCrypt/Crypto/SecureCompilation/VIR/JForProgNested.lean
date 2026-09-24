/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect

/-!
# Nested bounded loops: the emitted outer-`for`-over-inner-`for` denotes the
# two-level `n`-fold semantics (`NestedForProg`)

This module is the **additive nesting layer** on top of the single-level loop
theorem (`JForProgSemCorrect.loop_denote_eq`, `JForProgCT.loopRun_eq`). It
imports the single-level layer (`JForProgSemCorrect.lean`,
`JasminPrint.JForProg` / `toCfor` / `toProg`, `JForProgCT.lean`) and composes
its results without modifying it.

## The nested construct

A `NestedForProg accTy` is a two-level bounded loop:

* an outer trip count `outerN : Nat`, and
* an `inner : JForProg accTy` — a single-level bounded loop over the *same*
  accumulator type. The outer accumulator carries the inner loop's state.

Its denotation is the **outer-`outerN`-fold of (the inner-`inner.n`-fold)**:

```
NestedForProg.denote init
  = (List.range outerN).foldl (fun acc _ => inner.denote acc) init
```

i.e. each outer iteration runs the whole inner loop on the accumulator. This is
precisely the shape of the fixed-depth trees that motivate it: the FAEST binary
GGM seed tree (`faest-hax/src/ggm_tree.rs`) and the XMSS / SLH-DSA Merkle
treehash both pair-up / expand a tree level inside an outer level loop — the
inner loop folds one level, the outer loop steps the levels, with the whole tree
state in the accumulator.

## The emission

`NestedForProg.toCfor` emits an **outer `for` whose body contains an inner
`for`** — the structural target. The inner `for` is the *actual* emitted
`JForProg.toCfor` of `inner` (the verified single-level loop the main theorem
covers), wrapped in an outer `Cfor` over `0..outerN`. The shared `ppInstrR`
already prints a `Cfor` body recursively, so the emitted `.jazz` is literally an
inner `for` indented inside an outer `for`.

## The denotation-preservation theorem (the deliverable)

`nested_loop_denote_eq`: running the emitted nested loop — iterating the outer
body runner `outerN` times, where each outer step runs the emitted inner loop in
full — equals `NestedForProg.denote init`. The proof:

1. **Inner level (reuse, not re-prove):** for a single-leaf inner body, the
   emitted inner loop run equals `inner.denote` by the *already proven*
   `JForProgSemCorrect.loop_denote_eq`. So the inner loop runner *is* the outer's
   per-iteration step function (`outerStep`).
2. **Outer level (induct):** the outer `StepAgrees` (outer body run = outer step
   = `inner.denote`) is discharged by step 1, and `JForProgCT.loopRun_eq` closes
   the outer `outerN`-fold against `NestedForProg.denote`.

The only carried hypothesis is the opaque-leaf edge `LeafAgrees`, exactly as the
single-level main theorem — no open goals, axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## A concrete validating kernel: the 2D accumulate

`grid2D` is the simplest nested kernel that validates nesting: an outer loop of
`outerN` iterations, each running an inner loop of `inner.n` iterations of
`acc := acc + acc` (doubling). The total is doubling `outerN * inner.n` times.
For `outerN = 3`, `inner.n = 2` from `1` this computes `1 → 2^6 = 64`, KAT'd
byte-identical in `bench/nested_loop/`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JForProgNested

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect

/-! ## 1. The nested loop construct -/

/-- A **two-level (nested) bounded loop** over a single accumulator type. The
    outer loop runs `outerN` times; each outer iteration runs the *whole* inner
    single-level loop `inner` on the accumulator. The outer accumulator carries
    the inner loop's state — the treehash / GGM idiom (outer over tree levels,
    inner folds a level). -/
structure NestedForProg (accTy : JasminTy) where
  /-- The outer (static) trip count: number of times the inner loop is run. -/
  outerN : Nat
  /-- The inner single-level bounded loop, run in full on each outer iteration. -/
  inner : JForProg accTy

/-- One outer iteration: run the whole inner loop on the accumulator. This is the
    outer loop's per-iteration step — the inner loop's `denote`. -/
def NestedForProg.outerStep {accTy : JasminTy} (p : NestedForProg accTy)
    (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  p.inner.denote acc

/-- **Two-level `n`-fold denotation**: iterate the inner loop's denotation
    `outerN` times from the initial accumulator. No fuel — both counts are
    static. -/
def NestedForProg.denote {accTy : JasminTy} (p : NestedForProg accTy)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range p.outerN).foldl (fun acc _ => p.outerStep acc) init

/-! ## 2. The emitted nested `Cfor` (outer `for` over inner `for`) -/

/-- Emit the nested loop as an **outer `Cfor` whose body is the inner `Cfor`**.
    The inner `for` is the *actual* emitted single-level loop
    `inner.toCfor` (the verified loop the main theorem covers); the outer `for`
    runs `0..outerN` with the inner loop as its sole body instruction. The
    shared `ppInstrR` prints the inner `for` recursively-indented inside the
    outer `for`. The outer loop index is `j` (the inner loop's index is `i`,
    from `JForProg.toCfor`), so the two indices do not collide. -/
def NestedForProg.toCfor {accTy : JasminTy} (p : NestedForProg accTy) :
    CatCrypt.Crypto.Jasmin.InstrR :=
  .Cfor (mkVarI "j" .inlineInt)
    { dir := .UpTo, lo := 0, hi := p.outerN }
    [p.inner.toCfor]

/-- Lower a `NestedForProg` to a single-function `JasminProg`: parameter `acc`
    (the initial accumulator), the nested `Cfor` (outer over inner), and
    `ret acc`. -/
def NestedForProg.toProg {accTy : JasminTy} (name : String)
    (p : NestedForProg accTy) : CatCrypt.Crypto.Jasmin.JasminProg :=
  let fd : CatCrypt.Crypto.Jasmin.FunDecl :=
    { name := { name := name }
      params := [{ var := mkVarI "acc" accTy }]
      body := [p.toCfor]
      results := [mkVarI "acc" accTy] }
  { funcs := [fd] }

/-! ## 3. Structural facts about the emission -/

/-- **Structural fact: the outer loop is an `UpTo` loop over `0..outerN` whose
    single body instruction is the inner `Cfor`.** -/
theorem toCfor_outer {accTy : JasminTy} (p : NestedForProg accTy) :
    p.toCfor
      = .Cfor (mkVarI "j" .inlineInt)
          { dir := .UpTo, lo := 0, hi := p.outerN } [p.inner.toCfor] := rfl

/-- **Structural fact: the inner body of the outer `for` is itself a `for`
    (`Cfor`).** This is the headline structural property: an inner `for` nested
    inside an outer `for`. -/
theorem toCfor_inner_is_cfor {accTy : JasminTy} (p : NestedForProg accTy) :
    ∃ v r body, p.inner.toCfor = .Cfor v r body :=
  ⟨_, _, _, rfl⟩

/-- **Structural fact: the emitted program is single-function, one loop body,
    one accumulator parameter, one result.** -/
theorem toProg_shape {accTy : JasminTy} (name : String) (p : NestedForProg accTy) :
    (p.toProg name).funcs.length = 1
      ∧ ((p.toProg name).funcs.head?.map (fun fd => fd.body.length)) = some 1
      ∧ ((p.toProg name).funcs.head?.map (fun fd => fd.params.length)) = some 1
      ∧ ((p.toProg name).funcs.head?.map (fun fd => fd.results.length)) = some 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 4. `n`-fold unfolding of the nested denotation -/

/-- **Two-level `n`-fold unfolding (List.range form).** The nested denotation is
    the left-fold of the inner loop's denotation over `List.range outerN`. -/
theorem denote_eq_foldl {accTy : JasminTy} (p : NestedForProg accTy)
    (init : ⟦accTy⟧) :
    p.denote init
      = (List.range p.outerN).foldl (fun acc _ => p.inner.denote acc) init := rfl

/-- **The empty outer loop is the identity.** Zero outer iterations return the
    initial accumulator unchanged (the inner loop never runs). -/
theorem denote_outer_zero {accTy : JasminTy} (p : NestedForProg accTy)
    (init : ⟦accTy⟧) (h : p.outerN = 0) : p.denote init = init := by
  unfold NestedForProg.denote
  rw [h]
  rfl

/-! ## 5. The outer body runner is the emitted inner loop

The outer loop's per-iteration body runner is *the whole emitted inner loop run*.
We package it as the single-level `loopRun` of the inner program with the inner
body runner. For a single-leaf inner body, this equals `inner.denote` by the
already-proven single-level main theorem `loop_denote_eq` — so the outer body runner
is exactly `NestedForProg.outerStep`. -/

/-- The outer body runner: running the emitted inner loop in full on accumulator
    `acc` (the single-level `loopRun` of `inner` with its emitted body runner).
    This is the evaluator-side meaning of "run the inner `for` once per outer
    iteration". -/
def outerBodyRun {accTy : JasminTy} (leafSem : LeafSem) (p : NestedForProg accTy) :
    BodyRunner accTy :=
  fun acc => loopRun p.inner (bodyStepRun leafSem p.inner) acc

/-- **The outer body runner computes `outerStep` (= `inner.denote`).** For a
    single-leaf inner body, running the emitted inner loop in full equals the
    inner loop's `n`-fold denotation — by the *already-proven* single-level
    main theorem `JForProgSemCorrect.loop_denote_eq` (reused, not re-derived). Hence
    the outer body runner is exactly the outer step function. The only carried
    hypothesis is the opaque-leaf edge `LeafAgrees`. -/
theorem outerBodyRun_eq {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (p : NestedForProg accTy)
    (e : Expr jasminDialect [accTy] accTy)
    (hInner : p.inner.update = SingleVarBody e) (acc : ⟦accTy⟧) :
    outerBodyRun leafSem p acc = p.outerStep acc := by
  unfold outerBodyRun NestedForProg.outerStep
  -- Reuse the single-level main theorem for the inner loop.
  exact loop_denote_eq hLeaf e p.inner hInner acc

/-! ## 6. The main theorem: emitted nested loop run = two-level `n`-fold denotation

The outer level cannot route through `JForProgCT.loopRun_eq`: that lemma
compares against `JForProg.denote`, whose per-iteration step is *one* `Com`
application (`update.denote (.cons acc .nil)`), whereas the outer step is a
*whole inner loop* (`inner.denote acc`). So we close the outer level with a
self-contained `foldl` congruence: both `nestedLoopRun` and `NestedForProg.denote`
are left-folds over `List.range outerN`, and their per-element functions agree on
every accumulator by `outerBodyRun_eq`. -/

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

/-- Run the emitted nested loop abstractly: iterate the outer body runner
    `outerN` times, where each outer step runs the emitted inner loop. This is
    the evaluator-side two-level iteration the emitted nested `Cfor` performs. -/
def nestedLoopRun {accTy : JasminTy} (leafSem : LeafSem) (p : NestedForProg accTy)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range p.outerN).foldl (fun acc _ => outerBodyRun leafSem p acc) init

/-- **Main theorem — the emitted nested loop denotes the two-level `n`-fold
    semantics.** For a single-leaf inner body, running the emitted nested loop
    (outer `for` over inner `for`) by iterating the outer body runner `outerN`
    times — each outer step running the emitted inner loop in full — equals
    `NestedForProg.denote init` = the outer-`outerN`-fold of the
    inner-`inner.n`-fold. The inner level reuses the single-level main theorem
    `loop_denote_eq`; the outer level is closed by induction (the `foldl`
    congruence). The only hypothesis is the opaque-leaf edge `LeafAgrees`. -/
theorem nested_loop_denote_eq {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (p : NestedForProg accTy)
    (e : Expr jasminDialect [accTy] accTy)
    (hInner : p.inner.update = SingleVarBody e) (init : ⟦accTy⟧) :
    nestedLoopRun leafSem p init = p.denote init := by
  unfold nestedLoopRun NestedForProg.denote
  -- Both sides fold over `List.range outerN`; the per-element functions agree on
  -- every accumulator by `outerBodyRun_eq` (the inner main theorem).
  exact foldl_congr_fun
    (fun acc _ => outerBodyRun leafSem p acc)
    (fun acc _ => p.outerStep acc)
    (fun acc _ => outerBodyRun_eq hLeaf p e hInner acc)
    (List.range p.outerN) init

/-! ## 7. A jasminc-compilable nested `export fn` (outer `for` over inner `for`)

To *validate* the nested emission end-to-end we render it as a self-contained
jasminc `export fn`, mirroring `JForProg.toJazzExport`: the accumulator `acc` is
a `reg` initialised from the export parameter, the inner body's fresh SSA names
`v0, …` are declared registers, both loop indices (`i` for the inner loop, `j`
for the outer) are `inline int`, and the loop is the **actual** emitted nested
`Cfor` (outer `for j` whose body is the inner `for i`), printed by the shared
`ppInstrR` (NOT unrolled). The body is reused verbatim from
`NestedForProg.toCfor`, so the text jasminc KATs is the same nested loop the
proof covers. -/

/-- Emit a jasminc-compilable `export fn` for a `reg w` accumulator nested loop.
    The loop body is the *actual* emitted nested `Cfor` (outer `for j` over inner
    `for i`, from `toCfor`), printed by the shared `ppInstrR`.

    Shape (for a `reg w` accumulator):
    ```
    export fn <name>(reg u<w> acc0) -> reg u<w> {
      reg u<w> acc;
      reg u<w> v0; …             // one per inner-body binder
      inline int i;              // inner loop index
      inline int j;              // outer loop index
      acc = acc0;
      for j = 0 to outerN { for i = 0 to inner.n { <inner body> } }
      return acc;
    }
    ``` -/
def NestedForProg.toJazzExport {w : Nat} (name : String)
    (p : NestedForProg (.reg w)) : String :=
  let ws := (wsizeOfNat w).bits
  let wty := "u" ++ toString ws
  -- The emitted nested loop (outer `for j` over inner `for i`), via `ppInstrR`.
  let loopStr := CatCrypt.Crypto.Jasmin.LowCT.ppInstrR 2 p.toCfor
  -- Temporaries the inner body introduces: `v0 … v{k-1}`.
  let k := Com.numBinders p.inner.update
  let tempDecls := String.intercalate "\n"
    ((List.range k).map (fun jdx => "  reg " ++ wty ++ " v" ++ toString jdx ++ ";"))
  let tempBlock := if k = 0 then "" else tempDecls ++ "\n"
  "export fn " ++ name ++ "(reg " ++ wty ++ " acc0) -> reg " ++ wty ++ " {\n" ++
  "  reg " ++ wty ++ " acc;\n" ++
  tempBlock ++
  "  inline int i;\n" ++
  "  inline int j;\n" ++
  "  acc = acc0;\n" ++
  loopStr ++ "\n" ++
  "  return acc;\n" ++
  "}"

/-! ## 8. The 2D-accumulate validating kernel (the simplest nested loop)

The simplest nested kernel that validates nesting: an outer loop of `outerN`
iterations, each running an inner loop of `inner.n` doublings (`acc := acc + acc`,
the `JasminPrint.doubleLoop` body, a single `regArith add` leaf). The total is
doubling `outerN * inner.n` times. The leaf agreement is vacuous (no `extCall`),
so any `leafSem` works.

We take `outerN = 3`, `inner.n = 2`: each outer iteration quadruples (×2 twice),
three outer iterations give ×4^3 = ×64. From `1` this computes `64`. -/

/-- The inner single-level loop of the 2D-accumulate kernel: `acc := acc + acc`
    for `2` iterations (a `regArith add` body — the same single leaf as
    `JasminPrint.doubleLoop`, count `2`). -/
def grid2DInner : JForProg (.reg 64) :=
  { n := 2
    update :=
      .var (.mk (.regArith .add 64) rfl
              (.cons .here (.cons .here .nil)))
        (.ret .here) }

/-- The 2D-accumulate nested kernel: `3` outer iterations of the `2`-iteration
    inner doubling loop. Total: doubling `3 * 2 = 6` times. -/
def grid2D : NestedForProg (.reg 64) :=
  { outerN := 3, inner := grid2DInner }

/-- The inner body is a single-leaf body (one `regArith add` then `.ret .here`),
    so the inner main theorem applies. -/
theorem grid2DInner_singleVar :
    grid2DInner.update
      = SingleVarBody (accTy := .reg 64)
          (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil))) := rfl

/-- The inner loop doubles twice (× 4); iterating that `3` times from `1` gives
    `64` — the two-level `n`-fold denotation ground truth. -/
theorem grid2D_denote :
    grid2D.denote (1 : BitVec 64) = (64 : BitVec 64) := by rfl

/-- **2D-accumulate kernel — emitted nested loop denotes the two-level `n`-fold
    double.** Running the emitted nested loop (outer `for j = 0 to 3` over inner
    `for i = 0 to 2 { acc = acc + acc }`) by iterating the outer body runner from
    `init` equals `grid2D.denote init` (= `init` doubled six times). The leaf
    agreement is vacuous here. Instance of `nested_loop_denote_eq`. -/
theorem grid2D_nested_denote_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : BitVec 64) :
    nestedLoopRun leafSem grid2D init = grid2D.denote init :=
  nested_loop_denote_eq hLeaf grid2D _ grid2DInner_singleVar init

/-- The discharged nested main theorem, instantiated at the concrete counts and seed
    `init = 1`, computes `64` — byte-for-byte the unrolled/reference
    (`1 → 64` after six doublings). This ties the emitted nested-loop semantics
    the main theorem proves to the concrete KAT validated end-to-end in
    `bench/nested_loop/`. -/
theorem grid2D_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    nestedLoopRun leafSem grid2D (1 : BitVec 64) = (64 : BitVec 64) := by
  rw [grid2D_nested_denote_eq hLeaf]
  exact grid2D_denote

/-! ## 9. Structural smoke tests for the emitted nested `.jazz` -/

/-- The jasminc-compilable `export fn` for the 2D-accumulate nested kernel. -/
def grid2DExportJazz : String := NestedForProg.toJazzExport "grid2d" grid2D

#eval IO.println grid2DExportJazz

/- The exported `.jazz` has the **outer** `for` loop (`for j = 0 to 3`). -/
#guard (JasminPrint.strContains grid2DExportJazz "for j = 0 to 3")

/- The exported `.jazz` has the **inner** `for` loop (`for i = 0 to 2`). -/
#guard (JasminPrint.strContains grid2DExportJazz "for i = 0 to 2")

/- **Structural check: an inner `for` is nested inside the outer `for`.** The
    outer header `for j = 0 to 3 {` is followed (later in the text) by the inner
    header `for i = 0 to 2 {`, and both appear — the headline nesting property.
    We check the inner `for` occurs after the outer `for` opens by splitting on
    the outer header and finding the inner header in the tail. -/
#guard (JasminPrint.strContains ((grid2DExportJazz.splitOn "for j = 0 to 3 {").getLast!) "for i = 0 to 2 {")

/- The exported `.jazz` is an `export fn` jasminc unit. -/
#guard (JasminPrint.strContains grid2DExportJazz "export fn grid2d")

/-- The exported `.jazz` does NOT unroll: it has a single `acc = acc + acc`
    inside the inner loop body (one occurrence), confirming both loops are
    emitted as real `for`s, not `6` copies of the body. -/
theorem grid2DExport_not_unrolled :
    (grid2DExportJazz.splitOn "(acc + acc)").length = 2 := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.JForProgNested
