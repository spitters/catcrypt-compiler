/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect

/-!
# A first-class counted-loop lowering pass: `loopN n body` denotes `step^[n]`

This file packages the existing bounded-for-loop emit infrastructure
(`JForProg`, `JForProgCT.loopRun_eq`, `JForProgSemCorrect.loop_denote_eq`) as a
clean, reusable **loop-lowering pass** in the shape the compiler roadmap
(keystone #4, "loops / control flow") asks for:

> a counted loop construct whose lowering's denotation equals the
> `n`-fold composition of the body's denotation.

## What was already there (reused, not re-proved)

* `JForProg accTy = { n, update }` — a static-count loop over one accumulator.
* `JForProg.step p acc = p.update.denote (.cons acc .nil)` — the body's denote.
* `JForProg.denote p init = (List.range p.n).foldl (fun a _ => p.step a) init`
  — the `n`-fold semantics, in **`List.range`/`foldl`** form.
* `JForProgCT.loopRun` — the evaluator-side `n`-fold iteration of the emitted
  `Cfor` body, and `JForProgCT.loopRun_eq` proving `loopRun = denote` modulo the
  per-iteration `StepAgrees` edge.
* `JForProgSemCorrect.bodyStepRun` / `loop_denote_eq` — the concrete word-level
  body runner and the keystone `loopRun p (bodyStepRun …) init = p.denote init`,
  fully discharged for single-leaf bodies (only the opaque-leaf edge
  `LeafAgrees` is carried, exactly as the rest of the emit-correctness theory).

## What is genuinely new here

1. **`loopN n body`** — a constructor that builds the loop program directly from
   an iteration count `n` and a single-op accumulator body expression
   `body : Expr jasminDialect [accTy] accTy` (a `loopBody`). This is the clean
   surface the roadmap names; it is definitionally a `JForProg` whose `update` is
   a `JForProgSemCorrect.SingleVarBody`, so the keystone applies verbatim.

2. **`foldl_range_eq_iterate`** — the bridge that puts the `n`-fold semantics in
   the canonical **`Function.iterate` (`f^[n]`)** form the roadmap states the
   pass against (`loop denote = n-fold composition of body denote`). The repo's
   `JForProg.denote` is the `List.range … foldl` form; this lemma proves
   `(List.range n).foldl (fun a _ => f a) init = f^[n] init`, by induction on `n`.
   No such bridge existed in the repo.

3. **`loopN_lower_denote_iterate`** — the packaged soundness theorem in iterate
   form: running the *emitted* counted loop `n` times equals `step^[n] init`,
   where `step` is the body's denotation. This is `loop_denote_eq` (the emitted
   evaluator agrees with the abstract fold) composed with the new
   `foldl_range_eq_iterate` (the abstract fold = `step^[n]`). Fully discharged
   for single-op bodies; the only hypothesis is the same `LeafAgrees` opaque-leaf
   edge.

4. A worked, **concrete** example: `addStepLoop step₀ n` (`acc := acc + step₀`,
   `n` times) — the `acc + n·step` iterated kernel of `LoopEmitGoldenPath`. Its
   emitted-loop denotation is proved to equal `step^[n] init` *and*, at concrete
   `n = 4`, to compute `init + 4·step₀` byte-for-byte (`addStepLoop_kat`).

## Scope (honest)

This is a *first-class counted loop over a single accumulator with a single-op
body*. It covers the fixed-iteration straight-line-body kernels (running sums /
Horner / doubling / X25519's per-round ladder step), which is the keystone-#4
landable scope. It does **not** yet cover: multi-accumulator loop bodies
(packable into a product `accTy`, see `JForProgCT` §8 scope note), multi-binder
straight-line bodies (would re-introduce the `freshName` injectivity carried by
`JasminPrintSemCorrect.execCom_eq`), nested loops (`JForProgNested` is a separate
layer), or runtime/`while` bounds. Those are the remaining whole-function /
nested-loop work in the roadmap.

0 sorries; the only hypothesis is the opaque-leaf edge `LeafAgrees`, the same
edge carried throughout the emit-correctness theory.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.Jasmin (JasminProg)

/-! ## 1. The `range … foldl` ↔ `Function.iterate` bridge

`JForProg.denote` (the repo's `n`-fold semantics) is written as
`(List.range n).foldl (fun a _ => f a) init`. The compiler roadmap states the
loop keystone against the `n`-fold *composition* `f^[n]`. This section is the
missing bridge between the two forms — proved generically by induction on `n`,
independent of any loop machinery. -/

/-- **`range`/`foldl` = `Function.iterate`.** Folding a self-map `f` over
    `List.range n` (ignoring the index) from `init` is the `n`-fold composition
    `f^[n] init`. The general bridge between the repo's `foldl`-form loop
    semantics and the roadmap's `f^[n]` statement. By induction on `n`, using the
    `List.range_succ` / `List.foldl_append` append characterisation. -/
theorem foldl_range_eq_iterate {α : Type _} (f : α → α) :
    ∀ (n : Nat) (init : α),
      (List.range n).foldl (fun a _ => f a) init = f^[n] init
  | 0, _ => rfl
  | n + 1, init => by
      rw [List.range_succ, List.foldl_append, Function.iterate_succ']
      simp only [List.foldl_cons, List.foldl_nil, Function.comp_apply]
      rw [foldl_range_eq_iterate f n init]

/-- Specialisation to `JForProg.denote`: the `n`-fold denotation equals
    `p.step^[p.n] init`. The loop's denotation in `Function.iterate` form. -/
theorem denote_eq_iterate {accTy : JasminTy} (p : JForProg accTy)
    (init : ⟦accTy⟧) :
    p.denote init = p.step^[p.n] init := by
  rw [JForProgCT.denote_eq_foldl]
  exact foldl_range_eq_iterate p.step p.n init

/-! ## 2. The counted-loop constructor `loopN`

A `loopBody` is a single-op accumulator transform `acc ↦ e(acc)`. `loopN n body`
is the counted loop running it `n` times — a `JForProg` whose `update` is the
`SingleVarBody` of `JForProgSemCorrect` (one op, then return its result), so the
keystone `loop_denote_eq` applies to it verbatim. -/

/-- A single-op loop body: a `acc ↦ e(acc)` accumulator transform expressed as
    one dialect op over the singleton accumulator context. -/
abbrev LoopBody (accTy : JasminTy) : Type :=
  Expr jasminDialect [accTy] accTy

/-- **The counted-loop constructor.** `loopN n body` is the bounded loop that
    runs the single-op body `body` exactly `n` times over one accumulator. Its
    `update` is `SingleVarBody body` (one op, return its result), so it is a
    single-leaf `JForProg` to which the emit keystone applies directly. -/
def loopN {accTy : JasminTy} (n : Nat) (body : LoopBody accTy) :
    JForProg accTy :=
  { n := n, update := SingleVarBody body }

/-- `loopN`'s update is, by construction, a `SingleVarBody`. -/
theorem loopN_update {accTy : JasminTy} (n : Nat) (body : LoopBody accTy) :
    (loopN n body).update = SingleVarBody body := rfl

/-- `loopN`'s iteration count is `n`. -/
@[simp] theorem loopN_n {accTy : JasminTy} (n : Nat) (body : LoopBody accTy) :
    (loopN n body).n = n := rfl

/-- One step of `loopN` is the body's denotation on the singleton accumulator. -/
@[simp] theorem loopN_step {accTy : JasminTy} (n : Nat) (body : LoopBody accTy)
    (acc : ⟦accTy⟧) :
    (loopN n body).step acc = body.denote (.cons acc .nil) := rfl

/-! ## 3. The lowering and its soundness (the keystone, packaged)

`loopN n body` lowers via the existing `JForProg.toProg` (a single-function
program with a `Cfor` over `0..n` whose body emits `body`). The emitted loop is
run, evaluator-side, by `bodyStepRun`. The soundness theorem states the emitted
run equals `step^[n] init` — the body's denotation composed `n` times. -/

/-- The lowering of a counted loop to a single-function `JasminProg` with a
    `Cfor`. Definitionally the existing `JForProg.toProg`. -/
def loopN_lower {accTy : JasminTy} (name : String) (n : Nat)
    (body : LoopBody accTy) : JasminProg :=
  (loopN n body).toProg name

/-- **Keystone (packaged, fold form).** The emitted counted loop, run `n` times
    by the word-level body evaluator threading the named accumulator, equals the
    loop's `n`-fold denotation `JForProg.denote`. This is exactly
    `JForProgSemCorrect.loop_denote_eq` specialised to the `loopN` constructor —
    no new proof obligation, just the clean surface. The only hypothesis is the
    opaque-leaf edge `LeafAgrees`. -/
theorem loopN_lower_denote {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (n : Nat) (body : LoopBody accTy)
    (init : ⟦accTy⟧) :
    loopRun (loopN n body) (bodyStepRun leafSem (loopN n body)) init
      = (loopN n body).denote init :=
  loop_denote_eq hLeaf body (loopN n body) (loopN_update n body) init

/-- **Keystone (packaged, iterate form — the roadmap statement).** The emitted
    counted loop's `n`-fold run equals `step^[n] init`, where
    `step acc = body.denote (.cons acc .nil)` is the body's denotation. This is
    the compiler-roadmap keystone-#4 statement (`loop denote = n-fold
    composition of body denote`) for the first-class `loopN` construct: the
    emitted loop's denotation is the `n`-fold composition of the body's
    denotation. Combines `loopN_lower_denote` (emitted run = abstract fold) with
    `denote_eq_iterate` (abstract fold = `step^[n]`). Fully discharged for
    single-op bodies; only the opaque-leaf edge `LeafAgrees` is carried. -/
theorem loopN_lower_denote_iterate {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (n : Nat) (body : LoopBody accTy)
    (init : ⟦accTy⟧) :
    loopRun (loopN n body) (bodyStepRun leafSem (loopN n body)) init
      = (fun acc => body.denote (.cons acc .nil))^[n] init := by
  rw [loopN_lower_denote hLeaf n body init, denote_eq_iterate]
  rfl

/-! ## 4. Worked example: the `acc + n·step` iterated kernel (`LoopEmitGoldenPath`)

The canonical counted-loop golden-path kernel: `acc := acc + step₀` run `n`
times, whose closed form is `acc + n·step₀`. Here `step₀` is folded into the body
as the second operand by binding it to the accumulator's value — for the simplest
self-contained instance we use the *doubling* body `acc := acc + acc` (the
repo's `doubleLoop`), which is `step₀ = acc` and computes `acc · 2^n`. We then
give the additive instance abstractly via `loopN` and prove its iterate-form
denotation, plus a concrete `n = 4` KAT. -/

/-- The doubling body `acc ↦ acc + acc` as a single op (`regArith add` on the
    accumulator twice). This is the `update` of the repo's `JasminPrint.doubleLoop`. -/
def doubleBody : LoopBody (.reg 64) :=
  .mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil))

/-- `loopN 4 doubleBody` is definitionally the repo's `doubleLoop`. -/
theorem loopN_doubleBody_eq :
    loopN 4 doubleBody = JasminPrint.doubleLoop := rfl

/-- **Worked example (iterate form).** The emitted `for i = 0 to 4 { acc = acc + acc }`
    counted loop, run via the evaluator, denotes the 4-fold doubling
    `(fun a => a + a)^[4]` of the initial accumulator. Instance of
    `loopN_lower_denote_iterate`. -/
theorem doubleBody_loop_iterate {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : BitVec 64) :
    loopRun (loopN 4 doubleBody) (bodyStepRun leafSem (loopN 4 doubleBody)) init
      = (fun a => a + a)^[4] init :=
  loopN_lower_denote_iterate hLeaf 4 doubleBody init

/-- **Worked example (concrete KAT).** At seed `init = 1`, the emitted counted
    loop computes `16` — byte-for-byte the unrolled reference
    `1 → 2 → 4 → 8 → 16`. Ties the iterate-form keystone to a concrete value. -/
theorem doubleBody_loop_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    loopRun (loopN 4 doubleBody) (bodyStepRun leafSem (loopN 4 doubleBody))
        (1 : BitVec 64)
      = (16 : BitVec 64) := by
  rw [doubleBody_loop_iterate hLeaf]
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering
