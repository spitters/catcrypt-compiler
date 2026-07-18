/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering
import CatCrypt.Crypto.SecureCompilation.VIR.JForProgNested

/-!
# Nested counted-loop lowering: the emitted outer-over-inner loop denotes the
# two-level `Function.iterate` `((body.denote)^[m])^[n]` (= `(body.denote)^[n*m]`)

This file is the **iterate-form** capstone over the nested-loop emission layer.
It extends keystone #4 (single counted loop, `LoopLowering.loopN` /
`loopN_lower_denote_iterate`) to **two levels**: a counted outer loop whose body
is a counted inner loop over the same accumulator, with the whole thing's
denotation stated in the roadmap's `Function.iterate` (`f^[·]`) form.

## What was already there (reused, not re-proved)

* `LoopLowering.loopN n body` — the single-op counted loop constructor, and
  `LoopLowering.foldl_range_eq_iterate` / `denote_eq_iterate` — the
  `range … foldl` ↔ `f^[n]` bridge for **one** level.
* `JForProgNested.NestedForProg` — the two-level structure (outer trip count
  `outerN`, inner single-level `JForProg`), its emission `toCfor`/`toProg`
  (outer `for j` over inner `for i`), the evaluator-side `nestedLoopRun`, and the
  **nested keystone** `nested_loop_denote_eq` (emitted nested run =
  `NestedForProg.denote` = outer-fold of `inner.denote`). Reused verbatim — this
  file does not touch it.
* `Function.iterate_mul : f^[m * n] = f^[m]^[n]` (Mathlib) — the flattening.

## What is genuinely new here

1. **`loopNested n m body`** — a `NestedForProg` whose inner level is exactly
   `LoopLowering.loopN m body`. This is the clean "outer `n`, inner `m`, single
   single-op body, one accumulator" surface the roadmap names. Because its inner
   `update` is, by construction, a `SingleVarBody`, the nested keystone
   `nested_loop_denote_eq` applies verbatim (single-leaf inner body).

2. **`loopNested_denote_iterate_nested`** — the nested denotation in two-level
   iterate form: `loopNested … .denote init = ((step)^[m])^[n] init`, where
   `step acc = body.denote (.cons acc .nil)` is the body's denotation. Proved by
   applying the *single-level* `denote_eq_iterate` at **both** levels (inner via
   `loopN`, outer via a `foldl`-over-`range` bridge), reusing
   `foldl_range_eq_iterate`.

3. **`loopNested_denote_iterate_flat`** — the **flattened** form
   `loopNested … .denote init = step^[m * n] init`, via `Function.iterate_mul`.
   The nesting *does* flatten: running the inner `m`-fold `n` times is the
   `n*m`-fold (single accumulator, no per-level extra effect).

4. **`loopNested_lower_denote_iterate{_nested,_flat}`** — the packaged
   soundness theorems: the **emitted** nested loop's evaluator run
   (`JForProgNested.nestedLoopRun`) equals `((step)^[m])^[n] init` resp.
   `step^[n*m] init`. These compose the nested keystone `nested_loop_denote_eq`
   (emitted run = `NestedForProg.denote`) with the new iterate-form denotation
   lemmas. Fully discharged for single-op bodies; the only hypothesis is the
   opaque-leaf edge `LeafAgrees`, exactly as the single-level and nested
   keystones.

5. A worked, **concrete** example: `loopNested 3 2 doubleBody` — outer 3, inner 2
   doublings (`acc := acc + acc`), iterate-form denote proved, and a `n=3,m=2`,
   `init=1` ⇒ `64` KAT (six doublings). SORRY-FREE.

## Did the nesting flatten?

**Yes.** With a single accumulator and a single-op body, the two-level run is the
flattened `step^[n*m]` (`loopNested_denote_iterate_flat`); the genuinely
two-level `((step)^[m])^[n]` form is also available
(`loopNested_denote_iterate_nested`), and `Function.iterate_mul` bridges them.

## Scope (honest)

Counted outer loop whose body is a counted inner loop over **one** accumulator
with a **single-op** body — the keystone-#4-nested landable scope. It does **not**
cover: multi-accumulator nesting (would pack into a product `accTy` and re-prove
the inner keystone there), inner bodies with several binders, or runtime/`while`
outer/inner bounds. Those remain the whole-function / runtime-loop roadmap work.

0 sorries; the only hypothesis is the opaque-leaf edge `LeafAgrees`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NestedLoopLowering

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgNested
open CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering

/-! ## 1. The nested counted-loop constructor `loopNested` -/

/-- **The nested counted-loop constructor.** `loopNested n m body` is the
    two-level bounded loop that runs, `n` (outer) times, the inner counted loop
    `loopN m body` — i.e. the single-op body `body` is iterated `m` times per
    outer step, for `n` outer steps. One accumulator throughout. Definitionally a
    `NestedForProg` whose inner is `LoopLowering.loopN m body`. -/
def loopNested {accTy : JasminTy} (n m : Nat) (body : LoopBody accTy) :
    NestedForProg accTy :=
  { outerN := n, inner := loopN m body }

/-- `loopNested`'s outer trip count is `n`. -/
@[simp] theorem loopNested_outerN {accTy : JasminTy} (n m : Nat)
    (body : LoopBody accTy) : (loopNested n m body).outerN = n := rfl

/-- `loopNested`'s inner loop is `loopN m body`. -/
@[simp] theorem loopNested_inner {accTy : JasminTy} (n m : Nat)
    (body : LoopBody accTy) : (loopNested n m body).inner = loopN m body := rfl

/-- The inner loop's `update` is, by construction, a `SingleVarBody` — so the
    nested keystone `nested_loop_denote_eq` applies (single-leaf inner body). -/
theorem loopNested_inner_update {accTy : JasminTy} (n m : Nat)
    (body : LoopBody accTy) :
    (loopNested n m body).inner.update = SingleVarBody body :=
  loopN_update m body

/-! ## 2. The nested denotation in two-level `Function.iterate` form -/

/-- One outer step of `loopNested` is the inner loop's `m`-fold of the body. -/
theorem loopNested_outerStep_iterate {accTy : JasminTy} (n m : Nat)
    (body : LoopBody accTy) (acc : ⟦accTy⟧) :
    (loopNested n m body).outerStep acc
      = (fun a => body.denote (.cons a .nil))^[m] acc := by
  unfold NestedForProg.outerStep
  rw [loopNested_inner, denote_eq_iterate]
  rfl

/-- **Nested denotation, two-level iterate form.** The nested loop's abstract
    denotation is the outer-`n`-fold of the inner-`m`-fold of the body's
    denotation: `((step)^[m])^[n] init`. Both levels go through the single-level
    `denote_eq_iterate` / `foldl_range_eq_iterate` bridge. -/
theorem loopNested_denote_iterate_nested {accTy : JasminTy} (n m : Nat)
    (body : LoopBody accTy) (init : ⟦accTy⟧) :
    (loopNested n m body).denote init
      = ((fun a => body.denote (.cons a .nil))^[m])^[n] init := by
  unfold NestedForProg.denote
  rw [loopNested_outerN]
  rw [foldl_range_eq_iterate (fun acc => (loopNested n m body).outerStep acc) n init]
  -- The outer step is the inner `m`-fold; rewrite the iterated function.
  have hstep : (fun acc => (loopNested n m body).outerStep acc)
      = (fun a => body.denote (.cons a .nil))^[m] := by
    funext acc
    exact loopNested_outerStep_iterate n m body acc
  rw [hstep]

/-- **Nested denotation, flattened iterate form.** The two-level run flattens to
    the single `(n*m)`-fold of the body: `step^[n*m] init`. By
    `Function.iterate_mul` over the nested form. -/
theorem loopNested_denote_iterate_flat {accTy : JasminTy} (n m : Nat)
    (body : LoopBody accTy) (init : ⟦accTy⟧) :
    (loopNested n m body).denote init
      = (fun a => body.denote (.cons a .nil))^[m * n] init := by
  rw [loopNested_denote_iterate_nested, ← Function.iterate_mul]

/-! ## 3. The lowering and its iterate-form soundness (the packaged keystone) -/

/-- The lowering of a nested counted loop to a single-function `JasminProg` with
    an outer `for j` over an inner `for i`. Definitionally
    `JForProgNested.NestedForProg.toProg`. -/
def loopNested_lower {accTy : JasminTy} (name : String) (n m : Nat)
    (body : LoopBody accTy) : CatCrypt.Crypto.Jasmin.JasminProg :=
  (loopNested n m body).toProg name

/-- **Keystone (packaged, nested iterate form — the roadmap statement).** The
    *emitted* nested loop, run by the evaluator (`nestedLoopRun`: iterate the
    outer body runner `n` times, each outer step running the emitted inner loop
    in full), equals `((step)^[m])^[n] init` where
    `step acc = body.denote (.cons acc .nil)` is the body's denotation. Combines
    the nested keystone `nested_loop_denote_eq` (emitted run = abstract nested
    denote) with `loopNested_denote_iterate_nested` (abstract nested denote =
    two-level iterate). Fully discharged for single-op bodies; only the
    opaque-leaf edge `LeafAgrees` is carried. -/
theorem loopNested_lower_denote_iterate_nested {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (n m : Nat) (body : LoopBody accTy)
    (init : ⟦accTy⟧) :
    nestedLoopRun leafSem (loopNested n m body) init
      = ((fun a => body.denote (.cons a .nil))^[m])^[n] init := by
  rw [nested_loop_denote_eq hLeaf (loopNested n m body) body
        (loopNested_inner_update n m body) init,
     loopNested_denote_iterate_nested]

/-- **Keystone (packaged, flattened iterate form).** The emitted nested loop's
    evaluator run equals the single `(n*m)`-fold of the body, `step^[n*m] init`.
    `loopNested_lower_denote_iterate_nested` flattened by `Function.iterate_mul`. -/
theorem loopNested_lower_denote_iterate_flat {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (n m : Nat) (body : LoopBody accTy)
    (init : ⟦accTy⟧) :
    nestedLoopRun leafSem (loopNested n m body) init
      = (fun a => body.denote (.cons a .nil))^[m * n] init := by
  rw [loopNested_lower_denote_iterate_nested hLeaf n m body init,
     ← Function.iterate_mul]

/-! ## 4. Worked example: nested doubling (`loopNested 3 2 doubleBody`)

The simplest validating nested kernel in iterate form: outer `3`, inner `2`
doublings (`acc := acc + acc`, the `LoopLowering.doubleBody` single leaf). The
inner loop quadruples (×2 twice); three outer iterations give ×4³ = ×64. -/

/-- `loopNested 3 2 doubleBody` is the outer-3 / inner-2 nested doubling kernel.
    Its inner loop is `loopN 2 doubleBody`. -/
def doubleNested : NestedForProg (.reg 64) := loopNested 3 2 doubleBody

/-- **Worked example (nested iterate form).** The emitted nested doubling loop,
    run by the evaluator, denotes the outer-3-fold of the inner-2-fold doubling
    `((fun a => a + a)^[2])^[3]` of the seed. Instance of
    `loopNested_lower_denote_iterate_nested`. -/
theorem doubleNested_iterate_nested {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : BitVec 64) :
    nestedLoopRun leafSem doubleNested init
      = ((fun a => a + a)^[2])^[3] init :=
  loopNested_lower_denote_iterate_nested hLeaf 3 2 doubleBody init

/-- **Worked example (flattened iterate form).** Same emitted loop denotes the
    flattened six-fold doubling `(fun a => a + a)^[3 * 2]`. Instance of
    `loopNested_lower_denote_iterate_flat`. -/
theorem doubleNested_iterate_flat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : BitVec 64) :
    nestedLoopRun leafSem doubleNested init
      = (fun a => a + a)^[2 * 3] init :=
  loopNested_lower_denote_iterate_flat hLeaf 3 2 doubleBody init

/-- **Worked example (concrete KAT).** At seed `init = 1`, the emitted nested
    doubling loop computes `64` — byte-for-byte the unrolled reference of six
    doublings `1 → 2 → 4 → 8 → 16 → 32 → 64`. Ties the iterate-form nested
    keystone to a concrete value. -/
theorem doubleNested_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    nestedLoopRun leafSem doubleNested (1 : BitVec 64) = (64 : BitVec 64) := by
  rw [doubleNested_iterate_flat hLeaf]
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.NestedLoopLowering
