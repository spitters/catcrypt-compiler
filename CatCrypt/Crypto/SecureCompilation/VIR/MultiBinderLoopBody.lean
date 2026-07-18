/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering
import CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
import CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering

/-!
# Counted loop with a **multi-binder** straight-line body: `loopNMulti n body`

`LoopLowering.loopN` packages the counted-loop keystone for a **single-op**
accumulator body (`SingleVarBody e` — one dialect op, then return its result).
Real crypto loop bodies — a round function, an X25519 ladder step, a Merkle
compression — are *multi-binder*: they bind several intermediate SSA names
(`let s = …; let t = …; ret …`) before producing the new accumulator. This file
closes that gap: a first-class counted loop whose body is an **arbitrary
multi-binder straight-line `Com` over the singleton accumulator context**, with
the emitted run proved equal to the `n`-fold composition of the body's
denotation.

## How the gap closes (reuse, not rebuild)

The `JForProg` structure's `update : Com jasminDialect [accTy] accTy` field was
*already* an arbitrary `Com` — the single-op restriction lived only in the
**single-var keystone proof path** (`JForProgSemCorrect.loop_denote_eq`, which
sidesteps the whole-`Com` preservation theorem and so needs no fresh-name
injectivity). The scope note in `LoopLowering` flagged the blocker honestly:

> multi-binder straight-line bodies would re-introduce the `freshName`
> injectivity carried by `JasminPrintSemCorrect.execCom_eq`.

That `freshName` injectivity is now a **theorem**
(`FreshNameInjective.freshName_injective`), and `JForProgMultiOp` already used it
to discharge the per-iteration body run for **any** straight-line body:

* `JForProgMultiOp.bodyStepRun_multiOp_eq` — the emitted body runner computes
  `JForProg.step` for any `StraightLine` body, routed through `execCom_eq` with
  `hInj := freshName_injective` (the multi-binder fresh names `v0, v1, …` are
  kept distinct from the accumulator `"acc"` and from each other).
* `JForProgMultiOp.loop_denote_eq_multiOp` — hence the whole-loop keystone
  (emitted run = `JForProg.denote`) for any straight-line body.

This file is the **clean surface + iterate-form packaging** on top of those: it
mirrors `LoopLowering.loopN`/`loopN_lower_denote_iterate` but accepts a
multi-binder `Com` body, threading `loop_denote_eq_multiOp` (instead of the
single-var `loop_denote_eq`) through `LoopLowering.denote_eq_iterate` (the
`foldl` ↔ `f^[n]` bridge). The threading is **direct**: the multi-op body went
through `loopN`/`JForProg.denote` with no new proof obligation — the
`WholeFnLowering` straight-line bridge (`lowerComToProg_sem_eq'`) was *not*
needed at the loop level, because the per-iteration body-run discharge already
lives in `JForProgMultiOp` via the same `execCom_eq` + `freshName_injective`
keystone that `WholeFnLowering` uses for the whole-function case.

## Conditioned scope (honest)

The soundness is conditioned on exactly two hypotheses, both standard in this
emit-correctness theory and *neither* a `sorry`:

* `hLeaf : LeafAgrees leafSem` — the opaque-leaf edge (`extCall` agreement),
  carried throughout the emit theory; it is the genuine assumption about the
  leaf semantics.
* `hSL : StraightLine body` — every binder of the body is a non-`stackStore`
  op. This is the discipline `JForProgMultiOp` already requires; it excludes the
  aliasing `stackStore` op (whose in-place write breaks the fresh-name argument,
  see `stackStore_aliases_source`).

What this does **not** yet cover: multi-*accumulator* loop bodies (a body
carrying several live values across iterations — packable into a product `accTy`,
but the single-accumulator `JForProg` shape is hard-wired), control flow /
branches *inside* the body (`StraightLine` rejects them; that is the
`StructuredControlFlow` layer), function calls (the `extCall` leaf stays opaque
under `LeafAgrees`), and runtime/`while` bounds. The per-iteration fresh-name
threading — the honest blocker the loop work flagged — is fully discharged here;
it did **not** block, because `JForProgMultiOp` already carried it through
`execCom_eq` with the `freshName_injective` theorem.

0 sorries; the only carried hypotheses are `LeafAgrees` and `StraightLine body`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MultiBinderLoopBody

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
open CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering
open CatCrypt.Crypto.Jasmin (JasminProg)

/-! ## 1. The multi-binder counted-loop constructor `loopNMulti`

A `MultiBinderBody accTy` is an **arbitrary** `Com` over the singleton
accumulator context — any number of `let`-binders, then return the new
accumulator. `loopNMulti n body` is the counted loop running it `n` times. Unlike
`LoopLowering.loopN`, the body is not restricted to `SingleVarBody`. -/

/-- A multi-binder loop body: an arbitrary straight-line `Com` `acc ↦ body(acc)`
    over the singleton accumulator context. (Compare `LoopLowering.LoopBody`,
    which is a single dialect op.) -/
abbrev MultiBinderBody (accTy : JasminTy) : Type :=
  Com jasminDialect [accTy] accTy

/-- **The multi-binder counted-loop constructor.** `loopNMulti n body` is the
    bounded loop that runs the multi-binder body `body` exactly `n` times over one
    accumulator. Its `update` is `body` directly — the `JForProg.update` field is
    already an arbitrary `Com`, so no `SingleVarBody` wrapping is needed. -/
def loopNMulti {accTy : JasminTy} (n : Nat) (body : MultiBinderBody accTy) :
    JForProg accTy :=
  { n := n, update := body }

/-- `loopNMulti`'s update is the body verbatim. -/
@[simp] theorem loopNMulti_update {accTy : JasminTy} (n : Nat)
    (body : MultiBinderBody accTy) :
    (loopNMulti n body).update = body := rfl

/-- `loopNMulti`'s iteration count is `n`. -/
@[simp] theorem loopNMulti_n {accTy : JasminTy} (n : Nat)
    (body : MultiBinderBody accTy) :
    (loopNMulti n body).n = n := rfl

/-- One step of `loopNMulti` is the body's denotation on the singleton
    accumulator: `step acc = body.denote (.cons acc .nil)`. -/
@[simp] theorem loopNMulti_step {accTy : JasminTy} (n : Nat)
    (body : MultiBinderBody accTy) (acc : ⟦accTy⟧) :
    (loopNMulti n body).step acc = body.denote (.cons acc .nil) := rfl

/-! ## 2. The lowering and its soundness (the multi-binder keystone, packaged)

`loopNMulti n body` lowers via `JForProg.toProg`. The emitted loop is run,
evaluator-side, by `bodyStepRun`. The soundness states the emitted run equals
`step^[n] init` — the body's denotation composed `n` times — conditioned on the
opaque-leaf edge `LeafAgrees` and the straight-line discipline `StraightLine`. -/

/-- The lowering of a multi-binder counted loop to a single-function
    `JasminProg` with a `Cfor`. Definitionally the existing `JForProg.toProg`. -/
def loopNMulti_lower {accTy : JasminTy} (name : String) (n : Nat)
    (body : MultiBinderBody accTy) : JasminProg :=
  (loopNMulti n body).toProg name

/-- **Keystone (multi-binder, fold form).** The emitted counted loop with a
    multi-binder body, run `n` times by the word-level body evaluator threading
    the named accumulator, equals the loop's `n`-fold denotation
    `JForProg.denote`. This is `JForProgMultiOp.loop_denote_eq_multiOp`
    specialised to the `loopNMulti` constructor — the per-iteration body run is
    discharged through `execCom_eq` with `freshName_injective`, so no fresh-name
    side-condition remains. Hypotheses: the opaque-leaf edge `LeafAgrees` and the
    straight-line discipline `StraightLine body`. -/
theorem loopNMulti_lower_denote {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (n : Nat) (body : MultiBinderBody accTy)
    (hSL : StraightLine body) (init : ⟦accTy⟧) :
    loopRun (loopNMulti n body) (bodyStepRun leafSem (loopNMulti n body)) init
      = (loopNMulti n body).denote init :=
  loop_denote_eq_multiOp hLeaf (loopNMulti n body) hSL init

/-- **Keystone (multi-binder, iterate form — the roadmap statement).** The
    emitted counted loop's `n`-fold run equals `step^[n] init`, where
    `step acc = body.denote (.cons acc .nil)` is the multi-binder body's
    denotation. This is the loop keystone for the first-class **multi-binder**
    `loopNMulti` construct: the emitted loop's denotation is the `n`-fold
    composition of the body's denotation. Combines `loopNMulti_lower_denote`
    (emitted run = abstract fold) with `LoopLowering.denote_eq_iterate` (abstract
    fold = `step^[n]`). Conditioned on `LeafAgrees` and `StraightLine body`; no
    fresh-name side-condition — the multi-binder body's per-iteration fresh names
    are discharged inside `loop_denote_eq_multiOp`. -/
theorem loopNMulti_lower_denote_iterate {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (n : Nat) (body : MultiBinderBody accTy)
    (hSL : StraightLine body) (init : ⟦accTy⟧) :
    loopRun (loopNMulti n body) (bodyStepRun leafSem (loopNMulti n body)) init
      = (fun acc => body.denote (.cons acc .nil))^[n] init := by
  rw [loopNMulti_lower_denote hLeaf n body hSL init, denote_eq_iterate]
  rfl

/-! ## 3. Worked example: a concrete **two-op** straight-line round body

The body `acc ↦ (acc + acc) ^^^ acc` — two genuine `let`-binders (an `add` and a
`xor`), a minimal "round step" shape:

    let s = regArith add acc acc   -- s = acc + acc   : reg 64
    let r = regArith xor s   acc   -- r = s ^^^ acc    : reg 64
    ret r

so `body.denote ⟨acc⟩ = (acc + acc) ^^^ acc`. This is exactly the multi-binder
case the single-op `loopN` could not express. We prove it is `StraightLine`, give
its iterate-form emitted-loop denotation, and a concrete `n = 3` KAT. -/

/-- A concrete **two-op** (multi-binder) round body `acc ↦ (acc + acc) ^^^ acc`.
    First binder: `s = acc + acc` (`regArith add`, both operands the accumulator
    `.here`). Second binder: `r = s ^^^ acc` (`regArith xor`, first operand the
    fresh `s = .here`, second the accumulator now at `.there .here`). Returns
    `r = .here`. -/
def roundBody : MultiBinderBody (.reg 64) :=
  .var (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil)))
    (.var (.mk (.regArith .xor 64) rfl (.cons .here (.cons (.there .here) .nil)))
      (.ret .here))

/-- The round body denotes `acc ↦ (acc + acc) ^^^ acc`. -/
@[simp] theorem roundBody_denote (acc : BitVec 64) :
    roundBody.denote (.cons acc .nil) = (acc + acc) ^^^ acc := rfl

/-- The two-op round body is `StraightLine` (both binders are non-`stackStore`
    `regArith` ops). -/
theorem roundBody_straightLine : StraightLine roundBody := by
  refine ⟨fun w n h => ?_, ⟨fun w n h => ?_, trivial⟩⟩
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **Worked example (iterate form).** The emitted
    `for i = 0 to 3 { acc = (acc + acc) ^^^ acc }` counted loop, run via the
    evaluator, denotes the 3-fold composition of the round body. Instance of
    `loopNMulti_lower_denote_iterate` on the multi-binder `roundBody`. -/
theorem roundBody_loop_iterate {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : BitVec 64) :
    loopRun (loopNMulti 3 roundBody) (bodyStepRun leafSem (loopNMulti 3 roundBody))
        init
      = (fun acc => (acc + acc) ^^^ acc)^[3] init := by
  have h := loopNMulti_lower_denote_iterate hLeaf 3 roundBody
    roundBody_straightLine init
  simpa using h

/-- **Worked example (concrete KAT).** At seed `init = 1`, the emitted
    multi-binder counted loop computes the unrolled reference
    `1 → (1+1)^^^1 = 3 → (3+3)^^^3 = 5 → (5+5)^^^5 = 15`, i.e. `15`. Ties the
    iterate-form keystone for a multi-binder body to a concrete value. -/
theorem roundBody_loop_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    loopRun (loopNMulti 3 roundBody) (bodyStepRun leafSem (loopNMulti 3 roundBody))
        (1 : BitVec 64)
      = (15 : BitVec 64) := by
  rw [roundBody_loop_iterate hLeaf]
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.MultiBinderLoopBody
