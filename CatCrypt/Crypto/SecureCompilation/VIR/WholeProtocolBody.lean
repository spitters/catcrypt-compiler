/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering

/-!
# Whole-protocol body: a straight-line setup feeding a counted loop, in one
# function, with composed denote-correctness `loop ∘ setup`

`WholeFnLowering.lean` lowers a fixed-length **straight-line** body
(`runProg leafSem com V = com.denote V`, naming side-conditions discharged).
`LoopLowering.lean` lowers a **counted loop** over a single accumulator
(`loopRun (loopN n body) (bodyStepRun …) init = step^[n] init`). A protocol
body *interleaves* the two: it runs a straight-line prefix that produces the
loop's initial accumulator, then runs the counted loop over it. This module
composes the two theorems into ONE function body and proves its
denote-correctness is the
**function composition** `loop_semantics ∘ straightline_semantics`.

## Reused results

* `WholeFnLowering.lowerComToProg_sem_eq'` — the straight-line whole-function
  theorem with **both** SSA-naming side-conditions discharged: for a
  `StraightLine` `com`, `runProg leafSem com V = com.denote V`, conditioned only
  on the opaque-leaf edge `LeafAgrees`.
* `LoopLowering.loopN n body` / `loopN_lower_denote_iterate` — the counted-loop
  constructor and its iterate-form soundness: the emitted loop's `n`-fold
  evaluator run equals `(fun acc => body.denote (.cons acc .nil))^[n] init`,
  conditioned only on the same `LeafAgrees`.
* `JasminPrintSemCorrect.StraightLine` / `runProg`, and
  `JForProgSemCorrect.bodyStepRun` / `loopRun`.

## Contents

1. **`SetupThenLoop`** — the composed body: a straight-line setup
   `setup : Com jasminDialect Γ accTy` (whose `denote` produces the loop's
   initial accumulator) packaged with a counted loop `loopN n body` over that
   accumulator. One accumulator type `accTy`; the setup's return type *is* the
   loop's accumulator type (the seam). A single, named record — the surface a
   "straight-line prefix then counted loop, single return" function body has.

2. **`SetupThenLoop.run`** — the composed evaluator run: run the emitted setup
   function (`runProg`) on the inputs to get the initial accumulator, then run
   the emitted counted loop (`loopRun … bodyStepRun`) over it. This is the
   interleaved whole-body run: straight-line prefix, then loop.

3. **`SetupThenLoop.semantics`** — the composed reference semantics, *as a
   function composition*: `loop_semantics ∘ setup_semantics`, i.e.
   `(fun acc => body.denote (.cons acc .nil))^[n] (setup.denote V)`.

4. **`setupThenLoop_run_eq`** — the **composition** denote-correctness: the
   composed run equals the composed semantics, conditioned only on the shared
   opaque-leaf edge `LeafAgrees` (and the setup being straight-line). The proof
   rewrites the loop's `init` with `lowerComToProg_sem_eq'` (setup run =
   `setup.denote V`) and then closes the loop with `loopN_lower_denote_iterate`.
   Both halves are reused verbatim.

5. A worked, **concrete** example: setup `acc := a + b` (a single `regArith add`
   over `[reg 64, reg 64]`, producing `reg 64`) feeding the doubling loop
   `acc := acc + acc` `n` times. The composed run is proved to equal
   `(fun a => a + a)^[n] (a + b)`, and at `a = 3, b = 4, n = 4` to compute
   `(3 + 4) · 2^4 = 112` byte-for-byte (`addThenDouble_kat`).

## Conditioned scope

The composed body is exactly *straight-line setup → single counted loop over one
single-op-body accumulator → single return*, the union of the two theorems'
scopes. The only carried hypothesis is the opaque-leaf edge
`LeafAgrees` (plus the setup being `StraightLine`), the same edge carried
throughout the emit-correctness theory.

It does **not** cover the *full* whole-protocol body: branches / `if`
(`StructuredControlFlow`), calls *between* fragments (`extCall` stays opaque
under `LeafAgrees`; this composes the two emitted runs at the meta level, not a
single fused control-flow graph), several loops in sequence, a loop body that is
itself a multi-binder straight-line `Com` (would re-introduce `freshName`
injectivity), nested loops (`NestedLoopLowering`), or the instruction-selection
pass applied to the fused body.

All goals are closed; the only hypotheses are `LeafAgrees` and `StraightLine setup`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.WholeProtocolBody

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering
open CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering

/-! ## 1. The composed body: a straight-line setup feeding a counted loop

`SetupThenLoop Γ accTy` packages a straight-line `setup : Com jasminDialect Γ
accTy` whose return type `accTy` *is* the accumulator type of the counted loop
`loopN n body` it feeds. This is the seam where the whole-function and loop
lowerings meet: the setup's denotation is the loop's initial accumulator. -/

/-- **The composed whole-protocol body.** A straight-line setup `setup` (whose
    `Com.denote` produces the initial accumulator) followed by a counted loop of
    `n` iterations of the single-op body `body` over that accumulator. The setup's
    return type is exactly the loop's accumulator type `accTy` — the interleaving
    seam. Single accumulator, single return. -/
structure SetupThenLoop (Γ : Ctxt jasminDialect) (accTy : JasminTy) where
  /-- The straight-line prefix producing the loop's initial accumulator. -/
  setup : Com jasminDialect Γ accTy
  /-- The setup is loop-free / straight-line (no aliasing `stackStore`). -/
  setupSL : StraightLine setup
  /-- The loop trip count. -/
  n : Nat
  /-- The single-op loop body `acc ↦ body(acc)`. -/
  body : LoopBody accTy

/-! ## 2. The composed run and the composed reference semantics -/

/-- **The composed evaluator run.** Run the emitted setup function on the inputs
    `V` to obtain the initial accumulator (`runProg`), then run the emitted
    counted loop over it (`loopRun … bodyStepRun`). This is the interleaved
    whole-body run: straight-line prefix, then counted loop, single return. -/
def SetupThenLoop.run {Γ : Ctxt jasminDialect} {accTy : JasminTy}
    (P : SetupThenLoop Γ accTy) (leafSem : LeafSem) (V : Ctxt.Valuation Γ) :
    ⟦accTy⟧ :=
  let init := runProg leafSem P.setup V
  loopRun (loopN P.n P.body) (bodyStepRun leafSem (loopN P.n P.body)) init

/-- **The composed reference semantics, as a function composition.** The loop
    semantics `(fun acc => body.denote (.cons acc .nil))^[n]` composed with the
    setup semantics `setup.denote`: `loop_semantics ∘ setup_semantics`, applied to
    the inputs. This is the ground truth the composed run must match. -/
def SetupThenLoop.semantics {Γ : Ctxt jasminDialect} {accTy : JasminTy}
    (P : SetupThenLoop Γ accTy) (V : Ctxt.Valuation Γ) : ⟦accTy⟧ :=
  ((fun acc => P.body.denote (.cons acc .nil))^[P.n]) (P.setup.denote V)

/-! ## 3. The composition denote-correctness

The run equals the semantics — `loop ∘ setup` — conditioned only on the shared
opaque-leaf edge `LeafAgrees`. Rewrite the loop's `init` with the straight-line
theorem (`setup` run = `setup.denote V`), then discharge the loop with the
counted-loop theorem. Both halves are reused verbatim; the composition threads
the two semantics through one accumulator. -/

/-- **Composed whole-protocol-body denote-correctness (`loop ∘ setup`).** For a
    straight-line setup feeding a counted loop, the composed evaluator run equals
    the composed reference semantics — the loop's `n`-fold body denotation applied
    to the setup's denotation of the inputs. The only carried hypothesis is the
    opaque-leaf edge `LeafAgrees`; the setup-is-straight-line side-condition lives
    in the body record. Proof: rewrite the loop's initial accumulator with the
    straight-line theorem `lowerComToProg_sem_eq'`, then close the loop with the
    counted-loop theorem `loopN_lower_denote_iterate`. -/
theorem setupThenLoop_run_eq {Γ : Ctxt jasminDialect} {accTy : JasminTy}
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (P : SetupThenLoop Γ accTy) (V : Ctxt.Valuation Γ) :
    P.run leafSem V = P.semantics V := by
  unfold SetupThenLoop.run SetupThenLoop.semantics
  rw [lowerComToProg_sem_eq' hLeaf P.setup P.setupSL V]
  exact loopN_lower_denote_iterate hLeaf P.n P.body (P.setup.denote V)

/-! ## 4. Worked example: `acc := a + b`, then double `n` times

The simplest validating interleaved kernel: a straight-line setup
`acc := a + b` (one `regArith add` over `[reg 64, reg 64]`, returning `reg 64`),
feeding the doubling loop `acc := acc + acc` (`LoopLowering.doubleBody`). The
composed semantics is `(fun a => a + a)^[n] (a + b)` = `(a + b) · 2^n`. -/

/-- The straight-line setup `acc := a + b` as a single-op `Com` over
    `[reg 64, reg 64]` returning `reg 64` — `regArith add 64` on the two inputs,
    then return. (The `reg 64` analogue of `smokeProg`'s first binder; its return
    type matches `doubleBody`'s accumulator.) -/
def addSetup : Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.regArith .add 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- `addSetup` is straight-line (its lone binder is a `regArith`, not the
    aliasing `stackStore`). -/
theorem addSetup_straightLine : StraightLine addSetup := by
  refine ⟨fun w n h => ?_, trivial⟩
  exact absurd h (by simp)

/-- `addSetup.denote ⟨a, b⟩ = a + b`. -/
@[simp] theorem addSetup_denote (a b : BitVec 64) :
    addSetup.denote (.cons a (.cons b .nil)) = a + b := rfl

/-- **The worked composed body.** Setup `acc := a + b` (straight-line) feeding the
    doubling loop `acc := acc + acc`, `n` times. -/
def addThenDouble (n : Nat) :
    SetupThenLoop [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) where
  setup := addSetup
  setupSL := addSetup_straightLine
  n := n
  body := doubleBody

/-- **Worked example (composition form).** The composed run of `acc := a + b`
    then `n` doublings equals `(fun a => a + a)^[n] (a + b)` — the loop semantics
    composed with the setup semantics. Instance of `setupThenLoop_run_eq`. -/
theorem addThenDouble_run_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (n : Nat) (a b : BitVec 64) :
    (addThenDouble n).run leafSem (.cons a (.cons b .nil))
      = (fun x => x + x)^[n] (a + b) := by
  rw [setupThenLoop_run_eq hLeaf (addThenDouble n) (.cons a (.cons b .nil))]
  show (fun acc => doubleBody.denote (.cons acc .nil))^[n] (addSetup.denote _) = _
  rw [addSetup_denote]
  rfl

/-- **Worked example (concrete KAT).** On inputs `a = 3, b = 4` with `n = 4`, the
    composed body computes `(3 + 4) · 2^4 = 112` byte-for-byte — the unrolled
    reference `7 → 14 → 28 → 56 → 112`. Ties the composition theorem to a
    concrete value: the straight-line prefix runs first (`3 + 4 = 7`), then the
    counted loop doubles four times. -/
theorem addThenDouble_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    (addThenDouble 4).run leafSem
        (.cons (3 : BitVec 64) (.cons (4 : BitVec 64) .nil))
      = (112 : BitVec 64) := by
  rw [addThenDouble_run_eq hLeaf]
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.WholeProtocolBody
