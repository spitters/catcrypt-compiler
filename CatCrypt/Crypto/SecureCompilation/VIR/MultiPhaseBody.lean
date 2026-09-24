/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.WholeProtocolBody
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiBinderLoopBody

/-!
# Multi-phase whole-protocol body: a SEQUENCE of phases over one accumulator,
# with the composed run = the left-fold of the phases' semantics

`WholeProtocolBody.lean` composes a straight-line **setup** with **one** counted
loop (`setupThenLoop_run_eq : run = loop_semantics ∘ setup_semantics`). Real
protocols are not a single fragment: an absorb-then-squeeze sponge is
`absorb-loop; squeeze-loop`; a key-schedule-then-rounds block cipher is
`schedule; round-loop`; a streaming MAC is `setup; block-loop; finalize`. The
common shape is a **sequence** `phase₁; phase₂; …; phaseₖ`, each a self-map of
the accumulator (a straight-line block or a counted loop), run left-to-right.

This file generalises the two-component `SetupThenLoop` to an arbitrary-length
**list of phases** folded over the accumulator, and proves the composed emitted
run equals the left-fold of the phases' reference semantics — i.e. the function
composition `phaseₖ.sem ∘ … ∘ phase₂.sem ∘ phase₁.sem` of the per-phase
semantics. The induction is on the phase list; each phase's own soundness is
reused verbatim.

## The model (reuse, not rebuild)

A **phase** is bundled as a self-map of the accumulator together with its own
already-discharged soundness:

* `run  : ⟦accTy⟧ → ⟦accTy⟧` — the emitted evaluator run, threaded over the
  accumulator (the `runProg`/`loopRun` of the lowering theorems, abstracted to a
  function of the incoming accumulator).
* `sem  : ⟦accTy⟧ → ⟦accTy⟧` — the reference semantics (the `Com.denote` /
  `body.denote^[n]` of the lowering theorems).
* `sound : run = sem` — the per-phase soundness, **supplied by an existing
  lowering theorem** at construction time.

Smart constructors build phases from the lowering theorems, each
discharging `sound` with no new proof obligation:

* `loopPhase`   — from `LoopLowering.loopN n body`, sound via
  `LoopLowering.loopN_lower_denote_iterate` (single-op body).
* `loopPhaseMulti` — from `MultiBinderLoopBody.loopNMulti n body` for a
  multi-binder straight-line body, sound via
  `MultiBinderLoopBody.loopNMulti_lower_denote_iterate`.
* `straightPhase` — from a straight-line `Com jasminDialect [accTy] accTy`
  (a block over the singleton accumulator context), sound via
  `WholeFnLowering.lowerComToProg_sem_eq'` instantiated at `V = .cons init .nil`.

A **protocol** is then a `List (Phase accTy)`; its composed run / semantics are
the left-folds of the phases' `run` / `sem` over the initial accumulator, and
the composed soundness is `phasesRun_eq` by induction on the list.

## What is reused vs newly proved

* **Reused verbatim** (no new proof obligation): every per-phase soundness —
  `loopN_lower_denote_iterate`, `loopNMulti_lower_denote_iterate`,
  `lowerComToProg_sem_eq'`. The smart constructors thread them into the `sound`
  field.
* **Newly proved**: `Phase`/`phasesRun`/`phasesSem` (the list-folded
  multi-phase surface) and `phasesRun_eq` (the composed soundness, by induction
  on the phase list — threading per-phase soundness through a `List.foldl`).

## Conditioned scope

Each phase carries its own `sound`, so the carried hypotheses are exactly the
union of the per-phase hypotheses — every phase needs `LeafAgrees leafSem`, and
each straight-line / loop phase additionally needs its body `StraightLine`.
These are supplied once at construction (the smart constructors take `hLeaf`
and the per-phase `StraightLine` witness) and never re-incurred by the fold.

It does **not** cover: data-dependent phase **selection** (the phase list is
fixed, not chosen by a runtime predicate — that is the `if`/branch layer,
`StructuredControlFlow`); **calls between phases as a single fused control-flow
graph** (this composes the phases' emitted runs at the meta level over a shared
accumulator value, exactly as `WholeProtocolBody` composes setup and loop — the
`extCall` leaf stays opaque under `LeafAgrees`, it is not a fused CFG with a real
`call` instruction); or **heterogeneous accumulators** (every phase is a self-map
of the *same* `accTy`; a phase that grows/shrinks the live set would need a typed
seam `accTy₁ → accTy₂`, a dependent list — see the gap note).

All goals closed; the only carried hypotheses are `LeafAgrees` and the per-phase
`StraightLine` witnesses, the same edges carried throughout the emit theory.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MultiPhaseBody

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering
open CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBinderLoopBody

/-! ## 1. A single phase: a sound self-map of the accumulator

A `Phase accTy` is a self-map of the accumulator type `accTy`, bundling the
emitted evaluator run, the reference semantics, and a proof that they agree.
The proof is discharged at construction by one of the lowering theorems, so a
phase is *by construction* a verified accumulator transform. -/

/-- **A single verified phase.** A self-map of the accumulator `accTy` packaging
    the emitted evaluator `run`, the reference `sem`antics, and the per-phase
    soundness `sound : run = sem` (discharged at construction by a lowering
    theorem). The unit of composition for a multi-phase protocol body. -/
structure Phase (accTy : JasminTy) where
  /-- The emitted evaluator run, as a self-map of the accumulator. -/
  run : ⟦accTy⟧ → ⟦accTy⟧
  /-- The reference semantics, as a self-map of the accumulator. -/
  sem : ⟦accTy⟧ → ⟦accTy⟧
  /-- The per-phase soundness: the emitted run equals the reference semantics.
      Supplied by an existing lowering theorem at construction. -/
  sound : run = sem

/-! ## 2. Smart constructors — each discharges `sound` from a lowering theorem

Each constructor takes the opaque-leaf edge `hLeaf` (and any per-phase
`StraightLine` witness) and produces a `Phase` whose `sound` field is exactly
the corresponding lowering theorem applied pointwise. No new proof obligation. -/

/-- **A counted-loop phase (single-op body).** `loopPhase hLeaf n body` is the
    phase that runs the counted loop `loopN n body` over the incoming
    accumulator; its `sem` is the `n`-fold body denotation
    `(fun acc => body.denote (.cons acc .nil))^[n]`. `sound` is
    `LoopLowering.loopN_lower_denote_iterate` (no new obligation). -/
def loopPhase {accTy : JasminTy} {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (n : Nat) (body : LoopBody accTy) : Phase accTy where
  run := fun init =>
    loopRun (loopN n body) (bodyStepRun leafSem (loopN n body)) init
  sem := fun init => (fun acc => body.denote (.cons acc .nil))^[n] init
  sound := by
    funext init
    exact loopN_lower_denote_iterate hLeaf n body init

/-- **A counted-loop phase (multi-binder straight-line body).**
    `loopPhaseMulti hLeaf n body hSL` runs the multi-binder counted loop
    `loopNMulti n body` over the incoming accumulator; `sem` is the `n`-fold body
    denotation. `sound` is
    `MultiBinderLoopBody.loopNMulti_lower_denote_iterate` (no new obligation).
    Requires the body to be `StraightLine`. -/
def loopPhaseMulti {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (n : Nat) (body : MultiBinderBody accTy)
    (hSL : StraightLine body) : Phase accTy where
  run := fun init =>
    loopRun (loopNMulti n body) (bodyStepRun leafSem (loopNMulti n body)) init
  sem := fun init => (fun acc => body.denote (.cons acc .nil))^[n] init
  sound := by
    funext init
    exact loopNMulti_lower_denote_iterate hLeaf n body hSL init

/-- **A straight-line block phase.** `straightPhase hLeaf com hSL` runs the
    straight-line block `com : Com jasminDialect [accTy] accTy` (a block over the
    singleton accumulator context) over the incoming accumulator; `sem` is its
    `Com.denote`. `sound` is `WholeFnLowering.lowerComToProg_sem_eq'`
    instantiated at the singleton valuation `V = .cons init .nil` (no new
    obligation). Requires the block to be `StraightLine`. -/
def straightPhase {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (com : Com jasminDialect [accTy] accTy)
    (hSL : StraightLine com) : Phase accTy where
  run := fun init => runProg leafSem com (.cons init .nil)
  sem := fun init => com.denote (.cons init .nil)
  sound := by
    funext init
    exact lowerComToProg_sem_eq' hLeaf com hSL (.cons init .nil)

/-! ## 3. The multi-phase protocol body: a list of phases folded over the
# accumulator

A protocol is a `List (Phase accTy)`. Its composed emitted run / reference
semantics are the left-folds of the phases' `run` / `sem` over the initial
accumulator (left-to-right: `phase₁` first). The composed soundness is then by
induction on the list. -/

/-- **The composed emitted run.** Fold the phases' `run`s left-to-right over the
    initial accumulator `init`: `phase₁.run` first, then `phase₂.run`, … This is
    the whole multi-phase body run — each phase's emitted evaluator threaded over
    the accumulator produced by the previous phase. -/
def phasesRun {accTy : JasminTy} (phases : List (Phase accTy))
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  phases.foldl (fun acc p => p.run acc) init

/-- **The composed reference semantics.** Fold the phases' `sem`antics
    left-to-right over the initial accumulator — the left-fold form of the
    function composition `phaseₖ.sem ∘ … ∘ phase₁.sem`. The ground truth the
    composed run must match. -/
def phasesSem {accTy : JasminTy} (phases : List (Phase accTy))
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  phases.foldl (fun acc p => p.sem acc) init

/-! ## 4. The composed soundness — by induction on the phase list -/

/-- **Composed multi-phase denote-correctness.** The composed emitted run of a
    sequence of phases equals the composed reference semantics — the left-fold of
    the phases' `sem`antics over the initial accumulator, i.e. the function
    composition `phaseₖ.sem ∘ … ∘ phase₁.sem` applied to `init`. By induction on
    the phase list: the head phase's `run = sem` (its `sound` field) rewrites the
    first fold step, and the tail closes by the inductive hypothesis on the
    accumulator the head produced. Every per-phase soundness is reused verbatim;
    the threading through `List.foldl` is the new content. No global hypothesis:
    each phase already carries its own (`LeafAgrees` + `StraightLine`). -/
theorem phasesRun_eq {accTy : JasminTy} (phases : List (Phase accTy))
    (init : ⟦accTy⟧) :
    phasesRun phases init = phasesSem phases init := by
  unfold phasesRun phasesSem
  induction phases generalizing init with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.foldl_cons]
      rw [p.sound]
      exact ih (p.sem init)

/-- **Composition form.** The composed semantics of `phase₁ :: phase₂ :: rest`
    threads `phase₁.sem init` into the rest — the explicit "function composition
    of the phases' semantics" reading. A `simp`-normal restatement of
    `phasesSem` on a cons, exposing the left-to-right composition. -/
theorem phasesSem_cons {accTy : JasminTy} (p : Phase accTy)
    (ps : List (Phase accTy)) (init : ⟦accTy⟧) :
    phasesSem (p :: ps) init = phasesSem ps (p.sem init) := rfl

/-! ## 5. Worked example: a 3-phase protocol
# `setup (acc := a + b); loop₁ double n₁×; loop₂ add-step n₂×`

A concrete multi-phase body exercising both phase kinds twice over: a
straight-line **setup** `acc := a + b`, then a **doubling loop** (`acc := acc + acc`,
`n₁` times), then a **second doubling loop** (`n₂` times). The composed semantics
is `double^[n₂] ∘ double^[n₁] ∘ (a + b)`, i.e. `(a + b) · 2^(n₁ + n₂)`. We give
the protocol, its composed run, and a concrete KAT.

(The setup phase reuses `WholeProtocolBody.addSetup` — `acc := a + b` over the
singleton-after-currying context. Here the phase accumulator is `reg 64`, so the
setup block is a self-map `[reg 64] → reg 64`; we use the doubling body's shape
for the loops, and a single-input add-with-self for the setup so it is a
`[reg 64] → reg 64` straight-line block.) -/

/-- A straight-line setup block over the singleton accumulator context
    `[reg 64]`: `acc := acc + acc` (a self-map block, the simplest
    `[reg 64] → reg 64` straight-line `Com`). Denotes `acc ↦ acc + acc`. Reuses
    the doubling op shape as a `Com` (one `regArith add`, then return). -/
def setupBlock : Com jasminDialect [JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil)))
    (.ret .here)

/-- `setupBlock` is straight-line (its lone binder is a `regArith`). -/
theorem setupBlock_straightLine : StraightLine setupBlock := by
  refine ⟨fun w n h => ?_, trivial⟩
  exact absurd h (by simp)

/-- `setupBlock.denote ⟨acc⟩ = acc + acc`. -/
@[simp] theorem setupBlock_denote (acc : BitVec 64) :
    setupBlock.denote (.cons acc .nil) = acc + acc := rfl

/-- **The worked 3-phase protocol.** `straightPhase setupBlock` (doubling once),
    then `loopPhase n₁ doubleBody` (doubling `n₁` times), then
    `loopPhase n₂ doubleBody` (doubling `n₂` times). Three phases over the single
    accumulator `reg 64`. -/
def threePhaseDouble {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (n₁ n₂ : Nat) : List (Phase (.reg 64)) :=
  [ straightPhase hLeaf setupBlock setupBlock_straightLine,
    loopPhase hLeaf n₁ doubleBody,
    loopPhase hLeaf n₂ doubleBody ]

/-- **Worked example (composition form).** The composed run of the 3-phase
    protocol equals `double^[n₂] (double^[n₁] (init + init))` — the left-to-right
    composition of the three phases' semantics. Instance of `phasesRun_eq`. -/
theorem threePhaseDouble_run_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (n₁ n₂ : Nat) (init : BitVec 64) :
    phasesRun (threePhaseDouble hLeaf n₁ n₂) init
      = (fun a => a + a)^[n₂] ((fun a => a + a)^[n₁] (init + init)) := by
  rw [phasesRun_eq]
  unfold threePhaseDouble phasesSem
  simp only [List.foldl_cons, List.foldl_nil, straightPhase, loopPhase]
  rfl

/-- **Worked example (concrete KAT).** On seed `init = 1` with `n₁ = 2, n₂ = 3`,
    the 3-phase body computes `(1 + 1) · 2^(2+3) = 2 · 32 = 64` byte-for-byte:
    setup doubles `1 → 2`, loop₁ doubles twice `2 → 4 → 8`, loop₂ doubles thrice
    `8 → 16 → 32 → 64`. Ties the multi-phase composition theorem to a concrete
    value across two phase kinds. -/
theorem threePhaseDouble_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    phasesRun (threePhaseDouble hLeaf 2 3) (1 : BitVec 64) = (64 : BitVec 64) := by
  rw [threePhaseDouble_run_eq hLeaf]
  rfl

/-! ## 6. Worked example: a heterogeneous-kind 2-phase protocol with a
# multi-binder loop body, `setup; round-loop`

A second worked instance combining a straight-line setup with a **multi-binder**
loop phase (`loopPhaseMulti` on `MultiBinderLoopBody.roundBody`,
`acc ↦ (acc + acc) ^^^ acc`), to exercise all three smart constructors across
the file. -/

/-- **A 2-phase protocol** `setup (acc := acc + acc); round-loop n×` where the
    loop body is the multi-binder `roundBody = acc ↦ (acc + acc) ^^^ acc`. -/
def setupThenRound {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (n : Nat) : List (Phase (.reg 64)) :=
  [ straightPhase hLeaf setupBlock setupBlock_straightLine,
    loopPhaseMulti hLeaf n roundBody roundBody_straightLine ]

/-- **Worked example (composition form).** The composed run of `setup; round-loop`
    equals `round^[n] (init + init)`. Instance of `phasesRun_eq` exercising the
    multi-binder loop phase. -/
theorem setupThenRound_run_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (n : Nat) (init : BitVec 64) :
    phasesRun (setupThenRound hLeaf n) init
      = (fun acc => (acc + acc) ^^^ acc)^[n] (init + init) := by
  rw [phasesRun_eq]
  unfold setupThenRound phasesSem
  simp only [List.foldl_cons, List.foldl_nil, straightPhase, loopPhaseMulti]
  rfl

/-- **Worked example (concrete KAT).** On seed `init = 1` with `n = 2`: setup
    doubles `1 → 2`, then two round steps `2 → (2+2)^^^2 = 6 → (6+6)^^^6 = 10`,
    i.e. `10`. -/
theorem setupThenRound_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    phasesRun (setupThenRound hLeaf 2) (1 : BitVec 64) = (10 : BitVec 64) := by
  rw [setupThenRound_run_eq hLeaf]
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.MultiPhaseBody
