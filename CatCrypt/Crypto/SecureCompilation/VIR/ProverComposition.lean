/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow
public import CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow

/-!
# Prover phase composition — the verified sequencing scaffold

A whole-prover pipeline (`trace-gen → LDE → commit → fold → query → serialize`)
is, at the orchestration level, a **sequence of phase state-steps** threaded
through one prover state. Each phase is a state transformer `σ → σ` — a
straight-line `runRegBlock` body, or an `scfRepeat` loop over such a body
(the FRI round loop, the per-row trace loop, …). This file builds the verified
**composition scaffold** for that sequencing: a `pipeline` combinator that runs
a list of phase-steps left to right, with a denotation theorem proving the
composite equals the sequential function-composition of the phases.

## Scope

This proves the **orchestration sequencing** of a prover pipeline is
denotation-preserving: composing phases as a list and running them is exactly
the right-nested function composition `(fₖ ∘ … ∘ f₁)`. It gives the algebraic
laws a phase-scheduler needs — phases split/regroup freely (`pipeline_append`),
a single phase is itself (`pipeline_single`), the empty pipeline is the identity
(`pipeline_nil`) — so a prover's `prove()` can be assembled from, and reasoned
about as, its phase list.

## What this is NOT

This is **not** a full prover, and it does **not** compose the actual Plonky3
`prove()`. It is the structural layer of the composition: it proves the
*sequencing combinator* is correct, generically over the state `σ`. Owned emission
of the individual phases (trace-gen, LDE/NTT, Merkle commit, FRI fold, query,
serialize) is outside its scope. A looped phase
here is modelled by the verified `scfRepeat` loop from `StructuredControlFlow`
(its body a `runRegBlock` over verified tile leaves), but the phases used in the
worked example are stand-ins, not the emitted prover phases.

## `foldl` direction

`pipeline phases` is `fun s => phases.foldl (fun acc f => f acc) s`, i.e. the
first list element runs *first* on the initial state. Consequently
`pipeline (f :: fs) = pipeline fs ∘ f` (run `f`, then the rest), and
`pipeline_append` regroups as `pipeline (fs ++ gs) = pipeline gs ∘ pipeline fs`.
The headline `pipeline_denote` states the composite as the right-nested
composition `fₖ (… (f₁ s))` of the phases in order.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.ProverComposition

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow
open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel

/-! ## 1. The phase-pipeline combinator -/

/-- Run a list of phase state-steps left to right, threading the state: the
    first element runs first. The orchestration combinator of a prover `prove()` —
    `[traceGen, lde, commit, fold, query, serialize]` applied in order. -/
def pipeline {σ : Type _} (phases : List (σ → σ)) : σ → σ :=
  fun s => phases.foldl (fun acc f => f acc) s

/-- The empty pipeline is the identity (no phases ⇒ no state change). -/
@[simp] theorem pipeline_nil {σ : Type _} : pipeline ([] : List (σ → σ)) = id := rfl

/-- **Cons unrolling.** Running `f :: fs` runs `f` first, then the rest:
    `pipeline (f :: fs) = pipeline fs ∘ f`. (Matches the `foldl` direction —
    the head phase is applied to the initial state, the tail to the result.) -/
theorem pipeline_cons {σ : Type _} (f : σ → σ) (fs : List (σ → σ)) :
    pipeline (f :: fs) = pipeline fs ∘ f := by
  funext s
  simp only [pipeline, List.foldl_cons, Function.comp_apply]

/-- A single-phase pipeline is that phase. -/
@[simp] theorem pipeline_single {σ : Type _} (f : σ → σ) : pipeline [f] = f := by
  funext s
  simp only [pipeline, List.foldl_cons, List.foldl_nil]

/-- **Composition associativity / regrouping.** Concatenating two phase lists
    composes their pipelines: `pipeline (fs ++ gs) = pipeline gs ∘ pipeline fs`.
    Phases can be split into sub-pipelines and regrouped freely — the law a
    phase-scheduler needs to factor `prove()` into stages. -/
theorem pipeline_append {σ : Type _} (fs gs : List (σ → σ)) :
    pipeline (fs ++ gs) = pipeline gs ∘ pipeline fs := by
  funext s
  simp only [pipeline, List.foldl_append, Function.comp_apply]

/-! ## 2. The headline denotation — composite prover = its phases sequenced -/

/-- **The denotation.** Running a pipeline equals the right-nested function
    composition of its phases in order: `pipeline [f₁, …, fₖ] s = fₖ (… (f₁ s))`.
    Stated as a `foldr`-over-composition: `pipeline phases s` is
    `(phases.foldr (· ∘ ·) id ∘ <reversal>)`… concretely we prove the clean
    sequential form `pipeline phases = phases.foldl (fun g f => f ∘ g) id`,
    i.e. the composite transformer is exactly the phases composed left to right.
    This is the "the composite prover = its phases sequenced" statement: the
    orchestration is denotation-preserving. -/
theorem pipeline_denote {σ : Type _} (phases : List (σ → σ)) :
    pipeline phases = phases.foldl (fun g f => f ∘ g) id := by
  -- Generalize the accumulator: a `foldl` of application threaded from `acc s`
  -- equals the `foldl` of composition threaded from `acc`.
  have gen : ∀ (ps : List (σ → σ)) (acc : σ → σ),
      (fun s => ps.foldl (fun a f => f a) (acc s))
        = ps.foldl (fun g f => f ∘ g) acc := by
    intro ps
    induction ps with
    | nil => intro acc; rfl
    | cons f fs ih => intro acc; simp only [List.foldl_cons]; exact ih (f ∘ acc)
  exact gen phases id

/-- **Denotation, applied form.** Spelled out pointwise: a 3-phase pipeline
    applies the phases in order, `phase₃ (phase₂ (phase₁ s))`. The general
    pointwise unrolling is `pipeline_cons`; this is the shape a fixed-length
    `prove()` denotes to. -/
theorem pipeline_denote_apply3 {σ : Type _} (f₁ f₂ f₃ : σ → σ) (s : σ) :
    pipeline [f₁, f₂, f₃] s = f₃ (f₂ (f₁ s)) := by
  simp only [pipeline, List.foldl_cons, List.foldl_nil]

/-! ## 3. A worked 3-phase example over `TileModel.TileState 4 32`

Each phase is a state-step over the prover state, built from the verified
straight-line backend (`runRegBlock`) — exactly the leaves the structured-loop
layer (`StructuredControlFlow`) loops. We take three accumulator phases and tie
the 3-phase pipeline to their sequential application, then show a phase that is
itself an `scfRepeat` **loop** composes as just another pipeline element. -/

/-- Phase 1: `acc := acc + one` once (a straight-line `runRegBlock` body). -/
def phase1 (s : TileState 4 32) : TileState 4 32 :=
  runRegBlock s [ .bin .add "acc" "acc" "one" ]

/-- Phase 2: `acc := acc + acc` (double — another straight-line body). -/
def phase2 (s : TileState 4 32) : TileState 4 32 :=
  runRegBlock s [ .bin .add "acc" "acc" "acc" ]

/-- Phase 3: `acc := acc + one` once more. -/
def phase3 (s : TileState 4 32) : TileState 4 32 :=
  runRegBlock s [ .bin .add "acc" "acc" "one" ]

/-- A start state: `"one"` the all-ones tile, `"acc"` at 0. -/
def exInit : TileState 4 32 :=
  { regs := fun r => if r = "one" then (fun _ => (1 : BitVec 32)) else (fun _ => 0) }

/-- **The 3-phase pipeline is the sequential application of the verified leaves.**
    `pipeline [phase1, phase2, phase3] s = phase3 (phase2 (phase1 s))` for every
    state — the orchestration of three `runRegBlock`-backed phases equals running
    them in order. (Instance of `pipeline_denote_apply3`.) -/
theorem ex_pipeline_denote (s : TileState 4 32) :
    pipeline [phase1, phase2, phase3] s = phase3 (phase2 (phase1 s)) :=
  pipeline_denote_apply3 phase1 phase2 phase3 s

/-- **KAT.** From `acc = 0`: phase1 → 1, phase2 (double) → 2, phase3 → 3, on
    every lane. The composed pipeline computes the expected accumulator,
    matching the sequential leaf application. -/
theorem ex_pipeline_kat :
    let o := (pipeline [phase1, phase2, phase3] exInit).get "acc"
    (o 0 = 3) ∧ (o 1 = 3) ∧ (o 2 = 3) ∧ (o 3 = 3) := by native_decide

/-! ### 3a. A looped phase composes as a pipeline element

A real phase is often a runtime-sized loop (FRI rounds, trace rows). It is just
another `σ → σ` — built with the verified `scfRepeat` loop from
`StructuredControlFlow` — so it drops into the pipeline list with no special
casing. Here `loopPhase` runs the `acc += one` body 5 times via `scfRepeat`. -/

/-- A looped phase: apply the verified `accStep` body (`acc += one`) `count`
    times via `scfRepeat`. A loop is just a state transformer `σ → σ`. -/
def loopPhase (count : Nat) (s : TileState 4 32) : TileState 4 32 :=
  scfRepeat count accStep s

/-- **A looped (`scfRepeat`) phase composes as an ordinary pipeline element.**
    Placing `loopPhase 5` between two straight-line phases denotes to the plain
    sequential application — the loop is no different from any other phase. -/
theorem looped_phase_composes (s : TileState 4 32) :
    pipeline [phase1, loopPhase 5, phase3] s = phase3 (loopPhase 5 (phase1 s)) :=
  pipeline_denote_apply3 phase1 (loopPhase 5) phase3 s

/-- **KAT for the looped phase in a pipeline.** From `acc = 0`:
    phase1 → 1, then `loopPhase 5` adds 1 five times → 6, then phase3 → 7, on
    every lane. The loop body's `count`-fold application (proved
    `scfRepeat_eq_iterate` in `StructuredControlFlow`) sits inside the composed
    pipeline transparently. -/
theorem looped_phase_kat :
    let o := (pipeline [phase1, loopPhase 5, phase3] exInit).get "acc"
    (o 0 = 7) ∧ (o 1 = 7) ∧ (o 2 = 7) ∧ (o 3 = 7) := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.ProverComposition
