/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
public import CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
public import Mathlib.Logic.Function.Iterate

/-!
# Structured control flow — the verified `scf` layer (bounded counted loop)

This is the verified **structured-control-flow** layer: the prerequisite for
emitting runtime-sized prover loops (trace rows, NTT domain, FRI rounds, query
openings) as one owned artifact. The owned straight-line backend
(`TileModel.runRegBlock` and friends) has no control flow; a real prover's
round-loop is a runtime-sized iteration. This file builds the minimal,
self-contained, fully-proven seed of that layer: a **bounded counted loop**
combinator over a state, with a denotation theorem tying it to `n`-fold
application.

## Scope of THIS increment

* A bounded counted loop `scfFor count step : σ → σ` over an arbitrary state
  type `σ`, threading the state through `step 0, step 1, …, step (count-1)`.
  The body `step : Nat → σ → σ` receives the loop index (so it can read a round
  constant index, FRI-round number, etc.).
* The index-free `scfRepeat count step := scfFor count (fun _ => step)`.
* The denotation/unfolding lemmas: `scfFor_zero`, the end-unroll
  `scfFor_succ`, and the **key denotation** `scfRepeat_eq_iterate` tying a
  counted repeat to `Function.iterate` (`step^[count]`) — "loop = n-fold
  application".
* A concrete worked instance over `TileModel.TileState 4 32`: looping a fixed
  `runRegBlock` body `count` times, with a denotation showing the result is the
  `count`-fold application of the body, plus a `native_decide` KAT.

The body of a real loop is a straight-line `runRegBlock` over verified tile
leaves, so a prover's round-loop becomes a verified combinator over the same
verified leaves (`TileModel.lowerRegBlock_denote`).

## Unrolling direction

`scfFor` is `(List.range count).foldl (fun s i => step i s) s0`. The natural
`foldl` unroll is off the *front*; using `List.range_succ`
(`range (n+1) = range n ++ [n]`) the loop also unrolls cleanly off the *end*,
which is the form a round-loop wants (`scfFor (count+1) = step count ∘ scfFor
count`). Both directions are proved below.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel

/-! ## 1. The bounded counted-loop combinator -/

/-- A bounded counted loop: apply `step` for indices `0, 1, …, count-1`,
    threading the state. The index is passed to `step` so the body can read the
    loop counter (a round-constant index, FRI round number, …). Implemented as a
    left fold over `List.range count`. -/
def scfFor {σ : Type _} (count : Nat) (step : Nat → σ → σ) (s0 : σ) : σ :=
  (List.range count).foldl (fun s i => step i s) s0

/-- The index-free counted loop: apply a fixed `step` exactly `count` times. -/
def scfRepeat {σ : Type _} (count : Nat) (step : σ → σ) : σ → σ :=
  scfFor count (fun _ => step)

/-! ## 2. Denotation / unfolding lemmas -/

/-- A zero-count loop is the identity. -/
@[simp] theorem scfFor_zero {σ : Type _} (step : Nat → σ → σ) (s : σ) :
    scfFor 0 step s = s := rfl

/-- **End-unroll.** A `(count+1)`-loop is the `count`-loop followed by one more
    `step` at index `count`: `scfFor (count+1) step s = step count (scfFor count
    step s)`. This is the form a round-loop unrolls — the last iteration peels
    off the end. -/
theorem scfFor_succ {σ : Type _} (count : Nat) (step : Nat → σ → σ) (s : σ) :
    scfFor (count + 1) step s = step count (scfFor count step s) := by
  simp only [scfFor, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- **Front-unroll.** A `(count+1)`-loop first does `step 0`, then a `count`-loop
    of the *shifted* body `step (·+1)` from there. (The natural `foldl`
    direction; documented for completeness.) -/
theorem scfFor_succ_front {σ : Type _} (count : Nat) (step : Nat → σ → σ) (s : σ) :
    scfFor (count + 1) step s
      = scfFor count (fun i => step (i + 1)) (step 0 s) := by
  simp only [scfFor, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]

/-- `scfRepeat` zero-count is the identity. -/
@[simp] theorem scfRepeat_zero {σ : Type _} (step : σ → σ) (s : σ) :
    scfRepeat 0 step s = s := rfl

/-- **End-unroll for `scfRepeat`.** -/
theorem scfRepeat_succ {σ : Type _} (count : Nat) (step : σ → σ) (s : σ) :
    scfRepeat (count + 1) step s = step (scfRepeat count step s) :=
  scfFor_succ count (fun _ => step) s

/-- **The key denotation — a counted repeat is `n`-fold application.**
    `scfRepeat count step = step^[count]` (`Function.iterate`). This is the
    "loop = n-fold application of the body" denotation: a runtime-sized round
    loop over a straight-line body denotes the `count`-th iterate of that body. -/
theorem scfRepeat_eq_iterate {σ : Type _} (count : Nat) (step : σ → σ) :
    scfRepeat count step = (step^[count]) := by
  funext s
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [scfRepeat_succ, ih, Function.iterate_succ']
    rfl

/-! ## 3. A worked instance over `TileModel.TileState 4 32`

The loop body is a straight-line `runRegBlock` over the verified tile leaves, so
looping it is a verified combinator over the verified straight-line backend. We
take a one-op accumulator body (`acc := acc + one`) and show that looping it
`count` times denotes the `count`-fold application of the body — the loop
denotation specialised to a concrete state. -/

/-- The loop body: a straight-line block that adds the tile `"one"` into the
    accumulator `"acc"` (a single verified `runRegBlock` over tile leaves). -/
def accBody : List RegInstr := [ .bin .add "acc" "acc" "one" ]

/-- One loop iteration as a state step: run the straight-line `accBody`. -/
def accStep (s : TileState 4 32) : TileState 4 32 := runRegBlock s accBody

/-- The loop initial state: `"one"` is the all-ones tile, `"acc"` starts at 0. -/
def accInit : TileState 4 32 :=
  { regs := fun r => if r = "one" then (fun _ => (1 : BitVec 32)) else (fun _ => 0) }

/-- **The accumulator loop denotes `count`-fold application of its body.** This
    is the structured-loop denotation specialised: `scfRepeat count accStep`
    equals `accStep^[count]`, i.e. the runtime-sized loop over the straight-line
    `runRegBlock` body is exactly the `count`-th iterate of that verified leaf. -/
theorem accLoop_denote (count : Nat) :
    scfRepeat count accStep = (accStep^[count]) :=
  scfRepeat_eq_iterate count accStep

/-- **KAT.** Looping the `acc += one` body 3 times over `accInit` gives `acc`
    lanes all equal to `3` — the verified loop computes the expected accumulator,
    matching the `count`-fold body application. -/
theorem accLoop_kat :
    let o := (scfRepeat 3 accStep accInit).get "acc"
    (o 0 = 3) ∧ (o 1 = 3) ∧ (o 2 = 3) ∧ (o 3 = 3) := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow
