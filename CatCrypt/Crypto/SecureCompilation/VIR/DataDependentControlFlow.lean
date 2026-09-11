/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow
public import CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow

/-!
# Data-dependent control flow — the verified layer above counted loops

The structured-control-flow layer (`StructuredControlFlow.lean`) provides only
**counted** loops (`scfFor`/`scfRepeat`): a fixed iteration count known ahead of
time. A real prover's FRI query phase has **data-dependent** control flow — the
query indices are derived from the Fiat-Shamir transcript, so the prover branches
on runtime data and loops under a runtime-computed guard, not a static count.

This file is the verified seed of that next layer: data-dependent control flow
combinators over an arbitrary state `σ`, each fully proven and tied back to the
counted-loop layer where they coincide.

## Scope of THIS increment

* `scfIf cond thn els` — a **conditional state-step**: branch on a runtime
  predicate of the state. Lemmas `scfIf_true`, `scfIf_false`, `scfIf_const`.
* `scfWhile fuel guard step` — a **fuel-bounded guarded loop**: iterate `step`
  while `guard` holds, for at most `fuel` iterations (so it terminates). This is
  the FRI-query-style loop whose trip count is not statically known. Lemmas
  `scfWhile_zero`, `scfWhile_guard_false`, `scfWhile_guard_true`, and the tie
  `scfWhile_eq_scfRepeat_of_always` back to the counted loop when the guard is
  always taken.
* `scfSelect idx table dflt` — a **data-dependent dispatch**: pick the step by a
  runtime index into a table (the query phase's "open the i-th leaf"). Lemmas
  `scfSelect_getD`, `scfSelect_lt`.
* A concrete worked instance over `TileModel.TileState 4 32`: a `scfIf` that runs
  one `runRegBlock` body when a lane-0 predicate holds, else another, with a
  `native_decide` KAT showing the right branch fires.

Each combinator is generic over the state `σ`; the loop bodies in a real prover
are straight-line `runRegBlock` blocks over the verified tile leaves
(`TileModel.lowerRegBlock_denote`), so a data-dependent prover phase becomes a
verified combinator over the same verified straight-line backend.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.DataDependentControlFlow

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
open CatCrypt.Crypto.SecureCompilation.VIR.StructuredControlFlow

/-! ## 1. Conditional state-step (`scfIf`) -/

/-- A conditional state-step: run `thn` when the runtime predicate `cond` holds
    of the state, else `els`. This is the branch a data-dependent phase takes
    after reading the transcript. -/
def scfIf {σ : Type _} (cond : σ → Bool) (thn els : σ → σ) : σ → σ :=
  fun s => if cond s then thn s else els s

/-- When the guard fires, `scfIf` takes the `then` branch. -/
@[simp] theorem scfIf_true {σ : Type _} (cond : σ → Bool) (thn els : σ → σ)
    (s : σ) (h : cond s = true) : scfIf cond thn els s = thn s := by
  simp only [scfIf, h, if_true]

/-- When the guard is false, `scfIf` takes the `else` branch. -/
@[simp] theorem scfIf_false {σ : Type _} (cond : σ → Bool) (thn els : σ → σ)
    (s : σ) (h : cond s = false) : scfIf cond thn els s = els s := by
  simp only [scfIf, h, Bool.false_eq_true, if_false]

/-- A conditional with identical branches is that branch (irrespective of the
    guard) — the branch is dead, so the data-dependence collapses. -/
theorem scfIf_const {σ : Type _} (cond : σ → Bool) (body : σ → σ) :
    scfIf cond body body = body := by
  funext s
  simp only [scfIf, ite_self]

/-! ## 2. Fuel-bounded guarded loop (`scfWhile`) -/

/-- A fuel-bounded guarded loop: iterate `step` while `guard` holds, for at most
    `fuel` iterations. Terminating by structural recursion on `fuel`; stops early
    the moment `guard` is false. This is the FRI-query-style loop whose trip count
    is data-dependent (bounded by a static fuel for termination). -/
def scfWhile {σ : Type _} (fuel : Nat) (guard : σ → Bool) (step : σ → σ) : σ → σ :=
  fun s =>
    match fuel with
    | 0 => s
    | fuel + 1 => if guard s then scfWhile fuel guard step (step s) else s

/-- Out of fuel: the loop is the identity. -/
@[simp] theorem scfWhile_zero {σ : Type _} (guard : σ → Bool) (step : σ → σ)
    (s : σ) : scfWhile 0 guard step s = s := rfl

/-- Guard false at entry: the loop returns the state unchanged (even with fuel
    remaining). -/
theorem scfWhile_guard_false {σ : Type _} (fuel : Nat) (guard : σ → Bool)
    (step : σ → σ) (s : σ) (h : guard s = false) :
    scfWhile (fuel + 1) guard step s = s := by
  simp only [scfWhile, h, Bool.false_eq_true, if_false]

/-- Guard true at entry: peel one iteration — run `step`, then loop on the
    remaining fuel. -/
theorem scfWhile_guard_true {σ : Type _} (fuel : Nat) (guard : σ → Bool)
    (step : σ → σ) (s : σ) (h : guard s = true) :
    scfWhile (fuel + 1) guard step s = scfWhile fuel guard step (step s) := by
  simp only [scfWhile, h, if_true]

/-- **Tie to the counted loop.** When the guard is identically true, the
    fuel-bounded guarded loop is exactly the counted `scfRepeat` over the same
    fuel: the always-taken guarded loop denotes `fuel`-fold application of `step`.
    This is the data-dependent loop collapsing onto the counted-loop layer when
    every guard check passes. -/
theorem scfWhile_eq_scfRepeat_of_always {σ : Type _} (fuel : Nat) (step : σ → σ) :
    scfWhile fuel (fun _ => true) step = scfRepeat fuel step := by
  funext s
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [scfWhile_guard_true _ _ _ _ rfl, ih, scfRepeat_eq_iterate,
      scfRepeat_eq_iterate, Function.iterate_succ_apply]

/-! ## 3. Data-dependent dispatch (`scfSelect`) -/

/-- A data-dependent dispatch: select the step by a runtime index `idx s` into a
    `table` of steps, falling back to `dflt` when out of range. This is the
    "open the `i`-th leaf / run the `i`-th query handler" the FRI query phase
    needs — the index comes from the transcript at runtime. -/
def scfSelect {σ : Type _} (idx : σ → Nat) (table : List (σ → σ)) (dflt : σ → σ) :
    σ → σ :=
  fun s => (table.getD (idx s) dflt) s

/-- `scfSelect` applies the step at the runtime index (defaulting out of range):
    it is the `getD`-selected step applied to the state. -/
theorem scfSelect_getD {σ : Type _} (idx : σ → Nat) (table : List (σ → σ))
    (dflt : σ → σ) (s : σ) :
    scfSelect idx table dflt s = (table.getD (idx s) dflt) s := rfl

/-- In-bounds dispatch: when the runtime index is in range, `scfSelect` uses the
    table entry at that index (not the default). -/
theorem scfSelect_lt {σ : Type _} (idx : σ → Nat) (table : List (σ → σ))
    (dflt : σ → σ) (s : σ) (h : idx s < table.length) :
    scfSelect idx table dflt s = (table.get ⟨idx s, h⟩) s := by
  simp only [scfSelect, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
    Option.getD_some, List.get_eq_getElem]

/-! ## 4. A worked instance over `TileModel.TileState 4 32`

The branches are straight-line `runRegBlock` blocks over the verified tile leaves,
so the conditional is a verified data-dependent combinator over the verified
straight-line backend. The predicate reads lane 0 of a named tile — exactly the
"branch on a transcript-derived value" pattern a query phase uses. -/

/-- The `then` body: `acc := acc + one` (one verified `runRegBlock`). -/
def thnBody : List RegInstr := [ .bin .add "acc" "acc" "one" ]

/-- The `else` body: `acc := acc - one` (one verified `runRegBlock`). -/
def elsBody : List RegInstr := [ .bin .sub "acc" "acc" "one" ]

/-- `then`/`else` as state steps over the tile state. -/
def thnStep (s : TileState 4 32) : TileState 4 32 := runRegBlock s thnBody
def elsStep (s : TileState 4 32) : TileState 4 32 := runRegBlock s elsBody

/-- The data-dependent predicate: lane 0 of the `"flag"` tile is nonzero. This
    is the runtime, state-derived branch condition (a transcript bit, say). -/
def laneZeroSet (s : TileState 4 32) : Bool := s.get "flag" 0 ≠ 0

/-- The conditional state-step: run `thnStep` when the lane-0 flag is set, else
    `elsStep`. -/
def condStep : TileState 4 32 → TileState 4 32 :=
  scfIf laneZeroSet thnStep elsStep

/-- Initial state with the flag SET (lane 0 = 1), `acc = 0`, `one` all-ones. -/
def condInitSet : TileState 4 32 :=
  { regs := fun r =>
      if r = "one" then (fun _ => (1 : BitVec 32))
      else if r = "flag" then (fun _ => (1 : BitVec 32))
      else (fun _ => 0) }

/-- Initial state with the flag CLEAR (lane 0 = 0), `acc = 0`, `one` all-ones. -/
def condInitClear : TileState 4 32 :=
  { regs := fun r =>
      if r = "one" then (fun _ => (1 : BitVec 32))
      else (fun _ => 0) }

/-- **KAT — flag set fires the `then` branch.** With lane-0 flag set, `condStep`
    runs `acc += one`, so `acc` lanes all become `1`. -/
theorem condStep_kat_set :
    let o := (condStep condInitSet).get "acc"
    (o 0 = 1) ∧ (o 1 = 1) ∧ (o 2 = 1) ∧ (o 3 = 1) := by native_decide

/-- **KAT — flag clear fires the `else` branch.** With lane-0 flag clear,
    `condStep` runs `acc -= one`, so `acc` lanes all become `-1` (`0xFFFFFFFF`). -/
theorem condStep_kat_clear :
    let o := (condStep condInitClear).get "acc"
    (o 0 = (0 - 1 : BitVec 32)) ∧ (o 1 = (0 - 1 : BitVec 32)) ∧
      (o 2 = (0 - 1 : BitVec 32)) ∧ (o 3 = (0 - 1 : BitVec 32)) := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.DataDependentControlFlow
