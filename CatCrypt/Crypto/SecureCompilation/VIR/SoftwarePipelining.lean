/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.InstructionSchedule
public import CatCrypt.Crypto.SecureCompilation.VIR.InstructionSchedule

/-!
# Software-pipelining schedule for `JForProg` loop bodies

This module computes a 2-stage modulo schedule (stage assignment,
initiation interval, prologue / kernel / epilogue partition) for a
`JForProg` body. The `Com` transform that peels the first iteration, with its
denotation and CT theorems, is `SoftwarePipeliningReal`.

Software pipelining overlaps execution of consecutive loop iterations so
that operations from iter `N+1` issue concurrently with later
operations of iter `N`. The transformed loop has three phases:

* **prologue** — issues stages `0..s-1` of the first iteration only
  (one-shot "warm-up" code);
* **steady state** — the modulo-scheduled kernel: each iteration of the
  kernel executes stage `s` of iter `N + s` concurrently for all
  `s ∈ 0..S-1`, advancing all in-flight iterations by one slot per
  kernel cycle;
* **epilogue** — issues stages `s..S-1` of the last `S-1` iterations only
  (one-shot "cool-down" code).

For our crypto kernels this matters concretely: NTT butterfly stages
are pipelinable across iterations (the next butterfly's load can start
while the previous one's multiply is still in flight); Keccak round
chains expose ILP across rounds when interleaved. ChaCha20 quarter-round
loops similarly benefit from a 2-stage pipeline that overlaps the
add-rotate-add-rotate dependence chain with the next quarter-round's
initial adds.

## Dependences and stages on `Com`

The dependence relation on a straight-line `Com` body is **purely
data-driven** (same as `InstructionSchedule`): binder `i` depends on
binder `j` (written `j ≺ i`) iff some `Ctxt.Var` argument of `e_i`
resolves to position `j`. There are no aliasing concerns: `Com d Γ t`
is single-static-assignment by construction.

A **2-stage modulo schedule** assigns each binder a stage `s ∈ {0, 1}`.
In the steady-state kernel, stage `0` of iter `N+1` runs concurrently
with stage `1` of iter `N`. The constraint for stage assignment is
that every cross-iteration carried value (the accumulator) is consumed
at stage `≥` the stage where it is produced (otherwise we'd consume
before producing).

For a single-accumulator `JForProg`, the carried value is the
accumulator. The accumulator is produced at the very end of one
iteration (`Com.ret`) and consumed at the start of the next (the
input-context slot `.here` at depth = `numBinders`). So a stage-`0`
binder must not consume any value produced at stage `1` *of the same
iteration* — equivalently, any binder that consumes a stage-`1`
binder's output must itself be at stage `1`.

The simplest sound 2-stage assignment is the **dep-chain bisection**:
binders in the first half of the dep-chain (by topological distance
from the entry) go to stage `0`; the rest go to stage `1`. The kernel
of a 2-stage schedule executes 2 iterations in flight (prologue runs
stage `0` of iter `0` only; steady runs stage `0` of iter `N+1` and
stage `1` of iter `N` concurrently; epilogue runs stage `1` of the
last iter only).

**Initiation interval (II)**: the number of cycles between issuing
consecutive iterations. For a 2-stage pipeline, II is the maximum
load on either stage — equivalently, `max(|stage 0 binders|,
|stage 1 binders|)`. The full pipelined throughput is
`II ≤ ceil(|body| / S)` cycles per iteration, vs `|body|` cycles for
the un-pipelined loop.

## Main results

* `analyzeSwp_order_eq_scheduleGreedy`,
  `analyzeSchedule_analyzeSwp_order_agree` — the pipelining order is the
  `InstructionSchedule` order.
* `analyzeSwp_empty_body`, `assignStages2_empty`, `assignStages2_singleton`,
  `assignStages2_three`, `assignStages2_four` — the schedule on small shapes.

## Contents

* `Stage` — abbreviation for the stage index (`Nat`; at most `1` in the
  2-stage pipeline).
* `StageAssignment` — the per-binder stage map: `(pos, stage)`.
* `assignStages2` — a simple 2-stage assignment heuristic: bisect the
  topological order at its midpoint. Identity-safe on bodies with no
  cross-iteration ILP (single-binder, empty body).
* `SoftwarePipelineDecisions` — the analysis result: II, the prologue
  / kernel / epilogue partition, and the per-binder stage assignment.
* `analyzeSwp` — top-level: compute dependences (via
  `InstructionSchedule.computeDependences`), run the greedy schedule
  (via `InstructionSchedule.scheduleGreedy`), bisect for stages,
  compute II.
* Sanity examples on the empty body, a single-binder body, the 3-binder
  linear chain and a 4-binder ILP-exposing body.

The schedule has at most 2 iterations in flight, covers one bounded `Cfor`,
and assumes unit latency per operation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. Stage assignment for a 2-stage pipeline

We pick a topological order of the body's dependence DAG (reusing
`InstructionSchedule.scheduleGreedy`), then split it in half: the first
half goes to stage `0`, the second half goes to stage `1`. This
maintains the soundness invariant trivially — a consumer's position is
strictly later in the topological order than its producer's, so a
consumer can never be at a strictly earlier stage.

For a body of `k` binders, the midpoint is `(k + 1) / 2` (so a body
with 0 binders has all in stage 0, a body with 1 binder has that
binder in stage 0, a body with 3 binders has positions 0,1 in stage 0
and position 2 in stage 1, a body with 4 binders has positions 0,1 in
stage 0 and 2,3 in stage 1). -/

/-- Stage index, a `Nat`; in a 2-stage pipeline it is `0` or `1`. -/
abbrev Stage : Type := Nat

/-- The per-binder stage assignment: position → stage. -/
structure StageAssignment where
  /-- The mapping: each entry is `(binder position, assigned stage)`.
      Entries appear in the **scheduled** (topological) order, not the
      original `Com` order. -/
  entries : List (Nat × Stage)
  deriving Repr, DecidableEq

namespace StageAssignment

/-- The empty assignment — for empty-body programs. -/
def empty : StageAssignment where
  entries := []

/-- Look up a binder's stage by position. Returns `none` if the position
    isn't in this assignment. -/
def stageOf (a : StageAssignment) (pos : Nat) : Option Stage :=
  a.entries.find? (fun e => e.fst == pos) |>.map (·.snd)

/-- The number of binders assigned to a given stage. -/
def countStage (a : StageAssignment) (s : Stage) : Nat :=
  (a.entries.filter (fun e => e.snd == s)).length

end StageAssignment

/-- **2-stage bisection assignment.** Given a topological order of
    binder positions, assign the first half (rounded up) to stage `0`,
    the rest to stage `1`. Returns a list of `(position, stage)` pairs
    in the same order as the input. -/
def assignStages2 (order : List Nat) : StageAssignment :=
  let k := order.length
  let midpoint := (k + 1) / 2
  { entries := order.zipIdx.map fun e =>
      (e.fst, if e.snd < midpoint then 0 else 1) }

/-! ## 2. The analysis result -/

/-- **A software-pipelining decision.**

Records:

* `order` — the topological order of binder positions chosen by
  `scheduleGreedy` (so this pass composes cleanly with the
  `InstructionSchedule` intra-iteration scheduler);
* `stages` — the per-binder stage assignment;
* `numStages` — the total number of stages in the pipeline (capped at
  `2`);
* `initiationInterval` — the steady-state cycle count per iteration:
  `max (#stage-0 binders) (#stage-1 binders)`. The un-pipelined loop's
  per-iter cost is `numBinders`; the pipelined kernel's is II, so the
  expected speedup is `numBinders / II` (capped at `numStages`).

The prologue is stage `0` of iteration `0`, the kernel interleaves stage `0`
of iteration `N+1` with stage `1` of iteration `N`, and the epilogue is
stage `1` of the last iteration. -/
structure SoftwarePipelineDecisions where
  /-- The topological order of binder positions chosen by
      `scheduleGreedy` (composes cleanly with `InstructionSchedule`). -/
  order : List Nat
  /-- The per-binder stage assignment in scheduled order. -/
  stages : StageAssignment
  /-- The total number of stages (`2`). -/
  numStages : Nat
  /-- The initiation interval — steady-state cycles per iteration. -/
  initiationInterval : Nat
  deriving Repr

namespace SoftwarePipelineDecisions

/-- The trivial no-op decision: no pipelining, identity schedule. -/
def empty : SoftwarePipelineDecisions where
  order := []
  stages := StageAssignment.empty
  numStages := 1
  initiationInterval := 0

/-- The prologue's binder positions: stage `0` only (one-shot first-iter
    warm-up). -/
def prologue (d : SoftwarePipelineDecisions) : List Nat :=
  d.stages.entries.filterMap (fun e => if e.snd == 0 then some e.fst else none)

/-- The epilogue's binder positions: stage `1` only (one-shot last-iter
    cool-down). -/
def epilogue (d : SoftwarePipelineDecisions) : List Nat :=
  d.stages.entries.filterMap (fun e => if e.snd == 1 then some e.fst else none)

/-- The steady-state kernel's binder positions: **all stages**, since
    each kernel cycle issues a binder from every stage of a different
    in-flight iteration. -/
def kernel (d : SoftwarePipelineDecisions) : List Nat :=
  d.stages.entries.map (·.fst)

end SoftwarePipelineDecisions

/-! ## 3. The analyser

Top-level pipelining analysis: compute dependences, run the greedy
list scheduler (composing with `InstructionSchedule`), bisect for stages,
derive II. -/

/-- **Software-pipelining analysis.** Reuses `computeDependences` and
    `scheduleGreedy` from `InstructionSchedule.lean` to obtain a
    topological order; then bisects for the 2-stage assignment and
    computes II. The analysis is capped at 2 stages. -/
def analyzeSwp {accTy : JasminTy} (p : JForProg accTy) :
    SoftwarePipelineDecisions :=
  let deps := computeDependences p
  let order := scheduleGreedy deps
  let stages := assignStages2 order
  let s0 := stages.countStage 0
  let s1 := stages.countStage 1
  { order := order
  , stages := stages
  , numStages := 2
  , initiationInterval := max s0 s1 }

/-! ## 4. Analysis correctness on small shapes

The natural correctness statement for `analyzeSwp` is: the produced
stage assignment respects the data-dependence partial order (a
consumer is never at a strictly earlier stage than its producer), and
II is `max (#stage-0) (#stage-1)`. We discharge *single-shape*
instances here.

The full stage-soundness statement (every binder's stage is `≥` the
max stage of its dependences) is the operational invariant maintained
by `assignStages2` by construction: it bisects a topological order, so
a consumer at index `i` has all its producers at indices `< i`, hence
at a `≤` index, hence at a `≤` stage. -/

/-- **Empty-body pipelining is the empty decision.** For a `JForProg`
    whose body is `Com.ret v` (no binders), `analyzeSwp` returns the
    empty schedule, empty stages, II = 0. -/
theorem analyzeSwp_empty_body {accTy : JasminTy} (n : Nat)
    (v : Ctxt.Var (d := jasminDialect) [accTy] accTy) :
    (analyzeSwp { n := n, update := Com.ret v }) =
      { order := [], stages := StageAssignment.empty
      , numStages := 2, initiationInterval := 0 } :=
  rfl

/-- **`assignStages2` on the empty input is empty.** -/
theorem assignStages2_empty : assignStages2 [] = StageAssignment.empty := rfl

/-- **`assignStages2` on a singleton: the single binder is at stage 0.**
    Midpoint of 1 binders is `(1 + 1) / 2 = 1`; index `0 < 1`, so the
    binder is at stage `0`. -/
theorem assignStages2_singleton (pos : Nat) :
    assignStages2 [pos] = { entries := [(pos, 0)] } := by
  unfold assignStages2
  simp [List.zipIdx]

/-- **`assignStages2` bisects a 4-binder topological order.** Positions
    `0, 1` go to stage `0`; positions `2, 3` go to stage `1`. -/
theorem assignStages2_four :
    assignStages2 [0, 1, 2, 3] =
      { entries := [(0, 0), (1, 0), (2, 1), (3, 1)] } := by decide

/-- **`assignStages2` on a 3-binder topological order.** Midpoint of
    3 binders is `(3 + 1) / 2 = 2`. Positions `0, 1` go to stage `0`;
    position `2` goes to stage `1`. -/
theorem assignStages2_three :
    assignStages2 [0, 1, 2] =
      { entries := [(0, 0), (1, 0), (2, 1)] } := by decide

/-! ## 5. Sanity tests

These confirm `analyzeSwp` behaves correctly on small synthetic body
shapes — the smallest "is the pipelining analysis wired up?" smoke
tests. -/

/-- The empty body has the empty pipelining decision. -/
example {accTy : JasminTy} (v : Ctxt.Var (d := jasminDialect) [accTy] accTy) :
    (analyzeSwp { n := 0, update := Com.ret v }).order = [] := rfl

-- The empty body's analysis is computable: `#eval` returns the empty
-- decision.
#eval (analyzeSwp
        (accTy := .reg 64)
        { n := 0, update := Com.ret .here }).order

/-- A `regArith` binary `Expr` over `reg 64`, local helper for the
    sanity tests below. (Mirrors helpers in `DeadCodeElim.lean`,
    `CommonSubexprElim.lean`, `InstructionSchedule.lean`.) -/
def binExprR64 {Γ : Ctxt jasminDialect} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg 64)) : Expr jasminDialect Γ (.reg 64) :=
  { op := .regArith op 64, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-! **Single-binder body** (`singleBinderBody` / `singleBinderProg`, shared with
    `InstructionSchedule.lean`): one independent computation.

    ```
    v0 = acc + acc          -- position 0, deps = {} (only reads acc)
    ret v0
    ```

    The pipeline schedule is `[0]`; stages are `[(0, 0)]`; II = 1
    (one cycle per iter). -/

example : (analyzeSwp singleBinderProg).order = [0] := rfl
example : (analyzeSwp singleBinderProg).stages.entries = [(0, 0)] := rfl
example : (analyzeSwp singleBinderProg).initiationInterval = 1 := rfl
example : (analyzeSwp singleBinderProg).numStages = 2 := rfl

/-- **Canonical 3-stage linear-chain shape** (the smoke-test target):

    ```
    b = a + 5               -- position 0, deps = {}
    c = b * 2               -- position 1, deps = {0}
    d = c + 1               -- position 2, deps = {1}
    ret d
    ```

    The dep chain forces topological order `[0, 1, 2]`. Bisecting:
    positions `0, 1` → stage `0`; position `2` → stage `1`. II =
    `max 2 1 = 2`.

    Prologue: `[0, 1]` (issue stages 0 of iter 0 — i.e. `b` and `c`).
    Steady-state kernel: every position appears (issue stage 0 of iter
    `N+1` interleaved with stage 1 of iter `N` — i.e. `b'`, `c'`, and
    `d` from the previous iter).
    Epilogue: `[2]` (issue stage 1 of the last iter — i.e. `d`).

    With 2 iterations in flight, the pipelined cost per steady-state
    cycle is II = 2 vs the un-pipelined 3, a 1.5× speedup ceiling. -/
def chain3Body :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  -- pos 0: b = a + 5  (a is acc = .here; "5" simulated by acc+acc here,
  -- since we don't have const+var binexprs in this minimal setup).
  .var (binExprR64 .add .here .here)
    -- pos 1: c = b * 2  (b is .here after binding).
    (.var (binExprR64 .add .here .here)
      -- pos 2: d = c + 1  (c is .here after binding).
      (.var (binExprR64 .add .here .here)
        (.ret .here)))

def chain3Prog : JForProg (JasminTy.reg 64) :=
  { n := 4, update := chain3Body }

/-- The 3-element dep-chain produces a 3-element schedule, bisects to
    stages `[(0, 0), (1, 0), (2, 1)]`, and yields II = 2. -/
example : (analyzeSwp chain3Prog).order = [0, 1, 2] := rfl
example : (analyzeSwp chain3Prog).stages.entries = [(0, 0), (1, 0), (2, 1)] := rfl
example : (analyzeSwp chain3Prog).initiationInterval = 2 := rfl
example : (analyzeSwp chain3Prog).numStages = 2 := rfl

/-- The prologue contains stage-0 binders only: `[0, 1]`. -/
example : (analyzeSwp chain3Prog).prologue = [0, 1] := rfl

/-- The epilogue contains stage-1 binders only: `[2]`. -/
example : (analyzeSwp chain3Prog).epilogue = [2] := rfl

/-- The steady-state kernel contains every binder. -/
example : (analyzeSwp chain3Prog).kernel = [0, 1, 2] := rfl

/-- **4-binder ILP-exposing shape** (the headline shape from
    `InstructionSchedule`):

    ```
    v0 = acc + acc          -- pos 0, deps {}
    v1 = acc + acc          -- pos 1, deps {}
    v2 = v0 + v0            -- pos 2, deps {0}
    v3 = v1 + v1            -- pos 3, deps {1}
    ret v3
    ```

    `scheduleGreedy` produces topological order `[0, 1, 2, 3]`. `analyzeSwp`
    bisects: stages `0, 1` → stage `0`; stages `2, 3` → stage `1`.
    II = `max 2 2 = 2`. This is a balanced 2-stage pipeline — the
    expected speedup is `4 / 2 = 2×` (every kernel cycle issues 2
    binders concurrently from different iterations). -/
def ilpBody :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  -- pos 0: v0 = acc + acc.
  .var (binExprR64 .add .here .here)
    -- pos 1: v1 = acc + acc. After v0 is bound, acc is .there .here.
    (.var (binExprR64 .add (.there .here) (.there .here))
      -- pos 2: v2 = v0 + v0. v0 is .there .here.
      (.var (binExprR64 .add (.there .here) (.there .here))
        -- pos 3: v3 = v1 + v1. v1 is .there .here.
        (.var (binExprR64 .add (.there .here) (.there .here))
          (.ret .here))))

def ilpProg : JForProg (JasminTy.reg 64) :=
  { n := 1, update := ilpBody }

example : (analyzeSwp ilpProg).order = [0, 1, 2, 3] := rfl
example : (analyzeSwp ilpProg).stages.entries =
            [(0, 0), (1, 0), (2, 1), (3, 1)] := rfl
example : (analyzeSwp ilpProg).initiationInterval = 2 := rfl
example : (analyzeSwp ilpProg).prologue = [0, 1] := rfl
example : (analyzeSwp ilpProg).epilogue = [2, 3] := rfl

/-! ## 6. Agreement with `InstructionSchedule`

`analyzeSwp` runs `scheduleGreedy` (the `InstructionSchedule` scheduler), so
the pipelining decision is computed from the scheduled topological order. -/

/-- **`analyzeSwp`'s order is exactly `scheduleGreedy`'s.** A direct
    consequence of the definition, recording the scheduling / pipelining
    composition explicitly. -/
theorem analyzeSwp_order_eq_scheduleGreedy {accTy : JasminTy}
    (p : JForProg accTy) :
    (analyzeSwp p).order = scheduleGreedy (computeDependences p) :=
  rfl

/-- **`analyzeSchedule` and `analyzeSwp` agree on the emission order.**
    Both compute the same topological order via `scheduleGreedy`. -/
theorem analyzeSchedule_analyzeSwp_order_agree {accTy : JasminTy}
    (p : JForProg accTy) :
    (analyzeSchedule p).order = (analyzeSwp p).order :=
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR
