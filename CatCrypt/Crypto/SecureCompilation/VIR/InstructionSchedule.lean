/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation

/-!
# Dependence analysis and list scheduling for `JForProg` loop bodies

Instruction scheduling reorders data-independent instructions inside a
straight-line block to expose instruction-level parallelism. This module
computes the data dependences of a `JForProg` body and a topological emission
order of its binders. The `Com` rewrite that swaps adjacent independent
binders, with its denotation theorem, is `InstructionScheduleReal`.

## Dependences on `Com`

The dependence relation on a straight-line `Com` body is **purely
data-driven**: binder `i` depends on binder `j` (written `j ≺ i`) iff
some `Ctxt.Var` argument of `e_i` resolves to position `j`. There are no
aliasing concerns: `Com d Γ t` is single-static-assignment by construction
(every binder is fresh; binders are never overwritten), so we don't need
a kill set.

Two binders are **independent** iff neither depends on the other (in
either direction). On a straight-line block, independent binders may
be issued in either order without changing denotation. The scheduler
produces any *topological order* of the dependence DAG, and emits in
that order.

## Main results

* `computeDependences_empty_body`, `analyzeSchedule_empty_body`,
  `scheduleGreedy_empty`, `scheduleGreedy_empty_topological_sound` — the
  analysis on the empty body.

## Contents

* `Dependence` — the per-binder dependence record: `(pos, deps)` where
  `deps : List Nat` is the set of strictly-earlier binder positions
  that produce values consumed by `e_pos`.
* `computeDependences` — walk the body, extract each binder's
  dependence set from its expression's argument variables.
* `ScheduleDecisions` — the analysis result: a permutation of the
  binder positions in the chosen emission order.
* `scheduleGreedy` — a simple list-scheduler. Maintains a ready set
  (binders whose deps are all scheduled) and emits the
  smallest-numbered ready binder each step. This produces a stable
  topological order; on a body where every binder is independent, the
  output equals the input order.
* `analyzeSchedule` — top-level: compute dependences, run
  `scheduleGreedy`.
* Sanity examples on the empty body, a single-binder body and the
  4-binder ILP-exposing shape.

The schedule covers one straight-line body (one iteration), treats every
operation as unit-latency, and emits a flat instruction stream.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. Dependence extraction from a binder's expression

A binder at position `pos` sees the context `[v(pos-1), …, v0, acc]`.
The accumulator `acc` sits at *depth* `pos` (the deepest variable). A
variable of depth `d < pos` resolves to the binder at position
`pos - 1 - d`; a variable of depth `d ≥ pos` resolves to an input-context
slot (only `acc` exists in the singleton-context `JForProg` setting).

For scheduling, only **inter-binder dependences** matter: input-context
reads (`acc`) are available everywhere and impose no scheduling
constraint. The dependence set `deps : List Nat` for a binder at
position `pos` is exactly the set of strictly-earlier binder positions
whose values feed `e_pos`.
-/

/-- Extract the binder-position dependences from an `HVector` of argument
    variables at binder position `pos`. For each variable, if its depth
    `d < pos` (it resolves to a previously-bound binder), include the
    source position `pos - 1 - d`; otherwise (`d ≥ pos`, the accumulator
    or other input-context slot), skip it.

    Returns a deduplicated list in source-position order. -/
def collectArgDeps {Γ : Ctxt jasminDialect} (pos : Nat) :
    {tys : List jasminDialect.Ty} →
    HVector (fun ty => Ctxt.Var Γ ty) tys → List Nat
  | [], .nil => []
  | _ :: _, .cons v rest =>
      let d := RegisterAllocation.varDepth v
      let rest' := collectArgDeps pos rest
      if d < pos then
        let src := pos - 1 - d
        if rest'.contains src then rest' else src :: rest'
      else
        rest'

/-- The dependence set of a binder at position `pos` with expression `e`. -/
def exprDeps {Γ : Ctxt jasminDialect} {t : JasminTy}
    (pos : Nat) (e : Expr jasminDialect Γ t) : List Nat :=
  collectArgDeps pos e.args

/-- A single dependence record: `pos` is the binder's position; `deps`
    are the strictly-earlier binder positions consumed by `e_pos`. -/
structure Dependence where
  /-- This binder's position in the original left-to-right Com order. -/
  pos : Nat
  /-- Strictly-earlier binder positions that produce values consumed by
      this binder's expression. -/
  deps : List Nat
  deriving Repr

namespace Dependence

/-- A binder with no dependencies is *ready* from the start. -/
def isReady (d : Dependence) (scheduled : List Nat) : Bool :=
  d.deps.all (fun p => scheduled.contains p)

end Dependence

/-- Recursive worker for the dependence walker. Walks the body, emitting
    one `Dependence` per binder in left-to-right order. -/
def computeDependencesAux {Γ : Ctxt jasminDialect} {t : JasminTy}
    (pos : Nat) (acc : List Dependence) :
    Com jasminDialect Γ t → List Dependence
  | .ret _ => acc.reverse
  | .var e body =>
      let d : Dependence := { pos := pos, deps := exprDeps pos e }
      computeDependencesAux (pos + 1) (d :: acc) body

/-- **Dependence walker.** For each binder in the body, emit
    `(pos, deps)` where `deps` is the set of strictly-earlier binder
    positions consumed by `e_pos`. Output is in left-to-right binder
    order. -/
def computeDependences {accTy : JasminTy} (p : JForProg accTy) :
    List Dependence :=
  computeDependencesAux 0 [] p.update

/-! ## 2. The analysis result -/

/-- **An instruction-scheduling decision.**

`order` is the list of binder positions in the chosen emission order.
It is a permutation of `[0, …, numBinders - 1]` respecting the
dependence partial order (every binder's deps appear earlier in the
list).

We keep `order` as `List Nat` rather than `Vector Nat numBinders` to
make the analysis output structurally inspectable for the sanity tests
(matching the shape of `DceDecisions.deadPositions`,
`LicmDecisions.invariantPositions`, `CseDecisions.entries`). -/
structure ScheduleDecisions where
  /-- The emission order: a permutation of the binder positions
      respecting the data-dependence partial order. -/
  order : List Nat
  deriving Repr

namespace ScheduleDecisions

/-- The trivial schedule: empty order. -/
def empty : ScheduleDecisions where
  order := []

end ScheduleDecisions

/-! ## 3. The scheduler: greedy list-scheduling

We pick the smallest-numbered ready binder at each step. This is the
classical list-scheduling algorithm specialised to a unit-latency model.

`scheduleStep` examines the remaining (unscheduled) `Dependence`s; the
first one whose `deps` are all already in `scheduled` is removed and
returned. If none is ready (impossible on a valid acyclic DAG, but
defensive for robustness), we fall back to picking the
smallest-numbered remaining binder anyway.

The greedy choice is bias-stable: on a body where every binder is
independent of every other, the scheduler emits them in their
original (left-to-right) order. -/

/-- Find the first ready dependence in the list, returning
    `(picked, remaining)` if one exists, else `none`. -/
def findReady (scheduled : List Nat) :
    List Dependence → Option (Dependence × List Dependence)
  | [] => none
  | d :: rest =>
      if d.isReady scheduled then
        some (d, rest)
      else
        match findReady scheduled rest with
        | some (picked, remaining) => some (picked, d :: remaining)
        | none => none

/-- One step of the list scheduler: pick the smallest-numbered ready
    binder, append its position to the output, recurse on the rest.
    Falls back to the head if none is ready (defensive on malformed
    input). The `fuel` argument bounds recursion. -/
def scheduleStep (fuel : Nat) (scheduled : List Nat)
    (remaining : List Dependence) : List Nat :=
  match fuel with
  | 0 => scheduled.reverse
  | fuel + 1 =>
      match remaining with
      | [] => scheduled.reverse
      | _ =>
        match findReady scheduled remaining with
        | some (picked, rest) =>
            scheduleStep fuel (picked.pos :: scheduled) rest
        | none =>
            -- Defensive fallback: shouldn't happen on a valid DAG.
            -- Emit the head's position and continue.
            match remaining with
            | [] => scheduled.reverse
            | d :: rest => scheduleStep fuel (d.pos :: scheduled) rest

/-- **Greedy list scheduler.** Iterates `scheduleStep` until all
    dependences are placed. Fuel = length of the input list (one
    step removes exactly one entry). -/
def scheduleGreedy (deps : List Dependence) : List Nat :=
  scheduleStep deps.length [] deps

/-- **Schedule analysis.** Compute dependences for the body, then
    run the greedy list scheduler to produce an emission permutation. -/
def analyzeSchedule {accTy : JasminTy} (p : JForProg accTy) :
    ScheduleDecisions :=
  { order := scheduleGreedy (computeDependences p) }

/-! ## 4. Analysis correctness on small shapes

The natural correctness statement for `analyzeSchedule` is: the
produced order is a permutation of `[0, …, numBinders - 1]` respecting
the dependence partial order. We discharge *single-shape* instances
here — the trivial body `Com.ret v` has no binders, and a
single-binder body has a unique (singleton) schedule.

The full topological-soundness statement (every binder in `order` has
all its `deps` appearing earlier in `order`) is the operational
invariant maintained by `scheduleGreedy` by construction. Stating it
as a top-level theorem requires indexing into the body by binder
position, which the analysis walker already does. -/

/-- **Empty-body schedule is empty.** For a `JForProg` whose body is
    `Com.ret v` (no binders), `computeDependences` returns the empty
    list and `scheduleGreedy` produces the empty order. -/
theorem computeDependences_empty_body {accTy : JasminTy} (n : Nat)
    (v : Ctxt.Var (d := jasminDialect) [accTy] accTy) :
    computeDependences { n := n, update := Com.ret v } = [] :=
  rfl

/-- **Empty-body analysis returns the empty schedule.** -/
theorem analyzeSchedule_empty_body {accTy : JasminTy} (n : Nat)
    (v : Ctxt.Var (d := jasminDialect) [accTy] accTy) :
    (analyzeSchedule { n := n, update := Com.ret v }).order = [] :=
  rfl

/-- **`scheduleGreedy` on the empty input is the empty list.** -/
theorem scheduleGreedy_empty : scheduleGreedy [] = [] := rfl

/-- **Topological soundness, base case.** On the empty schedule, the
    vacuous condition "every entry's deps appear earlier" holds. -/
theorem scheduleGreedy_empty_topological_sound :
    ∀ pos ∈ (scheduleGreedy []),
      ∀ d ∈ ([] : List Dependence),
        d.pos = pos → ∀ dep ∈ d.deps,
          (scheduleGreedy []).contains dep := by
  intros pos hpos _ hd
  -- The schedule is empty, so the membership hypothesis `hpos` is false.
  simp [scheduleGreedy_empty] at hpos

/-! ## 5. Sanity tests

These confirm `analyzeSchedule` behaves correctly on small synthetic
body shapes — the smallest "is the analysis wired up?" smoke tests. -/

/-- The empty body has the empty schedule. -/
example {accTy : JasminTy} (v : Ctxt.Var (d := jasminDialect) [accTy] accTy) :
    (analyzeSchedule { n := 0, update := Com.ret v }).order = [] := rfl

-- The empty body's analysis is computable: `#eval` returns `[]`.
#eval (analyzeSchedule
        (accTy := .reg 64)
        { n := 0, update := Com.ret .here }).order

/-- A `regArith` binary `Expr` over `reg 64`, local helper for the sanity
    tests below. (Mirrors helpers in `DeadCodeElim.lean`,
    `CommonSubexprElim.lean`.) -/
def binExprR64IS {Γ : Ctxt jasminDialect} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg 64)) : Expr jasminDialect Γ (.reg 64) :=
  { op := .regArith op 64, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- A `regConst` nullary `Expr` over `reg 64`, local helper. -/
def constExprR64 {Γ : Ctxt jasminDialect} (k : Nat) :
    Expr jasminDialect Γ (.reg 64) :=
  { op := .regConst 64 k, retTy_eq := rfl, args := .nil }

/-- **Single-binder body**: one independent computation.

    ```
    v0 = acc + acc          -- position 0, deps = {} (only reads acc)
    ret v0
    ```

    The schedule is `[0]` (the only binder). -/
def singleBinderBody :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  .var (binExprR64IS .add .here .here)
    (.ret .here)

def singleBinderProg : JForProg (JasminTy.reg 64) :=
  { n := 1, update := singleBinderBody }

example : computeDependences singleBinderProg =
          [{ pos := 0, deps := [] }] := rfl

example : (analyzeSchedule singleBinderProg).order = [0] := rfl

/-- **Headline ILP-exposing shape**: four binders, two pairs of
    independent computations, then two dependent reductions.

    ```
    v0 = acc + acc          -- position 0, deps = {}     (a = x + y)
    v1 = acc + acc          -- position 1, deps = {}     (b = z * w)
    v2 = v0 + v0            -- position 2, deps = {0}    (c = a + 5)
    v3 = v1 + v1            -- position 3, deps = {1}    (d = b - 3)
    ret v3
    ```

    The greedy scheduler picks the smallest-numbered ready binder at
    each step. Initially `v0` and `v1` are both ready (no deps); the
    scheduler picks `v0` first. After `v0` is placed, `v2` becomes
    ready; `v1` is still ready. The scheduler picks `v1` (smaller
    position) → then `v2` → then `v3`. Final order: `[0, 1, 2, 3]`.

    The original order is already topologically sound here, but
    *importantly* the scheduler **never violates dependencies**, so
    this is the correct safe fallback. A latency-aware variant would
    prefer `[0, 1, 2, 3]` vs `[0, 2, 1, 3]` to maximise dual-issue. -/
def ilpExposingBody :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  -- Position 0: v0 = acc + acc. acc is .here.
  .var (binExprR64IS .add .here .here)
    -- Position 1: v1 = acc + acc. After v0 is bound, acc is .there .here.
    (.var (binExprR64IS .add (.there .here) (.there .here))
      -- Position 2: v2 = v0 + v0. v0 is .there .here (after v1's bind).
      (.var (binExprR64IS .add (.there .here) (.there .here))
        -- Position 3: v3 = v1 + v1. v1 is .there .here (after v2's bind).
        (.var (binExprR64IS .add (.there .here) (.there .here))
          -- ret v3 = .here.
          (.ret .here))))

def ilpExposingProg : JForProg (JasminTy.reg 64) :=
  { n := 1, update := ilpExposingBody }

/-- `ilpExposingBody` has four binders. -/
example : Com.numBinders ilpExposingBody = 4 := rfl

/-- The dependence walker correctly identifies each binder's deps.

    Note on indexing: at each position, the *innermost* `.there` chain
    points to the most-recently-bound binder. Specifically:
    * Position 1's `.there .here` (depth 1) at pos=1 → src = 1-1-1
      underflow → not a binder dep (resolves to acc).
    * Position 2's `.there .here` (depth 1) at pos=2 → src = 2-1-1 = 0.
    * Position 3's `.there .here` (depth 1) at pos=3 → src = 3-1-1 = 1.

    So position 1 has no binder deps (only reads acc), position 2
    depends on binder 0 (the most recent before v1), position 3
    depends on binder 1 (the most recent before v2). Wait — that means
    `v2 = v0 + v0` is actually wrong; let me re-check the indexing.

    Actually: the binder `v1` is at depth 0 (`.here`) immediately after
    its own binding; `v0` is at depth 1 (`.there .here`); `acc` is at
    depth 2 (`.there .there .here`). The expression for position 2
    uses `.there .here` which is depth 1 → src position 2-1-1 = 0 = v0.
    Correct: `v2 = v0 + v0`. Similarly v3 uses `.there .here` → depth 1
    at pos 3 → src 1 = v1. Correct: `v3 = v1 + v1`. -/
example : computeDependences ilpExposingProg =
          [{ pos := 0, deps := [] },
           { pos := 1, deps := [] },
           { pos := 2, deps := [0] },
           { pos := 3, deps := [1] }] := rfl

/-- The greedy scheduler produces a topologically sound order. The
    smallest-numbered ready binder is chosen at each step, yielding
    `[0, 1, 2, 3]` (which is the input order). On this body the
    scheduler is identity. -/
example : (analyzeSchedule ilpExposingProg).order = [0, 1, 2, 3] := rfl

end CatCrypt.Crypto.SecureCompilation.VIR
