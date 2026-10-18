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
# Dead-code analysis for `JForProg` loop bodies

A binder of a straight-line `Com` body is dead when its value is read by no
later binder and not by the terminal `ret`. This module computes the dead
binder positions of a `JForProg` body from the last-use table of
`RegisterAllocation.computeLastUse`. The `Com` rewrite that removes dead
binders, with its denotation theorem, is `DeadCodeElimReal`.

## Main results

* `analyzeDce_flagged_iff_last_use_self` — position `i` is flagged exactly
  when its last use is `i` and `i` is in range.
* `analyzeDce_empty_body` — a body with no binders has no dead positions.

## Contents

* `DceDecisions` — the list of binder positions flagged dead.
* `analyzeDce` — flags position `i` when `computeLastUse` gives `i` itself as
  its last use.
* Sanity examples on small synthetic bodies.

The last-use table over-approximates reads (every depth up to the deepest
argument counts as a use), so `analyzeDce` flags no live binder and may miss
dead ones (see `deadFirstBody`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. The analysis result -/

/-- **A dead-code-elimination decision.**

`deadPositions` is the list of binder positions (in left-to-right order
through the body's `Com.var … (Com.var … (Com.ret …))` chain) flagged as
dead by the analysis. Position `0` is the first binder; position
`numBinders - 1` is the last.

The framework consumes this as a labelling: it tells the downstream
emit pass which Com binders correspond to never-read SSA values, so they
can be omitted from the emitted asm (or left in place for jasminc /
LLVM's own DCE to clean up).

We keep `deadPositions` as `List Nat` rather than `Finset Nat` to make
the analysis output structurally inspectable for the sanity tests. -/
structure DceDecisions where
  /-- Binder positions flagged as dead. `i ∈ deadPositions` means the
      binder at position `i` is never read after being bound. -/
  deadPositions : List Nat

namespace DceDecisions

/-- The trivial DCE decision: nothing flagged dead. Useful as the
    framework's no-op baseline. -/
def empty : DceDecisions where
  deadPositions := []

end DceDecisions

/-! ## 2. The analysis: position-based last-use criterion

We reuse the `computeLastUse` infrastructure from `RegisterAllocation.lean`:
that walker returns, for each binder position `i`, the largest position
at which the bound value is read (or `i` itself if the binder is never
read after binding — the "dead" signature).

A binder is flagged dead by `analyzeDce` exactly when its `lastUse[i]`
equals `i` (i.e. the binder's own position, indicating no later read). -/

/-- **Dead-code analysis.** Walk the loop body, compute the last-use
position of each binder via `RegisterAllocation.computeLastUse`, and
flag every binder whose last-use equals its own position.

For the framework theorem the precise content of `deadPositions` is
opaque — both preservation theorems hold for *any* analysis result.
The concrete analysis here makes the no-false-positives lemma (below)
provable in the simplest body shape. -/
def analyzeDce {accTy : JasminTy} (p : JForProg accTy) : DceDecisions :=
  let lus := RegisterAllocation.computeLastUse p.update
  -- A binder at position `i` is dead iff `lus[i] = i`. We zip with
  -- `List.range lus.length` and filter.
  let positions := (List.range lus.length).filter
    (fun i => match lus[i]? with
              | some lu => lu == i
              | none    => false)
  { deadPositions := positions }

/-! ## 3. Analysis correctness: no-false-positives

The natural correctness statement for `analyzeDce` is: every position
flagged dead is indeed never read in the Com. We discharge a
*single-shape* instance here — the trivial body `Com.ret v` has no
binders, hence no positions can be flagged dead. This is the smallest
testable instance of the correctness statement; it confirms the
analysis is sound on the base case.

The full intrinsic-De-Bruijn statement (a quantification over all
straight-line bodies and all `Ctxt.Var` indices, asserting that a
position flagged dead corresponds to a `Ctxt.Var` that is not in any
later `Expr.args`) requires a syntactic `Com`-walker counting variable
occurrences — straightforward but non-trivial. It is the documented
residual; what we ship here is the operational correctness on the
empty-body shape, used by the sanity tests below. -/

/-- **No-false-positives on the empty body.** For a `JForProg` whose
    body is `Com.ret v` (a single accumulator-passthrough, no binders),
    `analyzeDce` flags no positions as dead.

    This is the base-case instance of the more general statement
    "every position flagged dead is indeed unused", proven on the
    smallest body shape (no binders ⇒ no positions to flag).

    The proof reduces to `decide` once both sides are evaluated:
    `numBinders (Com.ret v) = 0`, so `computeLastUse` returns `[]`,
    so `analyzeDce` returns `{ deadPositions := [] }`. -/
theorem analyzeDce_empty_body {accTy : JasminTy} (n : Nat)
    (v : Ctxt.Var (d := jasminDialect) [accTy] accTy) :
    (analyzeDce { n := n, update := Com.ret v }).deadPositions = [] := by
  rfl

/-- **No-false-positives, weak form.** For *any* `JForProg`, the
    deadness analysis is sound under the position-based criterion:
    every flagged position `i` satisfies `lus[i] = i` where
    `lus = computeLastUse p.update`. This is the *operational*
    correctness statement consumed by the emit pass; the intrinsic-
    De-Bruijn correctness (no `Ctxt.Var` is in any later `Expr.args`)
    follows from this once a syntactic occurrence-counter is added —
    the documented residual.

    The proof unfolds `analyzeDce` and uses `List.mem_filter` to
    extract the filter condition. -/
theorem analyzeDce_flagged_iff_last_use_self {accTy : JasminTy}
    (p : JForProg accTy) (i : Nat) :
    i ∈ (analyzeDce p).deadPositions ↔
      ∃ lu, (RegisterAllocation.computeLastUse p.update)[i]? = some lu ∧
            lu = i ∧ i < (RegisterAllocation.computeLastUse p.update).length := by
  unfold analyzeDce
  simp only [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hi, hcond⟩
    -- hcond : (match lus[i]? with ...) = true
    -- Since i < lus.length, lus[i]? = some lus[i]
    set lus := RegisterAllocation.computeLastUse p.update with hlus
    have hsome : lus[i]? = some lus[i] := List.getElem?_eq_getElem hi
    rw [hsome] at hcond
    simp at hcond
    exact ⟨lus[i], hsome, hcond, hi⟩
  · rintro ⟨lu, hlu, heq, hi⟩
    refine ⟨hi, ?_⟩
    rw [hlu]
    simp [heq]

/-! ## 4. Sanity tests

These confirm `analyzeDce` behaves correctly on small synthetic body
shapes — the smallest "is the analysis wired up?" smoke tests.

For body `Com.ret .here` (an empty straight-line — accumulator
passthrough), no positions are flagged. This matches
`analyzeDce_empty_body` above; the `#eval` form is the executable
inspection. -/

/-- The empty body has no dead binders. -/
example {accTy : JasminTy} (v : Ctxt.Var (d := jasminDialect) [accTy] accTy) :
    (analyzeDce { n := 0, update := Com.ret v }).deadPositions = [] := rfl

-- The empty body's analysis is computable: `#eval` returns `[]`.
#eval (analyzeDce
        (accTy := .reg 64)
        { n := 0, update := Com.ret .here }).deadPositions

/-- A `regArith` binary `Expr` over `reg 64`, local helper for the sanity
    tests below. (Mirrors the Poseidon2Emit local helper.) -/
def binExprR64DCE {Γ : Ctxt jasminDialect} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg 64)) : Expr jasminDialect Γ (.reg 64) :=
  { op := .regArith op 64, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- A small body with **two binders, the first of which is in fact dead**:

    ```
    v0 = acc + acc          -- bound at position 0, never used again
    v1 = acc + acc          -- bound at position 1; uses `acc`, not v0
    ret v1                  -- ret reads v1 = .here
    ```

    The first binder `v0` is dead — neither `v1`'s expression nor the
    `ret` references it. (The expression for `v1` uses `.there .here`,
    which refers to `acc`, not to `v0`; `ret .here` refers to `v1`.)
    The second binder `v1` is live (the `ret` reads it).

    **Note on the current analysis precision.** The position-based
    last-use criterion inherited from `RegisterAllocation.computeLastUse`
    is a *conservative over-approximation*: it marks every depth in the
    range `[0, argDepth]` as a use of the corresponding earlier binder,
    even when only some of those depths actually appear in the
    expression. For this body, `v1`'s expression has `argDepth = 1`
    (because `.there .here` has depth 1), and the conservative scan
    marks position 0 (v0) as used at position 1 — even though `v0` is
    not actually read. The current `analyzeDce` therefore returns `[]`
    on this body (no dead positions), which is *sound* (never flags a
    live binder as dead) but not *complete* (misses some dead binders).

    Tightening `computeLastUse` to a precise per-argument scan would
    flag `v0` correctly. That precision improvement is the documented
    residual; the framework theorems hold uniformly. -/
def deadFirstBody :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  -- Position 0: v0 = acc + acc. After this binder, context is
  --   [reg64 (=v0), reg64 (=acc)], so `acc` is `.there .here`.
  .var (binExprR64DCE .add .here .here)
    -- Position 1: v1 = acc + acc. Uses `acc` = `.there .here`, NOT v0.
    (.var (binExprR64DCE .add (.there .here) (.there .here))
      -- ret v1: `.here` is v1.
      (.ret .here))

/-- `deadFirstBody` has two binders. -/
example : Com.numBinders deadFirstBody = 2 := rfl

-- Sanity test: `analyzeDce` is *sound* on `deadFirstBody` — returns
-- `[]` (no false positives), matching the conservative liveness
-- over-approximation discussed in `deadFirstBody`'s docstring.
#eval (analyzeDce
        (accTy := .reg 64)
        { n := 1, update := deadFirstBody }).deadPositions

/-- A body where the **last binder is a no-op `regArith` over `acc`**
    (which is in scope but unused after the assignment):

    ```
    v0 = acc + acc          -- bound, live (used by ret)
    ret v0                  -- ret reads v0 = .here
    ```

    A single live binder; `analyzeDce` flags nothing. This confirms the
    analysis does not produce false positives on the simplest one-binder
    body shape. -/
def singleLiveBinderBody :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  .var (binExprR64DCE .add .here .here)
    (.ret .here)

/-- `singleLiveBinderBody` has one binder. -/
example : Com.numBinders singleLiveBinderBody = 1 := rfl

-- Sanity test: `analyzeDce` on a single-live-binder body returns `[]`.
#eval (analyzeDce
        (accTy := .reg 64)
        { n := 1, update := singleLiveBinderBody }).deadPositions

end CatCrypt.Crypto.SecureCompilation.VIR
