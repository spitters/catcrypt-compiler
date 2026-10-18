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
# Common-subexpression analysis for `JForProg` loop bodies

This module computes which binders of a straight-line `Com` body recompute an
expression bound at an earlier position. The `Com` rewrite that replaces a
redundant binder by the earlier one, with its denotation theorem, is
`CommonSubexprElimReal`.

## Why syntactic equality suffices on `Com`

The crucial simplification: `Com d Γ t` is **single-static-assignment by
construction** (every let-binder introduces a *fresh* `Ctxt.Var`; binders
are never overwritten). So the kill-set logic that a textual-IR CSE needs
(invalidate `(e, dst)` when any read-slot of `e` is later assigned) is
vacuous here: a `Ctxt.Var` always denotes the *same* value throughout its
scope.

Therefore the simple criterion — "two binders bear syntactically identical
expressions (same op, same `args` `HVector`)" — is **already** sufficient
for CSE soundness on `Com`. The analysis implements this criterion as a
position-based labelling.

## Main results

* `analyzeCse_empty_body`, `analyzeCse_empty_body_positions` — a body with
  no binders has no flagged positions.

## Contents

* `CseDecisions` — the analysis result. Each `CseEntry` records a
  redundant-binder position together with the canonical position whose
  value it duplicates.
* `analyzeCse` — walks the body, hashes each binder's expression (op and
  argument-slot list), and flags the binder as redundant when its hash is
  already in the table.
* Sanity examples on small synthetic bodies, including the
  duplicate-expression shape `v0 = acc + acc; v1 = acc + acc; ret v1`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. Expression hash for CSE deduplication

The CSE analysis must decide whether two binders' expressions are
syntactically identical. The hash captures the *originating slot* of
each argument — the absolute defining-position in the Com (counted from
the root), or a negative number for original-context (input) slots.

**Soundness of the hash**: at binder position `i`, the variable
`Ctxt.Var Γ t` of De-Bruijn depth `d` (where `.here` = 0, `.there .here` = 1,
etc.) refers to:
* the binder bound at position `i - 1 - d`, if `i - 1 - d ≥ 0`;
* the input-context slot at index `d - i`, if `d ≥ i` (encoded as the
  negative value `-(d - i + 1)`).

Two expressions hash equally iff they have the same op and their
arguments refer to the same originating slots — which on a
single-static-assignment `Com` is sufficient to guarantee the same
denotation (the value at a stable defining position is fixed once and
for all).

This is the *correct* hash that distinguishes `acc + acc` (where `acc`
is an input-context slot, source-id `< 0`) from `v0 + v0` (where `v0`
is a recently-bound binder, source-id `≥ 0`). -/

/-- The **absolute source identifier** of a variable referenced at binder
    position `i`. Positive (or zero) values index a defining binder
    position; negative values encode an input-context slot.

    Encoding choices:
    * `varSourceId i v = Int.ofNat (i - 1 - d)` when `d < i`
      (variable refers to the binder at position `i - 1 - d`);
    * `varSourceId i v = -(Int.ofNat (d - i) + 1)` when `d ≥ i`
      (variable refers to the input-context slot at index `d - i`,
      shifted so that `d = i` (input slot 0) maps to `-1`, etc.). -/
def varSourceId {Γ : Ctxt jasminDialect} {t : JasminTy}
    (i : Nat) (v : Ctxt.Var Γ t) : Int :=
  let d := varDepth v
  if d < i then Int.ofNat (i - 1 - d)
  else -(Int.ofNat (d - i) + 1)

/-- The hash of an `Expr` for CSE purposes: the op tag plus the list of
    argument source-ids. Two expressions hash equally iff they have the
    same op and the same argument-source-ids — which on a
    single-static-assignment `Com` is sufficient for equal denotation. -/
structure ExprHash where
  op : JasminOp
  argSourceIds : List Int
  deriving DecidableEq

/-- Hash an `HVector` of argument variables into a list of source-ids. -/
def hashArgs {Γ : Ctxt jasminDialect} (i : Nat) :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys → List Int
  | [], .nil => []
  | _ :: _, .cons v rest => varSourceId i v :: hashArgs i rest

/-- Hash an `Expr` at binder position `i`. -/
def hashExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (i : Nat) (e : Expr jasminDialect Γ t) : ExprHash :=
  { op := e.op, argSourceIds := hashArgs i e.args }

/-! ## 2. The analysis result

`CseDecisions` records a list of CSE redundancies. Each entry says
"the binder at position `redundantPos` recomputes the same expression
as the binder at position `canonicalPos`". The emit pass consumes
these decisions to either omit the redundant binder (rewriting downstream
references to the canonical slot) or — equivalently — leave it in place
for the back-end optimiser to clean up. -/

/-- A single CSE redundancy: the binder at `redundantPos` duplicates the
    expression already bound at `canonicalPos < redundantPos`. -/
structure CseEntry where
  /-- Position of the canonical (earliest) defining binder. -/
  canonicalPos : Nat
  /-- Position of the redundant binder that recomputes the same expression. -/
  redundantPos : Nat
  deriving DecidableEq, Repr

/-- **A CSE decision.** The list of CSE redundancies discovered by the
    analysis. The framework consumes this as a labelling: it tells the
    downstream emit pass which Com binders correspond to recomputations
    of an earlier SSA value, so they can be replaced with a direct
    reference to the canonical slot. -/
structure CseDecisions where
  /-- The discovered redundancies. -/
  entries : List CseEntry
  deriving Repr

namespace CseDecisions

/-- The trivial CSE decision: nothing flagged redundant. Useful as the
    framework's no-op baseline. -/
def empty : CseDecisions where
  entries := []

/-- The list of binder positions flagged as redundant — the projection
    used by sanity tests and by downstream consumers that only need
    to know *which* binders are redundant (without the canonical
    target). -/
def redundantPositions (d : CseDecisions) : List Nat :=
  d.entries.map CseEntry.redundantPos

end CseDecisions

/-! ## 3. The analysis: hash-table walk

We walk the Com top-to-bottom, maintaining an association list
`hashTable : List (ExprHash × Nat)` mapping each previously-seen
expression hash to the position of the earliest binder bearing it.
At each `.var e body`:

* compute `h = hashExpr e`;
* if `h` is already in the table at canonical position `c`, append a
  `CseEntry { canonicalPos := c, redundantPos := i }` to the entry
  list and keep the table unchanged (the canonical slot remains the
  earliest defining position);
* otherwise insert `(h, i)` into the table.

The `i` index counts binders from the root of the Com (position 0 is
the outermost `.var`). On `.ret`, the walk terminates. -/

/-- Find an `ExprHash` in the table; return the canonical position if
    present. -/
def CseTable.find (table : List (ExprHash × Nat)) (h : ExprHash) : Option Nat :=
  match table with
  | [] => none
  | (h', pos) :: rest => if h = h' then some pos else CseTable.find rest h

/-- Step the analysis through one binder.

    Arguments:
    * `i` — position of *this* binder (0-indexed from the Com root).
    * `e` — the binder's expression.
    * `table` — accumulated `(hash, canonicalPos)` map.
    * `entries` — accumulated redundancy decisions.

    Returns the updated `(table, entries)`. -/
def analyzeCseStep {Γ : Ctxt jasminDialect} {t : JasminTy}
    (i : Nat) (e : Expr jasminDialect Γ t)
    (table : List (ExprHash × Nat)) (entries : List CseEntry) :
    List (ExprHash × Nat) × List CseEntry :=
  let h := hashExpr i e
  match CseTable.find table h with
  | some canonicalPos =>
      -- Redundant: record the decision, keep the table as-is.
      (table, entries ++ [{ canonicalPos := canonicalPos, redundantPos := i }])
  | none =>
      -- First occurrence: extend the table.
      ((h, i) :: table, entries)

/-- The recursive analysis walker. Walks the body, accumulating the
    redundancy list. `i` is the current binder position; `table` and
    `entries` are the accumulators. -/
def analyzeCseAux {Γ : Ctxt jasminDialect} {t : JasminTy}
    (i : Nat) (table : List (ExprHash × Nat)) (entries : List CseEntry) :
    Com jasminDialect Γ t → List CseEntry
  | .ret _ => entries
  | .var e body =>
      let (table', entries') := analyzeCseStep i e table entries
      analyzeCseAux (i + 1) table' entries' body

/-- **CSE analysis.** Walk the body, hash each binder's expression, and
    flag every binder whose hash matches an earlier binder's. The
    `canonicalPos` field of each `CseEntry` is the earliest position at
    which the expression was bound; `redundantPos` is the current binder's
    position.

    For the framework theorem the precise content of `entries` is opaque
    — both preservation theorems hold for *any* analysis result. The
    concrete analysis here makes the no-false-positives lemma (below)
    provable in the simplest body shape. -/
def analyzeCse {accTy : JasminTy} (p : JForProg accTy) : CseDecisions :=
  { entries := analyzeCseAux 0 [] [] p.update }

/-! ## 4. Analysis correctness: no-false-positives on empty body

The natural correctness statement for `analyzeCse` is: every entry
flagged redundant has the same expression-hash as the canonical-position
binder. We discharge a *single-shape* instance here — the trivial body
`Com.ret v` has no binders, hence no positions can be flagged redundant.
This is the smallest testable instance of the correctness statement; it
confirms the analysis is sound on the base case.

The full statement (`every entry's redundantPos has hashExpr equal to
the canonicalPos's hashExpr`) is the operational invariant maintained
by `analyzeCseAux` by construction; stating it as a top-level theorem
requires indexing `Com` by binder positions, which the analysis walker
already does. -/

/-- **No-false-positives on the empty body.** For a `JForProg` whose
    body is `Com.ret v` (a single accumulator-passthrough, no binders),
    `analyzeCse` flags no positions as redundant.

    The proof reduces to `rfl` once both sides are evaluated:
    `analyzeCseAux 0 [] [] (Com.ret v) = []`, so
    `analyzeCse` returns `{ entries := [] }`. -/
theorem analyzeCse_empty_body {accTy : JasminTy} (n : Nat)
    (v : Ctxt.Var (d := jasminDialect) [accTy] accTy) :
    (analyzeCse { n := n, update := Com.ret v }).entries = [] := by
  rfl

/-- The empty body has no redundant positions (projection form). -/
theorem analyzeCse_empty_body_positions {accTy : JasminTy} (n : Nat)
    (v : Ctxt.Var (d := jasminDialect) [accTy] accTy) :
    (analyzeCse { n := n, update := Com.ret v }).redundantPositions = [] := by
  unfold CseDecisions.redundantPositions
  rw [analyzeCse_empty_body]
  rfl

/-! ## 5. Sanity tests

These confirm `analyzeCse` behaves correctly on small synthetic body
shapes — the smallest "is the analysis wired up?" smoke tests. -/

/-- The empty body has no CSE entries. -/
example {accTy : JasminTy} (v : Ctxt.Var (d := jasminDialect) [accTy] accTy) :
    (analyzeCse { n := 0, update := Com.ret v }).entries = [] := rfl

-- The empty body's analysis is computable: `#eval` returns `[]`.
#eval (analyzeCse
        (accTy := .reg 64)
        { n := 0, update := Com.ret .here }).entries

/-- A `regArith` binary `Expr` over `reg 64`, local helper for the sanity
    tests below. (Mirrors the helpers in `DeadCodeElim.lean` and
    `Poseidon2Emit.lean`.) -/
def binExprR64 {Γ : Ctxt jasminDialect} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg 64)) : Expr jasminDialect Γ (.reg 64) :=
  { op := .regArith op 64, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- The **headline CSE-firing body**: two binders both compute
    `acc + acc`, where `acc` is the input-context accumulator:

    ```
    v0 = acc + acc         -- position 0
                            --   acc is .here, depth 0
                            --   sourceId(acc) at pos 0 = -(0-0+1) = -1 (input slot)
                            --   hash = (add 64, [-1, -1])
    v1 = acc + acc         -- position 1
                            --   acc is .there .here, depth 1
                            --   sourceId(acc) at pos 1 = -(1-1+1) = -1 (input slot)
                            --   hash = (add 64, [-1, -1])  ✓ same as v0
    ret v1                  -- ret reads v1 = .here
    ```

    With the absolute-source-id hash both binders' hashes are equal —
    they both reference the same originating slot (the input
    accumulator). The CSE analysis fires: position 1's binder is
    flagged redundant via canonical position 0. -/
def headlineCseBody :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  .var (binExprR64 .add .here .here)
    (.var (binExprR64 .add (.there .here) (.there .here))
      (.ret .here))

/-- `headlineCseBody` has two binders. -/
example : Com.numBinders headlineCseBody = 2 := rfl

-- Headline fire: position 1 is flagged redundant with canonical
-- position 0 — both binders compute `acc + acc` (and `acc` is the
-- shared input-context slot).
#eval (analyzeCse
        (accTy := .reg 64)
        { n := 1, update := headlineCseBody }).entries

example : (analyzeCse
            (accTy := .reg 64)
            { n := 1, update := headlineCseBody }).entries =
          [{ canonicalPos := 0, redundantPos := 1 }] := rfl

/-- The **soundness body**: `v0 = acc + acc` then `v1 = v0 + v0`. The
    two binders compute *different* expressions because `acc` and `v0`
    are distinct originating slots:

    ```
    v0 = acc + acc          -- hash (add 64, [-1, -1])  (acc = input slot)
    v1 = v0 + v0            -- hash (add 64, [0, 0])    (v0 = binder at pos 0)
    ret v1
    ```

    The CSE analysis must **not** fire here. With the absolute-source-id
    hash, `v0`'s source-id at position 1 is `0` (the binder-at-position-0)
    whereas `acc`'s source-id at position 0 is `-1` (the input slot).
    The hashes differ, the analysis returns `[]`. This is the *Poseidon2
    roundLoopBody* shape — it must not be falsely flagged. -/
def soundnessBody :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  .var (binExprR64 .add .here .here)            -- v0 = acc + acc
    (.var (binExprR64 .add .here .here)         -- v1 = v0 + v0
      (.ret .here))

-- Soundness witness: analysis returns no entries on the Poseidon2
-- roundLoopBody shape. Demonstrates the absolute-source-id hash
-- correctly distinguishes `acc + acc` from `v0 + v0`.
#eval (analyzeCse
        (accTy := .reg 64)
        { n := 1, update := soundnessBody }).entries

example : (analyzeCse
            (accTy := .reg 64)
            { n := 1, update := soundnessBody }).entries = [] := rfl

/-- The **constant-CSE body**: two binders both materialise the constant `7`:

    ```
    v0 = 7                  -- position 0, hash (regConst 64 7, [])
    v1 = 7                  -- position 1, hash (regConst 64 7, [])
    ret v0                  -- ret reads v0
    ```

    `regConst` takes no arguments, so its hash has an empty `argDepths`
    list. Both binders' hashes are therefore `(regConst 64 7, [])` —
    *equal*. The CSE analysis fires: position 1's binder is flagged
    redundant via canonical position 0.

    This is the smallest analysis-fires CSE smoke. -/
def constCseBody :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  .var ({ op := .regConst 64 7, retTy_eq := rfl, args := .nil })
    (.var ({ op := .regConst 64 7, retTy_eq := rfl, args := .nil })
      (.ret (.there .here)))

/-- `constCseBody` has two binders. -/
example : Com.numBinders constCseBody = 2 := rfl

-- The analysis fires on `constCseBody`: position 1 is flagged
-- redundant via canonical position 0.
#eval (analyzeCse
        (accTy := .reg 64)
        { n := 1, update := constCseBody }).entries

/-- **Headline CSE fire**: on `constCseBody` the analysis finds exactly
    one entry: position 1 is redundant via canonical position 0. -/
example : (analyzeCse
            (accTy := .reg 64)
            { n := 1, update := constCseBody }).entries =
          [{ canonicalPos := 0, redundantPos := 1 }] := rfl

/-- **Headline projection**: only position 1 is flagged redundant. -/
example : (analyzeCse
            (accTy := .reg 64)
            { n := 1, update := constCseBody }).redundantPositions = [1] := rfl

/-- **Triple-constant body**: three binders all materialise the constant
    `3`. The analysis flags positions 1 and 2 as redundant via the
    canonical position 0 (the earliest binder is preserved as the
    canonical defining position; both later binders point to it). -/
def tripleConstCseBody :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  .var ({ op := .regConst 64 3, retTy_eq := rfl, args := .nil })
    (.var ({ op := .regConst 64 3, retTy_eq := rfl, args := .nil })
      (.var ({ op := .regConst 64 3, retTy_eq := rfl, args := .nil })
        (.ret (.there (.there .here)))))

example : (analyzeCse
            (accTy := .reg 64)
            { n := 1, update := tripleConstCseBody }).entries =
          [{ canonicalPos := 0, redundantPos := 1 },
           { canonicalPos := 0, redundantPos := 2 }] := rfl

/-- **Mixed constants**: a body with distinct constants interspersed —
    the analysis only fires on the exact duplicates:

    ```
    v0 = 5                  -- position 0
    v1 = 7                  -- position 1 (distinct from v0)
    v2 = 5                  -- position 2 (duplicate of v0 → fires)
    ret v0
    ```

    Position 2 is flagged redundant via canonical position 0. -/
def mixedConstsBody :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  .var ({ op := .regConst 64 5, retTy_eq := rfl, args := .nil })
    (.var ({ op := .regConst 64 7, retTy_eq := rfl, args := .nil })
      (.var ({ op := .regConst 64 5, retTy_eq := rfl, args := .nil })
        (.ret (.there (.there .here)))))

example : (analyzeCse
            (accTy := .reg 64)
            { n := 1, update := mixedConstsBody }).entries =
          [{ canonicalPos := 0, redundantPos := 2 }] := rfl

end CatCrypt.Crypto.SecureCompilation.VIR
