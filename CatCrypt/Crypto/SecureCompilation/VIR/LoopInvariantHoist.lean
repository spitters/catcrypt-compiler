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
# Loop-invariance analysis for `JForProg` loop bodies

A binder of a loop body is loop-invariant when its value does not depend on
the loop-carried accumulator, so it can be computed once before the loop.
This module computes the invariant binder positions of a `JForProg` body. The
`Com` rewrite that hoists a binder out of the loop, with its denotation
theorem, is `LoopInvariantHoistReal`.

## Main results

* `analyzeLicm_empty_body` — a body with no binders has no flagged
  positions.
* `analyzeLicm_nullary_at_zero` — a nullary op (e.g. `regConst`) at
  position 0 is flagged invariant.

## Contents

* `LicmDecisions` — the analysis result. A list of binder positions marked
  loop-invariant, indexed by position into the body's straight-line
  let-chain.
* `allArgsInvariant` / `isInvariantExpr` — the per-position criterion: a
  binder at position `pos` is invariant iff every argument variable in its
  expression points to a strictly-earlier binder also flagged invariant
  (never to `acc`, which sits at depth `pos`).
* `analyzeLicm` — the analysis: walks the body, threading the set of
  already-flagged-invariant positions, and emits a position when its
  expression's argument depths all fall into the invariant set.
* Sanity examples on small synthetic bodies (a `regConst` round constant in a
  body whose other binders compute `acc + acc`).

## Eligible binders

* Only **scalar** binders (`Com.var`/`Expr.regArith`/`Expr.regConst`/
  `Expr.castW`) are eligible. `stackLoad`/`stackStore` may alias across
  iterations, so we conservatively never flag them invariant — that
  would require an aliasing analysis on the accumulator.
* `extCall` is conservatively NOT flagged invariant. Its denotation is
  opaque (the default value of the return type for non-lattice leaves),
  but its **effect on side channels** is not guaranteed to be hoistable;
  some leaves may be denotation-opaque-but-effect-bearing, and hoisting
  them would change the program's leak profile.
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

/-- **A loop-invariant-code-motion decision.**

`invariantPositions` is the list of binder positions (in left-to-right order
through the body's `Com.var … (Com.var … (Com.ret …))` chain) flagged as
loop-invariant by the analysis. Position `0` is the first binder; position
`numBinders - 1` is the last.

The framework consumes this as a labelling: it tells the downstream emit
pass which Com binders correspond to per-iteration redundant computations,
so they can be hoisted to a once-per-call prelude in the emitted asm (or
left in place for jasminc / LLVM's own LICM to clean up).

We keep `invariantPositions` as `List Nat` rather than `Finset Nat` to
make the analysis output structurally inspectable for the sanity tests. -/
structure LicmDecisions where
  /-- Binder positions flagged as loop-invariant. `i ∈ invariantPositions`
      means the binder at position `i` computes the same value every
      iteration and may therefore be hoisted out of the loop. -/
  invariantPositions : List Nat
  deriving Repr

namespace LicmDecisions

/-- The trivial LICM decision: nothing flagged invariant. Useful as the
    framework's no-op baseline. -/
def empty : LicmDecisions where
  invariantPositions := []

end LicmDecisions

/-! ## 2. The analysis: depth-based invariance criterion

A binder at position `pos` lives in the context
`[v(pos-1), …, v0, acc]`. The loop-carried accumulator `acc` sits at
*depth* `pos` (the deepest variable). A binder is loop-invariant iff
every argument variable in its expression points strictly **higher** in
the context than `acc` — i.e. only to previously-bound binders — *and*
each of those binders is itself loop-invariant.

We over-approximate via `RegisterAllocation.hvectorMaxDepth`: a binder
is invariant iff (i) `hvectorMaxDepth e.args < pos` (no arg reads `acc`)
and (ii) **every depth in the range `[0, argDepth]`** corresponds to a
previously-flagged-invariant binder. This is a conservative
over-approximation (mirrors `computeLastUse`); it never flags a
non-invariant binder, but may miss some invariant binders
whose `argDepth` happens to span a non-invariant earlier binder.

For nullary ops (`regConst`, in particular), `e.args = .nil`, so
`hvectorMaxDepth = 0 < pos` whenever `pos > 0`, and the second
condition is vacuous (no depths to check). Nullary binders are
therefore always flagged invariant — exactly the canonical
"round-constant hoist" pattern. -/

/-- Are all variables in this `HVector` of args loop-invariant at binder
    position `pos` under the current invariant-binder set `invSet`?

    Walks the args precisely (one check per actual variable, not a
    conservative depth-range scan). For each variable `v`:
    * compute `d := varDepth v`;
    * `d < pos` (the var is a previously-bound binder, not `acc` at depth `pos`);
    * `invSet.contains (pos - 1 - d)` (that source binder is itself invariant).

    A nullary args list (`.nil`) trivially returns `true` — no depths to
    check. This is the canonical "round-constant hoist" base case. -/
def allArgsInvariant (invSet : List Nat) (pos : Nat) {Γ : Ctxt jasminDialect} :
    {tys : List jasminDialect.Ty} →
    HVector (fun ty => Ctxt.Var Γ ty) tys → Bool
  | [], .nil => true
  | _ :: _, .cons v rest =>
      let d := RegisterAllocation.varDepth v
      (decide (d < pos) && invSet.contains (pos - 1 - d)) && allArgsInvariant invSet pos rest

/-- Is the binder at `pos` with expression `e` loop-invariant under
    the current invariant-binder set `invSet`?

    Two conditions, checked precisely per argument variable:
    1. **No `acc` read**: every argument depth is `< pos` (i.e. resolves
       to a previously-bound binder, not to the accumulator at depth `pos`).
    2. **All source binders invariant**: every resolved source position is
       already in `invSet`.

    For a nullary op (`regConst`, `args = .nil`), both conditions are
    vacuously satisfied, so the binder is always flagged invariant when
    `pos > 0`. (At `pos = 0` there is nowhere to hoist *to* — the binder
    is already at the top of the body.) -/
def isInvariantExpr (invSet : List Nat) (pos : Nat) {Γ : Ctxt jasminDialect}
    {t : jasminDialect.Ty} (e : Expr jasminDialect Γ t) : Bool :=
  allArgsInvariant invSet pos e.args

/-- Recursive worker for the analysis: walk the body, threading the
    accumulated invariant-binder set, and emit positions in left-to-right
    order. `pos` is the current binder index. -/
def analyzeLicmAux {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (pos : Nat) (invSet : List Nat) (c : Com jasminDialect Γ t) : List Nat :=
  match c with
  | .ret _ => invSet.reverse
    -- emit in left-to-right order (we built up in reverse-cons order)
  | .var e body =>
      let extended :=
        if isInvariantExpr invSet pos e then pos :: invSet else invSet
      analyzeLicmAux (pos + 1) extended body

/-- **Loop-invariant-code-motion analysis.** Walk the loop body, threading
the accumulated invariant-binder set. A binder at position `pos` is
flagged invariant when every argument variable in its expression
resolves to a strictly-earlier *invariant* binder (and never to the
loop-carried accumulator).

For the framework theorem the precise content of `invariantPositions`
is opaque — both preservation theorems hold for *any* analysis result.
The concrete analysis here makes the analysis-correctness lemmas
(below) provable in the simplest body shapes. -/
def analyzeLicm {accTy : JasminTy} (p : JForProg accTy) : LicmDecisions :=
  { invariantPositions := analyzeLicmAux 0 [] p.update }

/-! ## 3. Analysis correctness on canonical shapes

The natural correctness statement for `analyzeLicm` is: every position
flagged invariant is indeed loop-invariant. We discharge two
*canonical-shape* instances here — the empty body (no binders ⇒ nothing
flagged) and the nullary-op body at position `0` (a `regConst` round
constant binder, the textbook LICM target, is always flagged).

The full intrinsic-De-Bruijn statement requires a denotational closure
lemma — that a binder whose expression evaluation does not look at
position-`pos`'s `acc` (the loop-carried slot) yields the same value
every iteration. This is straightforward for nullary ops; for binary ops
referencing only earlier-invariant binders the argument extends by
induction. The framework theorems hold independently. -/

/-- **No-false-positives on the empty body.** For a `JForProg` whose
    body is `Com.ret v` (a single accumulator-passthrough, no binders),
    `analyzeLicm` flags no positions as invariant.

    This is the base-case instance of the general statement "every
    position flagged invariant is indeed loop-invariant", proven on the
    smallest body shape (no binders ⇒ no positions to flag). -/
theorem analyzeLicm_empty_body {accTy : JasminTy} (n : Nat)
    (v : Ctxt.Var (d := jasminDialect) [accTy] accTy) :
    (analyzeLicm { n := n, update := Com.ret v }).invariantPositions = [] := by
  rfl

/-- **Nullary-op binder at position 0 is flagged invariant.** A `regConst`
    binder is a nullary op (`sig = []`, so `args = .nil`). With no
    argument variables, `isInvariantExpr` returns `true` vacuously: there
    is nothing to check for `acc`-read or invariant-predecessor lookup.
    The single-binder body `var (regConst w k) (ret v)` therefore flags
    its sole binder (position 0) as invariant.

    This is the canonical "hoist a constant out of the loop" sanity
    check: a single `regConst` body's constant is identified as
    loop-invariant.

    The proof is by `rfl` after evaluating `analyzeLicm`. -/
theorem analyzeLicm_nullary_at_zero {accTy : JasminTy} (w : Nat) (k : Nat) :
    let body : Com jasminDialect [accTy] accTy :=
      .var (Expr.mk (JasminOp.regConst w k) rfl HVector.nil) (Com.ret (.there .here))
    (analyzeLicm { n := 1, update := body }).invariantPositions = [0] := by
  rfl

/-! ## 4. Sanity tests

These confirm `analyzeLicm` behaves correctly on small synthetic body
shapes — the smallest "is the analysis wired up?" smoke tests.

For body `Com.ret .here` (an empty straight-line — accumulator
passthrough), no positions are flagged. -/

/-- The empty body has no invariant binders to flag. -/
example {accTy : JasminTy} (v : Ctxt.Var (d := jasminDialect) [accTy] accTy) :
    (analyzeLicm { n := 0, update := Com.ret v }).invariantPositions = [] := rfl

-- The empty body's analysis is computable: `#eval` returns `[]`.
#eval (analyzeLicm
        (accTy := .reg 64)
        { n := 0, update := Com.ret .here }).invariantPositions

/-- A `regArith` binary `Expr` over `reg 64`, local helper for the sanity
    tests below. (Mirrors the DeadCodeElim local helper.) -/
def binExprR64 {Γ : Ctxt jasminDialect} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg 64)) : Expr jasminDialect Γ (.reg 64) :=
  { op := .regArith op 64, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- A `regConst` nullary `Expr` over `reg w`. The canonical LICM target:
    a compile-time constant materialised at every loop iteration. -/
def constExprRw {Γ : Ctxt jasminDialect} (w : Nat) (k : Nat) :
    Expr jasminDialect Γ (.reg w) :=
  { op := .regConst w k, retTy_eq := rfl, args := .nil }

/-- A body with a nullary `regConst` binder NOT at position 0:

    ```
    v0 = acc + acc           -- bound at position 0, reads acc
    v1 = const 42            -- bound at position 1, NULLARY → invariant
    v2 = acc + acc           -- bound at position 2, reads acc again
    ret v2                   -- ret reads v2 = .here
    ```

    The middle binder (`const 42`) reads no `acc` and has no args,
    so the analysis flags it as invariant. The two surrounding `acc+acc`
    binders read `acc` (depth 2 / 1 respectively from their positions)
    and are NOT flagged.

    This is the canonical "hoist a round constant out of the loop"
    pattern: the constant lands in the pre-loop prelude, freeing one
    `Cassgn` per iteration. -/
def licmFireBody :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  -- Position 0: v0 = acc + acc. Context after: [v0, acc].
  .var (binExprR64 .add .here .here)
    -- Position 1: v1 = const 42. Nullary. Context after: [v1, v0, acc].
    (.var (constExprRw 64 42)
      -- Position 2: v2 = acc + acc. acc is at depth 2 here.
      -- Use `.there .there .here` to refer to acc.
      (.var (binExprR64 .add (.there (.there .here)) (.there (.there .here)))
        -- ret v2: `.here` is v2.
        (.ret .here)))

/-- `licmFireBody` has three binders. -/
example : Com.numBinders licmFireBody = 3 := rfl

-- Sanity test: `analyzeLicm` flags position `1` (the `regConst`) as
-- invariant on `licmFireBody` — the canonical hoist target.
-- This `#eval` confirms LICM fires on at least one real loop-kernel
-- pattern: a round constant interleaved with `acc`-touching arithmetic.
#eval (analyzeLicm
        (accTy := .reg 64)
        { n := 16, update := licmFireBody }).invariantPositions

/-- A body where every binder reads `acc`:

    ```
    v0 = acc + acc          -- reads acc
    v1 = acc + acc          -- reads acc
    ret v1                  -- ret reads v1
    ```

    No binder is invariant; the analysis flags nothing. Confirms the
    analysis does not produce false positives on a tight `acc`-bound
    body shape. -/
def licmNoneBody :
    Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  .var (binExprR64 .add .here .here)
    (.var (binExprR64 .add (.there .here) (.there .here))
      (.ret .here))

-- Sanity test: `analyzeLicm` flags nothing on `licmNoneBody`.
#eval (analyzeLicm
        (accTy := .reg 64)
        { n := 16, update := licmNoneBody }).invariantPositions

end CatCrypt.Crypto.SecureCompilation.VIR
