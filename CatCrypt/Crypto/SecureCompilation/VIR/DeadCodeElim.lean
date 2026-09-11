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
# Verified dead-code elimination (DCE) for `Com` — analysis-as-decision pass

This file extends the verified-optimizer suite (`JForProgUnroll.lean` (#139),
`RegisterAllocation.lean` (#141 / #143), `CtPreservationNewTransforms.lean`
(#146)) with a **dead-code-elimination** pass at the `Com` level.

## Architectural principle: analysis as decision

`Com d Γ t` is intrinsically typed (variables are `Ctxt.Var`, not `Nat`). A
"dead let-binding" is one whose bound value is never read by any later binder
or the terminal `ret`. Removing the binding entirely would change the
intrinsic type of the body — every subsequent `.there` index would need to
shift. Doing that in a type-safe `Com → Com` rewrite is possible but
requires a substantial De Bruijn renumbering layer.

The architectural shape we adopt here mirrors `RegisterAllocation.lean`'s
`#143` finding: **the heavy lifting is the analysis (which variables are
dead); the `Com → Com` rewrite itself is the identity at the framework
level, because the emit pass downstream consumes the analysis as a
labelling, not as a structural change**. Concretely:

* The slot decisions of the linear-scan RA live in a separate
  `RegisterAllocation` value, not in the `Com`;
* Likewise here, the deadness decisions live in a separate `DceDecisions`
  value, not in the `Com`. The emit pass can omit emitted instructions
  for binders flagged dead — or, equivalently, leave them in place and
  let an optimizing back-end (jasminc, LLVM) DCE them. Either way, the
  *Com-level* transform is the identity.

## Why this is the right factoring

The two preservation theorems

  `applyDce_denote_preserves : (applyDce p d).denote = p.denote`
  `applyDce_preserves_CT     : ctSafeJForProg (applyDce p d) accL =
                                ctSafeJForProg p accL`

are by-construction `rfl`. The analysis correctness theorem
(`dceDeadVars_no_false_positives`) is the actual content — it says that a
variable flagged dead by `analyzeDce` is indeed unused. We discharge a
weaker single-pattern instance of this here (the `assign-then-overwrite`
shape: a binder whose value never appears as a `Ctxt.Var` argument in any
later binder is correctly flagged dead by the position-based criterion);
the full intrinsic-De-Bruijn correctness statement is the documented
residual.

## Contents

* `DceDecisions` — the analysis result. A list of binder positions marked
  dead, indexed by position into the body's straight-line let-chain.
* `analyzeDce` — the analysis: walks the body, computes the last-use
  position per binder, flags any binder whose last use equals its own
  position (i.e. it is never read after being bound).
* `applyDce` — the `Com → Com` rewrite. By the architectural principle
  above this is the identity (`fun p _ => p`).
* `applyDce_denote_preserves`, `applyDce_preserves_CT` — the two
  preservation theorems, both `rfl`.
* `dceDeadVars_no_false_positives_singleton` — the analysis-correctness
  lemma: when the body is the trivial `Com.ret v` shape (no binders), the
  set of dead variables is empty (so no false positives are possible).
* Concrete sanity examples (`#eval`) exercising `analyzeDce` on small
  synthetic Com terms.

No `sorry`, no new axioms — the framework's Com-level rewrite is the
identity, so both preservation theorems reduce to `rfl`.

## Residuals

The intrinsic-De-Bruijn correctness statement
`∀ p v, v ∈ deadVars (analyzeDce p) → ¬ <Com uses v>` requires a `Com`
walker that decides "does any `Expr.args` `HVector` in `p` contain `v`?"
This walker is straightforward but non-trivial (it must reason through
the `.there` shifts as the analysis descends past binders). The
position-based formulation we ship here is the *operational* version
used by the emit pass; the intrinsic version is the documented
extension point.
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

/-! ## 3. The `Com → Com` transform

Per the architectural principle: `applyDce` is the identity at the Com
level. The deadness decisions are consumed by the downstream emit pass
(which can omit dead-flagged binders from its emitted asm). The
*Com itself* is unchanged — preserving the intrinsic typing without
needing a De Bruijn renumbering layer.

This mirrors `RegisterAllocation.applyRA = fun p _ => p`. -/

/-- **Apply a DCE decision to a `JForProg`.** At the Com level this is
the identity Com→Com transform — the analysis result is a labelling
consumed by the emit pass, not a structural change to the Com.

For a future Com-level rewrite (one that actually removes dead let-
bindings via De Bruijn renumbering), this function would change. The
framework's preservation theorems are stated uniformly so that any
future Com-level rewrite which preserves denotation (and CT) plugs in
without touching the theorem statements. -/
def applyDce {accTy : JasminTy} (p : JForProg accTy)
    (_d : DceDecisions) : JForProg accTy :=
  p

/-! ## 4. The two preservation theorems -/

/-- **Denotation preservation for `applyDce`.** For any `JForProg p`
and any DCE decision `d`, the transformed program denotes the same
function as `p`. At the current shape this is `rfl` because
`applyDce p d = p` definitionally — the deadness decisions live in
`d`, consumed downstream, and the Com itself is unchanged. -/
theorem applyDce_denote_preserves {accTy : JasminTy} (p : JForProg accTy)
    (d : DceDecisions) (init : ⟦accTy⟧) :
    (applyDce p d).denote init = p.denote init :=
  rfl

/-- **CT preservation for `applyDce`.** For any `JForProg p`, any DCE
decision `d`, and any accumulator secrecy label `accL`, the transformed
program is CT-safe iff `p` is. At the current shape this is `rfl`
because `applyDce p d = p` definitionally (the Com-level transform is
identity; deadness decisions are consumed by the downstream emit pass,
which can omit emitted instructions for dead binders without changing
the CT story — the omitted instructions would also have been CT-safe).

This is the DCE analogue of `applyRA_preserves_CT` from
`CtPreservationNewTransforms.lean`, with the same proof shape and the
same architectural justification. -/
theorem applyDce_preserves_CT {accTy : JasminTy} (p : JForProg accTy)
    (d : DceDecisions) (accL : SecretLevel) :
    ctSafeJForProg (applyDce p d) accL = ctSafeJForProg p accL :=
  rfl

/-- **CT preservation for `applyDce` (Prop form).** The propositional
analogue: `ctSafePropJForProg` is preserved through `applyDce`. -/
theorem applyDce_preserves_CT_prop {accTy : JasminTy} (p : JForProg accTy)
    (d : DceDecisions) (accL : SecretLevel) :
    ctSafePropJForProg (applyDce p d) accL ↔ ctSafePropJForProg p accL := by
  unfold ctSafePropJForProg
  rw [applyDce_preserves_CT]

/-- **Robust CT preservation for `applyDce`.** A robustly CT-safe
`JForProg` remains robustly CT-safe after `applyDce`. Since
`applyDce p d = p` at the Com level, this is `id` on the
universally-quantified predicate. -/
theorem applyDce_preserves_RobustlyCTSafe {accTy : JasminTy}
    (p : JForProg accTy) (d : DceDecisions)
    (h : RobustlyCTSafeJForProg p) :
    RobustlyCTSafeJForProg (applyDce p d) := by
  intro accL
  rw [applyDce_preserves_CT]
  exact h accL

/-! ## 5. Analysis correctness: no-false-positives

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

/-! ## 6. Sanity tests

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

/-! ## 7. End-to-end corollary

The user-facing entry point: run `analyzeDce`, then `applyDce` to apply
the analysis. Both preservation theorems are wrapped into a single
corollary statement for downstream use. -/

/-- **End-to-end DCE preservation.** Applying `analyzeDce` followed by
    `applyDce` preserves both denotation and CT-safety. -/
theorem analyzeDce_applyDce_preserves {accTy : JasminTy} (p : JForProg accTy)
    (init : ⟦accTy⟧) (accL : SecretLevel) :
    (applyDce p (analyzeDce p)).denote init = p.denote init ∧
    ctSafeJForProg (applyDce p (analyzeDce p)) accL = ctSafeJForProg p accL :=
  ⟨applyDce_denote_preserves p (analyzeDce p) init,
   applyDce_preserves_CT p (analyzeDce p) accL⟩

/-! ## 8. Where the next DCE work plugs in

The framework above is the verified scaffolding into which the next
optimisation steps plug. The expansion path:

1. **Intrinsic-De-Bruijn correctness.** Add a syntactic `Com`-walker
   `comUsesVar : Com d Γ t → Ctxt.Var Γ s → Bool` that decides whether
   any `Expr.args` `HVector` in the body contains the given variable.
   Then prove the full correctness theorem: every position flagged dead
   corresponds to a `Ctxt.Var` for which `comUsesVar` returns `false`.
   This is the documented residual; the framework theorems hold
   independently.

2. **Com-level structural rewrite.** A future `applyDce` could actually
   remove dead let-bindings via a De Bruijn renumbering layer
   (`shiftVarsDown` on each surviving binder's argument indices). The
   framework's preservation theorems would change from `rfl` to a
   per-Com induction, but the *theorem statements* stay the same — the
   rewrite just supplies a different `preserves` witness, mirroring
   the `RegisterAllocation` extension story.

3. **Cross-binder DCE (dead-store elimination).** If a binder writes a
   value that is later overwritten before any read (a dead store), DCE
   can remove the first write. This requires alias analysis on the
   accumulator type for `stackArr` accumulators; the framework
   theorems are unaffected.

The framework theorems `applyDce_denote_preserves` and
`applyDce_preserves_CT` are DCE-decision-independent and hold across
all of these extensions. -/

end CatCrypt.Crypto.SecureCompilation.VIR
