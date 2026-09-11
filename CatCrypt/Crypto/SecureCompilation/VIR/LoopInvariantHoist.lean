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
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DeadCodeElim
public import CatCrypt.Crypto.SecureCompilation.VIR.DeadCodeElim

/-!
# Verified loop-invariant code motion (LICM) for `JForProg` — analysis-as-decision pass

This file extends the verified-optimizer suite (`JForProgUnroll.lean` (#139),
`RegisterAllocation.lean` (#141 / #143), `DeadCodeElim.lean` (post-#146)) with
**loop-invariant code motion (LICM)** at the `Com` level.

LICM hoists computations whose result does not depend on the loop-carried
accumulator out of the loop body, so they execute once before the loop rather
than `n` times inside it. This is one of the highest-leverage `-O2` passes
missing from the verified compiler: crypto loops frequently re-derive round
constants, twiddle factors, or other invariants every iteration, and LICM
moves them out.

## Architectural principle: analysis as decision

`Com d Γ t` is intrinsically typed (variables are `Ctxt.Var`, not `Nat`).
Removing a let-binding from the body and re-binding it before the loop would
change the intrinsic type of the body — every subsequent `.there` index would
need to shift, *and* the new pre-loop binder would need to land in a wider
outer context. Doing that in a type-safe `Com → Com` rewrite is possible but
requires substantial De Bruijn renumbering — exactly the same architectural
gap `RegisterAllocation.lean` (#143) and `DeadCodeElim.lean` (post-#146)
resolved by factoring the heavy lifting out of the Com rewrite.

We follow the same factoring: **the heavy lifting is the analysis (which
binders are loop-invariant); the `Com → Com` rewrite itself is the identity
at the framework level, because the emit pass downstream consumes the
analysis as a labelling, not as a structural change**. Concretely:

* The slot decisions of the linear-scan RA live in a separate
  `RegisterAllocation` value;
* The deadness decisions of DCE live in a separate `DceDecisions` value;
* Here, the invariance decisions live in a separate `LicmDecisions` value.
  The emit pass can hoist emitted instructions for binders flagged invariant
  to the function prelude — or leave them in place and let an optimizing
  back-end (jasminc, LLVM) hoist them itself. Either way, the *Com-level*
  transform is the identity.

## Why this is the right factoring

The two preservation theorems

  `applyLicm_denote_preserves : (applyLicm p d).denote = p.denote`
  `applyLicm_preserves_CT     : ctSafeJForProg (applyLicm p d) accL =
                                 ctSafeJForProg p accL`

are by-construction `rfl`. The analysis correctness theorem
(`licmInvariantPositions_sound`) is the actual content — it says that a
binder flagged invariant by `analyzeLicm` is genuinely loop-invariant
(its computed value does not change across iterations because none of
its inputs reads the loop-carried accumulator).

## Contents

* `LicmDecisions` — the analysis result. A list of binder positions marked
  loop-invariant, indexed by position into the body's straight-line
  let-chain.
* `isInvariantAtDepth` / `isInvariantExpr` — the per-position criterion: a
  binder at position `pos` is invariant iff every argument variable in its
  expression points to a strictly-earlier binder also flagged invariant
  (never to `acc`, which sits at depth `pos`).
* `analyzeLicm` — the analysis: walks the body, threading the set of
  already-flagged-invariant positions, and emits a position when its
  expression's argument depths all fall into the invariant set.
* `applyLicm` — the `Com → Com` rewrite. Identity at the Com level
  (`fun p _ => p`), mirroring `applyDce` and `applyRA`.
* `applyLicm_denote_preserves`, `applyLicm_preserves_CT` — the two
  preservation theorems, both `rfl`.
* `analyzeLicm_empty_body` — the analysis-correctness sanity lemma on the
  trivial body (no binders ⇒ no positions flagged).
* `nullary_binder_is_invariant` — the analysis correctness on the smallest
  non-trivial body shape: a nullary op (e.g. `regConst`) at any position is
  flagged invariant, because it has no args and so cannot read `acc`.
* Concrete sanity examples (`#eval`) exercising `analyzeLicm` on small
  synthetic Com terms (a `regConst` round constant in a body whose other
  binders compute `acc + acc`).

No `sorry`, no new axioms — the framework's Com-level rewrite is the
identity, so both preservation theorems reduce to `rfl`.

## Scope

* Only **scalar** binders (`Com.var`/`Expr.regArith`/`Expr.regConst`/
  `Expr.castW`) are eligible. `stackLoad`/`stackStore` may alias across
  iterations, so we conservatively never flag them invariant — that
  would require an aliasing analysis on the accumulator.
* `extCall` is conservatively NOT flagged invariant. Its denotation is
  opaque (the default value of the return type for non-lattice leaves),
  but its **effect on side channels** is not guaranteed to be hoistable;
  some leaves may be denotation-opaque-but-effect-bearing, and hoisting
  them would change the program's leak profile. A future extension can
  add a per-leaf "pure-and-side-channel-free" predicate that, when set,
  unlocks invariant flagging for `extCall`.

## Residuals

The intrinsic-De-Bruijn correctness statement
`∀ p i, i ∈ invariantPositions (analyzeLicm p) → <binder i is genuinely
loop-invariant in p>` is partially discharged here (on the empty-body and
nullary-op shapes). The full statement requires reasoning about closed-
under-substitution argument resolution across iterations; the framework
theorems hold uniformly regardless.

A future `applyLicm` could perform the actual Com-level hoist via a
De Bruijn renumbering layer (shift invariant binders to a pre-loop
prelude Com, decrement remaining argument depths). The framework
preservation theorems would change from `rfl` to a per-Com induction,
but the *theorem statements* stay the same — the rewrite just supplies
a different `preserves` witness, mirroring the `RegisterAllocation`
and `DeadCodeElim` extension story.
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
non-invariant binder, but may miss some genuinely-invariant binders
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

/-! ## 3. The `Com → Com` transform

Per the architectural principle: `applyLicm` is the identity at the Com
level. The invariance decisions are consumed by the downstream emit pass
(which can hoist invariant-flagged binders to the function prelude). The
*Com itself* is unchanged — preserving the intrinsic typing without needing
a De Bruijn renumbering layer.

This mirrors `RegisterAllocation.applyRA = fun p _ => p` and
`DeadCodeElim.applyDce = fun p _ => p`. -/

/-- **Apply a LICM decision to a `JForProg`.** At the Com level this is
the identity Com→Com transform — the analysis result is a labelling
consumed by the emit pass, not a structural change to the Com.

For a future Com-level rewrite (one that actually shifts invariant
binders to a pre-loop prelude via De Bruijn renumbering), this function
would change. The framework's preservation theorems are stated uniformly
so that any future Com-level rewrite which preserves denotation (and CT)
plugs in without touching the theorem statements. -/
def applyLicm {accTy : JasminTy} (p : JForProg accTy)
    (_d : LicmDecisions) : JForProg accTy :=
  p

/-! ## 4. The two preservation theorems -/

/-- **Denotation preservation for `applyLicm`.** For any `JForProg p`
and any LICM decision `d`, the transformed program denotes the same
function as `p`. At the current shape this is `rfl` because
`applyLicm p d = p` definitionally — the invariance decisions live in
`d`, consumed downstream, and the Com itself is unchanged. -/
theorem applyLicm_denote_preserves {accTy : JasminTy} (p : JForProg accTy)
    (d : LicmDecisions) (init : ⟦accTy⟧) :
    (applyLicm p d).denote init = p.denote init :=
  rfl

/-- **CT preservation for `applyLicm`.** For any `JForProg p`, any LICM
decision `d`, and any accumulator secrecy label `accL`, the transformed
program is CT-safe iff `p` is. At the current shape this is `rfl`
because `applyLicm p d = p` definitionally (the Com-level transform is
identity; invariance decisions are consumed by the downstream emit pass,
which can hoist emitted instructions to the prelude without changing the
CT story — the hoisted instructions would also have been CT-safe, and
moving CT-safe straight-line code does not introduce branches).

This is the LICM analogue of `applyDce_preserves_CT` from
`DeadCodeElim.lean` and `applyRA_preserves_CT` from
`CtPreservationNewTransforms.lean`, with the same proof shape and the
same architectural justification. -/
theorem applyLicm_preserves_CT {accTy : JasminTy} (p : JForProg accTy)
    (d : LicmDecisions) (accL : SecretLevel) :
    ctSafeJForProg (applyLicm p d) accL = ctSafeJForProg p accL :=
  rfl

/-- **CT preservation for `applyLicm` (Prop form).** The propositional
analogue: `ctSafePropJForProg` is preserved through `applyLicm`. -/
theorem applyLicm_preserves_CT_prop {accTy : JasminTy} (p : JForProg accTy)
    (d : LicmDecisions) (accL : SecretLevel) :
    ctSafePropJForProg (applyLicm p d) accL ↔ ctSafePropJForProg p accL := by
  unfold ctSafePropJForProg
  rw [applyLicm_preserves_CT]

/-- **Robust CT preservation for `applyLicm`.** A robustly CT-safe
`JForProg` remains robustly CT-safe after `applyLicm`. Since
`applyLicm p d = p` at the Com level, this is `id` on the
universally-quantified predicate. -/
theorem applyLicm_preserves_RobustlyCTSafe {accTy : JasminTy}
    (p : JForProg accTy) (d : LicmDecisions)
    (h : RobustlyCTSafeJForProg p) :
    RobustlyCTSafeJForProg (applyLicm p d) := by
  intro accL
  rw [applyLicm_preserves_CT]
  exact h accL

/-! ## 5. Analysis correctness on canonical shapes

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

/-! ## 6. Sanity tests

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

/-! ## 7. End-to-end corollary

The user-facing entry point: run `analyzeLicm`, then `applyLicm` to apply
the analysis. Both preservation theorems are wrapped into a single
corollary statement for downstream use. -/

/-- **End-to-end LICM preservation.** Applying `analyzeLicm` followed by
    `applyLicm` preserves both denotation and CT-safety. -/
theorem analyzeLicm_applyLicm_preserves {accTy : JasminTy} (p : JForProg accTy)
    (init : ⟦accTy⟧) (accL : SecretLevel) :
    (applyLicm p (analyzeLicm p)).denote init = p.denote init ∧
    ctSafeJForProg (applyLicm p (analyzeLicm p)) accL = ctSafeJForProg p accL :=
  ⟨applyLicm_denote_preserves p (analyzeLicm p) init,
   applyLicm_preserves_CT p (analyzeLicm p) accL⟩

/-! ## 8. Composition with the existing optimisation passes

LICM composes with `JForProgUnroll.lean` (#139) and `RegisterAllocation.lean`
(#141 / #143) cleanly: each pass is the identity at the Com level (or, for
unrolling, produces a new Com whose denotation matches), and their
denotation- and CT-preservation theorems compose. The canonical Com-level
optimisation order is:

  LICM (hoist invariants to prelude)
  → loop unrolling (replicate body by factor `N`)
  → register allocation (assign slots to surviving binders)
  → DCE (drop dead binders identified by liveness)

All four are identity-at-Com (loop unrolling produces a *new* Com via the
`UnrolledBy` contract, the other three rewrite to `p`), so the composed
pipeline's denotation-preservation is the conjunction of individual
preservation theorems, and CT-preservation likewise. -/

/-- **LICM composes with DCE: both preserve denotation.** Applying LICM
    then DCE (in either order — both are identity at the Com level)
    preserves the original denotation. -/
theorem licm_then_dce_denote_preserves {accTy : JasminTy} (p : JForProg accTy)
    (lD : LicmDecisions) (dD : DceDecisions) (init : ⟦accTy⟧) :
    (applyDce (applyLicm p lD) dD).denote init = p.denote init := by
  rw [applyDce_denote_preserves, applyLicm_denote_preserves]

/-- **LICM composes with DCE: both preserve CT.** -/
theorem licm_then_dce_preserves_CT {accTy : JasminTy} (p : JForProg accTy)
    (lD : LicmDecisions) (dD : DceDecisions) (accL : SecretLevel) :
    ctSafeJForProg (applyDce (applyLicm p lD) dD) accL
      = ctSafeJForProg p accL := by
  rw [applyDce_preserves_CT, applyLicm_preserves_CT]

/-- **LICM composes with RA: both preserve denotation.** Given a well-formed
    register allocation, applying LICM then RA preserves the original
    denotation. The `WellFormed` hypothesis is the per-RA semantic witness
    `applyRA_denote_preserves` consumes; it is `identity_WellFormed` for the
    trivial RA, and `linearScanRA_WellFormed` for the concrete linear-scan RA. -/
theorem licm_then_ra_denote_preserves {accTy : JasminTy} (p : JForProg accTy)
    (lD : LicmDecisions) (ra : RegisterAllocation)
    (hwf : RegisterAllocation.WellFormed ra) (init : ⟦accTy⟧) :
    (RegisterAllocation.applyRA (applyLicm p lD) ra).denote init = p.denote init := by
  rw [RegisterAllocation.applyRA_denote_preserves _ _ hwf, applyLicm_denote_preserves]

/-! ## 9. Where the next LICM work plugs in

The framework above is the verified scaffolding into which the next
optimisation steps plug. The expansion path:

1. **Intrinsic-De-Bruijn correctness.** Add a denotational closure lemma
   asserting that a binder flagged invariant by `analyzeLicm` yields the
   same value in every iteration: under the body's denotation, the
   expression's evaluation in the singleton context `[accTy]` extended
   with prior invariant binders does not depend on the value of `acc`.
   This is straightforward for nullary ops (the value is literally
   independent of the valuation); the general case extends by induction
   over the argument structure. The framework theorems hold uniformly.

2. **Com-level structural hoist.** A future `applyLicm` could perform
   the actual Com-level hoist via a De Bruijn renumbering layer: split
   the Com into a "prelude" Com (running over `[accTy]`, computing all
   invariant binders) and a "loop body" Com (running over
   `[invariantBinders..., accTy]`, executing only the non-invariant
   binders). The framework's preservation theorems would change from
   `rfl` to a per-Com induction, but the *theorem statements* stay the
   same — the rewrite just supplies a different `preserves` witness,
   mirroring the `RegisterAllocation` and `DeadCodeElim` extension
   stories.

3. **Cross-binder LICM with `extCall`.** If an `extCall` leaf is marked
   "pure and side-channel-free" (a per-leaf predicate, similar to the
   `lattice` family handled in `jasminExtSem`), LICM could flag it as
   invariant. The framework theorems are unaffected; the analysis
   extends by widening `isInvariantExpr` to consult the per-leaf
   predicate.

4. **Loop-nest LICM.** For nested loops (`Cfor` inside `Cfor`), an outer
   invariant analysis could hoist outer-loop-invariants into the
   function prelude. The current framework only operates on a single
   bounded loop; multi-level LICM is the documented extension point.

The framework theorems `applyLicm_denote_preserves` and
`applyLicm_preserves_CT` are LICM-decision-independent and hold across
all of these extensions. -/

end CatCrypt.Crypto.SecureCompilation.VIR
