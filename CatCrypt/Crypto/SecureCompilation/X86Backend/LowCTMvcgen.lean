/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT


@[expose] public section
set_option autoImplicit false

/-!
# Deterministic compiler correctness as an `mvcgen`-driven unary Hoare logic

This module recasts the backend's deterministic **compiler-correctness** theorem
(`LowCTToJInstrCT.lowerSeq_denote`: the machine block run tracks the folded source
semantics under `StateMatch`) as a unary `Std.Do` **Hoare triple** discharged by
`mvcgen`, reusing the very same `@[spec]`/`Triple`/`mvcgen` infrastructure the
bignum-kernel proofs use in `CatCrypt/Crypto/Jasmin/BignumStepSpecs.lean`.

## The logic stays unary; the relation lives in the assertions

The source↔target *relational* content of compiler correctness is carried entirely
inside the pre/post **assertions**: the precondition asserts `StateMatch ρ rs js`
(the machine register `ρ v` holds the truncated source scalar `v`), and the
postcondition asserts `StateMatch ρ (srcDenote ps rs) js'` (the same relation
against the source post-state).  The Hoare logic itself is the ordinary *unary*
one over machine states `JState 64` — no relational/product program is built.

This is the deterministic counterpart to the probabilistic security layer, where
the source≈target relation is instead carried by a **relational** Hoare
logic, the pRHL `rHoare` judgement.  Here, because the backend
is deterministic, the relation collapses into a unary triple whose assertions are
`StateMatch`.

## The monad

We run a block in `StateM (JState 64) = StateT (JState 64) Id` — the standard
state monad `Std.Do.mvcgen` supports out of the box (its `modify`/`forM` `@[spec]`
lemmas fire automatically, so unlike the `StateT _ Option` bignum monad we need no
custom `wp_apply` lemma).  `runBlockM_run` proves the monadic form agrees with the
fold `runBlock`, so the triple is a statement about the real machine execution.

## What is proved

* `runBlockM_run` — the monadic block run equals the `runBlock` fold (faithfulness).
* `stepM_spec` — the `@[spec]` Hoare triple for the per-instruction step
  `modify (evalInstr · i)`, whose post records the per-instruction `JState` effect.
* `compile_correct_triple` — **the headline**: the whole-block triple
  `⦃StateMatch ρ rs⦄ runBlockM (lowerSeq ρ ps) ⦃StateMatch ρ (srcDenote ps rs)⦄`,
  discharged by `mvcgen` composing `stepM_spec` over the block, with the residual
  relational VC closed by the existing `lowerSeq_denote` correctness lemma.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMvcgen

open Std.Do
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.Jasmin.LowCT (RustState rsSetScalar)

/-! ## 1. The monadic block run and its agreement with `runBlock` -/

/-- The per-instruction monadic step: update the machine state by `evalInstr · i`.
    This is the `do`-shaped atom `mvcgen` walks. -/
def stepM (i : JInstr 64) : StateM (JState 64) Unit :=
  modify (fun s => evalInstr s i)

/-- **The monadic block run.**  `forM` of the per-instruction step over the block —
    the `do`-shaped form of `runBlock` that `mvcgen` can walk. -/
def runBlockM (block : List (JInstr 64)) : StateM (JState 64) Unit :=
  block.forM stepM

/-- `runBlockM` over `[]` is the trivial program (`mvcgen` recursion base). -/
@[simp] theorem runBlockM_nil : runBlockM [] = pure () := rfl

/-- `runBlockM` over `i :: is` unrolls to a `stepM`-then-rest bind chain — the
    explicit `do`-shape `mvcgen` composes `stepM_spec` across.  Mirror of
    `BignumExec.bignumExecM_cons`. -/
@[simp] theorem runBlockM_cons (i : JInstr 64) (is : List (JInstr 64)) :
    runBlockM (i :: is) = stepM i >>= fun _ => runBlockM is := by
  unfold runBlockM; simp

/-- **Faithfulness.**  Running the monadic block from `s` returns the same final
    state as the `runBlock` fold, so a triple about `runBlockM` is a statement
    about the real machine execution `runBlock`. -/
theorem runBlockM_run (block : List (JInstr 64)) (s : JState 64) :
    (runBlockM block).run s = ((), runBlock s block) := by
  induction block generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (stepM i >>= fun _ => runBlockM is).run s = _
    simp only [stepM, StateT.run_bind, StateT.run_modify, runBlock_cons, ih]
    rfl

/-! ## 2. The `PostShape` and the per-instruction `@[spec]` triple -/

/-- The `PostShape` of `StateM (JState 64) = StateT (JState 64) Id`: a single state
    argument over the pure (no-throw) base. -/
abbrev psJM : PostShape := .arg (JState 64) .pure

/-- **The per-instruction step spec.**  The Hoare triple for one step
    `modify (evalInstr · i)`: the precondition is the explicit weakest
    precondition (the post evaluated at the `evalInstr`-updated state), so applying
    this spec inside `mvcgen` records exactly the per-instruction effect on
    `JState` and leaves the continuation goal.  Mirrors `BignumStepSpecs`' pure
    register-update `@[spec]` lemma form; here `mvcgen`'s built-in `modify` spec
    discharges it directly (the `StateM` monad needs no custom `wp` lemma). -/
@[spec]
theorem stepM_spec (i : JInstr 64) (Q : PostCond Unit psJM) :
    Triple (stepM i) (fun s => Q.1 () (evalInstr s i)) Q := by
  unfold stepM Triple
  mvcgen

/-- **The composed block-run triple.**  For *any* block and *any* state predicate
    `R`, running the block from a state where `R` holds leaves a state where `R`
    holds at `runBlock s block`.  Proven by induction over the block, composing the
    `stepM_spec` per-instruction spec through `Triple.bind` — the structural
    analogue of `BignumExec.bignumExecM_append`-style chunking, generalised to the
    whole symbolic block.  This is the spec-composed engine the headline uses. -/
theorem runBlockM_spec (block : List (JInstr 64)) (R : JState 64 → Prop) :
    Triple (runBlockM block)
      (fun s => ⌜R (runBlock s block)⌝)
      (⇓ _ => fun s => ⌜R s⌝) := by
  induction block with
  | nil =>
    simp only [runBlockM_nil, runBlock_nil]
    mvcgen
  | cons i is ih =>
    rw [runBlockM_cons]
    refine Triple.bind (stepM i) _ (Q := fun _ s => ⌜R (runBlock s is)⌝) ?_ ?_
    · have := stepM_spec i (PostCond.noThrow fun _ s => ⌜R (runBlock s is)⌝)
      simpa [runBlock_cons] using this
    · intro _; exact ih

/-! ## 3. The headline: compiler correctness as an `mvcgen`-discharged triple

The unary triple whose pre/post assertions are `StateMatch` *is* the
source↔target compiler-correctness relation: it says that whenever the machine
state matches the source state under the register map `ρ`, running the lowered
block leaves the machine state matching the source *post*-state `srcDenote ps rs`.
-/

/-- **Compiler correctness, as a unary Hoare triple.**  Under the
    register-allocation well-formedness side conditions (`ρ` injective, each
    statement's second-operand register distinct from its destination), the
    lowered block satisfies the triple

      `⦃ StateMatch ρ rs ⦄ runBlockM (lowerSeq ρ ps) ⦃ StateMatch ρ (srcDenote ps rs) ⦄`.

    The relational source↔target content lives entirely in the `StateMatch`
    pre/post assertions; the logic is the ordinary unary state-monad Hoare logic.

    The proof composes the per-instruction `stepM_spec` over the whole block via
    `runBlockM_spec` (the `Triple.bind`-chained engine), instantiated at the
    relation `R js := StateMatch ρ (srcDenote ps rs) js`.  That yields the triple
    with precondition `R (runBlock js (lowerSeq ρ ps))`; strengthening it to the
    intended `StateMatch ρ rs` precondition is exactly the existing deterministic
    correctness lemma `lowerSeq_denote`. -/
theorem compile_correct_triple (ρ : RegMap) (hρ : Function.Injective ρ)
    (ps : List ArithSrc) (hwf : ∀ p ∈ ps, p.b ≠ p.dst) (rs : RustState) :
    Triple (runBlockM (lowerSeq ρ ps))
      (fun js => ⌜StateMatch ρ rs js⌝)
      (⇓ _ => fun js => ⌜StateMatch ρ (srcDenote ps rs) js⌝) := by
  -- Compose `stepM_spec` over the block via `runBlockM_spec` at the source-match
  -- relation; strengthen the precondition with the deterministic correctness lemma.
  have hcomposed := runBlockM_spec (lowerSeq ρ ps)
    (fun js => StateMatch ρ (srcDenote ps rs) js)
  unfold Triple at hcomposed ⊢
  intro js hmatch
  exact hcomposed js (lowerSeq_denote ρ hρ ps hwf rs js hmatch)

/-! ## 4. `mvcgen` composing `stepM_spec` over a *literal* block

`compile_correct_triple` runs over a *symbolic* block `lowerSeq ρ ps` (a `forM`
over a symbolic list), composed by `runBlockM_spec`'s `Triple.bind` induction.
Plain `mvcgen` cannot unroll a finite `do`-chain over a symbolic list — it would
expose a single `forM`-VC.

To show that on a *literal* block plain `mvcgen` drives the composition end to end,
here is the single-statement lowering — the literal two-instruction block
`[mov ρdst ρa, op ρdst ρb]` — whose triple `mvcgen [stepM_spec]` discharges by
composing `stepM_spec` twice (once per instruction, via `runBlockM_cons`), leaving
only the residual relational VC closed by `lowerArith_denote`. -/

/-- **Single-statement compiler correctness, `mvcgen`-driven.**  For the literal
    two-instruction block of one `ArithSrc` lowering, `mvcgen` composes the
    `stepM_spec` step spec across both instructions; the residual VC is the
    single-statement denote lemma. -/
theorem compile_correct_triple_stmt (ρ : RegMap) (hρ : Function.Injective ρ)
    (p : ArithSrc) (hb : p.b ≠ p.dst) (rs : RustState) :
    Triple (runBlockM (lowerArith ρ p))
      (fun js => ⌜StateMatch ρ rs js⌝)
      (⇓ _ => fun js =>
        ⌜StateMatch ρ (rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar)) js⌝) := by
  unfold lowerArith
  simp only [runBlockM_cons, runBlockM_nil]
  mvcgen [stepM_spec]
  -- `mvcgen` composed `stepM_spec` across both literal instructions; the residual
  -- VC is the pointwise `StateMatch` obligation, i.e. exactly `lowerArith_denote`
  -- (the two nested `evalInstr` steps = `runBlock` over the literal block).
  rename_i s hmatch
  have h := lowerArith_denote ρ p rs s hρ hb hmatch
  simpa [lowerArith, runBlock_cons, runBlock_nil] using h

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMvcgen
