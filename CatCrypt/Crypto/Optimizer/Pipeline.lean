/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.LowCTExec
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis
public import CatCrypt.Crypto.Optimizer.BarrettReduce
public import CatCrypt.Crypto.Optimizer.MontgomeryReduce
public import CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul
public import CatCrypt.Crypto.Optimizer.Lattice.NTTHoist
public import CatCrypt.Crypto.Optimizer.SchedulerPass
public import CatCrypt.Crypto.SecureCompilation.VIR.CommonSubexprElim
public import CatCrypt.Crypto.SecureCompilation.VIR.StrengthReduce
public import CatCrypt.Crypto.SecureCompilation.VIR.DeadCodeElim
public import CatCrypt.Crypto.SecureCompilation.VIR.CtPreservationNewTransforms
public import CatCrypt.Crypto.Optimizer.RegAllocLeakTrace
public import CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline

/-!
# Pass Pipeline Orchestrator

Composes per-pass denotational-equivalence theorems into a single
`pipeline_denote_eq` meta-theorem.  Lets passes compose without
re-proving end-to-end after each new pass.

This is the orchestration layer for Tier 1 (local arithmetic), Tier 2 (loop and data layout),
and Tier 3 (algorithmic rewrites) passes.

## Architecture

An `OptimizerPass` packages a syntactic rewrite `LowCT → LowCT`
together with a parametric denotational-equivalence theorem:

```
∀ N leafSpec c rs rs', RustExec N leafSpec (rewrite c) rs rs'
                     ↔ RustExec N leafSpec c rs rs'
```

The pipeline `[p1, p2, ..., pn]` applies passes left-to-right.  The
composed equivalence is proved by induction on the list — each step
chains its theorem with the accumulated equivalence.

## Pass preconditions

Some passes (Montgomery, NTT) carry per-leaf agreement assumptions
on the LeafSpec (`hAgree`).  The pipeline carries these forward as
typeclass instances or explicit parameters; this file's `OptimizerPass`
captures the simplest case where the equivalence is unconditional.
The more general `OptimizerPassWithPrecond` covers passes that need
hypotheses.

## Idempotence and fixed-point

The pipeline can be run to a fixed point: `applyUntilFixed passes c`
re-applies the pipeline until no rewrite triggers (modulo a max-iter
bound for termination).  Verification: each iteration preserves
semantics by the per-pass theorems; fixed-point convergence is
syntactic, not semantic.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Pipeline

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  OptimizerPass record

The basic unit of optimization.  A `rewrite` function paired with its
denotational-equivalence theorem (carried as a `Prop`-valued field —
the consumer instantiates the theorem when constructing an instance). -/

/-- Unconditional optimizer pass: a syntactic rewrite preserving
    `RustExec` semantics for all `leafSpec` / `N` / `rs` / `rs'`. -/
structure OptimizerPass where
  /-- The rewrite function. -/
  rewrite : LowCT → LowCT
  /-- The denotational-equivalence theorem (as a Prop). -/
  denote_eq :
    ∀ (N : Nat) (leafSpec : LeafSpec) (c : LowCT) (rs rs' : RustState),
      RustExec N leafSpec (rewrite c) rs rs' ↔ RustExec N leafSpec c rs rs'

/-- Conditional pass: rewrite is correct under a precondition on the
    `LeafSpec` (e.g., Barrett requires `leafSpec` to agree on the
    `barrett_q` and `mod_q` calls).  Use this when the pass has
    per-leaf agreement axioms. -/
structure OptimizerPassWithPrecond where
  /-- The rewrite function. -/
  rewrite : LowCT → LowCT
  /-- The precondition on the LeafSpec. -/
  precond : LeafSpec → Prop
  /-- The conditional equivalence theorem. -/
  denote_eq :
    ∀ (N : Nat) (leafSpec : LeafSpec) (h : precond leafSpec)
      (c : LowCT) (rs rs' : RustState),
      RustExec N leafSpec (rewrite c) rs rs' ↔ RustExec N leafSpec c rs rs'

/-! ## §2  Identity pass (used as base case for empty pipelines) -/

/-- The identity pass: doesn't change the LowCT. -/
def identityPass : OptimizerPass where
  rewrite := id
  denote_eq := fun _ _ c rs rs' => by simp

/-! ## §3  Pipeline composition

A pipeline is a list of passes applied left-to-right.  The composed
rewrite is `pn ∘ ... ∘ p2 ∘ p1`; the composed equivalence chains the
per-pass theorems. -/

/-- Apply a list of passes left-to-right. -/
def applyPipeline (passes : List OptimizerPass) (c : LowCT) : LowCT :=
  passes.foldl (fun acc p => p.rewrite acc) c

/-- Composed denotational-equivalence theorem for the pipeline. -/
theorem applyPipeline_denote_eq (passes : List OptimizerPass) :
    ∀ (N : Nat) (leafSpec : LeafSpec) (c : LowCT) (rs rs' : RustState),
      RustExec N leafSpec (applyPipeline passes c) rs rs'
    ↔ RustExec N leafSpec c rs rs' := by
  induction passes with
  | nil => intros; simp [applyPipeline]
  | cons p ps ih =>
    intro N leafSpec c rs rs'
    -- Unfold one step of foldl: applyPipeline (p :: ps) c = applyPipeline ps (p.rewrite c)
    have hUnfold : applyPipeline (p :: ps) c = applyPipeline ps (p.rewrite c) := rfl
    rw [hUnfold]
    -- Chain: applyPipeline ps (p.rewrite c) ≡ p.rewrite c (by IH) ≡ c (by p.denote_eq)
    have h_ih := ih N leafSpec (p.rewrite c) rs rs'
    have h_p := p.denote_eq N leafSpec c rs rs'
    exact h_ih.trans h_p

/-! ## §4  Pipeline-with-precondition variant -/

/-- Apply a list of conditional passes.  The composed precondition
    is the conjunction of each pass's precondition. -/
def applyPipelineCond (passes : List OptimizerPassWithPrecond)
    (c : LowCT) : LowCT :=
  passes.foldl (fun acc p => p.rewrite acc) c

/-- All passes' preconditions hold for the given LeafSpec. -/
def allPrecondsHold (passes : List OptimizerPassWithPrecond)
    (leafSpec : LeafSpec) : Prop :=
  ∀ p ∈ passes, p.precond leafSpec

/-- Composed equivalence under combined preconditions.  Same structure
    as `applyPipeline_denote_eq` but threading the per-pass precondition
    witness through each step. -/
theorem applyPipelineCond_denote_eq (passes : List OptimizerPassWithPrecond) :
    ∀ (N : Nat) (leafSpec : LeafSpec)
      (_hAllPreconds : allPrecondsHold passes leafSpec)
      (c : LowCT) (rs rs' : RustState),
      RustExec N leafSpec (applyPipelineCond passes c) rs rs'
    ↔ RustExec N leafSpec c rs rs' := by
  induction passes with
  | nil => intros; simp [applyPipelineCond]
  | cons p ps ih =>
    intro N leafSpec hAllPreconds c rs rs'
    have hp : p.precond leafSpec := hAllPreconds p (List.Mem.head _)
    have hps : allPrecondsHold ps leafSpec :=
      fun q hq => hAllPreconds q (List.Mem.tail _ hq)
    have hUnfold : applyPipelineCond (p :: ps) c
                 = applyPipelineCond ps (p.rewrite c) := rfl
    rw [hUnfold]
    have h_ih := ih N leafSpec hps (p.rewrite c) rs rs'
    have h_p := p.denote_eq N leafSpec hp c rs rs'
    exact h_ih.trans h_p

/-! ## §5  Fixed-point application

For passes that may need multiple iterations (e.g., constant folding
exposing new optimization opportunities), apply the pipeline until
the result stops changing OR a maximum iteration count is reached. -/

/-- Iterate the pipeline up to `maxIter` times.  Termination is by
    fuel (`maxIter` strictly decreases per recursive call).

    A more precise "stop early when output stops changing" variant
    would require `BEq LowCT`, which the framework doesn't currently
    derive (LowCT has nested structure that doesn't auto-derive
    BEq).  Fuel-based iteration suffices for the pipeline orchestrator;
    the per-pass equivalences compose across iterations regardless. -/
def applyNTimes (passes : List OptimizerPass) (maxIter : Nat) (c : LowCT) :
    LowCT :=
  match maxIter with
  | 0 => c
  | n + 1 => applyNTimes passes n (applyPipeline passes c)

/-- Fixed-iteration semantics preservation: `applyNTimes` preserves
    `RustExec` semantics for any iteration count.  Folds the per-pass
    equivalence through the fuel decrement. -/
theorem applyNTimes_denote_eq (passes : List OptimizerPass) :
    ∀ (maxIter : Nat) (N : Nat) (leafSpec : LeafSpec)
      (c : LowCT) (rs rs' : RustState),
      RustExec N leafSpec (applyNTimes passes maxIter c) rs rs'
    ↔ RustExec N leafSpec c rs rs' := by
  intro maxIter
  induction maxIter with
  | zero => intros; simp [applyNTimes]
  | succ k ih =>
    intro N leafSpec c rs rs'
    simp only [applyNTimes]
    have h1 := ih N leafSpec (applyPipeline passes c) rs rs'
    have h2 := applyPipeline_denote_eq passes N leafSpec c rs rs'
    exact h1.trans h2

/-! ## §6  Pre-built pipelines for the named tiers

Concrete pipelines that bundle the canonical Tier 1 / Tier 2 / Tier 3
passes.  Consumers instantiate these in protocol bridge files. -/

/-- Empty pipeline — useful as a placeholder. -/
def emptyPipeline : List OptimizerPass := []

/-- Tier 1 unconditional passes (empty; the conditional Tier 1 passes are in
    `tier1ConditionalPipeline`). -/
def tier1Pipeline : List OptimizerPass :=
  -- TODO: add identityPass-style placeholders for:
  --   - constFold
  --   - cse
  -- Conditional passes (Barrett, Montgomery) go in tier1ConditionalPipeline.
  []

/-! ### Tier 1 — Barrett reduction pass

Wraps `BarrettReduce.barrettReduce q` and its agreement precondition
`barrettAgreesModQ leafSpec q`.  Two protocol-specific specialisations
land: ML-KEM (`q = 3329`) and ML-DSA-65 (`q = 8380417`).

The `denote_eq` field unfolds `BarrettReduce.barrettReduce_denote_eq`
under the supplied agreement hypothesis. -/

open CatCrypt.Crypto.Optimizer.BarrettReduce in
/-- Barrett-reduction pass parameterised by the modulus `q`. -/
def barrettPass (q : Nat) : OptimizerPassWithPrecond where
  rewrite := barrettReduce q
  precond leafSpec := barrettAgreesModQ leafSpec q
  denote_eq N leafSpec hAgree c rs rs' :=
    barrettReduce_denote_eq q N leafSpec hAgree c rs rs'

/-- Barrett pass specialised for ML-KEM-768 (`q = 3329`). -/
def barrettMlkemPass : OptimizerPassWithPrecond := barrettPass 3329

/-- Barrett pass specialised for ML-DSA-65 (`q = 8380417`). -/
def barrettMldsaPass : OptimizerPassWithPrecond := barrettPass 8380417

/-! ### Tier 1 — Montgomery reduction pass

Wraps `MontgomeryReduce.montgomeryReduce q R` and its agreement
precondition `montAgreesMulModQ leafSpec q R`. -/

open CatCrypt.Crypto.Optimizer.MontgomeryReduce in
/-- Montgomery-reduction pass parameterised by modulus `q` and radix `R`. -/
def montgomeryPass (q R : Nat) : OptimizerPassWithPrecond where
  rewrite := montgomeryReduce q R
  precond leafSpec := montAgreesMulModQ leafSpec q R
  denote_eq N leafSpec hAgree c rs rs' :=
    montgomeryReduce_denote_eq q R N leafSpec hAgree c rs rs'

/-- Montgomery pass specialised for ML-KEM-768 (`q = 3329`, `R = 2^16`). -/
def montgomeryMlkemPass : OptimizerPassWithPrecond := montgomeryPass 3329 65536

/-- Montgomery pass specialised for ML-DSA-65 (`q = 8380417`,
`R = 2^32`). -/
def montgomeryMldsaPass : OptimizerPassWithPrecond :=
  montgomeryPass 8380417 4294967296

/-- Tier 1 conditional passes — Barrett, Montgomery.  Specialised for
ML-KEM-768; protocols pick the specialisation matching their `q` (and
`R` for Montgomery).  Sequential order: Barrett first, then Montgomery
— Montgomery's rewrite recognises `mul_mod_q`/`mul_reduce`, neither of
which is touched by Barrett. -/
def tier1ConditionalPipeline : List OptimizerPassWithPrecond :=
  [barrettMlkemPass, montgomeryMlkemPass]

/-- ML-DSA-65 Tier 1 conditional pipeline. -/
def tier1ConditionalPipelineMldsa : List OptimizerPassWithPrecond :=
  [barrettMldsaPass, montgomeryMldsaPass]

/-! ### Tier 3 — algorithmic rewrites

The NTT-backed poly-mul pass is a Tier 3 entry.  It wraps
`Lattice.NTTPolyMul.nttPolyMul q n` together with its agreement
precondition `nttAgreesPolyMul · q n` and the closing equivalence
theorem.

The precondition is concrete-`LeafSpec`-dependent: protocols supply
a discharge via `NTTPolyMul_CompPoly.nttAgreesPolyMul_of_pointwise`
(plumbing) or a `CompPoly.fastMulImpl_eq_mul`-backed concrete
construction (algebraic).
-/

open CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul in
/-- The NTT poly-mul pass specialised to ML-KEM-768: `q = 3329`, `n = 256`. -/
def nttPolyMulMlkemPass : OptimizerPassWithPrecond where
  rewrite := nttPolyMulMlkem
  precond leafSpec := nttAgreesPolyMul leafSpec 3329 256
  denote_eq N leafSpec hAgree c rs rs' :=
    nttPolyMulMlkem_denote_eq N leafSpec hAgree c rs rs'

open CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul in
/-- The NTT poly-mul pass specialised to ML-DSA-65: `q = 8380417`, `n = 256`. -/
def nttPolyMulMldsaPass : OptimizerPassWithPrecond where
  rewrite := nttPolyMulMldsa
  precond leafSpec := nttAgreesPolyMul leafSpec 8380417 256
  denote_eq N leafSpec hAgree c rs rs' :=
    nttPolyMulMldsa_denote_eq N leafSpec hAgree c rs rs'

/-- Tier 3 conditional passes — algorithmic rewrites:
    the ML-KEM specialisation of the NTT poly-mul pass.  ML-DSA's
    specialisation lives in `nttPolyMulMldsaPass`; protocol bridges
    typically pick the one matching their `(q, n)` parameters rather
    than running both. -/
def tier3MlkemPipeline : List OptimizerPassWithPrecond :=
  [nttPolyMulMlkemPass]

/-- Tier 3 conditional passes for ML-DSA-65. -/
def tier3MldsaPipeline : List OptimizerPassWithPrecond :=
  [nttPolyMulMldsaPass]

/-! ### Tier 3 — `invntt` hoist (observational pass)

The hoist (`Lattice.NTTHoist.nttHoist`) runs *after* the NTT poly-mul pass: the
latter turns `poly_mul` into `ntt_poly_mul_{q}_{n}`, and the hoist recognises an
accumulate-loop of those calls and hoists the per-iteration `invntt` into
a single one after the loop (NTT-domain accumulation in between).

**Soundness is weaker than for the NTT poly-mul pass, so the hoist is not an
`OptimizerPass`.**  The poly-mul pass's `denote_eq` is a *full state*
equivalence (`RustExec (rewrite c) rs rs' ↔ RustExec c rs rs'`).  The
hoist restructures the program — the rewritten loop leaves `prod` in the
NTT domain and accumulates in the NTT domain — so the post-states differ
on the scratch slot `prod`; only the *observable accumulator* agrees, and
only when that accumulator is zero at loop entry (so `invntt 0 = 0`
applies).  The certificate is therefore the **observational** theorem
`NTTHoist.nttHoist_maccLoop_eq` (output `acc` agrees, under leaf-additivity
of `invntt` and a zeroed-accumulator entry state), not an unconditional
state equivalence.  This is why the hoist is registered as a composed
*rewrite* (`tier3MlkemHoisted`) rather than appended to
`tier3MlkemPipeline : List OptimizerPassWithPrecond`. -/

open CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul
open CatCrypt.Crypto.Optimizer.Lattice.NTTHoist

/-- ML-KEM-768 hoist rewrite (`q = 3329`, `n = 256`). -/
def nttHoistMlkem : LowCT → LowCT := nttHoist 3329 256

/-- ML-DSA-65 hoist rewrite (`q = 8380417`, `n = 256`). -/
def nttHoistMldsa : LowCT → LowCT := nttHoist 8380417 256

/-- ML-KEM-768 poly-mul + hoist: first the NTT poly-mul rewrite, then the
    `invntt` hoist.  This is the rewrite the optimizer actually applies to
    a `polyvec_dot`-shaped kernel; its observable correctness is
    `NTTHoist.nttHoist_maccLoop_eq` (see the section docstring). -/
def tier3MlkemHoisted : LowCT → LowCT :=
  nttHoistMlkem ∘ nttPolyMulMlkem

/-- ML-DSA-65 poly-mul + hoist rewrite. -/
def tier3MldsaHoisted : LowCT → LowCT :=
  nttHoistMldsa ∘ nttPolyMulMldsa

/-! ### Hoist smoke test

The composed `tier3MlkemHoisted` rewrite, applied to a canonical
`polyvec_dot`-shaped kernel (accumulator `acc` and scratch `prod`
freshly declared, then the multiply-accumulate loop), produces the
hoisted form: the inner `poly_mul` becomes `ntt_basemul_3329_256` and a
single `ntt_invntt_3329_256` is appended after the loop.  The
`RLetZero acc` / `RLetZero prod` wrappers are what license the guarded
hoist (the accumulator is provably zeroed at loop entry). -/

def hoistSmokeTy : TowerType := .TPolyMod 3329 256

/-- Canonical kernel (k = 3): declare `acc`, `prod`, then the loop. -/
def hoistSmokeKernel : LowCT :=
  .RLetZero "acc" hoistSmokeTy (.RLetZero "prod" hoistSmokeTy
    (.RFor "i" 3
      (.RSeq (.RCall "poly_mul" ⟨"prod", hoistSmokeTy⟩
                [⟨"a", hoistSmokeTy⟩, ⟨"b", hoistSmokeTy⟩])
             (.RCall "poly_add" ⟨"acc", hoistSmokeTy⟩
                [⟨"acc", hoistSmokeTy⟩, ⟨"prod", hoistSmokeTy⟩]))))

/-- Expected output: NTT-domain `basemul` loop + a single closing
    `invntt`, inside the same accumulator scope. -/
def hoistSmokeExpected : LowCT :=
  .RLetZero "acc" hoistSmokeTy (.RLetZero "prod" hoistSmokeTy
    (.RSeq
      (.RFor "i" 3
        (.RSeq (.RCall (nttBasemulName 3329 256) ⟨"prod", hoistSmokeTy⟩
                  [⟨"a", hoistSmokeTy⟩, ⟨"b", hoistSmokeTy⟩])
               (.RCall "poly_add" ⟨"acc", hoistSmokeTy⟩
                  [⟨"acc", hoistSmokeTy⟩, ⟨"prod", hoistSmokeTy⟩])))
      (.RCall (nttInvnttName 3329 256) ⟨"acc", hoistSmokeTy⟩ [⟨"acc", hoistSmokeTy⟩])))

-- `tier3MlkemHoisted_smoke` moved out of Lean: checked by `lake exe optimizer-smoke-kat`.

def hoistSmokeTyDsa : TowerType := .TPolyMod 8380417 256

/-- ML-DSA-65 canonical kernel. -/
def hoistSmokeKernelDsa : LowCT :=
  .RLetZero "acc" hoistSmokeTyDsa (.RLetZero "prod" hoistSmokeTyDsa
    (.RFor "i" 6
      (.RSeq (.RCall "poly_mul" ⟨"prod", hoistSmokeTyDsa⟩
                [⟨"a", hoistSmokeTyDsa⟩, ⟨"b", hoistSmokeTyDsa⟩])
             (.RCall "poly_add" ⟨"acc", hoistSmokeTyDsa⟩
                [⟨"acc", hoistSmokeTyDsa⟩, ⟨"prod", hoistSmokeTyDsa⟩]))))

/-- ML-DSA-65 expected hoisted form. -/
def hoistSmokeExpectedDsa : LowCT :=
  .RLetZero "acc" hoistSmokeTyDsa (.RLetZero "prod" hoistSmokeTyDsa
    (.RSeq
      (.RFor "i" 6
        (.RSeq (.RCall (nttBasemulName 8380417 256) ⟨"prod", hoistSmokeTyDsa⟩
                  [⟨"a", hoistSmokeTyDsa⟩, ⟨"b", hoistSmokeTyDsa⟩])
               (.RCall "poly_add" ⟨"acc", hoistSmokeTyDsa⟩
                  [⟨"acc", hoistSmokeTyDsa⟩, ⟨"prod", hoistSmokeTyDsa⟩])))
      (.RCall (nttInvnttName 8380417 256) ⟨"acc", hoistSmokeTyDsa⟩
        [⟨"acc", hoistSmokeTyDsa⟩])))

-- `tier3MldsaHoisted_smoke` moved out of Lean: checked by `lake exe optimizer-smoke-kat`.

/-! ## §7  Composition theorem (top-level meta-theorem)

The headline result: any pipeline of verified passes preserves the
underlying simulation. -/

/-- Headline meta-theorem: applying the pipeline to a LowCT produces
    a semantically-equivalent LowCT.  Combined with the framework's
    `rustExecSimulates` (LowCT ↔ Jasmin), this means the optimized
    LowCT's Jasmin lowering simulates the same semantics as the
    original — the optimizer adds no trust. -/
theorem optimizer_preserves_simulates
    (passes : List OptimizerPass) (N : Nat) (leafSpec : LeafSpec)
    (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (applyPipeline passes c) rs rs'
  ↔ RustExec N leafSpec c rs rs' :=
  applyPipeline_denote_eq passes N leafSpec c rs rs'

/-! ## §7.5  Intra-block instruction scheduling wired in

The ILP list scheduler (`SchedulerPass.scheduleBlock`) is a
`LowCT → LowCT` reorder, but its certificates are phrased over a
`List BBStmt` lowered with `blockToCmd` (because `scheduleBlock` reorders
the statements of a *block*).  We wire it into this orchestrator at that
level: the emit entry point presents a hot basic block as a
`List BBStmt`, the scheduler reorders it for ILP, and the resulting
`LowCT` is then fed through the existing `applyPipeline` so the
algebraic/strength-reduction passes (Barrett, Montgomery, NTT, …) run on
the scheduled block.

The scheduler is *perf-neutral on a wide out-of-order
core* (Zen4 reorders the independent multiplies regardless of static
issue order) — it is a free, verified transform, not a guaranteed win.
The point of wiring it in is composability: the composed transform
carries **both** the denotation-equivalence (`scheduledThenPipeline_denote_eq`)
and the constant-time-preservation (`scheduledThenPipeline_ct_eq`)
certificates end-to-end.

`scheduleBlock` is *denotation-* and *CT-* preserving; the `applyPipeline`
passes are denotation-preserving (the `OptimizerPass` record carries only
`denote_eq`).  So the composed transform's CT certificate covers exactly
the scheduling half — that is the half this orchestrator introduces; the
algebraic passes' own CT story lives with each pass. -/

open CatCrypt.Crypto.Optimizer.SchedulerPass

/-- Schedule a hot block (`List BBStmt`) for ILP, then run the verified
    `LowCT → LowCT` pipeline on the scheduled block.  This is the
    emit entry point that composes the ILP scheduler with the existing
    Barrett/Montgomery/NTT passes (peephole + algebraic canonicalisation
    happen one IR up, on the VIR `Com jasminDialect`; see
    `Optimizer.Rewrite.ComPipeline`). -/
def scheduleThenPipeline (passes : List OptimizerPass) (b : List BBStmt) :
    LowCT :=
  applyPipeline passes (blockToCmd (scheduleBlock b))

/-- **Composed denotation equivalence (scheduler ∘ pipeline).**  The
    scheduled-and-optimised block reaches exactly the same final states as
    the original unscheduled block, for every fuel / leaf spec / start
    state.  Chains the scheduler's `scheduleBlock_denote_eq` with the
    pipeline's `applyPipeline_denote_eq`.  This is the formal KAT
    byte-identity guarantee for the composed transform. -/
theorem scheduledThenPipeline_denote_eq (passes : List OptimizerPass)
    (N : Nat) (leafSpec : LeafSpec) (b : List BBStmt) (rs rs' : RustState) :
    RustExec N leafSpec (scheduleThenPipeline passes b) rs rs'
  ↔ RustExec N leafSpec (blockToCmd b) rs rs' := by
  unfold scheduleThenPipeline
  -- pipeline half: applyPipeline preserves semantics
  rw [applyPipeline_denote_eq passes N leafSpec (blockToCmd (scheduleBlock b)) rs rs']
  -- scheduler half: scheduling preserves semantics
  exact scheduleBlock_denote_eq N leafSpec b rs rs'

/-- **CT preservation of the scheduling half.**  Scheduling reorders only
    public-structure straight-line statements, so the constant-time
    classification of the scheduled block equals that of the original.
    Instance of the scheduler's `scheduleBlock_isCT_eq` lifted to the
    composed entry point's input.  (The `applyPipeline` passes' CT story
    is each pass's own concern; this orchestrator's contribution — the
    reorder — is CT-neutral.) -/
theorem scheduled_ct_eq (lt : LevelTable) (leafCT : LeafCTTable)
    (b : List BBStmt) :
    cmdCT (blockToCmd (scheduleBlock b)) lt leafCT
  = cmdCT (blockToCmd b) lt leafCT :=
  scheduleBlock_isCT_eq lt leafCT b

/-! ## §7.6  Default `JForProg`-level optimisation pipeline

The composition for the typed VIR IR (`JForProg accTy`, a bounded for-loop
whose body is a `Com jasminDialect [accTy] accTy`). `optPipelineJ` sequences
four `JForProg → JForProg` analysis-then-apply stages. Each `apply*` function
(`applyCse`, `applyStrengthReduce`, `applyDce`, `RegisterAllocation.applyRA`)
returns its program argument and ignores the analysis result, so
`optPipelineJ p` is `p` definitionally, and `optPipelineJ_denote` and
`optPipelineJ_isCT` hold by rewriting with identity lemmas. They state no
property of any analysis. The program-changing passes are the `*Real.lean`
transforms (`DeadCodeElimReal`, `CommonSubexprElimReal`, …); the register
allocator with a semantic theorem is `physScanSpill`
(`toLprogPhysAbi_faithful_uniform`).

### Stages of `optPipelineJ` (each `apply*` is the identity)

Applied left-to-right:

1. **CSE / GVN** — `analyzeCse` then `applyCse`
   (`CommonSubexprElim.lean`); denote: `applyCse_denote_preserves`,
   CT: `applyCse_preserves_CT`.
2. **Strength reduction** — `analyzeStrengthReduce` then
   `applyStrengthReduce` (`StrengthReduce.lean`); denote:
   `applyStrengthReduce_denote_preserves`, CT:
   `applyStrengthReduce_preserves_CT`.
3. **Dead-code elimination** — `analyzeDce` then `applyDce`
   (`DeadCodeElim.lean`); denote: `applyDce_denote_preserves`, CT:
   `applyDce_preserves_CT`.
4. **Register allocation** — `linearScanRA` then
   `RegisterAllocation.applyRA` (`RegisterAllocation.lean`); denote:
   `linearScanRA_denote_preserves`, CT: `applyRA_preserves_CT`. Both hold for
   every allocation because `applyRA` is the identity.

`optPipelineJ_denote` and `optPipelineJ_isCT` carry no extra hypotheses,
because each stage is the identity.

### Passes composed elsewhere / deferred (and why)

* **Egraph equality-saturation + peephole** — composed in
  `Optimizer.Rewrite.ComPipeline.comAlgebraicPipeline`, over a bare
  `Com jasminDialect Γ t` (not `JForProg`).  Its preservation theorem
  `comAlgebraicPipeline_denote` is **conditional** on a known-constant
  environment consistent with the valuation (`KEnv.Consistent k V`), so it
  does not slot into the unconditional `JForProg → JForProg` chain.  It is
  the algebraic-canonicalisation stage that runs on the body `Com` before
  this loop-level pipeline; we re-export it as `optComAlgebraic` below for
  callers that have a `KEnv`, and chain it in `optPipelineJ_withAlgebraic`.
* **Loop unrolling** — `JForProgUnroll.lean` packages unrolling as a
  *witness* (`UnrolledBy p N` carrying the unrolled program + a
  `step_eq`/`factor_correct` proof), not as a total `JForProg → JForProg`
  function: the unrolled body Com is produced by the emit pass, not
  prescribed.  Its denotation lemma `UnrolledBy.denote_eq` therefore takes
  the witness; its CT lemma `unrollN_preserves_CT` additionally needs the
  emit-pass obligation `ctSafeJasmin u.unrolled.update … = true`.  We expose
  `optPipelineJ_afterUnroll` that chains the unroll witness in front of the
  core pipeline, taking the unroll witness as a hypothesis.
* **Verified vectorizer** — the lane-ring `scalarFold`
  construction (`LaneMap.lean`, `VectorReduce.lean`) is, like unrolling, a
  per-kernel construction with a `scalarFold_eq_hsum`-style equality rather
  than a uniform `JForProg → JForProg` rewrite; deferred for the same
  structural reason.
* **Instruction scheduler** — composed at the `LowCT` block level
  in `scheduleThenPipeline` / `scheduledThenPipeline_denote_eq` above
  (§7.5).  It reorders a `List BBStmt`, one IR down from `JForProg`, so it
  belongs to that entry point, not this one. -/

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgUnroll
open CatCrypt.Crypto.SecureCompilation.VIR.StrengthReduce
open CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
open CatCrypt.Crypto.SecureCompilation.VIR.CtPreservationNewTransforms
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph

/-- **The default `JForProg`-level optimisation pipeline.**

    Sequences four analysis-then-apply stages: CSE → strength reduction →
    dead-code elimination → register allocation. Each `apply*` function
    returns its program argument, so `optPipelineJ p` is `p`
    definitionally; the analyses are computed and discarded. -/
def optPipelineJ {accTy : JasminTy} (p : JForProg accTy) : JForProg accTy :=
  let p₁ := applyCse p (analyzeCse p)
  let p₂ := applyStrengthReduce p₁ (analyzeStrengthReduce p₁)
  let p₃ := applyDce p₂ (analyzeDce p₂)
  RegisterAllocation.applyRA p₃ (linearScanRA p₃)

/-- **End-to-end denotation preservation of `optPipelineJ`.**  The optimised
    program denotes exactly the same accumulator function as the input, for
    every initial accumulator.  Chains, in pipeline order,
    `applyCse_denote_preserves`, `applyStrengthReduce_denote_preserves`,
    `applyDce_denote_preserves`, and `linearScanRA_denote_preserves`.

    Carries no extra hypotheses: every stage is the identity, so the statement
    holds by `rfl` and constrains no analysis. -/
theorem optPipelineJ_denote {accTy : JasminTy} (p : JForProg accTy)
    (init : ⟦accTy⟧) :
    (optPipelineJ p).denote init = p.denote init := by
  unfold optPipelineJ
  -- peel passes from the outside in: RA, then DCE, then SR, then CSE
  rw [linearScanRA_denote_preserves, applyDce_denote_preserves,
      applyStrengthReduce_denote_preserves, applyCse_denote_preserves]

/-- **End-to-end constant-time preservation of `optPipelineJ`.**  The
    optimised program is CT-safe (under accumulator secrecy label `accL`)
    iff the input is — in particular if the input is CT-safe so is the
    output.  Chains the four per-pass CT-preservation lemmas
    (`applyRA_preserves_CT`, `applyDce_preserves_CT`,
    `applyStrengthReduce_preserves_CT`, `applyCse_preserves_CT`).

    Carries no extra hypotheses: every stage is the identity. -/
theorem optPipelineJ_isCT {accTy : JasminTy} (p : JForProg accTy)
    (accL : SecretLevel) :
    ctSafeJForProg (optPipelineJ p) accL = ctSafeJForProg p accL := by
  unfold optPipelineJ
  rw [applyRA_preserves_CT, applyDce_preserves_CT,
      applyStrengthReduce_preserves_CT, applyCse_preserves_CT]

/-- **CT-in ⇒ CT-out corollary.**  If the input loop is CT-safe, so is the
    optimised one.  Direct consequence of `optPipelineJ_isCT`. -/
theorem optPipelineJ_isCT_of {accTy : JasminTy} (p : JForProg accTy)
    (accL : SecretLevel) (h : ctSafeJForProg p accL = true) :
    ctSafeJForProg (optPipelineJ p) accL = true := by
  rw [optPipelineJ_isCT]; exact h

/-! ### §7.6.1  Composing the conditional stages

The algebraic-canonicalisation stage (egraph + peephole) and loop unrolling
are conditional and are exposed as chainable corollaries that thread their
hypotheses explicitly. -/

/-- Re-export of the algebraic-canonicalisation transform (peephole then
    bounded equality-saturation) on a body `Com`, from
    `Optimizer.Rewrite.ComPipeline`.  Conditional on a known-constant
    environment; see `optComAlgebraic_denote`. -/
abbrev optComAlgebraic {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    Com jasminDialect Γ t :=
  CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.comAlgebraicPipeline fuel c k

/-- The algebraic stage preserves denotation under a consistent
    known-constant environment.  Re-export of
    `ComPipeline.comAlgebraicPipeline_denote`. -/
theorem optComAlgebraic_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ)
    (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V) :
    (optComAlgebraic fuel c k).denote V = c.denote V :=
  CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline.comAlgebraicPipeline_denote fuel c k V hk

/-- **Unroll then core pipeline — denotation preservation.**  Given an
    `UnrolledBy p N` witness `u`, optimising the unrolled program with the
    core pipeline denotes the same function as the *original* (un-unrolled)
    program.  Chains `optPipelineJ_denote` on `u.unrolled` with the unroll
    witness's `UnrolledBy.denote_eq`.  The unroll witness is the explicit
    hypothesis (loop unrolling is a relation, not a total function — see the
    §7.6 deferral note). -/
theorem optPipelineJ_afterUnroll {accTy : JasminTy} {p : JForProg accTy}
    {N : Nat} (u : UnrolledBy p N) (init : ⟦accTy⟧) :
    (optPipelineJ u.unrolled).denote init = p.denote init := by
  rw [optPipelineJ_denote]
  exact u.denote_eq init

/-! ## §7.7  `JForProg`-level pass record (DCE packaged as a composable pass)

The §1 `OptimizerPass` record is `LowCT → LowCT`; the §7.6 pipeline
(`optPipelineJ`) instead composes the four unconditional analysis-and-rewrite
passes at the *typed VIR* level (`JForProg accTy`).  Those passes —
`applyCse`, `applyStrengthReduce`, `applyDce`, `applyRA` — are
`JForProg accTy → JForProg accTy` (modulo their analysis-decision argument),
not `LowCT → LowCT`, so they cannot inhabit `OptimizerPass`.

`JForProgPass` is the `JForProg`-level analogue of `OptimizerPass`: it bundles a
`rewrite : JForProg accTy → JForProg accTy` with the **same two obligations**
the §7.6 pipeline discharges per pass — a denotation-equivalence and a
constant-time-equivalence theorem.  Packaging `applyDce` (composed with its
analysis `analyzeDce`) as a `JForProgPass` value (`dcePass`) makes DCE a
*composable list element* of `applyJForProgPipeline`, whose
`applyJForProgPipeline_denote_eq` / `applyJForProgPipeline_ct_eq` meta-theorems
are the `JForProg`-level counterpart of `applyPipeline_denote_eq` (§3).  The
two obligations are discharged directly from `DeadCodeElim.applyDce`'s proved
`applyDce_denote_preserves` / `applyDce_preserves_CT`. -/

/-- A `JForProg`-level optimisation pass: a self-contained
    `JForProg accTy → JForProg accTy` rewrite (analysis already folded in)
    paired with its denotation- and constant-time-preservation theorems.
    The `JForProg` analogue of the §1 `OptimizerPass` (which is `LowCT`-typed). -/
structure JForProgPass (accTy : JasminTy) where
  /-- The (analysis-folded) rewrite. -/
  rewrite : JForProg accTy → JForProg accTy
  /-- Denotation preservation: the rewrite denotes the same accumulator
      function for every initial accumulator. -/
  denote_eq :
    ∀ (p : JForProg accTy) (init : ⟦accTy⟧),
      (rewrite p).denote init = p.denote init
  /-- Constant-time preservation: the rewrite leaves the CT classification
      (under accumulator secrecy label `accL`) unchanged. -/
  ct_eq :
    ∀ (p : JForProg accTy) (accL : SecretLevel),
      ctSafeJForProg (rewrite p) accL = ctSafeJForProg p accL

/-- **Dead-code elimination as a composable `JForProgPass`.**  Folds the
    analysis `analyzeDce` into the rewrite `applyDce`, discharging the
    record's denotation/CT obligations from `DeadCodeElim`'s proved
    `applyDce_denote_preserves` / `applyDce_preserves_CT`.  This is the pass
    `optPipelineJ` runs as its third stage, exposed as a stand-alone list
    element feeding `applyJForProgPipeline`. -/
def dcePass (accTy : JasminTy) : JForProgPass accTy where
  rewrite p := applyDce p (analyzeDce p)
  denote_eq p init := applyDce_denote_preserves p (analyzeDce p) init
  ct_eq p accL := applyDce_preserves_CT p (analyzeDce p) accL

/-- Apply a list of `JForProgPass` passes left-to-right.  The `JForProg`-level
    analogue of `applyPipeline` (§3). -/
def applyJForProgPipeline {accTy : JasminTy}
    (passes : List (JForProgPass accTy)) (p : JForProg accTy) : JForProg accTy :=
  passes.foldl (fun acc q => q.rewrite acc) p

/-- **Composed denotation equivalence for a `JForProgPass` pipeline.**  The
    `JForProg`-level counterpart of `applyPipeline_denote_eq` (§3): chains each
    pass's `denote_eq` by induction on the list. -/
theorem applyJForProgPipeline_denote_eq {accTy : JasminTy}
    (passes : List (JForProgPass accTy)) :
    ∀ (p : JForProg accTy) (init : ⟦accTy⟧),
      (applyJForProgPipeline passes p).denote init = p.denote init := by
  induction passes with
  | nil => intros; rfl
  | cons q qs ih =>
    intro p init
    have hU : applyJForProgPipeline (q :: qs) p
            = applyJForProgPipeline qs (q.rewrite p) := rfl
    rw [hU, ih (q.rewrite p) init, q.denote_eq p init]

/-- **Composed constant-time equivalence for a `JForProgPass` pipeline.**
    Chains each pass's `ct_eq` by induction on the list — in particular a
    CT-safe input stays CT-safe through the whole pipeline. -/
theorem applyJForProgPipeline_ct_eq {accTy : JasminTy}
    (passes : List (JForProgPass accTy)) :
    ∀ (p : JForProg accTy) (accL : SecretLevel),
      ctSafeJForProg (applyJForProgPipeline passes p) accL
    = ctSafeJForProg p accL := by
  induction passes with
  | nil => intros; rfl
  | cons q qs ih =>
    intro p accL
    have hU : applyJForProgPipeline (q :: qs) p
            = applyJForProgPipeline qs (q.rewrite p) := rfl
    rw [hU, ih (q.rewrite p) accL, q.ct_eq p accL]

/-! ## §8  Status -/

/-- This file is the orchestration layer.  Concrete passes land in
    sibling files (`BarrettReduce.lean`, `MontgomeryReduce.lean`,
    `SchedulerPass.lean`, …) and register themselves into the canonical
    pipelines above. -/
theorem pipeline_compiles : True := trivial

end CatCrypt.Crypto.Optimizer.Pipeline
