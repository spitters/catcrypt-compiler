/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.TranslationValidationEgraph
public import CatCrypt.Crypto.Optimizer.TranslationValidationSched

/-!
# The master verified translation-validation checker

This module unifies the verified
translation-validation (TV) checkers into a single master checker plus
soundness theorem.  The methodology throughout is the same: an *untrusted*
optimizer oracle proposes a candidate program, and a small *verified* Boolean
acceptance check certifies — or rejects — the candidate.  The optimizer is never
in the TCB; only the checker and its soundness lemma are.

## The committed pieces

* `TranslationValidation.tvCheck` / `tvCheck_sound` — `Com jasminDialect`-level:
  the candidate is structurally the input or the verified local peephole output.
* `TranslationValidation.tvCheckCanon` / `tvCheckCanon_sound` —
  `Com jasminDialect`-level: the candidate is the full algebraic canonicalisation
  pipeline `comAlgebraicPipeline` (peephole then bounded equality-saturation
  under a known-constant environment).
* `TranslationValidationSched.tvCheckSched` / `tvCheckSched_sound` —
  `List BBStmt` / `RustExec`-level: the candidate is the input unchanged or the
  verified latency-aware `scheduleBlock` schedule.

## The representation split

The first two checkers share the `Com jasminDialect Γ t` representation and a
single denotation notion `Com.denote`, so they unify into one
`Com`-level disjunction.  `tvCheckAny` accepts the candidate when it is the
identity, the peephole, *or* the full canonicalise pipeline.

`tvCheckSched`, by contrast, lives at the `List BBStmt` representation lowered to
`LowCT` by `blockToCmd`, with soundness phrased over the big-step relation
`RustExec`.  `Com jasminDialect` and `LowCT` are *distinct* inductive families
with *distinct* denotation notions, so a single Boolean disjunction cannot
literally range over both.  We therefore **do not force-unify across
representations**: `tvCheckSched` is re-exported here as the block-level master
checker (`tvCheckBlockMaster`), alongside the `Com`-level `tvCheckAny`.

## What is proved

* `tvCheckAny_sound` — the headline `Com`-level master soundness:
  `tvCheckAny fuel k c c' = true → ∀ V, KEnv.Consistent k V → c'.denote V =
  c.denote V`.  Proved by case-splitting the `||` and dispatching to
  `tvCheck_sound` (identity/peephole arm, no consistency needed) and
  `tvCheckCanon_sound` (canonicalise arm, which requires the threaded
  `KEnv.Consistent k V` hypothesis).
* `tvCheckBlockMaster_sound` — the block-level master soundness, a re-export of
  `tvCheckSched_sound` at the `List BBStmt` / `RustExec` representation.

Both are sound and incomplete: each certifies only its conservative accepted
relation, but neither ever certifies a candidate that changes the denotation.
The accepted relation widens — more verified rewrites, the canonicalisation
pipeline, the latency schedule — without enlarging the TCB, because each arm
carries its own soundness lemma.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.TranslationValidationAll

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
open CatCrypt.Crypto.Optimizer.TranslationValidation

/-! ## §1  The `Com`-level master checker

`tvCheck` and `tvCheckCanon` share the `Com jasminDialect Γ t` representation and
the single denotation notion `Com.denote`, so they unify into one disjunction. -/

/-- **The `Com`-level master TV checker.**  Accepts the candidate `c'`
(output of an untrusted optimizer oracle) against the input `c` when *any* of the
verified `Com`-level acceptance arms fires: `c'` is structurally the input
itself, the verified local peephole canonicalisation `peepCom c`, *or* the full
algebraic canonicalisation pipeline `comAlgebraicPipeline fuel c k`.  Decidable,
hence executable as a checker; reuses the already-verified `tvCheck` and
`tvCheckCanon`. -/
def tvCheckAny {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) (c c' : Com jasminDialect Γ t) : Bool :=
  tvCheck c c' || tvCheckCanon fuel k c c'

/-- **Soundness of the `Com`-level master TV checker.**  If
`tvCheckAny fuel k c c' = true`, then for every valuation `V` for which the
known-constant environment `k` is consistent, the candidate `c'` denotes the same
function as the input `c`.  The optimizer that produced `c'` is *not* trusted:
the result is certified by case-splitting the disjunction and dispatching to the
already-verified `tvCheck_sound` (identity/peephole arm) and `tvCheckCanon_sound`
(algebraic-canonicalisation arm, which consumes the threaded `KEnv.Consistent k
V` hypothesis).  Incomplete (only the union of the conservative per-arm relations
is accepted) but never unsound. -/
theorem tvCheckAny_sound {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) (c c' : Com jasminDialect Γ t)
    (h : tvCheckAny fuel k c c' = true) :
    ∀ V : Ctxt.Valuation Γ, KEnv.Consistent k V → c'.denote V = c.denote V := by
  intro V hk
  simp only [tvCheckAny, Bool.or_eq_true] at h
  rcases h with h | h
  · -- identity / peephole arm: no consistency hypothesis needed
    exact tvCheck_sound c c' h V
  · -- algebraic-canonicalisation arm: thread `KEnv.Consistent k V`
    exact tvCheckCanon_sound fuel k c c' h V hk

/-! ## §2  The block-level master checker (distinct representation)

`tvCheckSched` lives at `List BBStmt` / `RustExec`, a *different* inductive
family and denotation notion from `Com jasminDialect` / `Com.denote`.  We do not
force-unify across representations; instead we re-export the scheduler checker as
the block-level master. -/

/-- **The block-level master TV checker.**  A re-export of the verified
schedule-aware checker `TranslationValidationSched.tvCheckSched`, which lives at
the `List BBStmt` representation (lowered to `LowCT` by `blockToCmd`, with
soundness over the big-step `RustExec` relation).  It accepts the candidate block
when it is structurally the input or the verified latency-aware `scheduleBlock`
schedule.  This is the block-level counterpart of `tvCheckAny`; the two operate
on distinct representations and are intentionally kept separate. -/
def tvCheckBlockMaster
    (b b' : List CatCrypt.Crypto.Optimizer.SchedulerPass.BBStmt) : Bool :=
  TranslationValidationSched.tvCheckSched b b'

/-- **Soundness of the block-level master TV checker.**  A re-export of
`TranslationValidationSched.tvCheckSched_sound`: if `tvCheckBlockMaster b b' =
true`, the candidate block `b'` lowers to a program reaching exactly the same
final states as the input `b` under the big-step `RustExec` semantics, for every
leaf spec and start state.  Stated at the `List BBStmt` / `RustExec`
representation, where the scheduler's soundness composes cleanly. -/
theorem tvCheckBlockMaster_sound (N : Nat)
    (leafSpec : CatCrypt.Crypto.Jasmin.LowCT.LeafSpec)
    (b b' : List CatCrypt.Crypto.Optimizer.SchedulerPass.BBStmt)
    (h : tvCheckBlockMaster b b' = true)
    (rs rs' : CatCrypt.Crypto.Jasmin.LowCT.RustState) :
    CatCrypt.Crypto.Jasmin.LowCT.RustExec N leafSpec
        (CatCrypt.Crypto.Optimizer.SchedulerPass.blockToCmd b') rs rs'
  ↔ CatCrypt.Crypto.Jasmin.LowCT.RustExec N leafSpec
        (CatCrypt.Crypto.Optimizer.SchedulerPass.blockToCmd b) rs rs' :=
  TranslationValidationSched.tvCheckSched_sound N leafSpec b b' h rs rs'

/-! ## §3  Self-contained validation

The master checker subsumes every individual arm of the committed pieces. -/

/-- **Accept (identity arm, via `tvCheck`).**  The optimizer that returns its
input unchanged is certified by the master checker. -/
example : tvCheckAny 4 demoK demoSelfSub demoSelfSub = true := by decide

/-- **Accept (canonicalisation arm, via `tvCheckCanon`).**  A candidate equal to
the full algebraic canonicalisation of the demo is certified by the master
checker — exercising the disjunct that the base `tvCheck` does *not* cover. -/
example :
    tvCheckAny 4 demoK demoMulZero (comAlgebraicPipeline 4 demoMulZero demoK)
      = true := by
  decide

/-- The master soundness theorem applied to the canonicalisation demo: the
accepted candidate denotes the same function as the input. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (comAlgebraicPipeline 4 demoMulZero demoK).denote V = demoMulZero.denote V :=
  tvCheckAny_sound 4 demoK demoMulZero _ (by decide) V (demoK_consistent V)

end CatCrypt.Crypto.Optimizer.TranslationValidationAll
