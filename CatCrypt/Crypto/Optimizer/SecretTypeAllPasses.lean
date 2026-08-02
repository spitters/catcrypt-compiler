/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.SecretTypePipeline
import CatCrypt.Crypto.Optimizer.SecretTypeScheduler
import CatCrypt.Crypto.Optimizer.SecretTypeX86

/-!
# Compositional CT, consolidated: every committed pass is declassify-monotone (#594 capstone)

This is the **capstone** of the #594 compositional-CT arc. The earlier files each
proved, for one optimizer pass, that it never raises the program's overall
secrecy level (its taint summary). They live at three *different* program
representations and so cannot be stated against a single Lean type:

| Pass | Representation | Taint env | Summary | Per-pass fact |
|------|----------------|-----------|---------|---------------|
| peephole `peepCom` | `Com jasminDialect` | `Taint Γ` | `comMaxTaint` | `peepCom_comMaxTaint` (=, exact) |
| egraph `saturateCom` | `Com jasminDialect` | `Taint Γ` | `comMaxTaint` | `saturateCom_comMaxTaint_le` (⊑ₛ) |
| canonicalize `comAlgebraicPipeline` | `Com jasminDialect` | `Taint Γ` | `comMaxTaint` | `comAlgebraicPipeline_comMaxTaint_le` (⊑ₛ) |
| ILP scheduler `scheduleBlock` | `List BBStmt` | `BBTaint` | `blockMaxTaint` | `scheduleBlock_blockMaxTaint_eq` (=, exact) |
| owned-x86 driver `optimizeX86Block` | `List (JInstr 64)` | `RegTaint × CellTaint` | `blockMaxTaintX` | `optimizeX86Block_blockMaxTaintX_le` (⊑ₛ) |

This file does **not** restate any of those proofs. It (1) gives a single,
representation-agnostic notion of a *declassify-monotone pass* — a transform
that, under *every* taint assignment, never moves the summary up the
`SecretLevel` lattice — and (2) consolidates the five committed facts into one
record `AllPassesMonotone`, each field being exactly the corresponding existing
lemma (so the bundle is non-vacuous by construction). The new content
is §3: because `⊑ₛ` is transitive, the **composition of any two same-summary
passes is itself declassify-monotone**, which is what makes "CT-preservation is
a compositional typing invariant" a *compositional* statement — the optimizer
may run these passes in any order/repetition and the secrecy budget is still
respected.

The summaries are scalars: peephole/scheduler/x86-forwarding preserve
them *exactly* (an equality, hence trivially `⊑ₛ`), while the egraph engine and
the composed canonicalize pipeline *declassify* (the `demoMulZero`
validation drops a binder `sec ↦ pub`). The `IsDeclassifyMonotone` predicate is
the common shape; equality facts feed it via `le_of_eq` (here
`SecretLevel.leq_of_eq`), so a single transitivity lemma covers all
combinations.

All goals closed.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SecretTypeAllPasses

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
open CatCrypt.Crypto.Optimizer.SchedulerPass
open CatCrypt.Crypto.Optimizer.SecretType
open CatCrypt.Crypto.Optimizer.SecretType.SecretLevel (leq leq_refl leq_trans)
open CatCrypt.Crypto.Optimizer.SecretTypeScheduler
open CatCrypt.Crypto.Optimizer.SecretTypeX86

/-! ## 0. `⊑ₛ` absorbs equalities

Equality is a special case of the lattice order, so an exact-preservation fact
(`= `) feeds the same `IsDeclassifyMonotone` shape as a strict declassification
(`⊑ₛ`). -/

/-- An equality of secrecy levels is, in particular, a `⊑ₛ`. -/
theorem SecretLevel.leq_of_eq {x y : SecretLevel} (h : x = y) : x ⊑ₛ y := by
  subst h; exact SecretLevel.leq_refl _

/-! ## 1. A representation-agnostic *declassify-monotone* pass

A pass on representation `Rep` with taint-environment type `Env` and overall
secrecy summary `μ : Env → Rep → SecretLevel` is **declassify-monotone** when,
under every taint assignment `E`, applying it never moves the summary up the
lattice: `μ E (f r) ⊑ₛ μ E r`. This is the single shape the per-representation
facts of §2 all instantiate (the exact-preservation ones via
`SecretLevel.leq_of_eq`). -/

/-- A transform `f : Rep → Rep` is **declassify-monotone** w.r.t. the secrecy
summary `μ : Env → Rep → SecretLevel` when, under every taint assignment, it
never raises the summary: `μ E (f r) ⊑ₛ μ E r`. The common shape of every
committed per-pass CT fact, regardless of representation. -/
def IsDeclassifyMonotone {Rep Env : Type _} (μ : Env → Rep → SecretLevel)
    (f : Rep → Rep) : Prop :=
  ∀ (E : Env) (r : Rep), μ E (f r) ⊑ₛ μ E r

namespace IsDeclassifyMonotone

variable {Rep Env : Type _} {μ : Env → Rep → SecretLevel}

/-- The identity pass is declassify-monotone (it changes nothing). -/
theorem id : IsDeclassifyMonotone μ (fun r => r) :=
  fun E r => leq_refl (μ E r)

/-- **Composition of two declassify-monotone passes is declassify-monotone.**
The compositional heart of the capstone: by transitivity of `⊑ₛ`, running `g`
after `f` still never raises the summary. Hence the optimizer may sequence any
two same-summary passes and the secrecy budget is preserved — CT-preservation
composes. -/
theorem comp {f g : Rep → Rep}
    (hf : IsDeclassifyMonotone μ f) (hg : IsDeclassifyMonotone μ g) :
    IsDeclassifyMonotone μ (fun r => g (f r)) :=
  fun E r => leq_trans (hg E (f r)) (hf E r)

/-- Iterating a declassify-monotone pass stays declassify-monotone. -/
theorem iterate {f : Rep → Rep} (hf : IsDeclassifyMonotone μ f) :
    ∀ (n : Nat), IsDeclassifyMonotone μ (fun r => f^[n] r)
  | 0 => IsDeclassifyMonotone.id
  | n + 1 => fun E r => by
      simp only [Function.iterate_succ', Function.comp_apply]
      exact leq_trans (hf E (f^[n] r)) (IsDeclassifyMonotone.iterate hf n E r)

end IsDeclassifyMonotone

/-! ## 2. The committed per-pass facts, each as a `IsDeclassifyMonotone` witness

Every witness below is *exactly* one of the committed lemmas, re-expressed in the
common shape. No proof is restated: the bodies are the cited lemmas (with
`leq_of_eq` turning the three exact-preservation equalities into `⊑ₛ`). The
`Com`-summary passes share env type `Taint Γ` and summary `comMaxTaint`; the
`BBStmt` pass uses `BBTaint`/`blockMaxTaint`; the owned-x86 pass uses the paired
`RegTaint × CellTaint` env and `blockMaxTaintX`. -/

/-- **Peephole is declassify-monotone** on `Com jasminDialect` (in fact exact).
Witness: `peepCom_comMaxTaint`. -/
theorem peepCom_monotone {Γ : Ctxt jasminDialect} {t : JasminTy} :
    IsDeclassifyMonotone (Rep := Com jasminDialect Γ t) (Env := Taint Γ)
      comMaxTaint (fun c => peepCom c) :=
  fun T c => SecretLevel.leq_of_eq (peepCom_comMaxTaint T c)

/-- **Bounded equality-saturation is declassify-monotone** on `Com jasminDialect`.
Witness: `saturateCom_comMaxTaint_le`. The summary drops on
`demoMulZero` (`sec ↦ pub`), so this is a strict `⊑ₛ`, not an equality. The known
constants `k` are a fixed parameter of the engine. -/
theorem saturateCom_monotone {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) :
    IsDeclassifyMonotone (Rep := Com jasminDialect Γ t) (Env := Taint Γ)
      comMaxTaint (fun c => saturateCom fuel c k) :=
  fun T c => saturateCom_comMaxTaint_le fuel T c k

/-- **The canonicalize pipeline (peephole then saturation) is declassify-monotone**
on `Com jasminDialect`. Witness: `comAlgebraicPipeline_comMaxTaint_le`. This is
itself the composition of the two `Com`-passes above — see
`canonicalize_eq_comp` below for the explicit composition view. -/
theorem comAlgebraicPipeline_monotone {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) :
    IsDeclassifyMonotone (Rep := Com jasminDialect Γ t) (Env := Taint Γ)
      comMaxTaint (fun c => comAlgebraicPipeline fuel c k) :=
  fun T c => comAlgebraicPipeline_comMaxTaint_le fuel T c k

/-- **The ILP scheduler is declassify-monotone** on `List BBStmt` (in fact exact:
a pure reorder). Witness: `scheduleBlock_blockMaxTaint_eq`. -/
theorem scheduleBlock_monotone :
    IsDeclassifyMonotone (Rep := List BBStmt) (Env := BBTaint)
      blockMaxTaint (fun b => scheduleBlock b) :=
  fun T b => SecretLevel.leq_of_eq (scheduleBlock_blockMaxTaint_eq T b)

/-- **The owned-x86 driver is declassify-monotone** on `List (JInstr 64)`:
forwarding copies a value where it already flows, and the two shrinking peepholes
delete instructions, dropping contributions from the running join. Witness:
`optimizeX86Block_blockMaxTaintX_le`. The taint env is the pair `RegTaint ×
CellTaint`, so the summary is uncurried over the pair. -/
theorem optimizeX86Block_monotone :
    IsDeclassifyMonotone (Rep := List (JInstr 64)) (Env := RegTaint × CellTaint)
      (fun E b => blockMaxTaintX E.1 E.2 b)
      (fun b => CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline.optimizeX86Block b) :=
  fun E b => optimizeX86Block_blockMaxTaintX_le E.1 E.2 b

/-! ## 3. The capstone bundle and the compositional theorem

`AllPassesMonotone` collects the five committed facts in their common shape. Its
fields are *exactly* the witnesses of §2 (no new proof obligation), so the
record is non-vacuous: it is inhabited precisely because each committed lemma
holds. The accompanying instances `allPassesMonotone` build that single witness.

The compositional payoff is then immediate from §1's `IsDeclassifyMonotone.comp`:
any two same-representation passes compose to a declassify-monotone pass — which
is the formal meaning of "CT-preservation is a *compositional* typing invariant
across all passes". -/

/-- **The #594 capstone bundle.** Every committed optimizer pass is
declassify-monotone w.r.t. its representation's secrecy summary. The fields are
the five committed per-pass facts (§2), recorded in the common
`IsDeclassifyMonotone` shape. Parameterised over the `Com`-pass data (`Γ`, `t`,
`fuel`, `k`) that those facts quantify; the `BBStmt`/`x86` passes take no such
parameter. -/
structure AllPassesMonotone {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) : Prop where
  /-- Peephole preserves the `Com` summary (`peepCom_comMaxTaint`). -/
  peephole : IsDeclassifyMonotone (Rep := Com jasminDialect Γ t) (Env := Taint Γ)
    comMaxTaint (fun c => peepCom c)
  /-- Equality-saturation declassifies the `Com` summary
    (`saturateCom_comMaxTaint_le`). -/
  saturate : IsDeclassifyMonotone (Rep := Com jasminDialect Γ t) (Env := Taint Γ)
    comMaxTaint (fun c => saturateCom fuel c k)
  /-- The canonicalize pipeline declassifies the `Com` summary
    (`comAlgebraicPipeline_comMaxTaint_le`). -/
  canonicalize : IsDeclassifyMonotone (Rep := Com jasminDialect Γ t) (Env := Taint Γ)
    comMaxTaint (fun c => comAlgebraicPipeline fuel c k)
  /-- The scheduler preserves the `BBStmt` summary
    (`scheduleBlock_blockMaxTaint_eq`). -/
  scheduler : IsDeclassifyMonotone (Rep := List BBStmt) (Env := BBTaint)
    blockMaxTaint (fun b => scheduleBlock b)
  /-- The owned-x86 driver declassifies the `JInstr` summary
    (`optimizeX86Block_blockMaxTaintX_le`). -/
  x86Backend : IsDeclassifyMonotone (Rep := List (JInstr 64)) (Env := RegTaint × CellTaint)
    (fun E b => blockMaxTaintX E.1 E.2 b)
    (fun b => CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline.optimizeX86Block b)

/-- **The capstone bundle is inhabited: every committed pass is
declassify-monotone.** Each field is exactly the corresponding committed lemma
(via the §2 witnesses). This is the consolidated statement of "CT-preservation
as a compositional typing invariant across all passes" (#594). -/
theorem allPassesMonotone {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) : AllPassesMonotone (Γ := Γ) (t := t) fuel k where
  peephole := peepCom_monotone
  saturate := saturateCom_monotone fuel k
  canonicalize := comAlgebraicPipeline_monotone fuel k
  scheduler := scheduleBlock_monotone
  x86Backend := optimizeX86Block_monotone

/-! ### The compositional corollaries

For each representation, the composition of any two of its declassify-monotone
passes is again declassify-monotone — the compositional-CT invariant. We state
the corollaries directly from the bundle. -/

/-- **Two `Com`-passes compose to a declassify-monotone pass.** Concretely:
running the egraph saturation after the peephole never raises the `Com` summary.
By `IsDeclassifyMonotone.comp` over the two `Com`-summary fields of the bundle.
(The composed transform is, up to `comAlgebraicPipeline`'s definition, the
canonicalize pass — see `canonicalize_eq_comp`.) -/
theorem peephole_then_saturate_monotone {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) :
    IsDeclassifyMonotone (Rep := Com jasminDialect Γ t) (Env := Taint Γ)
      comMaxTaint (fun c => saturateCom fuel (peepCom c) k) :=
  ((allPassesMonotone fuel k).peephole.comp (allPassesMonotone fuel k).saturate)

/-- The canonicalize pass *is* the composition of peephole and saturation, so its
declassify-monotonicity is an instance of the generic composition law applied to
the two committed `Com`-pass facts — not an independent assumption. -/
theorem canonicalize_eq_comp {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) (c : Com jasminDialect Γ t) :
    comAlgebraicPipeline fuel c k = saturateCom fuel (peepCom c) k := rfl

/-- **Iterating any `Com`-pass stays declassify-monotone.** E.g. running the
egraph saturation `n` times never raises the summary. -/
theorem saturate_iterate_monotone {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) (n : Nat) :
    IsDeclassifyMonotone (Rep := Com jasminDialect Γ t) (Env := Taint Γ)
      comMaxTaint (fun c => (fun c' => saturateCom fuel c' k)^[n] c) :=
  (allPassesMonotone fuel k).saturate.iterate n

/-- **Two scheduler passes compose to a declassify-monotone pass** on `List BBStmt`
(in fact still exact). By `IsDeclassifyMonotone.comp` on the scheduler field. -/
theorem scheduler_comp_monotone :
    IsDeclassifyMonotone (Rep := List BBStmt) (Env := BBTaint)
      blockMaxTaint (fun b => scheduleBlock (scheduleBlock b)) :=
  (allPassesMonotone 0 (Γ := []) (t := .reg 32) KEnv.nil).scheduler.comp
    (allPassesMonotone 0 (Γ := []) (t := .reg 32) KEnv.nil).scheduler

/-- **Two owned-x86 driver passes compose to a declassify-monotone pass** on
`List (JInstr 64)`. By `IsDeclassifyMonotone.comp` on the x86 field. -/
theorem x86Backend_comp_monotone :
    IsDeclassifyMonotone (Rep := List (JInstr 64)) (Env := RegTaint × CellTaint)
      (fun E b => blockMaxTaintX E.1 E.2 b)
      (fun b => CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline.optimizeX86Block
        (CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline.optimizeX86Block b)) :=
  (allPassesMonotone 0 (Γ := []) (t := .reg 32) KEnv.nil).x86Backend.comp
    (allPassesMonotone 0 (Γ := []) (t := .reg 32) KEnv.nil).x86Backend

/-! ## 4. Validation: the capstone re-derives the demo declassification

Composing peephole then saturation on the egraph `demoMulZero` strictly
declassifies the program's overall secrecy level `sec ↦ pub` — well within the
`⊑ₛ` budget the capstone composition law guarantees. This exercises the §3
composition corollary on concrete data. -/

/-- The composed peephole-then-saturate pass declassifies the demo's summary from
`sec` to `pub` (peephole no-op, saturation drops the secret), and the composition
law `peephole_then_saturate_monotone` certifies it never raises it. -/
example :
    comMaxTaint egDemoTaint (saturateCom 4 (peepCom demoMulZero) demoK)
      ⊑ₛ comMaxTaint egDemoTaint demoMulZero :=
  peephole_then_saturate_monotone 4 demoK egDemoTaint demoMulZero

end CatCrypt.Crypto.Optimizer.SecretTypeAllPasses
