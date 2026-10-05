/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
public import CatCrypt.Crypto.Optimizer.ComCleanupPipeline

/-!
# The canonical `Com → Com` compiler optimizer (general pass)

This is the single optimizer every typed `Com jasminDialect` kernel flows
through before MLIR lowering.  It composes the two stages:

1. `ComPipeline.comAlgebraicPipeline fuel · k` — algebraic canonicalisation
   (peephole + `fuel`-bounded equality saturation under the known-constant
   environment `k`: `x+0 ↦ x`, `x*0 ↦ 0`, `x*2^k ↦ x<<<k`, …).
2. `ComCleanup.comCleanup k` — the clean-up stack: constant folding / partial
   evaluation (`ConstFold.foldCom`), structural CSE (`ComCSE.comCSE`),
   uncompute-after-last-use (`UncomputePass.uncompute`), then trailing
   dead-let elimination (`ComDCE.comDCE`).

Both stages carry (non-`rfl`) denotation-preservation proofs and run
under the same constant environment `k`, so they compose directly.  The result
is the general-purpose optimizer `comCanonical`, wired into the MLIR emit entry
`MLIRBackend.emitFuncCanon` so it applies to **every** emitted kernel.

## Guarantees

* `comCanonical_denote` — denotation preservation (every valuation consistent
  with `k`).  Chains `comAlgebraicPipeline_denote` and `comCleanup_denote`.
* `comCleanup_ctLeak_eq`, `comCanonical_ctLeak_eq` — under a leakage model
  whose `regArith` operations are quiet, equal leakage of the source at two
  valuations consistent with `k` gives equal leakage of the optimized kernel.
  Chains `comAlgebraicPipeline_ctLeak`, `foldCom_ctLeak_eq`, `comCSE_ctLeak`,
  `uncompute_ctLeak_eq` and `comDCE_ctLeak_eq`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ComCanonical

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
open CatCrypt.Crypto.Optimizer.ComCleanup

/-- The canonical general optimizer: algebraic canonicalisation, then the
    fold/CSE/uncompute/DCE clean-up stack, under the constant environment `k`. -/
def comCanonical {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) (c : Com jasminDialect Γ t) : Com jasminDialect Γ t :=
  comCleanup k (comAlgebraicPipeline fuel c k)

/-- **Denotation preservation** of the canonical optimizer: for every valuation
    consistent with the known-constant environment, the optimized kernel denotes
    exactly the source. -/
theorem comCanonical_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) (c : Com jasminDialect Γ t)
    (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V) :
    (comCanonical fuel k c).denote V = c.denote V := by
  unfold comCanonical
  rw [comCleanup_denote k (comAlgebraicPipeline fuel c k) V hk,
    comAlgebraicPipeline_denote fuel c k V hk]

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck

/-- **Leakage of the clean-up stack.** Under a leakage model whose `regArith` operations
    are quiet, equal leakage of `c` at two valuations consistent with `k` gives equal
    leakage of `comCleanup k c` there. -/
theorem comCleanup_ctLeak_eq (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (k : KEnv Γ) (c : Com jasminDialect Γ t) (V₁ V₂ : Ctxt.Valuation Γ)
    (h₁ : KEnv.Consistent k V₁) (h₂ : KEnv.Consistent k V₂)
    (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (comCleanup k c) V₁ = Com.ctLeak L (comCleanup k c) V₂ := by
  unfold comCleanup
  refine ComDCE.comDCE_ctLeak_eq L _ V₁ V₂ (UncomputePass.uncompute_ctLeak_eq L _ V₁ V₂ ?_)
  rw [ComCSE.comCSE_ctLeak, ComCSE.comCSE_ctLeak]
  exact ConstFold.foldCom_ctLeak_eq L hq c k V₁ V₂ h₁ h₂ h

/-- **Leakage of the canonical optimizer.** Under a leakage model whose `regArith`
    operations are quiet, equal leakage of `c` at two valuations consistent with `k`
    gives equal leakage of `comCanonical fuel k c` there. -/
theorem comCanonical_ctLeak_eq (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (fuel : Nat) (k : KEnv Γ) (c : Com jasminDialect Γ t)
    (V₁ V₂ : Ctxt.Valuation Γ) (h₁ : KEnv.Consistent k V₁) (h₂ : KEnv.Consistent k V₂)
    (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (comCanonical fuel k c) V₁ = Com.ctLeak L (comCanonical fuel k c) V₂ := by
  unfold comCanonical
  refine comCleanup_ctLeak_eq L hq k _ V₁ V₂ h₁ h₂ ?_
  rw [comAlgebraicPipeline_ctLeak L hq fuel c k V₁ h₁,
    comAlgebraicPipeline_ctLeak L hq fuel c k V₂ h₂]
  exact h

end Leak

end CatCrypt.Crypto.Optimizer.ComCanonical
