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
* `comCanonical_ctSafe` — both sides are `true` by `ctSafeComJ_true`, so the
  statement carries no information about leakage. The leakage of the
  algebraic stage is `comAlgebraicPipeline_ctLeak`; the clean-up stack has no
  leakage theorem for its CSE and uncompute passes.
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

/-- The structural predicate `ctSafeComJ` agrees on the optimized kernel and the
    source. `ctSafeComJ` is `true` on every program (`ctSafeComJ_true`), so the
    statement carries no information about leakage. -/
theorem comCanonical_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) (c : Com jasminDialect Γ t) :
    ctSafeComJ (comCanonical fuel k c) = ctSafeComJ c := by
  rw [ctSafeComJ_true (comCanonical fuel k c), ctSafeComJ_true c]

end CatCrypt.Crypto.Optimizer.ComCanonical
