/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
public import CatCrypt.Crypto.Optimizer.CopyProp
public import CatCrypt.Crypto.Optimizer.ComDCE

/-!
# The full `Com → Com` optimizer pipeline

This module composes **all** the denotation-preserving `Com → Com`
clean-up passes over the typed VIR `jasminDialect` into a single full
pipeline, with one end-to-end denotation-preservation meta-theorem. It is the
generic optimizer that kernels flow through.

The composed passes (each already carries its own non-`rfl`
preservation proof; we reuse those lemmas verbatim and do **not** restate
them):

* `comAlgebraicPipeline fuel · k`
  (`Optimizer/Rewrite/ComPipeline.lean`) — the algebraic-canonicalisation
  stage: peephole (`a - a ↦ a ^^^ a`, `a &&& a ↦ a ||| a`) then `fuel`-bounded
  equality saturation (`x + 0 ↦ x`, `x * 0 ↦ 0`, …) under the known-constant
  environment `k`. Lemma `comAlgebraicPipeline_denote` — needs a
  `KEnv.Consistent k V` hypothesis (the saturation engine reasons under `k`).
* `copyProp` (`Optimizer/CopyProp.lean`) — copy propagation through self-`or`
  register aliases (`let z = a ||| a` redirects uses of `z` to `a`). Lemma
  `copyProp_denote`.
* `comDCE`   (`Optimizer/ComDCE.lean`) — trailing dead-let elimination (drops
  the dead copy bindings). Lemma `comDCE_denote`.

## The pipeline

`comFullOpt fuel k := comDCE ∘ copyProp ∘ (comAlgebraicPipeline fuel · k)`:
algebraic-canonicalise first (peephole + equality saturation), then
copy-propagate (which redirects uses of register copies past their binders,
which become dead), then drop the dead copy bindings with DCE. This subsumes the
peephole-only front of `Optimizer/ComOptPipeline.lean`'s `comOptPipeline` by
running the full equality-saturation engine in the canonicalisation stage.

The `copyProp`/`comDCE` passes share the signature
`Com jasminDialect Γ t → Com jasminDialect Γ t` (`comDCE` is dialect-generic
and specialises to it here), and `comAlgebraicPipeline fuel · k` does too once
the constant environment `k` is fixed, so they compose directly with no
reindex adapter.

## The meta-theorem

`comFullOpt_denote : ∀ V, KEnv.Consistent k V → (comFullOpt fuel k c).denote V
= c.denote V`, obtained by `Eq.trans`-chaining the three component `*_denote`
lemmas. The `comAlgebraicPipeline` arm consumes the `KEnv.Consistent k V`
hypothesis exactly as `comAlgebraicPipeline_denote` requires. **Not `rfl`** —
it inherits the inductive/saturation preservation proofs of the
components.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ComFullOpt

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
open CatCrypt.Crypto.Optimizer.CopyProp
open CatCrypt.Crypto.Optimizer.ComDCE

/-! ## 1. The full pipeline -/

/-- The full `Com → Com` optimizer pipeline: algebraic-canonicalise (peephole +
`fuel`-bounded equality saturation under the known-constant environment `k`),
then copy-propagate, then dead-let-eliminate. The classic clean-up order — copy
propagation makes the copy bindings dead, and DCE then removes them. -/
def comFullOpt {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) :
    Com jasminDialect Γ t → Com jasminDialect Γ t :=
  comDCE ∘ copyProp ∘ (fun c => comAlgebraicPipeline fuel c k)

/-! ## 2. The end-to-end denotation-preservation meta-theorem -/

/-- **End-to-end denotation preservation for the full optimizer pipeline.**
For every valuation `V` consistent with the known-constant environment `k`,
`(comFullOpt fuel k c).denote V = c.denote V`. Obtained by transitively chaining
the three component preservation lemmas (`comDCE_denote`, `copyProp_denote`,
`comAlgebraicPipeline_denote`) — the last consumes the `KEnv.Consistent k V`
hypothesis, and each component is itself an induction / equality
saturation over the `Com` let-chain, **not** `rfl`. -/
theorem comFullOpt_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) (c : Com jasminDialect Γ t)
    (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V) :
    (comFullOpt fuel k c).denote V = c.denote V :=
  -- comDCE (copyProp (alg c))  =  copyProp (alg c)  =  alg c  =  c
  (comDCE_denote (copyProp (comAlgebraicPipeline fuel c k)) V).trans
    ((copyProp_denote (comAlgebraicPipeline fuel c k) V).trans
      (comAlgebraicPipeline_denote fuel c k V hk))

/-! ## 3. Self-contained validation

We exercise the full pipeline on the same program as
`Optimizer/ComOptPipeline.lean`'s demo, under the known-constant
environment of `Egraph.demoMulZero` / `CopyProp.demoCopy` style — here using a
trivial empty-constant environment that is consistent with every valuation, so
the algebraic stage's saturation simply finds no constants to fire and the
peephole/copyprop/DCE stages do the work. Denotation is preserved end-to-end. -/

/-- The full pipeline preserves the denotation of `CopyProp.demoCopy`
(`let z = x|||x; let w = z+z; ret w`) under any `k`/`V`-consistent pair. The
algebraic stage leaves it (no firing constant), copy-propagation redirects the
uses of the `z = x|||x` alias, and DCE drops the dead copy binder. -/
example (k : KEnv [.reg 32]) (V : Ctxt.Valuation (d := jasminDialect) [.reg 32])
    (hk : KEnv.Consistent k V) :
    (comFullOpt 4 k demoCopy).denote V = demoCopy.denote V :=
  comFullOpt_denote 4 k demoCopy V hk

/-- The full pipeline preserves the denotation of `ComDCE.demoDeadTrailing`
(`v0 = x+x; v1 = x+x; ret v0`) under any `k`/`V`-consistent pair: the dead
trailing binder `v1` is dropped by the DCE stage. -/
example (k : KEnv [.reg 32]) (V : Ctxt.Valuation (d := jasminDialect) [.reg 32])
    (hk : KEnv.Consistent k V) :
    (comFullOpt 4 k demoDeadTrailing).denote V = demoDeadTrailing.denote V :=
  comFullOpt_denote 4 k demoDeadTrailing V hk

end CatCrypt.Crypto.Optimizer.ComFullOpt
