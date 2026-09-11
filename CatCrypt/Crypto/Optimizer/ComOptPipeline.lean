/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.Peephole
public import CatCrypt.Crypto.Optimizer.CopyProp
public import CatCrypt.Crypto.Optimizer.ComDCE

/-!
# The `Com → Com` optimizer pipeline (#555/#566 integration)

This file *rounds out and wires together* the three newly-landed,
denotation-preserving `Com → Com` passes over the typed VIR `jasminDialect`
into a single pipeline, with one end-to-end denotation-preservation
meta-theorem.

The composed passes (each already carries its own genuine, non-`rfl`
preservation proof; we reuse those lemmas verbatim and do **not** restate
them):

* `peepCom`  (`Optimizer/Rewrite/Peephole.lean`) — local syntactic
  canonicalisation (`a - a ↦ a ^^^ a`, `a &&& a ↦ a ||| a`). Lemma
  `peepCom_denote`.
* `copyProp` (`Optimizer/CopyProp.lean`) — copy propagation through self-`or`
  register aliases (`let z = a ||| a` redirects uses of `z` to `a`). Lemma
  `copyProp_denote`.
* `comDCE`   (`Optimizer/ComDCE.lean`) — trailing dead-let elimination (drops
  the now-dead copy bindings). Lemma `comDCE_denote`.

## The pipeline

`comOptPipeline := comDCE ∘ copyProp ∘ peepCom`: the classic clean-up
sequence — peephole-canonicalise first, then copy-propagate (which redirects
uses of register copies past their now-dead binders), then drop the dead
copy bindings with DCE.

All three passes share the identical signature
`Com jasminDialect Γ t → Com jasminDialect Γ t` (`comDCE` is dialect-generic
and specialises to it here), so they compose directly with no reindex
adapter.

## The meta-theorem

`comOptPipeline_denote : (comOptPipeline c).denote V = c.denote V`, obtained by
`Eq.trans`-chaining the three component `*_denote` lemmas. **Not `rfl`** — it
inherits the genuine inductive preservation proofs of the components.

We also record `comOptPipeline_ctSafe`: the whole pipeline preserves
constant-time safety (the dialect is branch-free; via the components'
`*_ctSafe` corollaries).

All goals closed. No `sorry`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ComOptPipeline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole
open CatCrypt.Crypto.Optimizer.CopyProp
open CatCrypt.Crypto.Optimizer.ComDCE

/-! ## 1. The pipeline -/

/-- The `Com → Com` optimizer pipeline: peephole-canonicalise, then
copy-propagate, then dead-let-eliminate. The classic clean-up order — copy
propagation makes the copy bindings dead, and DCE then removes them. -/
def comOptPipeline {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Com jasminDialect Γ t :=
  comDCE ∘ copyProp ∘ peepCom

/-! ## 2. The end-to-end denotation-preservation meta-theorem -/

/-- **End-to-end denotation preservation for the optimizer pipeline.**
`(comOptPipeline c).denote V = c.denote V` for every valuation `V`. Obtained by
transitively chaining the three component preservation lemmas
(`comDCE_denote`, `copyProp_denote`, `peepCom_denote`) — each itself a genuine
induction over the `Com` let-chain, **not** `rfl`. -/
theorem comOptPipeline_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    (comOptPipeline c).denote V = c.denote V :=
  -- comDCE (copyProp (peepCom c))  =  copyProp (peepCom c)  =  peepCom c  =  c
  (comDCE_denote (copyProp (peepCom c)) V).trans
    ((copyProp_denote (peepCom c) V).trans
      (peepCom_denote c V))

/-! ## 3. Constant-time preservation corollary

Each component preserves CT-safety on `jasminDialect` (the dialect is
branch-free). Chaining their `*_ctSafe` corollaries gives the same for the
whole pipeline. -/

/-- **The pipeline preserves constant-time safety.** Via the components'
`*_ctSafe` corollaries (the dialect has no conditional op, so every `Com` —
before or after any pass — is CT-safe). -/
theorem comOptPipeline_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) :
    ctSafeComJ (comOptPipeline c) = ctSafeComJ c := by
  -- every Com over the branch-free dialect is CT-safe
  rw [ctSafeComJ_true (comOptPipeline c), ctSafeComJ_true c]

/-! ## 4. Self-contained validation

We exercise the pipeline on a program that hits all three passes in sequence:

    let z = x ||| x      -- a register copy of x  (copyProp source)
    let d = x - x        -- a self-subtract (peephole: ↦ xor x x, → 0)
    ret z                -- returns the copy; d is a dead trailing binder

Peephole canonicalises `x - x ↦ x ^^^ x`; copy propagation redirects the
return through the `z = x ||| x` alias; DCE drops the now-dead trailing
binder. Denotation is preserved end-to-end (both map `x` to `x`). -/

/-- The pipeline demo: `let z = x|||x; let d = x-x; ret z`. -/
def demoPipeline : Com jasminDialect [.reg 32] (.reg 32) :=
  -- z = x ||| x   (x is `.here`)
  .var (binE .or .here .here)
    -- d = x - x    (x is `.there .here` here)
    (.var (binE .sub (.there .here) (.there .here))
      -- ret z      (z is `.there .here` here, skipping d)
      (.ret (.there .here)))

/-- **Denotation preserved end-to-end** on the demo, via the meta-theorem.
Both the input and the fully-optimized program map `x` to `x`. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (comOptPipeline demoPipeline).denote V = demoPipeline.denote V :=
  comOptPipeline_denote demoPipeline V

/-- Concretely, on `x = 42`, the input denotes `42`. -/
example : demoPipeline.denote (.cons (42 : BitVec 32) .nil) = (42 : BitVec 32) := rfl

/-- And so does the fully-optimized program. -/
example :
    (comOptPipeline demoPipeline).denote (.cons (42 : BitVec 32) .nil)
      = (42 : BitVec 32) := rfl

/-- **CT preserved** on the demo. -/
example : ctSafeComJ (comOptPipeline demoPipeline) = ctSafeComJ demoPipeline :=
  comOptPipeline_ctSafe demoPipeline

/-- A bare `ret` program is a pipeline fixpoint. -/
example :
    comOptPipeline (Com.ret (Γ := [JasminTy.reg 8]) (t := JasminTy.reg 8) .here)
      = Com.ret .here := rfl

end CatCrypt.Crypto.Optimizer.ComOptPipeline
