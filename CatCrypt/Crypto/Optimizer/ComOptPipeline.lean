/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.Peephole
public import CatCrypt.Crypto.Optimizer.CopyProp
public import CatCrypt.Crypto.Optimizer.ComDCE
public import CatCrypt.Crypto.Optimizer.Rewrite.ComGVN

/-!
# The `Com → Com` optimizer pipeline

This module composes three denotation-preserving `Com → Com` passes over the
typed VIR `jasminDialect` into a single pipeline, with one end-to-end
denotation-preservation meta-theorem.

The composed passes (each already carries its own non-`rfl`
preservation proof; we reuse those lemmas verbatim and do **not** restate
them):

* `peepCom`  (`Optimizer/Rewrite/Peephole.lean`) — local syntactic
  canonicalisation (`a - a ↦ a ^^^ a`, `a &&& a ↦ a ||| a`). Lemma
  `peepCom_denote`.
* `copyProp` (`Optimizer/CopyProp.lean`) — copy propagation through self-`or`
  register aliases (`let z = a ||| a` redirects uses of `z` to `a`). Lemma
  `copyProp_denote`.
* `comDCE`   (`Optimizer/ComDCE.lean`) — trailing dead-let elimination (drops
  the dead copy bindings). Lemma `comDCE_denote`.

## The pipeline

`comOptPipeline := comDCE ∘ copyProp ∘ peepCom`: the classic clean-up
sequence — peephole-canonicalise first, then copy-propagate (which redirects
uses of register copies past their binders, which become dead), then drop the dead
copy bindings with DCE.

All three passes share the identical signature
`Com jasminDialect Γ t → Com jasminDialect Γ t` (`comDCE` is dialect-generic
and specialises to it here), so they compose directly with no reindex
adapter.

## The meta-theorem

`comOptPipeline_denote : (comOptPipeline c).denote V = c.denote V`, obtained by
`Eq.trans`-chaining the three component `*_denote` lemmas. **Not `rfl`** — it
inherits the inductive preservation proofs of the components.

`comOptPipeline_ctLeak_eq`: under a leakage model whose `regArith` operations
are quiet, equal leakage of `c` at two valuations gives equal leakage of
`comOptPipeline c` there. The peephole keeps the leakage (`peepCom_ctLeak`),
copy propagation keeps it for every leakage model (`copyProp_ctLeak`), and
dead-let elimination maps equal leakage to equal leakage (`comDCE_ctLeak_eq`).

All goals closed.
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
(`comDCE_denote`, `copyProp_denote`, `peepCom_denote`) — each itself an
induction over the `Com` let-chain, **not** `rfl`. -/
theorem comOptPipeline_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    (comOptPipeline c).denote V = c.denote V :=
  -- comDCE (copyProp (peepCom c))  =  copyProp (peepCom c)  =  peepCom c  =  c
  (comDCE_denote (copyProp (peepCom c)) V).trans
    ((copyProp_denote (peepCom c) V).trans
      (peepCom_denote c V))

/-! ## 3. Leakage

Copy propagation keeps every binding and renames the continuation of a copy to read the
source of the copy, which holds the same value, so it keeps the leakage of a program at
every valuation for every leakage model. -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck

/-- The events of a renamed program are those of the program at the pulled-back
    valuation. -/
theorem Com.ctLeak_rename (L : LeakModel jasminDialect) {Γ Γ' : Ctxt jasminDialect}
    {τ : JasminTy} :
    ∀ (h : Ctxt.Hom Γ Γ') (c : Com jasminDialect Γ τ) (V : Ctxt.Valuation Γ'),
      Com.ctLeak L (c.rename h) V = Com.ctLeak L c (pullV h V)
  | _, .ret _, _ => rfl
  | h, .var e body, V => by
      simp only [Com.rename, Com.ctLeak]
      rw [Rewrite.ComGVN.Expr.ctLeak_rename L h e V, CopyProp.Expr.denote_rename h e V,
        Com.ctLeak_rename L h.lift body (V.extend (e.denote (pullV h V))),
        pullV_lift h V (e.denote (pullV h V))]

/-- **Leakage of copy propagation.** For every leakage model, `copyProp c` has the
    leakage of `c` at every valuation. -/
theorem copyProp_ctLeak (L : LeakModel jasminDialect) {Γ : Ctxt jasminDialect}
    {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ),
      Com.ctLeak L (copyProp c) V = Com.ctLeak L c V
  | .ret _, _ => rfl
  | .var e body, V => by
      show Com.ctLeak L (match isCopy e with
            | some a => Com.var e ((copyProp body).rename (copyHom a))
            | none   => Com.var e (copyProp body)) V
            = Com.ctLeak L (Com.var e body) V
      rcases hc : isCopy e with _ | a
      · simp only [Com.ctLeak]
        rw [copyProp_ctLeak L body (V.extend (e.denote V))]
      · simp only [Com.ctLeak]
        rw [Com.ctLeak_rename L (copyHom a) (copyProp body) (V.extend (e.denote V)),
          isCopy_denote e a V hc, pullV_copyHom a V,
          copyProp_ctLeak L body (V.extend (a.lookup V))]

/-- **Leakage of the pipeline.** Under a leakage model whose `regArith` operations are
    quiet, equal leakage of `c` at two valuations gives equal leakage of
    `comOptPipeline c` there. -/
theorem comOptPipeline_ctLeak_eq (L : LeakModel jasminDialect)
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t) (V₁ V₂ : Ctxt.Valuation Γ)
    (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (comOptPipeline c) V₁ = Com.ctLeak L (comOptPipeline c) V₂ :=
  comDCE_ctLeak_eq L _ V₁ V₂ (by
    show Com.ctLeak L (copyProp (peepCom c)) V₁ = Com.ctLeak L (copyProp (peepCom c)) V₂
    rw [copyProp_ctLeak, copyProp_ctLeak, peepCom_ctLeak L hq, peepCom_ctLeak L hq]
    exact h)

end Leak

/-! ## 4. Self-contained validation

We exercise the pipeline on a program that hits all three passes in sequence:

    let z = x ||| x      -- a register copy of x  (copyProp source)
    let d = x - x        -- a self-subtract (peephole: ↦ xor x x, → 0)
    ret z                -- returns the copy; d is a dead trailing binder

Peephole canonicalises `x - x ↦ x ^^^ x`; copy propagation redirects the
return through the `z = x ||| x` alias; DCE drops the dead trailing
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

/-- A bare `ret` program is a pipeline fixpoint. -/
example :
    comOptPipeline (Com.ret (Γ := [JasminTy.reg 8]) (t := JasminTy.reg 8) .here)
      = Com.ret .here := rfl

end CatCrypt.Crypto.Optimizer.ComOptPipeline
