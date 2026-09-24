/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.ConstFold
public import CatCrypt.Crypto.Optimizer.ComCSE
public import CatCrypt.Crypto.Optimizer.UncomputePass
public import CatCrypt.Crypto.Optimizer.ComDCE

/-!
# Composed `Com → Com` clean-up pipeline (constant-fold · CSE · uncompute · DCE)

This file wires the four denotation-preserving `Com → Com` clean-up passes over
the typed VIR `jasminDialect` into a single pipeline with one end-to-end
preservation meta-theorem.  Each component already carries its own
(non-`rfl`) preservation proof; we reuse those lemmas verbatim and `Eq.trans`-
chain them.

The stages, in order:

1. `ConstFold.foldCom · k` — constant folding / partial evaluation under the
   known-constant environment `k` (`regConst a ⊕ regConst b ↦ regConst (a⊕b)`,
   `x+0 ↦ x`, `x*0 ↦ 0`, …).  This is the IR realisation of *classical-operand
   partial evaluation* (folding a classical operand collapses gates).  Lemma
   `foldCom_denote` — needs `KEnv.Consistent k V`.
2. `ComCSE.comCSE` — structural common-subexpression elimination (redirect a
   redundant binder to its earlier syntactic duplicate).  Lemma `comCSE_denote`.
3. `UncomputePass.uncompute` — *uncompute-after-last-use*: drop any binder that
   is dead in its continuation (the IR realisation of measurement-based
   uncomputation — a compute/uncompute ancilla pair whose uncompute is free once
   the value is dead).  Lemma `uncompute_denote`.
4. `ComDCE.comDCE` — trailing dead-let elimination (sweep the dead bindings
   the earlier stages exposed).  Lemma `comDCE_denote`.

The four share the signature `Com jasminDialect Γ t → Com jasminDialect Γ t`
(once `foldCom`'s constant environment `k` is fixed; `uncompute`/`comDCE` are
dialect-generic and specialise here), so they compose directly with no reindex
adapter.

## The meta-theorem

`comCleanup_denote : KEnv.Consistent k V → (comCleanup k c).denote V = c.denote V`,
obtained by chaining the four component `*_denote` lemmas.  The `foldCom` arm
consumes the `KEnv.Consistent k V` hypothesis exactly as `foldCom_denote`
requires.  **Not `rfl`** — it inherits the inductive preservation proofs
of the components.

This complements `ComFullOpt.lean` (algebraic-saturation · copy-prop · DCE) with
the fold/CSE/uncompute/DCE clean-up stack.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ComCleanup

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph

/-- The composed clean-up pass: constant-fold (under `k`), then structural CSE,
    then uncompute-after-last-use, then trailing DCE. -/
def comCleanup {Γ : Ctxt jasminDialect} {t : JasminTy}
    (k : KEnv Γ) (c : Com jasminDialect Γ t) : Com jasminDialect Γ t :=
  ComDCE.comDCE
    (UncomputePass.uncompute
      (ComCSE.comCSE
        (ConstFold.foldCom c k)))

/-- **End-to-end denotation preservation**: the composed clean-up pipeline
    preserves the program's denotation on every valuation consistent with the
    known-constant environment. -/
theorem comCleanup_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (k : KEnv Γ) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ)
    (hk : KEnv.Consistent k V) :
    (comCleanup k c).denote V = c.denote V := by
  unfold comCleanup
  rw [ComDCE.comDCE_denote, UncomputePass.uncompute_denote, ComCSE.comCSE_denote,
    ConstFold.foldCom_denote c k V hk]

end CatCrypt.Crypto.Optimizer.ComCleanup
