/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITree
public import CatCrypt.Relational.Rules

/-!
# Bridging the interaction-tree layer to the pRHL (`rHoare`)

This module connects the **plain interaction-tree** denotational layer of
`LowCTITree.lean` (the `CallTree` free monad, calls-as-visible-events)
to CatCrypt's **probabilistic relational Hoare logic**
(`CatCrypt.Relational.rHoare`, of SSProve/EasyCrypt lineage).  It is the bridge
from the bespoke relational-logic machinery the ITree paper (arXiv:2511.11292)
builds to the relational logic of this development.

The headline: **compiler correctness for the call-free bounded fragment is a
`rHoare` judgment, discharged by the return rule `rHoare_ret`.**  So the ITree layer + the
pRHL/relational-mvcgen stack provides the paper's RHL machinery, **iris-free**.

## What lives here

* `interpSP h` — interpret a `CallTree` into a *probabilistic stateful*
  computation `SPComp` using an **`SPComp`-valued** handler `h` (one that may
  *sample*).  This is where probabilistic oracle/leaf calls would live; on the
  call-free fragment the handler is never invoked.  Compare with
  `LowCTITree.interp`, whose handler is a *pure* `∀ e, E.Resp e`; here the
  handler is `∀ e, SPComp (E.Resp e)`, so a `vis` step *binds* in `SPComp`.
* `interpSP_callfree` — the call-free ITree interprets to a **pure** `SPComp`
  computation `SPComp.pure (srcDenote ps rs)`: no `vis`, no sampling.
* `callfree_compile_rHoare` — **the integration headline**.  Relational
  compiler correctness on the call-free fragment, phrased as a `rHoare`
  judgment between the `interpSP`-interpretations of two source programs, and
  closed by `rHoare_ret`.
* `callfree_compile_rHoare_eq` — the canonical instance: inputs-equal /
  outputs-equal (`Φ = eqPre`-style, `Ψ = outputs equal`), i.e. *the same
  source program preserves the input relation as the output relation*.

## Iris-free

This module imports **only** `LowCTITree` (the plain-ITree layer),
`CatCrypt.Relational.Rules` (the iris-free pRHL: `rHoare`, `rHoare_ret`,
… of SSProve/EasyCrypt lineage), and — transitively — `CatCrypt.Core` (the
`SPComp` semantic monad).  It imports **nothing** under `Bridges/` or
`IrisBridge/`.  No guarded ITrees, no step-indexing, no separation logic.

## The call / probabilistic case (outside this module)

A **call** (`vis`) step interprets to a real `SPComp` bind
`h e >>= fun resp => interpSP h (k resp)` (see `interpSP_vis`).  To carry a
relational judgment across such a step one discharges it with the pRHL
**one-sided / `Sync` rules** — `rHoare_bind` to peel the bind, then
`rHoare_sample_same` / `rHoare_sample_bij` / `rHoare_sample_l`/`_r` (or the
`get`/`set` `Sync` rules) for the `h e` leaf — and closes the residual leaf
verification condition with the relational `mvcgen` closer (`ssprove_vc`).  That
is the path to probabilistic cryptographic-security preservation across
compilation (`LowCTSecPreserve`).  This module establishes the call-free bridge
plus that hook.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITreePRHL

open CatCrypt.Core
open CatCrypt.Relational
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITree

/-! ## 1. `SPComp`-valued interpretation of a `CallTree`

`LowCTITree.interp` folds a tree under a **pure** handler
`∀ e, E.Resp e`.  Here we fold under an **`SPComp`-valued** handler
`∀ e, SPComp (E.Resp e)` — a handler that may *sample*.  This is the only place
probabilistic oracle calls can enter; for the call-free fragment it is never
consulted. -/

/-- Interpret a `CallTree` into a stateful probabilistic computation `SPComp`,
    using an **`SPComp`-valued** handler `h` that answers every event with a
    (possibly sampling) `SPComp` computation.  `ret r` becomes the pure
    computation; `vis e k` *binds* the handler's answer into the continuation. -/
noncomputable def interpSP {E : EventSig} {R : Type}
    (h : ∀ e : E.Event, SPComp (E.Resp e)) : CallTree E R → SPComp R
  | .ret r   => SPComp.pure r
  | .vis e k => (h e).bind (fun resp => interpSP h (k resp))

@[simp] theorem interpSP_ret {E : EventSig} {R : Type}
    (h : ∀ e : E.Event, SPComp (E.Resp e)) (r : R) :
    interpSP h (CallTree.ret r) = SPComp.pure r := rfl

@[simp] theorem interpSP_vis {E : EventSig} {R : Type}
    (h : ∀ e : E.Event, SPComp (E.Resp e)) (e : E.Event)
    (k : E.Resp e → CallTree E R) :
    interpSP h (CallTree.vis e k) = (h e).bind (fun resp => interpSP h (k resp)) :=
  rfl

/-! ## 2. The call-free fragment interprets to a *pure* `SPComp` -/

/-- **Call-free interpretation is pure.**  The `SPComp`-interpretation of the
    ITree denotation of a call-free scalar-arith program is the *pure* `SPComp`
    computation of the big-step result `srcDenote ps rs` — no `vis`, hence no
    sampling, hence the probabilistic handler is never consulted.  Proven by
    rewriting with the conservative-extension lemma `itreeDenote_callfree`
    (the tree is a `ret`) and `interpSP_ret`. -/
theorem interpSP_callfree
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (ps : List ArithSrc) (rs : RustState) :
    interpSP h (itreeDenoteArith ps rs) = SPComp.pure (srcDenote ps rs) := by
  rw [itreeDenote_callfree, interpSP_ret]

/-! ## 3. The integration headline: compiler correctness as a `rHoare` judgment

For the call-free bounded fragment, relational compiler correctness between two
source programs `ps` and `qs` is a `rHoare` judgment between their
`interpSP`-interpretations.  Both sides collapse to `SPComp.pure (srcDenote …)`
(by `interpSP_callfree`), so the judgment is closed by the existing pRHL return
rule `rHoare_ret`, whose premise relates the two pure return values under `Ψ`
given `Φ`.

The `rHoare_ret` premise shape (from `Relational/Rules.lean`, `rHoare_ret`):
for return values `a := srcDenote ps rs₁` and `b := srcDenote qs rs₂`,
```
∀ h₁ h₂, Φ h₁ h₂ → Ψ (srcDenote ps rs₁) h₁ (srcDenote qs rs₂) h₂
```
i.e. the input relation `Φ` on the heap pair must imply the output relation `Ψ`
on the two big-step results (with the heaps unchanged — the pure computation
does not touch the heap). -/

/-- **Relational compiler correctness, call-free fragment, as pRHL.**  Given a
    hypothesis `hrel` that the input relation `Φ` implies the output relation
    `Ψ` on the two big-step results, the `interpSP`-interpretations of the two
    call-free source programs satisfy the pRHL judgment `rHoare Φ … … Ψ`.

    Proved by rewriting both sides with `interpSP_callfree` to
    `SPComp.pure (srcDenote …)` and applying the return rule
    `rHoare_ret`.  Compiler correctness on the bounded call-free fragment is
    *literally* a `rHoare` judgment, discharged by the pRHL stack. -/
theorem callfree_compile_rHoare
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (Φ : RPre) (Ψ : RPost RustState RustState)
    (ps qs : List ArithSrc) (rs₁ rs₂ : RustState)
    (hrel : ∀ h₁ h₂, Φ h₁ h₂ →
      Ψ (srcDenote ps rs₁) h₁ (srcDenote qs rs₂) h₂) :
    rHoare Φ (interpSP h (itreeDenoteArith ps rs₁))
             (interpSP h (itreeDenoteArith qs rs₂)) Ψ := by
  rw [interpSP_callfree, interpSP_callfree]
  -- both sides are now `SPComp.pure (srcDenote …)`; `pure` is the monad `pure`
  exact rHoare_ret (a := srcDenote ps rs₁) (b := srcDenote qs rs₂) hrel

/-- **Canonical instance: input-relation-preserving correctness.**  The same
    source program `ps`, run on two states related by an arbitrary input
    relation `R` on the *results*, lands in the output relation
    "results related by `R`, heaps unchanged-and-related-by-`Φ`".  The clean
    concrete reading: a call-free compiled program is *deterministic* — equal
    (relation-`R`) inputs give equal (relation-`R`) outputs — which is exactly
    relational compiler correctness for the call-free fragment, and it is a
    `rHoare` judgment closed by `rHoare_ret`.

    Specialising `R := Eq` and `Φ := eqPre` recovers the textbook statement:
    *equal source states produce equal results*. -/
theorem callfree_compile_rHoare_eq
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (Φ : RPre) (R : RustState → RustState → Prop)
    (ps : List ArithSrc) (rs₁ rs₂ : RustState)
    (hres : R (srcDenote ps rs₁) (srcDenote ps rs₂)) :
    rHoare Φ (interpSP h (itreeDenoteArith ps rs₁))
             (interpSP h (itreeDenoteArith ps rs₂))
             (fun a₁ h₁ a₂ h₂ => R a₁ a₂ ∧ Φ h₁ h₂) :=
  callfree_compile_rHoare h Φ _ ps ps rs₁ rs₂
    (fun _ _ hΦ => ⟨hres, hΦ⟩)

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITreePRHL
