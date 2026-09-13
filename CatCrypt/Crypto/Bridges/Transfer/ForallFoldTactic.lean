/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Transfer.Base.HigherOrderTransfer

/-!
# Lean-Trocq, Phase 3 — tactic wrappers for the 3a–3c transfer lemmas

`HigherOrderTransfer.lean` delivers the binder / higher-order / ∀ transfer
capability as proven generic lemmas (`funMap_transfer`, `foldl_transfer`,
`forall_transfer`). This module packages the two recurring *shapes* — fold
transfer and ∀-transfer — as small `tactic` macros, so a user can discharge a
higher-order transfer goal by naming only the registered commuting square or
pointwise transfer.

## The wrappers

* `fold_transfer` — applies `foldl_transfer`, leaving the commuting-square
  premise as a goal tagged `comm`. The user discharges it with the registered
  square. Robust against the `enc`/`op`/`bop`/`init`/`list` metavariables
  because they are all inferred by unification with the goal.
* `forall_transfer'` — applies `forall_transfer`, reducing a `∀`-quantified
  equivalence transfer to the *pointwise* transfer, left as a goal tagged
  `pointwise`. Nesting the macro transfers each `∀` layer.

Both leave exactly the residual as a goal: the wrapper never invents the
commuting square or the pointwise witness, it composes a given one — the same
non-fabrication invariant the underlying lemmas carry.

This module depends only on the generic transfer layer; its consumers supply
the realization.

## Scope

These are thin `refine`-macros, not the full Phase-3d `MetaM` `⟦·⟧` elaborator
that would *find* the registered square automatically. They remove the
boilerplate of restating the lemma's metavariables while keeping the trust
surface (the square, the pointwise transfer) explicit at the call site.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer

/-- **Fold-transfer wrapper.** Reduce a `List.foldl`-transfer goal
    `enc (l.foldl op init) = (l.map enc).foldl bop (enc init)` to its
    commuting-square premise, left as the goal `comm`
    (`∀ a b, enc (op a b) = bop (enc a) (enc b)`). Discharge `comm` with the
    registered square. All other arguments are inferred by unification. -/
macro "fold_transfer" : tactic =>
  `(tactic| refine foldl_transfer _ _ _ ?comm _ _)

/-- **∀-transfer wrapper.** Reduce a `∀`-quantified equivalence transfer
    `(∀ i, P i) ↔ (∀ i, Q i)` to the *pointwise* transfer `∀ i, P i ↔ Q i`,
    left as the goal `pointwise`. Discharge `pointwise` with `intro` + the
    Phase-2 pointwise transfer. Re-apply for each nested `∀` binder. -/
macro "forall_transfer'" : tactic =>
  `(tactic| refine forall_transfer _ _ ?pointwise)

end Transfer
