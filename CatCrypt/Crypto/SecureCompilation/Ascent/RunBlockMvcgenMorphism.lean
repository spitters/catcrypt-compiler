/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockMvcgen


@[expose] public section
set_option autoImplicit false

/-!
# The base-change monad morphism `StateM S → StateT S Option` on the `Std.Do` WP

`Ascent/RunBlockMvcgen.lean` puts the **total** machine `runBlock` on the `Std.Do`
weakest-precondition metatheory: `runBlockM : List (JInstr 64) → StateM (JState 64) Unit`
lives in the pure state monad, `PostShape = .arg (JState 64) .pure`, and `mvcgen`
walks it natively. The **partial** bignum interpreter (`Jasmin/BignumHoare.lean`)
instead runs in `StateT _ Option` — `PostShape = .arg _ (.except PUnit .pure)` — and
its triples do not literally subsume the total ones.

`mvcgen`'s `Std.Do` WP metatheory transfers weakest preconditions along the standard
transformer *lifts* (`monadLift_StateT`, `monadLift_OptionT`, `monadMap_OptionT`, …),
but there is **no** built-in transfer along a **base-monad change** `StateM S → StateT
S Option` (`StateT S Id → StateT S Option`, changing the base `Id → Option` by `some`).
This module adds exactly that transfer as one `@[spec]` lemma, so that `mvcgen`
transports a total `StateM` triple into the partial `StateT _ Option` monad
automatically. It is the base-change analogue of the upstream `Spec.monadMap_OptionT`.

## The construction

`θ : StateM S α → StateT S Option α` is the base change by `some`: run the total state
computation, always succeed (`θ x = fun s => some (x.run s)`). It is a lawful monad
morphism (`theta_pure`, `theta_bind`). The WP-transfer lemma `Spec.wp_theta` is the
deliverable: `wp⟦θ x : StateT S Option α⟧ Q` equals `wp⟦x : StateM S α⟧` at the pushed
-forward postcondition `PostCond.noThrow Q.1` (the success branch threads the state
and value verbatim; the `.fail`/`PUnit` branch is unreachable because `θ` never fails).
Both sides compute definitionally to `fun s => Q.1 (x.run s).1 (x.run s).2`, so the WP
equation `wp_theta_eq` is `rfl` and the `@[spec]` triple is reflexivity of `⊢ₛ`.

`theta_sbb_leaf_triple` demonstrates it: the total subtract-with-borrow ascend leaf
`sbb_leaf_triple` is transported into `StateT (JState 64) Option` by `mvcgen [θ]` firing
the base-change spec lemma, with the residual VC discharged by the total leaf.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.Do
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The base-change monad morphism -/

/-- **The base-change morphism `StateM S → StateT S Option`.** Run the total state
    computation and always succeed. Concretely `θ x = fun s => some (x.run s)`: the
    base monad is changed `Id → Option` by `some`, threading state unchanged. -/
def θ {S α : Type} (x : StateM S α) : StateT S Option α :=
  StateT.mk (fun s => some (x.run s))

@[simp] theorem theta_run {S α : Type} (x : StateM S α) (s : S) :
    (θ x).run s = some (x.run s) := rfl

/-- `θ` preserves `pure`. -/
theorem theta_pure {S α : Type} (a : α) :
    θ (pure a : StateM S α) = pure a := rfl

/-- `θ` preserves `bind` — it is a lawful monad morphism. -/
theorem theta_bind {S α β : Type} (x : StateM S α) (f : α → StateM S β) :
    θ (x >>= f) = θ x >>= (fun a => θ (f a)) := by
  ext s; rfl

/-! ## 2. The base-change WP-transfer lemma (the deliverable)

The `PostShape` of `StateT S Option` is `.arg S (.except PUnit .pure)`; that of
`StateM S = StateT S Id` is `.arg S .pure`. Both have the same *state* spine `[S]`,
so `Assertion (.arg S (.except PUnit .pure)) = Assertion (.arg S .pure) = SPred [S]`
definitionally, and a success postcondition `Q.1 : α → SPred [S]` is shared verbatim.
The pushforward drops the (unreachable) failure barrel: `PostCond.noThrow Q.1`. -/

/-- **The base-change WP equation.** The weakest precondition of `θ x` in `StateT S
    Option` at post `Q` equals the weakest precondition of the total `x` in `StateM S`
    at the pushed-forward post `PostCond.noThrow Q.1`. Both sides reduce definitionally
    to `fun s => Q.1 (x.run s).1 (x.run s).2` — the success branch threads state and
    value; the `PUnit` failure branch of `Q` is discarded because `θ` never fails. -/
theorem wp_theta_eq {S α : Type} (x : StateM S α)
    (Q : PostCond α (.arg S (.except PUnit .pure))) :
    wp⟦θ x : StateT S Option α⟧ Q = wp⟦x : StateM S α⟧ (PostCond.noThrow Q.1) := rfl

/-- **The base-change `@[spec]` transfer lemma** — the analogue of
    `Spec.monadMap_OptionT` for a base-monad change. Given `x : StateM S α`, a triple
    for `θ x : StateT S Option α` at post `Q` holds under the precondition
    `wp⟦x : StateM S α⟧ (PostCond.noThrow Q.1)`. `mvcgen` uses this to rewrite
    `wp⟦θ x⟧ Q` into the total-monad weakest precondition, transporting any total
    `StateM` triple into the partial `StateT _ Option` monad. -/
@[spec]
theorem Spec.wp_theta {S α : Type} (x : StateM S α)
    (Q : PostCond α (.arg S (.except PUnit .pure))) :
    Triple (ps := .arg S (.except PUnit .pure))
      (θ x : StateT S Option α)
      (wp⟦x : StateM S α⟧ (PostCond.noThrow Q.1))
      Q :=
  Triple.iff.mpr (SPred.entails.refl _)

/-! ## 3. Demonstration: a total ascend leaf transported into `StateT _ Option`

The total subtract-with-borrow ascend leaf `sbb_leaf_triple` (over `StateM (JState 64)`)
is transported into the partial `StateT (JState 64) Option` monad. `mvcgen [θ]` fires
the base-change spec lemma `Spec.wp_theta`, reducing the partial-monad goal to the total
weakest precondition; the residual VC is exactly the total leaf. -/

/-- **The `sbb` ascend leaf transported into `StateT (JState 64) Option`.** The very
    triple of `sbb_leaf_triple`, but for the base-changed `θ (runBlockM …)` in the
    partial (option-failing) monad. `mvcgen [θ]` walks `θ (runBlockM …)`: the
    base-change spec lemma `Spec.wp_theta` rewrites the partial weakest precondition to
    the total one, and the residual is discharged by the total leaf `sbb_leaf_triple`.
    This is a total `StateM` triple transported into `StateT _ Option` automatically. -/
theorem theta_sbb_leaf_triple (dst src : String) (a : ACarry) :
    ⦃fun st => ⌜SRcarry st a⌝⦄
      (θ (runBlockM [.sbb dst (.reg src)]) : StateT (JState 64) Option Unit)
      ⦃⇓ _ st => ⌜SRcarry st (sbbStep dst src a)⌝⦄ := by
  mvcgen [θ]
  rename_i s h
  exact Triple.iff.mp (sbb_leaf_triple dst src a) s h

end CatCrypt.Crypto.SecureCompilation.Ascent
