/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA

/-!
# Substitution of trees for events

A call of a function of the module is an event of the call tree of a program before the calls are
inlined, and the run of the call tree of the callee after. `substT σ t` replaces every event `e`
of `t` by the tree `σ e`, whose leaves are the answers to `e`, and continues at each leaf: it is
the interpretation of `t` in the monad of call trees. An event kept as it is has the tree
`.vis e .ret`.

Two trees related by `RuttSA` stay related under substitution when the substituted trees of
related events are related, their leaves by the answer relation, and when the source substitution
is consistent with the skip predicates: every leaf that the substituted tree of a source event
returns along answers admitted by the new skip predicate is admitted by the old one, so that a
skipped source event becomes a skipped source tree. At the answers of handlers this is the
consistency `interp h₁' (σ₁ e) = h₁ e` (`retsA_eq_iff`, `ruttSA_iff_ruttS`).

## Main results

* `substT`: the substitution of trees for the events of a tree.
* `interp_substT`: interpreting a substituted tree interprets the substituted trees.
* `RuttSA.substT`: substitution keeps `RuttSA`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubst

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA (RuttSA RetsA)

/-- **Substitution of trees for events**: every event `e` of the tree is replaced by the tree
    `σ e` over the events `E'`, and the continuation runs at its leaf. -/
def substT {E E' : EventSig} {R : Type} (σ : ∀ e : E.Event, CallTree E' (E.Resp e)) :
    CallTree E R → CallTree E' R
  | .ret r => .ret r
  | .vis e k => (σ e).bind fun a => substT σ (k a)

/-- Unfolding lemma of `substT` at a leaf. -/
@[simp] theorem substT_ret {E E' : EventSig} {R : Type}
    (σ : ∀ e : E.Event, CallTree E' (E.Resp e)) (r : R) : substT σ (.ret r) = .ret r := rfl

/-- Unfolding lemma of `substT` at an event. -/
@[simp] theorem substT_vis {E E' : EventSig} {R : Type}
    (σ : ∀ e : E.Event, CallTree E' (E.Resp e)) (e : E.Event) (k : E.Resp e → CallTree E R) :
    substT σ (.vis e k) = (σ e).bind fun a => substT σ (k a) := rfl

/-- **Interpretation of a substituted tree**: under the handler `h'` of the new events, the
    substituted tree interprets as the tree under the handler that interprets the substituted
    trees. -/
theorem interp_substT {E E' : EventSig} {R : Type} (σ : ∀ e : E.Event, CallTree E' (E.Resp e))
    (h' : ∀ e : E'.Event, E'.Resp e) (t : CallTree E R) :
    interp h' (substT σ t) = interp (fun e => interp h' (σ e)) t := by
  induction t with
  | ret r => rfl
  | vis e k ih => rw [substT_vis, interp_bind, ih]; rfl

/-- **Substitution keeps `RuttSA`.** Let `t₁` and `t₂` be related by `RuttSA` at the skip
    predicate `Sk`. Substitute `σ₁` in `t₁` and `σ₂` in `t₂`. When the substituted trees of related
    events are related by `RuttSA` at the skip predicate `Sk'` and the new relations, their leaves
    by the answer relation and none of their source leaves failed, and when every leaf that the
    substituted tree of a source event returns along answers admitted by `Sk'` is admitted by `Sk`,
    the substituted trees are related at `Sk'` and the new relations of events and answers. -/
theorem RuttSA.substT {E₁ E₂ E₁' E₂' : EventSig} {R₁ R₂ : Type}
    {Sk : (e : E₁.Event) → E₁.Resp e → Prop} {Sk' : (e : E₁'.Event) → E₁'.Resp e → Prop}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RE' : E₁'.Event → E₂'.Event → Prop}
    {RA' : (e₁ : E₁'.Event) → (e₂ : E₂'.Event) → E₁'.Resp e₁ → E₂'.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    {σ₁ : ∀ e : E₁.Event, CallTree E₁' (E₁.Resp e)} {σ₂ : ∀ e : E₂.Event, CallTree E₂' (E₂.Resp e)}
    (hσ : ∀ e₁ e₂, RE e₁ e₂ →
      RuttSA Sk' RE' RA' (RA e₁ e₂) (fun _ => False) (σ₁ e₁) (σ₂ e₂))
    (hh : ∀ e₁ a, RetsA Sk' (σ₁ e₁) a → Sk e₁ a)
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : RuttSA Sk RE RA RR Fail t₁ t₂) :
    RuttSA Sk' RE' RA' RR Fail (substT σ₁ t₁) (substT σ₂ t₂) := by
  induction h with
  | ret h => exact .ret h
  | fail h => exact .fail h
  | vis he _ ih =>
    exact RuttSA.bind (hσ _ _ he) (fun a₁ a₂ ha => ih a₁ a₂ ha) (fun _ hf => hf.elim)
  | @skip e₁ k₁ t₂ _ ih =>
    rw [substT_vis]
    exact RuttSA.skip_bind (σ₁ e₁) fun a ha => ih a (hh _ _ ha)

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubst
