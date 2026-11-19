/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract

/-!
# Related call trees with skips at an answer predicate: the relation and its laws

`RuttS h₁` relates two call trees up to source events that the target does not perform, each
continued at the answer `h₁ e` of a source handler. This module states the relation `RuttSA Sk`
in which a skipped source event `e` is continued at every answer `a` with `Sk e a`. At the answers
of a handler, `Sk e a := a = h₁ e`, it is `RuttS h₁` (`ruttSA_iff_ruttS`). A source prefix is
skipped at every leaf it returns along admitted answers (`RetsA`, `RuttSA.skip_bind`); at the
answers of a handler the only such leaf is the interpretation (`retsA_eq_iff`).

## Main definitions

* `RuttSA`: two finite call trees related up to relations, with skipped source events continued
  at every answer of a skip predicate.
* `RetsA`: a leaf that a tree returns along answers of a predicate.

## Main results

* `ruttSA_iff_ruttS`, `retsA_eq_iff`: the instances at a handler.
* `RuttSA.imp`, `RuttSA.mono`, `RuttSA.of_rutt`, `RuttSA.bind`, `RuttSA.skip_bind`,
  `RuttSA.refl`, `RuttSA.of_ret_fail`, `RetsA.imp`: the laws of the relation.
* `interp_ruttSA`: under a handler whose answers satisfy the skip predicate, related trees
  interpret to a failed source leaf or to related leaves.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree (Rutt)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS interp_ruttS)

/-! ## The relation -/

/-- **Two finite call trees related up to relations, with skips at an answer predicate**: the
    clauses of `Rutt`, and a source event `e₁` that the target does not perform, whose
    continuation at every answer `a` with `Sk e₁ a` is related to the target tree. -/
inductive RuttSA {E₁ E₂ : EventSig} {R₁ R₂ : Type} (Sk : (e : E₁.Event) → E₁.Resp e → Prop)
    (RE : E₁.Event → E₂.Event → Prop)
    (RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop)
    (RR : R₁ → R₂ → Prop) (Fail : R₁ → Prop) : CallTree E₁ R₁ → CallTree E₂ R₂ → Prop
  | ret {r₁ : R₁} {r₂ : R₂} (h : RR r₁ r₂) : RuttSA Sk RE RA RR Fail (.ret r₁) (.ret r₂)
  | fail {r₁ : R₁} {t₂ : CallTree E₂ R₂} (h : Fail r₁) : RuttSA Sk RE RA RR Fail (.ret r₁) t₂
  | vis {e₁ : E₁.Event} {e₂ : E₂.Event} {k₁ : E₁.Resp e₁ → CallTree E₁ R₁}
      {k₂ : E₂.Resp e₂ → CallTree E₂ R₂} (he : RE e₁ e₂)
      (hk : ∀ a₁ a₂, RA e₁ e₂ a₁ a₂ → RuttSA Sk RE RA RR Fail (k₁ a₁) (k₂ a₂)) :
      RuttSA Sk RE RA RR Fail (.vis e₁ k₁) (.vis e₂ k₂)
  | skip {e₁ : E₁.Event} {k₁ : E₁.Resp e₁ → CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
      (hk : ∀ a, Sk e₁ a → RuttSA Sk RE RA RR Fail (k₁ a) t₂) :
      RuttSA Sk RE RA RR Fail (.vis e₁ k₁) t₂

/-- **A leaf that a tree returns along answers of a predicate**: the leaf of a `ret`, and a leaf
    of the continuation of an event at an answer `a` with `Sk e a`. -/
inductive RetsA {E : EventSig} {R : Type} (Sk : (e : E.Event) → E.Resp e → Prop) :
    CallTree E R → R → Prop
  | ret (r : R) : RetsA Sk (.ret r) r
  | vis {e : E.Event} {k : E.Resp e → CallTree E R} {a : E.Resp e} {r : R} (ha : Sk e a)
      (h : RetsA Sk (k a) r) : RetsA Sk (.vis e k) r

/-- At the answers of a handler, the only leaf a tree returns is its interpretation. -/
theorem retsA_eq_iff {E : EventSig} {R : Type} {h : ∀ e : E.Event, E.Resp e} {t : CallTree E R}
    {r : R} : RetsA (fun e a => a = h e) t r ↔ r = interp h t := by
  constructor
  · intro hr
    induction hr with
    | ret r => rfl
    | vis ha _ ih => subst ha; simpa using ih
  · rintro rfl
    induction t with
    | ret r => exact .ret r
    | vis e k ih => simpa using RetsA.vis (k := k) rfl (ih (h e))

/-- The leaves returned along answers of a predicate are those along a larger predicate. -/
theorem RetsA.imp {E : EventSig} {R : Type} {Sk Sk' : (e : E.Event) → E.Resp e → Prop}
    (hS : ∀ e a, Sk e a → Sk' e a) {t : CallTree E R} {r : R} (h : RetsA Sk t r) :
    RetsA Sk' t r := by
  induction h with
  | ret r => exact .ret r
  | vis ha _ ih => exact .vis (hS _ _ ha) ih

section RuttSA

variable {E₁ E₂ : EventSig} {R₁ R₂ : Type}

/-- **At the answers of a handler, `RuttSA` is `RuttS`.** -/
theorem ruttSA_iff_ruttS {h₁ : ∀ e : E₁.Event, E₁.Resp e} {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} :
    RuttSA (fun e a => a = h₁ e) RE RA RR Fail t₁ t₂ ↔ RuttS h₁ RE RA RR Fail t₁ t₂ := by
  constructor
  · intro h
    induction h with
    | ret h => exact .ret h
    | fail h => exact .fail h
    | vis he _ ih => exact .vis he ih
    | skip _ ih => exact .skip (ih _ rfl)
  · intro h
    induction h with
    | ret h => exact .ret h
    | fail h => exact .fail h
    | vis he _ ih => exact .vis he ih
    | skip _ ih => exact .skip fun a ha => ha ▸ ih

/-- **`RuttSA` is monotone in the relations of events, leaves and failure and antitone in the
    skip predicate and the answer relation**, the answers compared at related events. -/
theorem RuttSA.imp {Sk Sk' : (e : E₁.Event) → E₁.Resp e → Prop}
    {RE RE' : E₁.Event → E₂.Event → Prop}
    {RA RA' : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR RR' : R₁ → R₂ → Prop} {Fail Fail' : R₁ → Prop}
    (hS : ∀ e a, Sk' e a → Sk e a) (hE : ∀ e₁ e₂, RE e₁ e₂ → RE' e₁ e₂)
    (hA : ∀ e₁ e₂ a₁ a₂, RE e₁ e₂ → RA' e₁ e₂ a₁ a₂ → RA e₁ e₂ a₁ a₂)
    (hR : ∀ r₁ r₂, RR r₁ r₂ → RR' r₁ r₂) (hF : ∀ r₁, Fail r₁ → Fail' r₁)
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : RuttSA Sk RE RA RR Fail t₁ t₂) :
    RuttSA Sk' RE' RA' RR' Fail' t₁ t₂ := by
  induction h with
  | ret h => exact .ret (hR _ _ h)
  | fail h => exact .fail (hF _ h)
  | vis he _ ih => exact .vis (hE _ _ he) fun a₁ a₂ ha => ih a₁ a₂ (hA _ _ _ _ he ha)
  | skip _ ih => exact .skip fun a ha => ih a (hS _ _ ha)

variable {Sk : (e : E₁.Event) → E₁.Resp e → Prop} {RE : E₁.Event → E₂.Event → Prop}
  {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}

/-- `RuttSA` is monotone in the relation of the leaves. -/
theorem RuttSA.mono {RR RR' : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    (hR : ∀ a b, RR a b → RR' a b) {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    (h : RuttSA Sk RE RA RR Fail t₁ t₂) : RuttSA Sk RE RA RR' Fail t₁ t₂ :=
  h.imp (fun _ _ ha => ha) (fun _ _ he => he) (fun _ _ _ _ _ ha => ha) hR (fun _ hf => hf)

/-- **A relation by `Rutt` is a relation by `RuttSA`**, at every skip predicate. -/
theorem RuttSA.of_rutt {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {t₁ : CallTree E₁ R₁}
    {t₂ : CallTree E₂ R₂} (h : Rutt RE RA RR Fail t₁ t₂) : RuttSA Sk RE RA RR Fail t₁ t₂ := by
  induction h with
  | ret h => exact .ret h
  | fail h => exact .fail h
  | vis he _ ih => exact .vis he ih

/-- **Sequencing of related trees**: related prefixes and continuations related at related
    leaves, each failed leaf continuing to a tree related to every target tree. -/
theorem RuttSA.bind {S₁ S₂ : Type} {RR' : S₁ → S₂ → Prop} {Fail' : S₁ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {t₁ : CallTree E₁ S₁} {t₂ : CallTree E₂ S₂}
    {k₁ : S₁ → CallTree E₁ R₁} {k₂ : S₂ → CallTree E₂ R₂}
    (h : RuttSA Sk RE RA RR' Fail' t₁ t₂)
    (hk : ∀ s₁ s₂, RR' s₁ s₂ → RuttSA Sk RE RA RR Fail (k₁ s₁) (k₂ s₂))
    (hf : ∀ s₁, Fail' s₁ → ∀ t, RuttSA Sk RE RA RR Fail (k₁ s₁) t) :
    RuttSA Sk RE RA RR Fail (t₁.bind k₁) (t₂.bind k₂) := by
  induction h with
  | ret h => exact hk _ _ h
  | fail h => exact hf _ h _
  | vis he _ ih => exact .vis he ih
  | skip _ ih => exact .skip ih

/-- **Skip of a source prefix**: a source tree `t.bind k₁` is related to `t₂` when the
    continuation at every leaf that `t` returns along admitted answers is. -/
theorem RuttSA.skip_bind {S : Type} {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    (t : CallTree E₁ S) {k₁ : S → CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    (h : ∀ s, RetsA Sk t s → RuttSA Sk RE RA RR Fail (k₁ s) t₂) :
    RuttSA Sk RE RA RR Fail (t.bind k₁) t₂ := by
  induction t with
  | ret s => exact h s (.ret s)
  | vis e c ih => exact .skip fun a ha => ih a fun s hs => h s (.vis ha hs)

/-- A source tree related to a target leaf at which every related source leaf failed is related
    to every target tree. -/
theorem RuttSA.of_ret_fail {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {o : R₂}
    (ho : ∀ r, RR r o → Fail r) {s : CallTree E₁ R₁} (h : RuttSA Sk RE RA RR Fail s (.ret o)) :
    ∀ t, RuttSA Sk RE RA RR Fail s t := by
  generalize ht : (CallTree.ret o : CallTree E₂ R₂) = t₂ at h
  induction h with
  | ret hr =>
    cases ht
    exact fun _ => .fail (ho _ hr)
  | fail hf => exact fun _ => .fail hf
  | vis => cases ht
  | skip _ ih => exact fun t => .skip fun a ha => ih a ha ht t

/-- **Interpretation of related trees**: under a source handler whose answers satisfy the skip
    predicate and a target handler whose answers at related events are related to those of the
    source handler, two trees related by `RuttSA` interpret to a failed source leaf or to related
    leaves. -/
theorem interp_ruttSA {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    (h₁ : ∀ e : E₁.Event, E₁.Resp e) (h₂ : ∀ e : E₂.Event, E₂.Resp e)
    (hS : ∀ e, Sk e (h₁ e)) (hh : ∀ e₁ e₂, RE e₁ e₂ → RA e₁ e₂ (h₁ e₁) (h₂ e₂))
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : RuttSA Sk RE RA RR Fail t₁ t₂) :
    Fail (interp h₁ t₁) ∨ RR (interp h₁ t₁) (interp h₂ t₂) :=
  interp_ruttS h₂ hh (ruttSA_iff_ruttS.mp
    (h.imp (fun e _ ha => ha ▸ hS e) (fun _ _ he => he) (fun _ _ _ _ _ ha => ha)
      (fun _ _ hr => hr) (fun _ hf => hf)))

end RuttSA

/-! ## Equal events -/

section Eq

variable {E : EventSig} {Sk : (e : E.Event) → E.Resp e → Prop}

/-- **Reflexivity**: a tree is related to itself at equal events and answers, at every
    reflexive relation of the leaves. -/
theorem RuttSA.refl {R : Type} {RR : R → R → Prop} {Fail : R → Prop} (hR : ∀ r, RR r r)
    (t : CallTree E R) :
    RuttSA Sk (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail t t := by
  induction t with
  | ret r => exact .ret (hR r)
  | vis e c ih =>
    refine .vis rfl fun a₁ a₂ ha => ?_
    cases ha
    exact ih a₁

end Eq

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA
