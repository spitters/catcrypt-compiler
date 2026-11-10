/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract
public import PolyFun.ITree.Bisim.CrossSignature

/-!
# Finite call trees embedded in the interaction trees of PolyFun

The finite call tree `CallTree E R` of the chain of `compileA` embeds in the coinductive
interaction tree `_root_.ITree (sigPF E) R` of PolyFun: an event signature is a polynomial functor,
a leaf is a `pure` node and an event is a `query` node. The embedding `toITree` has no silent
steps, commutes with sequencing and is injective.

On the images of finite trees the relation up to tau `ITree.CrossSignatureWeakBisim` is the
fragment of `Rutt` without failed source leaves: `Rutt` at the empty failure predicate is
equivalent to `CrossSignatureWeakBisim` of the images, at the event, answer and leaf relations
that `Rutt` carries. Bisimilar images give `RuttS` at every source handler and failure predicate.

## Main definitions

* `sigPF`: the polynomial functor of an event signature.
* `toITree`: the embedding of finite call trees in interaction trees.
* `sigRel`: the relation of event signatures given by an event and an answer relation.

## Main results

* `toITree_bind`: the embedding commutes with sequencing.
* `toITree_injective`: the embedding is injective.
* `rutt_iff_crossSignatureWeakBisim`: `Rutt` at the empty failure predicate is
  `CrossSignatureWeakBisim` of the images.
* `ruttS_of_crossSignatureWeakBisim`: bisimilar images are related by `RuttS`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeRutt

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract
open _root_.ITree (CrossSignatureWeakBisim EventSignatureRel TauSteps shape'_pure shape'_query)

/-! ## The embedding -/

/-- The polynomial functor of an event signature: positions are events, directions answers. -/
def sigPF (E : EventSig) : PFunctor.{0, 0} where
  A := E.Event
  B := E.Resp

/-- The interaction tree of a finite call tree: a leaf is a `pure` node and an event a `query`
    node. The image has no silent steps. -/
def toITree {E : EventSig} {R : Type} : CallTree E R → _root_.ITree (sigPF E) R
  | .ret r => _root_.ITree.pure r
  | .vis e c => _root_.ITree.query e (fun a => toITree (c a))

/-- The embedding commutes with sequencing. -/
theorem toITree_bind {E : EventSig} {α β : Type} (t : CallTree E α) (k : α → CallTree E β) :
    toITree (t.bind k) = _root_.ITree.bind (toITree t) (fun a => toITree (k a)) := by
  induction t with
  | ret a => simp only [CallTree.bind, toITree, _root_.ITree.bind_pure_left]
  | vis e c ih =>
    simp only [CallTree.bind, toITree]
    exact (congrArg (_root_.ITree.query (F := sigPF E) e) (funext ih)).trans
      (_root_.ITree.bind_query (F := sigPF E) e (fun a => toITree (c a)) _).symm

/-- The relation of event signatures given by a relation on events and a relation on answers. -/
def sigRel {E₁ E₂ : EventSig} (RE : E₁.Event → E₂.Event → Prop)
    (RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop) :
    EventSignatureRel (sigPF E₁) (sigPF E₂) where
  event := RE
  reply := fun e₁ e₂ _ a₁ a₂ => RA e₁ e₂ a₁ a₂

/-! ## Inversion at observable heads -/

section Inversion

variable {E F : PFunctor.{0, 0}} {α β : Type} {er : EventSignatureRel E F} {RR : α → β → Prop}

/-- Bisimilar `pure` trees have related leaves. -/
theorem cswb_pure_pure_inv {a : α} {b : β}
    (h : CrossSignatureWeakBisim er RR (_root_.ITree.pure a) (_root_.ITree.pure b)) : RR a b := by
  obtain ⟨t', s', ht, hs, hm⟩ := h.dest
  obtain rfl := TauSteps.rigid_of_pure a (shape'_pure a) ht
  obtain rfl := TauSteps.rigid_of_pure b (shape'_pure b) hs
  cases hm with
  | pure x y hxy ht' hs' =>
    rw [shape'_pure] at ht' hs'
    cases ht'
    cases hs'
    exact hxy
  | query _ _ _ _ _ ht' _ _ => rw [shape'_pure] at ht'; cases ht'
  | tau _ _ ht' _ _ => rw [shape'_pure] at ht'; cases ht'

/-- A `pure` tree is not bisimilar to a `query` tree. -/
theorem cswb_pure_query_false {a : α} {b : F.A} {l : F.B b → _root_.ITree F β}
    (h : CrossSignatureWeakBisim er RR (_root_.ITree.pure a) (_root_.ITree.query b l)) : False := by
  obtain ⟨t', s', ht, hs, hm⟩ := h.dest
  obtain rfl := TauSteps.rigid_of_pure a (shape'_pure a) ht
  obtain rfl := TauSteps.rigid_of_query b l (shape'_query b l) hs
  cases hm with
  | pure _ _ _ _ hs' => rw [shape'_query] at hs'; cases hs'
  | query _ _ _ _ _ ht' _ _ => rw [shape'_pure] at ht'; cases ht'
  | tau _ _ ht' _ _ => rw [shape'_pure] at ht'; cases ht'

/-- A `query` tree is not bisimilar to a `pure` tree. -/
theorem cswb_query_pure_false {a : E.A} {k : E.B a → _root_.ITree E α} {b : β}
    (h : CrossSignatureWeakBisim er RR (_root_.ITree.query a k) (_root_.ITree.pure b)) : False := by
  obtain ⟨t', s', ht, hs, hm⟩ := h.dest
  obtain rfl := TauSteps.rigid_of_query a k (shape'_query a k) ht
  obtain rfl := TauSteps.rigid_of_pure b (shape'_pure b) hs
  cases hm with
  | pure _ _ _ ht' _ => rw [shape'_query] at ht'; cases ht'
  | query _ _ _ _ _ _ hs' _ => rw [shape'_pure] at hs'; cases hs'
  | tau _ _ ht' _ _ => rw [shape'_query] at ht'; cases ht'

/-- Bisimilar `query` trees have related events and continuations bisimilar at related
    replies. -/
theorem cswb_query_query_inv {a : E.A} {k : E.B a → _root_.ITree E α} {b : F.A}
    {l : F.B b → _root_.ITree F β}
    (h : CrossSignatureWeakBisim er RR (_root_.ITree.query a k) (_root_.ITree.query b l)) :
    ∃ hab : er.event a b, ∀ x y, er.reply a b hab x y →
      CrossSignatureWeakBisim er RR (k x) (l y) := by
  obtain ⟨t', s', ht, hs, hm⟩ := h.dest
  obtain rfl := TauSteps.rigid_of_query a k (shape'_query a k) ht
  obtain rfl := TauSteps.rigid_of_query b l (shape'_query b l) hs
  cases hm with
  | pure _ _ _ ht' _ => rw [shape'_query] at ht'; cases ht'
  | query a' b' hab ct cs ht' hs' hc =>
    rw [shape'_query] at ht' hs'
    cases ht'
    cases hs'
    exact ⟨hab, hc⟩
  | tau _ _ ht' _ _ => rw [shape'_query] at ht'; cases ht'

end Inversion

/-! ## The relations on images of finite trees -/

section Relation

variable {E₁ E₂ : EventSig} {R₁ R₂ : Type} {RE : E₁.Event → E₂.Event → Prop}
  {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
  {RR : R₁ → R₂ → Prop}

/-- `Rutt` at the empty failure predicate gives `CrossSignatureWeakBisim` of the images. -/
theorem crossSignatureWeakBisim_of_rutt {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    (h : Rutt RE RA RR (fun _ => False) t₁ t₂) :
    CrossSignatureWeakBisim (sigRel RE RA) RR (toITree t₁) (toITree t₂) := by
  induction h with
  | ret h =>
    simp only [toITree]
    exact .pure h
  | fail h => exact h.elim
  | vis he _ ih =>
    simp only [toITree]
    exact .query _ _ he _ _ ih

/-- `CrossSignatureWeakBisim` of the images gives `Rutt` at the empty failure predicate. -/
theorem rutt_of_crossSignatureWeakBisim {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    (h : CrossSignatureWeakBisim (sigRel RE RA) RR (toITree t₁) (toITree t₂)) :
    Rutt RE RA RR (fun _ => False) t₁ t₂ := by
  induction t₁ generalizing t₂ with
  | ret r₁ =>
    cases t₂ with
    | ret r₂ =>
      simp only [toITree] at h
      exact .ret (cswb_pure_pure_inv h)
    | vis e c =>
      simp only [toITree] at h
      exact (cswb_pure_query_false h).elim
  | vis e₁ k₁ ih =>
    cases t₂ with
    | ret r₂ =>
      simp only [toITree] at h
      exact (cswb_query_pure_false h).elim
    | vis e₂ k₂ =>
      simp only [toITree] at h
      obtain ⟨he, hk⟩ := cswb_query_query_inv h
      exact .vis he fun a₁ a₂ ha => ih a₁ (hk a₁ a₂ ha)

/-- **`Rutt` at the empty failure predicate is `CrossSignatureWeakBisim` of the images**, at the
    event, answer and leaf relations that `Rutt` carries. -/
theorem rutt_iff_crossSignatureWeakBisim {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} :
    Rutt RE RA RR (fun _ => False) t₁ t₂ ↔
      CrossSignatureWeakBisim (sigRel RE RA) RR (toITree t₁) (toITree t₂) :=
  ⟨crossSignatureWeakBisim_of_rutt, rutt_of_crossSignatureWeakBisim⟩

/-- **Bisimilar images are related by `RuttS`**, at every source handler and every failure
    predicate. -/
theorem ruttS_of_crossSignatureWeakBisim (h₁ : ∀ e : E₁.Event, E₁.Resp e) (Fail : R₁ → Prop)
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    (h : CrossSignatureWeakBisim (sigRel RE RA) RR (toITree t₁) (toITree t₂)) :
    RuttS h₁ RE RA RR Fail t₁ t₂ := by
  have hr := rutt_of_crossSignatureWeakBisim h
  clear h
  induction hr with
  | ret h => exact .ret h
  | fail h => exact h.elim
  | vis he _ ih => exact .vis he ih

end Relation

/-! ## Injectivity -/

/-- `Rutt` at equal events, answers and leaves and the empty failure predicate is equality. -/
theorem eq_of_rutt_eq {E : EventSig} {R : Type} {t s : CallTree E R}
    (h : Rutt (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) (fun r₁ r₂ => r₁ = r₂)
      (fun _ => False) t s) : t = s := by
  induction h with
  | ret h => rw [h]
  | fail h => exact h.elim
  | vis he _ ih =>
    cases he
    congr
    funext a
    exact ih a a HEq.rfl

/-- The embedding of finite call trees in interaction trees is injective. -/
theorem toITree_injective {E : EventSig} {R : Type} :
    Function.Injective (toITree : CallTree E R → _root_.ITree (sigPF E) R) := by
  intro t s hts
  have h : CrossSignatureWeakBisim (sigRel (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂))
      (fun r₁ r₂ => r₁ = r₂) (toITree t) (toITree s) := by
    rw [← hts]
    exact CrossSignatureWeakBisim.refl (toITree t)
  exact eq_of_rutt_eq (rutt_of_crossSignatureWeakBisim h)

end CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeRutt
