/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubst

/-!
# Composition and substitution of trees related with skips at an answer predicate

The relation `RuttSA` composes with `RuttSA` (`RuttSA.trans`) and with the fuel relation
`RuttFA` of the back half (`RuttSA.trans_ruttFA`). Where the second relation skips an
intermediate event that the first relates to a source event, the source event is skipped: every
source answer admitted by the source skip predicate needs an intermediate answer admitted by the
intermediate skip predicate and related to it. At the answers of handlers this is the side
condition `RA₁ e₀ e₁ (h₀ e₀) (h₁ e₁)` of `RuttS.trans` and `RuttS.trans_ruttF`.

Answering the source events outside `keep` by a handler whose answers are admitted keeps the
relation (`RuttSA.answerOut`), and so does substitution of the events by trees whose returned
leaves are admitted answers (`RuttSA.substK`).

## Main results

* `RuttSA.trans`, `RuttSA.trans_ruttFA`: composition.
* `RuttSA.answerOut`: events outside `keep` answered by a handler.
* `RuttSA.substK`: substitution with failed answers.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSAComp

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (CompRE CompRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle (RuttFA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeSubst (substT substT_ret substT_vis)

/-! ## Composition -/

section Compose

variable {E₀ E₁ E₂ : EventSig} {R₀ R₁ R₂ : Type}
  {Sk₀ : (e : E₀.Event) → E₀.Resp e → Prop} {Sk₁ : (e : E₁.Event) → E₁.Resp e → Prop}
  {RE₁ : E₀.Event → E₁.Event → Prop}
  {RA₁ : (e₀ : E₀.Event) → (e₁ : E₁.Event) → E₀.Resp e₀ → E₁.Resp e₁ → Prop}
  {RE₂ : E₁.Event → E₂.Event → Prop}
  {RA₂ : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
  {RR₁ : R₀ → R₁ → Prop} {RR₂ : R₁ → R₂ → Prop} {F : R₀ → Prop} {F' : R₁ → Prop}

/-- **Two relations with skips at answer predicates compose.** Let every source answer admitted
    by `Sk₀` at an event related by `RE₁` to an intermediate event have a related intermediate
    answer admitted by `Sk₁`, and let a source leaf related to a failed intermediate leaf be
    failed. Then the relations of `t₀` with `t₁` and of `t₁` with `t₂` give the relation of `t₀`
    and `t₂` at the compositions of the relations and the skip predicate `Sk₀`. -/
theorem RuttSA.trans
    (hh : ∀ e₀ e₁, RE₁ e₀ e₁ → ∀ a₀, Sk₀ e₀ a₀ → ∃ a₁, Sk₁ e₁ a₁ ∧ RA₁ e₀ e₁ a₀ a₁)
    (hF : ∀ r₀ r₁, RR₁ r₀ r₁ → F' r₁ → F r₀)
    {t₀ : CallTree E₀ R₀} {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    (h01 : RuttSA Sk₀ RE₁ RA₁ RR₁ F t₀ t₁) (h12 : RuttSA Sk₁ RE₂ RA₂ RR₂ F' t₁ t₂) :
    RuttSA Sk₀ (CompRE RE₁ RE₂) (CompRA RE₁ RE₂ RA₁ RA₂) (Relation.Comp RR₁ RR₂) F t₀ t₂ := by
  induction h01 generalizing t₂ with
  | ret h =>
    cases h12 with
    | ret h' => exact .ret ⟨_, h, h'⟩
    | fail h' => exact .fail (hF _ _ h h')
  | fail h => exact .fail h
  | @vis e₀ e₁ k₀ k₁ he _ ih =>
    cases h12 with
    | vis he' hk' =>
      refine .vis ⟨e₁, he, he'⟩ fun a₀ a₂ ha => ?_
      obtain ⟨a₁, ha₁, ha₂⟩ := ha e₁ he he'
      exact ih a₀ a₁ ha₁ (hk' a₁ a₂ ha₂)
    | skip hk' =>
      refine .skip fun a₀ ha₀ => ?_
      obtain ⟨a₁, hs₁, ha₁⟩ := hh _ _ he a₀ ha₀
      exact ih a₀ a₁ ha₁ (hk' a₁ hs₁)
  | skip _ ih => exact .skip fun a ha => ih a ha h12

/-- **A relation with skips followed by a relation with a family composes**: under the
    hypotheses of `RuttSA.trans`, `RuttSA Sk₀ RE₁ RA₁ RR₁ F t₀ t₁` and
    `RuttFA Sk₁ RE₂ RA₂ RR₂ F' t₁ T` give the relation of `t₀` and `T` at the compositions of the
    relations and the skip predicate `Sk₀`. -/
theorem RuttSA.trans_ruttFA
    (hh : ∀ e₀ e₁, RE₁ e₀ e₁ → ∀ a₀, Sk₀ e₀ a₀ → ∃ a₁, Sk₁ e₁ a₁ ∧ RA₁ e₀ e₁ a₀ a₁)
    (hF : ∀ r₀ r₁, RR₁ r₀ r₁ → F' r₁ → F r₀)
    {t₀ : CallTree E₀ R₀} {t₁ : CallTree E₁ R₁} {T : Nat → CallTree E₂ R₂}
    (h01 : RuttSA Sk₀ RE₁ RA₁ RR₁ F t₀ t₁) (h12 : RuttFA Sk₁ RE₂ RA₂ RR₂ F' t₁ T) :
    RuttFA Sk₀ (CompRE RE₁ RE₂) (CompRA RE₁ RE₂ RA₁ RA₂) (Relation.Comp RR₁ RR₂) F t₀ T := by
  induction h01 generalizing T with
  | ret h =>
    cases h12 with
    | ret n hT h' => exact .ret n hT ⟨_, h, h'⟩
    | fail h' => exact .fail (hF _ _ h h')
  | fail h => exact .fail h
  | @vis e₀ e₁ k₀ k₁ he _ ih =>
    cases h12 with
    | vis n hT he' hk' =>
      refine .vis n hT ⟨e₁, he, he'⟩ fun a₀ a₂ ha => ?_
      obtain ⟨a₁, ha₁, ha₂⟩ := ha e₁ he he'
      exact ih a₀ a₁ ha₁ (hk' a₁ a₂ ha₂)
    | skip hk' =>
      refine .skip fun a₀ ha₀ => ?_
      obtain ⟨a₁, hs₁, ha₁⟩ := hh _ _ he a₀ ha₀
      exact ih a₀ a₁ ha₁ (hk' a₁ hs₁)
  | skip _ ih => exact .skip fun a ha => ih a ha h12

end Compose

/-! ## Events answered by a handler -/

section AnswerOut

variable {E E₂ : EventSig} {R R₂ : Type}

/-- **Answering events outside `keep`**: when every event that `RE` relates to a target event
    satisfies `keep` and the answers of the handler `h` at the other events are admitted by the
    skip predicate, a relation by `RuttSA` holds from the tree whose events outside `keep` are
    answered by `h`. -/
theorem RuttSA.answerOut {Sk : (e : E.Event) → E.Resp e → Prop} {h : ∀ e : E.Event, E.Resp e}
    {RE : E.Event → E₂.Event → Prop}
    {RA : (e₁ : E.Event) → (e₂ : E₂.Event) → E.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R → R₂ → Prop} {Fail : R → Prop} (keep : E.Event → Bool)
    (hkeep : ∀ e₁ e₂, RE e₁ e₂ → keep e₁ = true) (hS : ∀ e, keep e = false → Sk e (h e))
    {t₁ : CallTree E R} {t₂ : CallTree E₂ R₂} (hr : RuttSA Sk RE RA RR Fail t₁ t₂) :
    RuttSA Sk RE RA RR Fail (NFProgCallTreeCompose.answerOut keep h t₁) t₂ := by
  induction hr with
  | ret h => exact .ret h
  | fail h => exact .fail h
  | @vis e₁ e₂ k₁ k₂ he _ ih =>
    simp only [NFProgCallTreeCompose.answerOut, hkeep _ _ he, ite_true]
    exact .vis he ih
  | @skip e₁ k₁ t₂ _ ih =>
    by_cases hk : keep e₁ = true
    · simp only [NFProgCallTreeCompose.answerOut, hk, ite_true]
      exact .skip ih
    · simp only [NFProgCallTreeCompose.answerOut, hk, Bool.false_eq_true, ite_false]
      exact ih _ (hS _ (by simpa using hk))

end AnswerOut

/-! ## Substitution with failed answers -/

section Subst

variable {E₁ E₂ E₁' E₂' : EventSig} {R₁ R₂ : Type}

/-- **Substitution keeps `RuttSA`, with failed answers.** Let `t₁` and `t₂` be related by
    `RuttSA` at the skip predicate `Sk`, and `t₂` satisfy an invariant `K` under which every
    event satisfies `G`, its continuation at the answer `kill` is a leaf at which every related
    source leaf failed, and every continuation satisfies `K`. Substitute `σ₁` in `t₁` and `σ₂`
    in `t₂`. When the substituted trees of related events, the target event satisfying `G`, are
    related at the skip predicate `Sk'`, a source leaf related by the answer relation to the
    target leaf or to the answer `kill`, and a source leaf failed when the answer relation
    relates it to `kill`, and when every leaf that the substituted tree of a source event returns
    along answers admitted by `Sk'` is admitted by `Sk`, the substituted trees are related. -/
theorem RuttSA.substK {Sk : (e : E₁.Event) → E₁.Resp e → Prop}
    {Sk' : (e : E₁'.Event) → E₁'.Resp e → Prop}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RE' : E₁'.Event → E₂'.Event → Prop}
    {RA' : (e₁ : E₁'.Event) → (e₂ : E₂'.Event) → E₁'.Resp e₁ → E₂'.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    {σ₁ : ∀ e : E₁.Event, CallTree E₁' (E₁.Resp e)} {σ₂ : ∀ e : E₂.Event, CallTree E₂' (E₂.Resp e)}
    (kill : ∀ e : E₂.Event, E₂.Resp e) {G : E₂.Event → Prop} {K : CallTree E₂ R₂ → Prop}
    (hK : ∀ e k, K (.vis e k) →
      G e ∧ (∃ o, k (kill e) = .ret o ∧ ∀ r, RR r o → Fail r) ∧ ∀ a, K (k a))
    (hσ : ∀ e₁ e₂, RE e₁ e₂ → G e₂ →
      RuttSA Sk' RE' RA' (fun a₁ a₂ => RA e₁ e₂ a₁ a₂ ∨ RA e₁ e₂ a₁ (kill e₂))
        (fun a₁ => RA e₁ e₂ a₁ (kill e₂)) (σ₁ e₁) (σ₂ e₂))
    (hh : ∀ e₁ a, RetsA Sk' (σ₁ e₁) a → Sk e₁ a)
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : RuttSA Sk RE RA RR Fail t₁ t₂) :
    K t₂ → RuttSA Sk' RE' RA' RR Fail (substT σ₁ t₁) (substT σ₂ t₂) := by
  induction h with
  | ret h => exact fun _ => .ret h
  | fail h => exact fun _ => .fail h
  | @vis e₁ e₂ k₁ k₂ he _ ih =>
    intro hKt
    obtain ⟨hG, ⟨o, hko, ho⟩, hKk⟩ := hK _ _ hKt
    rw [substT_vis, substT_vis]
    refine RuttSA.bind (hσ _ _ he hG) (fun a₁ a₂ ha => ?_) (fun a₁ ha t => ?_)
    · rcases ha with ha | ha
      · exact ih a₁ a₂ ha (hKk a₂)
      · have H := ih a₁ (kill e₂) ha (hKk _)
        rw [hko, substT_ret] at H
        exact RuttSA.of_ret_fail ho H _
    · have H := ih a₁ (kill e₂) ha (hKk _)
      rw [hko, substT_ret] at H
      exact RuttSA.of_ret_fail ho H _
  | @skip e₁ k₁ t₂ _ ih =>
    intro hKt
    rw [substT_vis]
    exact RuttSA.skip_bind (σ₁ e₁) fun a ha => ih a (hh _ _ ha) hKt

end Subst

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSAComp
