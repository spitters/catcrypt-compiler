/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvent

/-!
# Composition of related trees at the events of the trees

`NFProgCallTreeChain.RuttS.trans` composes two relations of trees under the condition that the
intermediate handler answers every pair of events related by the first relation as the source
handler does, at every such pair of events. The condition is used only where the second relation
skips an event of the intermediate tree that the first relation relates to an event of the source
tree. Restricted to the events of the two trees (`AllEvT`), it is a condition on the calls the
trees perform only. The condition on every related pair asks more: the relation of the
translation `ExtRE` relates leaf calls of different types to one call of `catCryptDialect`
(`catTy` sends a word, an integer and an unsigned integer of 64 bits to the same word), and the
leaf table need not answer them by values related to one answer.

## Main results

* `RuttS.trans_allEvT`: the composition of `RuttS.trans` with the condition on the intermediate
  handler restricted to the events of the source tree and of the intermediate tree.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTransEv

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (CompRE CompRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvent (AllEvT)

variable {E₀ E₁ E₂ : EventSig}

/-- **Two relations of trees compose at the events of the trees.** As
    `NFProgCallTreeChain.RuttS.trans`, with the condition on the intermediate handler `h₁` asked
    only at events `e₀` of the source tree (`P₀`) and `e₁` of the intermediate tree (`P₁`). -/
theorem RuttS.trans_allEvT {R₀ R₁ R₂ : Type} {h₀ : ∀ e : E₀.Event, E₀.Resp e}
    {h₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE₁ : E₀.Event → E₁.Event → Prop} {RE₂ : E₁.Event → E₂.Event → Prop}
    {RA₁ : (e₀ : E₀.Event) → (e₁ : E₁.Event) → E₀.Resp e₀ → E₁.Resp e₁ → Prop}
    {RA₂ : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR₁ : R₀ → R₁ → Prop} {RR₂ : R₁ → R₂ → Prop} {F : R₀ → Prop} {F' : R₁ → Prop}
    {P₀ : E₀.Event → Prop} {P₁ : E₁.Event → Prop}
    (hh : ∀ e₀ e₁, P₀ e₀ → P₁ e₁ → RE₁ e₀ e₁ → RA₁ e₀ e₁ (h₀ e₀) (h₁ e₁))
    (hF : ∀ r₀ r₁, RR₁ r₀ r₁ → F' r₁ → F r₀)
    {t₀ : CallTree E₀ R₀} {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    (h01 : RuttS h₀ RE₁ RA₁ RR₁ F t₀ t₁) (h12 : RuttS h₁ RE₂ RA₂ RR₂ F' t₁ t₂)
    (hP₀ : AllEvT P₀ t₀) (hP₁ : AllEvT P₁ t₁) :
    RuttS h₀ (CompRE RE₁ RE₂) (CompRA RE₁ RE₂ RA₁ RA₂) (Relation.Comp RR₁ RR₂) F t₀ t₂ := by
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
      exact ih a₀ a₁ ha₁ (hk' a₁ a₂ ha₂) (hP₀.2 a₀) (hP₁.2 a₁)
    | skip hk' =>
      exact .skip (ih _ _ (hh _ _ hP₀.1 hP₁.1 he) hk' (hP₀.2 _) (hP₁.2 _))
  | skip _ ih => exact .skip (ih h12 (hP₀.2 _) hP₁)

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTransEv
