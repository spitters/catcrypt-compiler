/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract
public import CatCryptCore.Relational.Rules
public import CatCryptCore.Prob.Support

/-!
# Probabilistic interpretation of related call trees

`interp_rutt` and `interp_ruttS` interpret two related call trees under pure handlers. This
module gives their counterparts for the interpretation `interpSP` in stateful probabilistic
computations, as judgments `rHoare` of the probabilistic relational Hoare logic.

The handlers are coupled: at related events, the computations of the two handlers are coupled
with answers related by the answer relation, and a relation `I` of the heaps is kept. A source
leaf that fails is related to every target tree; a coupling of a point mass with the
interpretation of the target tree exists only when the latter does not fail, so the target
handler is required not to fail (`HandlerNoFail`). With skipped source events (`RuttS`), the
source handler is the point mass at a pure handler `h₁`, so that a skipped event continues at
the answer `h₁ e`.

For the linked functions of a module `m`, the source handler is the point mass at the meanings
`linkHandler m`. Because `contractRAC` fixes the source answer to the meaning, a source handler
coupled with a target handler on it is this point mass; `HandlerCoupledC` is a target handler in
`SPComp` coupled with it on the separation contracts, the probabilistic form of
`HandlerMeetsC`.

## Main definitions

* `HandlerCoupled`: two handlers in `SPComp` coupled at related events.
* `HandlerNoFail`: a handler in `SPComp` that does not fail.
* `HandlerCoupledC`: a target handler coupled with the meanings of the linked functions on the
  separation contracts.

## Main results

* `interpSP_noFail`: under a handler that does not fail, an interpretation does not fail.
* `interpSP_rutt`: trees related by `Rutt` interpret, under coupled handlers, to a failed source
  leaf or to related leaves at related heaps.
* `interpSP_ruttS`: the same for trees related by `RuttS`, at the point mass of the source
  handler.
* `handlerCoupledC_of_handlerMeetsC`: the point mass of a target handler meeting the separation
  contracts is coupled with the meanings on them.
* `interpSP_ruttS_contract`: `interpSP_ruttS` at the separation contracts of the linked
  functions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSP

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax (HaxModule)

/-! ## Coupled handlers -/

section Generic

variable {E₁ E₂ : EventSig} {R₁ R₂ : Type}

/-- **Two handlers in `SPComp` coupled at related events**: at events related by `RE`, from
    heaps related by `I`, the computations of the two handlers are coupled with answers related
    by `RA` and final heaps related by `I`. -/
def HandlerCoupled (I : RPre) (RE : E₁.Event → E₂.Event → Prop)
    (RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop)
    (h₁ : ∀ e : E₁.Event, SPComp (E₁.Resp e)) (h₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e)) :
    Prop :=
  ∀ e₁ e₂, RE e₁ e₂ → rHoare I (h₁ e₁) (h₂ e₂) (fun a₁ s₁ a₂ s₂ => RA e₁ e₂ a₁ a₂ ∧ I s₁ s₂)

/-- A handler in `SPComp` that does not fail: at every event and every heap, the computation
    of the handler has failure weight zero. -/
def HandlerNoFail {E : EventSig} (h : ∀ e : E.Event, SPComp (E.Resp e)) : Prop :=
  ∀ e s, (h e s) none = 0

/-- **Interpretation under a handler that does not fail does not fail.** -/
theorem interpSP_noFail {E : EventSig} {R : Type} {h : ∀ e : E.Event, SPComp (E.Resp e)}
    (hh : HandlerNoFail h) (t : CallTree E R) (s : Heap) : (interpSP h t s) none = 0 := by
  induction t generalizing s with
  | ret r => exact SDistr.pure_apply_none _
  | vis e k ih =>
    rw [interpSP_vis, SPComp.bind_def, SDistr.bind_apply_none, hh e s]
    simp [ih]

/-- A point mass on the left is coupled with a computation that does not fail, for every
    postcondition that holds at the left value and its heap and at every right outcome. -/
theorem rHoare_pure_left_of_noFail {α β : Type} {Φ : RPre} {a : α} {c : SPComp β}
    {Ψ : RPost α β} (hc : ∀ s, (c s) none = 0)
    (hΨ : ∀ s₁ s₂, Φ s₁ s₂ → ∀ b s₂', Ψ a s₁ b s₂') :
    rHoare Φ (SPComp.pure a) c Ψ := by
  intro s₁ s₂ hΦ
  refine ⟨Coupling.prod _ _ (SDistr.mass_pure _) (by simp [SDistr.mass, hc s₂]), ?_⟩
  intro p₁ p₂ hp
  have h1 : p₁ = (a, s₁) := by
    have := Coupling.in_left_support _ hp
    classical
    simpa [SPComp.pure, SDistr.pure, PMF.pure_apply, eq_comm] using this
  rw [h1]
  exact hΨ s₁ s₂ hΦ p₂.1 p₂.2

/-- **Probabilistic interpretation of related trees.** Under handlers coupled at related events,
    with a target handler that does not fail, two trees related by `Rutt` interpret, from heaps
    related by `I`, to a failed source leaf or to leaves related by `RR` at heaps related by
    `I`. -/
theorem interpSP_rutt {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {I : RPre}
    {h₁ : ∀ e : E₁.Event, SPComp (E₁.Resp e)} {h₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e)}
    (hc : HandlerCoupled I RE RA h₁ h₂) (hf : HandlerNoFail h₂)
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : Rutt RE RA RR Fail t₁ t₂) :
    rHoare I (interpSP h₁ t₁) (interpSP h₂ t₂)
      (fun r₁ s₁ r₂ s₂ => Fail r₁ ∨ (RR r₁ r₂ ∧ I s₁ s₂)) := by
  induction h with
  | ret h => exact rHoare_ret fun _ _ hI => .inr ⟨h, hI⟩
  | fail h =>
    exact rHoare_pure_left_of_noFail (interpSP_noFail hf _) fun _ _ _ _ _ => .inl h
  | vis he _ ih =>
    refine rHoare_bind (hc _ _ he) ?_
    intro a₁ a₂ s₁ s₂ hΨ
    exact ih a₁ a₂ hΨ.1 s₁ s₂ hΨ.2

/-- **Probabilistic interpretation of trees related with skipped source events.** Under a
    target handler that does not fail, coupled at related events with the point mass of the
    source handler `h₁`, two trees related by `RuttS` at `h₁` interpret, from heaps related by
    `I`, to a failed source leaf or to leaves related by `RR` at heaps related by `I`. -/
theorem interpSP_ruttS {h₁ : ∀ e : E₁.Event, E₁.Resp e} {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {I : RPre}
    {h₂ : ∀ e : E₂.Event, SPComp (E₂.Resp e)}
    (hc : HandlerCoupled I RE RA (fun e => SPComp.pure (h₁ e)) h₂) (hf : HandlerNoFail h₂)
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : RuttS h₁ RE RA RR Fail t₁ t₂) :
    rHoare I (interpSP (fun e => SPComp.pure (h₁ e)) t₁) (interpSP h₂ t₂)
      (fun r₁ s₁ r₂ s₂ => Fail r₁ ∨ (RR r₁ r₂ ∧ I s₁ s₂)) := by
  induction h with
  | ret h => exact rHoare_ret fun _ _ hI => .inr ⟨h, hI⟩
  | fail h =>
    exact rHoare_pure_left_of_noFail (interpSP_noFail hf _) fun _ _ _ _ _ => .inl h
  | vis he _ ih =>
    refine rHoare_bind (hc _ _ he) ?_
    intro a₁ a₂ s₁ s₂ hΨ
    exact ih a₁ a₂ hΨ.1 s₁ s₂ hΨ.2
  | skip _ ih =>
    rw [interpSP_vis, SPComp.pure_bind]
    exact ih

end Generic

/-! ## The separation contracts of the linked functions -/

/-- **A target handler in `SPComp` coupled with the meanings of the linked functions on the
    separation contracts**: at events related by `contractRE`, from heaps related by `I`, the
    point mass at the meaning `linkHandler m` and the target handler are coupled with answers
    related by `contractRAC` and final heaps related by `I`. -/
def HandlerCoupledC (m : HaxModule) (I : RPre)
    (h₂ : ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)) : Prop :=
  HandlerCoupled I (contractRE m) (contractRAC m) (fun e => SPComp.pure (linkHandler m e)) h₂

/-- **The point mass of a handler meeting the separation contracts is coupled with the
    meanings on them**, at the equality of heaps. -/
theorem handlerCoupledC_of_handlerMeetsC {m : HaxModule}
    {h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e} (h : HandlerMeetsC m h₂) :
    HandlerCoupledC m eqPre (fun e => SPComp.pure (h₂ e)) := by
  intro e₁ e₂ he
  exact rHoare_ret fun _ _ hs => ⟨h e₁ e₂ he, hs⟩

/-- **Probabilistic interpretation at the separation contracts.** Under a target handler that
    does not fail and is coupled with the meanings of the linked functions of `m` on the
    separation contracts, two trees related by `RuttS` at the meanings, `contractRE` and
    `contractRAC` interpret, from heaps related by `I`, to a failed source leaf or to leaves
    related by `RR` at heaps related by `I`. -/
theorem interpSP_ruttS_contract {m : HaxModule} {R₁ R₂ : Type} {RR : R₁ → R₂ → Prop}
    {Fail : R₁ → Prop} {I : RPre}
    {h₂ : ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hc : HandlerCoupledC m I h₂) (hf : HandlerNoFail h₂)
    {t₁ : CallTree linkSig R₁} {t₂ : CallTree (kSig AState) R₂}
    (h : RuttS (linkHandler m) (contractRE m) (contractRAC m) RR Fail t₁ t₂) :
    rHoare I (interpSP (fun e => SPComp.pure (linkHandler m e)) t₁) (interpSP h₂ t₂)
      (fun r₁ s₁ r₂ s₂ => Fail r₁ ∨ (RR r₁ r₂ ∧ I s₁ s₂)) :=
  interpSP_ruttS hc hf h

end CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSP
