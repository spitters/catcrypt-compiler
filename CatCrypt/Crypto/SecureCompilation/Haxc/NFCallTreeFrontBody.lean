/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeLetsInto
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeMapClosure
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeWhileTrue
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeANorm3
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInlineSpineBlocks
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFFront
public import CatCrypt.Crypto.Hax.HaxFrontOracle

/-!
# The body of the front after the inlining of closures, at the level of call trees

The front prepares a body by inlining let-bound closures (`inlineSpine`), moving bindings into
statements (`letsInto`), rewriting `map` over closure literals (`inlineMapClosures`),
A-normalisation (`aNormalizeTotal`), reading the literal counts of `repeat`
(`repeatCountInline`), choosing among the normal form and its rewritings (`anfEPick`) and
rewriting `while true` loops onto a flag (`wtFn`). Every stage after the first relates the call
trees of its input and output by `RuttS` at equal events and answers; their composition relates
the call tree of `inlineSpine e` to the call tree of the body `haxFrontBodyP O e`, a value leaf
matched by a leaf whose outcome is related by `RetRel`, the other leaves failed.

## Main results

* `RuttS.mono_fail`: a relation by `RuttS` holds at every larger set of failed source leaves.
* `BodyRel.trans`: the relation of the composed stages is transitive.
* `prepBody_relT`: the call tree of `inlineSpine e` and that of `haxFrontBodyP O e`.
* `body_relT`: the call tree of `e`, its closures read as internal table entries, and that of
  `haxFrontBodyP O e`, when the arguments of the calls of inlined closures are call-free
  (`spineArgsOk`).
* `nfBody_relT`: the same for the body `nfBody te` of the front.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontBody

open _root_.Hax
open _root_.Hax.InlineLocalClosures (IsErr inlineSpine)
open _root_.Hax.EarlyReturnElim (RetRel)
open CatCrypt.Crypto.Hax (haxFrontBodyP haxFrontOkP haxFrontRouteOkP haxFrontAnfEP haxFrontAnf
  haxFrontPrep haxFrontFlag FrontOracle)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)

variable {E : EventSig}

/-- **Monotonicity in the failed leaves**: trees related by `RuttS` with the failed source leaves
    `F` are related with every larger set of failed source leaves. -/
theorem RuttS.mono_fail {E₁ E₂ : EventSig} {R₁ R₂ : Type} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {F F' : R₁ → Prop} (hF : ∀ r, F r → F' r) {t₁ : CallTree E₁ R₁}
    {t₂ : CallTree E₂ R₂} (h : RuttS h₁ RE RA RR F t₁ t₂) : RuttS h₁ RE RA RR F' t₁ t₂ := by
  induction h with
  | ret h => exact .ret h
  | fail h => exact .fail (hF _ h)
  | vis he _ ih => exact .vis he ih
  | skip _ ih => exact .skip ih

/-- The relation of the composed stages: equal events and answers, value leaves related by
    `RetRel` of the outcomes, the source leaves that are not values failed. -/
abbrev BodyRel (h₁ : ∀ e : E.Event, E.Resp e) (t₁ t₂ : CallTree E (Outcome × Env)) : Prop :=
  RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) (fun r₁ r₂ => RetRel r₁.1 r₂.1)
    (fun r => ¬ ∃ v, r.1 = .val v) t₁ t₂

/-- A stage relating equal outcomes, its error leaves failed, extends a composed relation. -/
theorem BodyRel.trans_eqOut {h₁ : ∀ e : E.Event, E.Resp e}
    {t₀ t₁ t₂ : CallTree E (Outcome × Env)} {F : Outcome × Env → Prop}
    (hF : ∀ r, F r → ¬ ∃ v, r.1 = .val v) (h01 : BodyRel h₁ t₀ t₁)
    (h12 : RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => r₂.1 = r₁.1) F t₁ t₂) : BodyRel h₁ t₀ t₂ := by
  refine NFProgCallTreeExt.RuttS.mono ?_ (NFProgCallTreeFlat.ruttS_eqTrans ?_ h01 h12)
  · rintro r₀ r₂ ⟨r₁, h1, h2⟩
    rw [h2]
    exact h1
  · intro r₀ r₁ h1 hf ⟨v, hv⟩
    apply hF r₁ hf
    rcases h1 with h | ⟨w, -, -, h'⟩
    · exact ⟨v, h.trans hv⟩
    · exact ⟨w, h'⟩

/-- A stage relating outcomes by `RetRel` extends a relation of equal outcomes. -/
theorem BodyRel.of_eqOut_retRel {h₁ : ∀ e : E.Event, E.Resp e}
    {t₀ t₁ t₂ : CallTree E (Outcome × Env)}
    (h01 : RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => r₂.1 = r₁.1) (fun r => ¬ ∃ v, r.1 = .val v) t₀ t₁)
    (h12 : BodyRel h₁ t₁ t₂) : BodyRel h₁ t₀ t₂ := by
  refine NFProgCallTreeExt.RuttS.mono ?_ (NFProgCallTreeFlat.ruttS_eqTrans ?_ h01 h12)
  · rintro r₀ r₂ ⟨r₁, h1, h2⟩
    rw [← h1]
    exact h2
  · intro r₀ r₁ h1 hf ⟨v, hv⟩
    exact hf ⟨v, h1.trans hv⟩

/-- **The relation of the composed stages is transitive**: `RetRel` composes, and a source leaf
    related to a failed middle leaf is not a value. -/
theorem BodyRel.trans {h₁ : ∀ e : E.Event, E.Resp e} {t₀ t₁ t₂ : CallTree E (Outcome × Env)}
    (h01 : BodyRel h₁ t₀ t₁) (h12 : BodyRel h₁ t₁ t₂) : BodyRel h₁ t₀ t₂ := by
  refine NFProgCallTreeExt.RuttS.mono ?_ (NFProgCallTreeFlat.ruttS_eqTrans ?_ h01 h12)
  · rintro r₀ r₂ ⟨r₁, h1, h2⟩
    rcases h1 with h1 | ⟨w, hw, h0, h1⟩
    · rcases h2 with h2 | ⟨u, hu, h1', h2⟩
      · exact .inl (h2.trans h1)
      · exact .inr ⟨u, hu, h1.symm.trans h1', h2⟩
    · rcases h2 with h2 | ⟨u, -, h1', -⟩
      · exact .inr ⟨w, hw, h0, h2.trans h1⟩
      · rw [h1] at h1'
        cases h1'
        simp at hw
  · intro r₀ r₁ h1 hf ⟨v, hv⟩
    apply hf
    rcases h1 with h | ⟨w, -, -, h'⟩
    · exact ⟨v, h.trans hv⟩
    · exact ⟨w, h'⟩

/-- **The stages after the inlining of closures.** Under the side conditions `haxFrontOkP O e`
    of the front, from every environment the call tree of `inlineSpine e` and the call tree of
    the body `haxFrontBodyP O e` are related by `BodyRel`. -/
theorem prepBody_relT (h₁ : ∀ e : E.Event, E.Resp e) (bt : TreeTable E) (fuel : Nat)
    (O : FrontOracle) (e : ImpExpr) (hok : haxFrontOkP O e = true) (env : Env) :
    BodyRel h₁ (denoteT bt fuel (inlineSpine e) env) (denoteT bt fuel (haxFrontBodyP O e) env) := by
  unfold haxFrontOkP at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hanf, hroute⟩ := hok
  -- steps 1 to 3: bindings moved into statements and `map` sites rewritten
  have hA := NFCallTreeMapClosure.inlineMapClosures_relT (h₁ := h₁) bt fuel
    (_root_.Hax.LetIntoBranches.letsInto (inlineSpine e)) env
  rw [NFCallTreeLetsInto.denoteT_letsInto] at hA
  have h3 : BodyRel h₁ (denoteT bt fuel (inlineSpine e) env)
      (denoteT bt fuel (haxFrontPrep e) env) :=
    RuttS.mono_fail (fun _ ⟨m, hm⟩ ⟨_, hv⟩ => by rw [hm] at hv; cases hv)
      (NFProgCallTreeExt.RuttS.mono (fun _ _ h => .inl (congrArg Prod.fst h)) hA)
  -- step 4: A-normalisation
  have h4 : BodyRel h₁ (denoteT bt fuel (inlineSpine e) env)
      (denoteT bt fuel (haxFrontAnf e) env) :=
    BodyRel.trans_eqOut (fun _ ⟨m, hm⟩ ⟨_, hv⟩ => by rw [hm] at hv; cases hv) h3
      (NFCallTreeANorm.aNormalizeTotal_relT h₁ bt fuel _ hanf env)
  -- the literal counts of `repeat`, and the choice among the normal form and its rewritings
  have h5 : BodyRel h₁ (denoteT bt fuel (inlineSpine e) env)
      (denoteT bt fuel (haxFrontAnfEP O e) env) := by
    refine BodyRel.trans h4 ?_
    have hP := NFCallTreeAnfPick.anfEPick_relT (h₁ := h₁) bt fuel (haxFrontRouteOkP O)
      (CatCrypt.Crypto.Hax.repeatCountInline (haxFrontAnf e)) env
    rw [NFCallTreeRepeatCount.denoteT_repeatCountInline] at hP
    exact hP
  -- step 5: the flag of the `while true` loops
  unfold haxFrontRouteOkP at hroute
  cases hF : O.plain (haxFrontAnfEP O e) with
  | true =>
    have hB : haxFrontBodyP O e = haxFrontAnfEP O e := by simp [haxFrontBodyP, hF]
    rw [hB]
    exact h5
  | false =>
    simp only [hF, Bool.false_eq_true, ite_false, Bool.and_eq_true] at hroute
    have hB : haxFrontBodyP O e = _root_.Hax.WhileTrueFlag.wtFn haxFrontFlag
        (haxFrontAnfEP O e) := by simp [haxFrontBodyP, hF]
    rw [hB]
    exact BodyRel.trans_eqOut (fun _ hf => hf.elim) h5
      (NFCallTreeWhileTrue.wtFn_relT_same h₁ bt hroute.1 fuel env)

/-- **The body of the front from the source reading.** Under the side conditions
    `haxFrontOkP O e` and call-free arguments at the calls of inlined closures
    (`spineArgsOk e`), from every environment the call tree of `e`, its let-bound closures read
    as internal table entries, and the call tree of the body `haxFrontBodyP O e` are related by
    `BodyRel`. -/
theorem body_relT (h₁ : ∀ e : E.Event, E.Resp e) (bt : TreeTable E) (fuel : Nat)
    (O : FrontOracle) (e : ImpExpr) (hok : haxFrontOkP O e = true)
    (hs : NFCallTreeInlineSpine.spineArgsOk e = true) (env : Env) :
    BodyRel h₁ (nfTree bt fuel e env) (denoteT bt fuel (haxFrontBodyP O e) env) :=
  BodyRel.of_eqOut_retRel
    (RuttS.mono_fail (fun _ ⟨m, hm⟩ ⟨_, hv⟩ => by rw [hm] at hv; cases hv)
      (NFProgCallTreeExt.RuttS.mono (fun _ _ h => h.1)
        (NFCallTreeInlineSpine.inlineSpine_relT h₁ bt e fuel env hs)))
    (prepBody_relT h₁ bt fuel O e hok env)

/-- **The body `nfBody te` of the front from the source reading of the extraction `te`**,
    under the shape conditions `haxFrontShapeOk te` and `spineArgsOk` of the extraction. -/
theorem nfBody_relT (h₁ : ∀ e : E.Event, E.Resp e) (bt : TreeTable E) (fuel : Nat) (te : TExpr)
    (hok : CatCrypt.Crypto.Hax.haxFrontShapeOk te = true)
    (hs : NFCallTreeInlineSpine.spineArgsOk te.erase = true) (env : Env) :
    BodyRel h₁ (nfTree bt fuel te.erase env) (denoteT bt fuel (nfBody te) env) :=
  body_relT h₁ bt fuel _ te.erase (CatCrypt.Crypto.Hax.haxFrontOkP_of_shapeOk hok) hs env

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontBody
