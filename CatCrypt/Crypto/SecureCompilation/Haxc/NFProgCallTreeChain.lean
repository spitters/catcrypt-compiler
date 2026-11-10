/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSel
public import CatCrypt.Crypto.SecureCompilation.Haxc.ExtChain

/-!
# The steps of `extChainCore` composed at the level of call trees

The stage lemmas of the chain `extChainCore` at the tree level relate the call tree of the
input of a stage to the call tree of its output, by `RuttS` at relations of events and answers
for a stage that changes the dialect, and by the refinement `RefinesT` for a stage within a
dialect. This module composes them into one relation from the call tree of the source program
of `nfDialect`, read by `linkReader` under the handler of the leaf table of the builtins, to
the call tree `mfTree` of the output of the chain.

Two relations `RuttS` compose (`RuttS.trans`) at the relational composition of the leaves
(`Relation.Comp`) and of the events (`CompRE`), and at the answer relation `CompRA`, which
asks of every intermediate event related to both ends an intermediate answer related to both
answers. The composition needs two conditions: the intermediate handler answers related source
events by related answers (an intermediate event that the target skips is skipped in the
source at the answer of the source handler), and a source leaf related to a failed
intermediate leaf is a failed source leaf.

## Main definitions

* `CompRE`, `CompRA`: the composition of event relations and of answer relations.

## Main results

* `RuttS.trans`: two relations `RuttS` compose.
* `RefinesT.trans_ruttS`: a refinement followed by a relation `RuttS` is a relation `RuttS`.
* `refinesT_outTyStep`: the stage lemma of the check of the result type.
* `ruttS_extChainFront`: the steps of `extChainCore` up to `map?`, from the call tree of the
  source program to the call tree with call events of the program of `jasminDialect`.
* `ruttS_extChainCore`: the steps of `extChainCore`, from the call tree of the source program
  to the tree `mfTree` of the output of the chain.
* `ruttS_widenJ`: the stage lemma of the widening, the first stage of `narrowPrep`, between
  trees with call events.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes catToJasmin_varTransports catToJasmin_mapValExtends
  catToJasmin_block catToJasmin_regionTransports)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV_id)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSel
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montifyStep montEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc (fieldEnv)
open CatCrypt.Crypto.Hax.ImpToNF (tableOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep (fieldDialectStep)
open Ctxt (Var Valuation)

/-! ## Composition of relations of trees -/

section Comp

variable {E₀ E₁ E₂ : EventSig}

/-- **The composition of event relations**: an intermediate event related to both. -/
def CompRE (RE₁ : E₀.Event → E₁.Event → Prop) (RE₂ : E₁.Event → E₂.Event → Prop)
    (e₀ : E₀.Event) (e₂ : E₂.Event) : Prop :=
  ∃ e₁, RE₁ e₀ e₁ ∧ RE₂ e₁ e₂

/-- **The composition of answer relations**: at every intermediate event related to both
    events, an intermediate answer related to both answers. -/
def CompRA (RE₁ : E₀.Event → E₁.Event → Prop) (RE₂ : E₁.Event → E₂.Event → Prop)
    (RA₁ : (e₀ : E₀.Event) → (e₁ : E₁.Event) → E₀.Resp e₀ → E₁.Resp e₁ → Prop)
    (RA₂ : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop)
    (e₀ : E₀.Event) (e₂ : E₂.Event) (a₀ : E₀.Resp e₀) (a₂ : E₂.Resp e₂) : Prop :=
  ∀ e₁, RE₁ e₀ e₁ → RE₂ e₁ e₂ → ∃ a₁, RA₁ e₀ e₁ a₀ a₁ ∧ RA₂ e₁ e₂ a₁ a₂

/-- **Two relations of trees compose.** Let the intermediate handler `h₁` answer events
    related by `RE₁` with answers related by `RA₁` to those of the source handler `h₀`, and let
    a source leaf related to a failed intermediate leaf be a failed source leaf. Then
    `RuttS h₀ RE₁ RA₁ RR₁ F t₀ t₁` and `RuttS h₁ RE₂ RA₂ RR₂ F' t₁ t₂` give the relation of
    `t₀` and `t₂` at the compositions of the relations: an event of `t₁` that `t₂` skips is
    skipped in `t₀` at the answer of `h₀`. -/
theorem RuttS.trans {R₀ R₁ R₂ : Type} {h₀ : ∀ e : E₀.Event, E₀.Resp e}
    {h₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE₁ : E₀.Event → E₁.Event → Prop} {RE₂ : E₁.Event → E₂.Event → Prop}
    {RA₁ : (e₀ : E₀.Event) → (e₁ : E₁.Event) → E₀.Resp e₀ → E₁.Resp e₁ → Prop}
    {RA₂ : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR₁ : R₀ → R₁ → Prop} {RR₂ : R₁ → R₂ → Prop} {F : R₀ → Prop} {F' : R₁ → Prop}
    (hh : ∀ e₀ e₁, RE₁ e₀ e₁ → RA₁ e₀ e₁ (h₀ e₀) (h₁ e₁))
    (hF : ∀ r₀ r₁, RR₁ r₀ r₁ → F' r₁ → F r₀)
    {t₀ : CallTree E₀ R₀} {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    (h01 : RuttS h₀ RE₁ RA₁ RR₁ F t₀ t₁) (h12 : RuttS h₁ RE₂ RA₂ RR₂ F' t₁ t₂) :
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
      exact ih a₀ a₁ ha₁ (hk' a₁ a₂ ha₂)
    | skip hk' => exact .skip (ih _ _ (hh _ _ he) hk')
  | skip _ ih => exact .skip (ih h12)

/-- **A refinement followed by a relation is a relation.** When the source leaf `none` is a
    failed source leaf, `RefinesT h₀ t₀ t₁` and `RuttS h₀ RE RA RR Fail t₁ t₂` give
    `RuttS h₀ RE RA RR Fail t₀ t₂`. -/
theorem RefinesT.trans_ruttS {α R₂ : Type} {h₀ : ∀ e : E₀.Event, E₀.Resp e}
    {RE : E₀.Event → E₂.Event → Prop}
    {RA : (e₀ : E₀.Event) → (e₂ : E₂.Event) → E₀.Resp e₀ → E₂.Resp e₂ → Prop}
    {RR : Option α → R₂ → Prop} {Fail : Option α → Prop} (hF : Fail none)
    {t₀ t₁ : CallTree E₀ (Option α)} {t₂ : CallTree E₂ R₂}
    (h01 : RefinesT h₀ t₀ t₁) (h12 : RuttS h₀ RE RA RR Fail t₁ t₂) :
    RuttS h₀ RE RA RR Fail t₀ t₂ := by
  induction h01 generalizing t₂ with
  | ret h => subst h; exact h12
  | fail h => subst h; exact .fail hF
  | vis he _ ih =>
    subst he
    cases h12 with
    | vis he' hk' => exact .vis he' fun a₀ a₂ ha => ih a₀ a₀ HEq.rfl (hk' a₀ a₂ ha)
    | skip hk' => exact .skip (ih _ _ HEq.rfl hk')
  | skip _ ih => exact .skip (ih h12)

end Comp

/-! ## The check of the result type -/

/-- **The stage lemma of `outTyStep`**: the check returns its input, so the tree of its output
    refines the tree of its input at every reader, tree call environment, handler and fuel. -/
theorem refinesT_outTyStep {E : EventSig} (h₁ : ∀ e : E.Event, E.Resp e)
    (ex : ExprReader E nfDialect) (tE : TreeCallEnv E nfDialect) (fuel : Nat)
    {Γ : Ctxt nfDialect} {t : NfTy} {p q : NFProg nfDialect Γ [t]}
    (h : (outTyStep Γ t).run p = some q) (V : Valuation Γ) :
    RefinesT h₁ (treeAt ex tE fuel p V) (treeAt ex tE fuel q V) := by
  simp only [outTyStep] at h
  split at h
  · cases h
    exact RefinesT.refl _
  · cases h

/-! ## The steps of `extChainCore` -/

section Chain

/-- **The steps of `extChainCore` up to `map?` at the tree level.** Let `bi` satisfy
    `SubTable bi`, and let the handler `h₂` of the calls of `catCryptDialect` answer events
    related by `ExtRE` with answers related by `ExtRA` to those of the leaf table of `bi`.
    For a program `p` whose steps `outTyStep`, `dceStep`, `extCallStep D`, the e-graph pass at
    `catRules` and `mapStep catToJasmin` return `q`, and a valuation `V` in range, the tree of
    `p` at `linkReader`, the source fuel `tf` and the handler of the leaf table is related to
    the tree with call events of `q` at the transported valuation, at every fuel at least `tf`:
    events related by `ExtRE` then `MapRE`, answers by `ExtRA` then `MapRA`, leaves by `VRelL`
    then the transport, and the failed source leaf `none`. -/
theorem ruttS_extChainFront {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (D : List ExtDecl)
    (tE : TreeCallEnv leafSig nfDialect)
    (h₂ : ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e)
    (hh₂ : ∀ e₁ e₂, ExtRE e₁ e₂ → ExtRA e₁ e₂ (leafHandler (tableOf bi) e₁) (h₂ e₂))
    {Γ : Ctxt nfDialect} {t : NfTy} {p p₀ p₁ : NFProg nfDialect Γ [t]}
    {p₂ p₃ : NFProg catCryptDialect (Γ.map catTy) [catTy t]}
    {p₄ : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]}
    (s0 : (outTyStep Γ t).run p = some p₀) (s1 : (dceStep Γ [t]).run p₀ = some p₁)
    (s2 : (extCallStep D Γ [t]).run p₁ = some p₂)
    (s3 : (aegraphStep catRules (Γ.map catTy) [catTy t]).run p₂ = some p₃)
    (s4 : (mapStep catToJasmin catToJasmin_regionTypes (Γ.map catTy) [catTy t]).run p₃ =
      some p₄)
    (V : Valuation Γ) (hin : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V))
    (tf fuel : Nat) (hle : tf ≤ fuel) :
    RuttS (leafHandler (tableOf bi))
      (CompRE ExtRE (MapRE catToJasmin fun x => ctTransTy x))
      (CompRA ExtRE (MapRE catToJasmin fun x => ctTransTy x) ExtRA
        (MapRA catToJasmin fun x => ctTransTy x))
      (Relation.Comp (OutRel (VRelL [t]))
        (OutRel fun x y => y = transArgs catToJasmin.mapTy (fun x => ctTransTy x) x))
      (fun o => o = none)
      (treeAt linkReader tE tf p V) (nfProgTree fuel p₄ (ctMapValD (mapVal V))) := by
  have hdce := ruttS_treeAt_dce (leafHandler (tableOf bi)) linkReader_renameInv tE tf
    p₀ V
  have hext := nfToCatExt_ruttS hbi (fieldDeclsFor D p₁) tE p₁ TRd.id p₂ s2 V (mapVal V)
    (TRd.agree_id V hin) tf fuel hle
  have hopt := refinesT_aegraphOptNF catRules p₂ fuel (mapVal V) h₂
  have hmap := map?_ruttS catToJasmin (fun x => ctTransTy x) ctMapValD catToJasmin_regionTypes
    (fun _ => True) catToJasmin_varTransports
    (fun e _ blk hblk V => catToJasmin_block e blk hblk V) catToJasmin_mapValExtends
    catToJasmin_regionTransports h₂ fuel p₃ (NFProg.covered_of_forall _ (fun _ => trivial) p₃)
    (fun v => v) (mapVal V) (ctMapValD (mapVal V)) (pullV_id _) p₄ s4
  cases s1
  cases s3
  refine RefinesT.trans_ruttS (Fail := fun o => o = none) rfl (refinesT_outTyStep _ linkReader tE tf s0 V) ?_
  refine RefinesT.trans_ruttS (Fail := fun o => o = none) rfl hdce ?_
  refine RuttS.trans hh₂ ?_ ?_ hmap
  · rintro r₀ r₁ h rfl
    cases r₀ with
    | none => rfl
    | some a => obtain ⟨b, hb, -⟩ := h a rfl; cases hb
  · exact RuttS.trans_refinesT hh₂ (fun r h => by
      cases r with
      | none => rfl
      | some a => obtain ⟨b, hb, -⟩ := h a rfl; cases hb) hext hopt

/-- **The steps of `extChainCore` at the tree level.** Under the hypotheses of
    `ruttS_extChainFront`, a handler `h₃` of the calls of `jasminDialect` that answers events
    related by `MapRE` with answers related by `MapRA` to those of `h₂`, and that answers the
    inner field and reduction heads by `montEnv (fieldEnv CallEnv.empty)`, a program `p` that
    the chain `extChainCore D Γ t` turns into `q` and a valuation `V` in range: the tree of `p`
    at `linkReader`, the source fuel `tf` and the handler of the leaf table of `bi` is related
    to the tree `mfTree` of `q` at the transported valuation, at every fuel at least `tf`. -/
theorem ruttS_extChainCore {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (D : List ExtDecl)
    (tE : TreeCallEnv leafSig nfDialect)
    (h₂ : ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e)
    (h₃ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hh₂ : ∀ e₁ e₂, ExtRE e₁ e₂ → ExtRA e₁ e₂ (leafHandler (tableOf bi) e₁) (h₂ e₂))
    (hh₃ : ∀ e₁ e₂, MapRE catToJasmin (fun x => ctTransTy x) e₁ e₂ →
      MapRA catToJasmin (fun x => ctTransTy x) e₁ e₂ (h₂ e₁) (h₃ e₂))
    (hinner : ∀ (f : String) (as rs : List JasminTy) (x : Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₃ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    {Γ : Ctxt nfDialect} {t : NfTy} {p : NFProg nfDialect Γ [t]}
    {q : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]}
    (h : (extChainCore D Γ t).run p = some q)
    (V : Valuation Γ) (hin : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V))
    (tf fuel : Nat) (hle : tf ≤ fuel) :
    RuttS (leafHandler (tableOf bi))
      (CompRE ExtRE (MapRE catToJasmin fun x => ctTransTy x))
      (CompRA ExtRE (MapRE catToJasmin fun x => ctTransTy x) ExtRA
        (MapRA catToJasmin fun x => ctTransTy x))
      (Relation.Comp (OutRel (VRelL [t]))
        (OutRel fun x y => y = transArgs catToJasmin.mapTy (fun x => ctTransTy x) x))
      (fun o => o = none)
      (treeAt linkReader tE tf p V) (mfTree fuel q (ctMapValD (mapVal V))) := by
  simp only [extChainCore, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨p₀, s0, p₁, s1, p₂, s2, p₃, s3, p₄, s4, q₁, s5, q₂, s6, q₃, s7, q₄, s8, q₅, s9,
    hq⟩ := h
  cases hq
  refine ruttS_jasminTail h₃ ?_ ?_ hinner fuel jasminRules s5 s6 s7 s8 s9 _
    (ruttS_extChainFront hbi D tE h₂ hh₂ s0 s1 s2 s3 s4 V hin tf fuel hle)
  · rintro e₀ e ⟨e₁, he₁, he₂⟩ e₁' he₁' he₂'
    exact ⟨h₂ e₁', hh₂ _ _ he₁', hh₃ _ _ he₂'⟩
  · rintro r ⟨r₁, h₁, h₂⟩
    have : r₁ = none := by
      cases r₁ with
      | none => rfl
      | some a => obtain ⟨b, hb, -⟩ := h₂ a rfl; cases hb
    subst this
    cases r with
    | none => rfl
    | some a => obtain ⟨b, hb, -⟩ := h₁ a rfl; cases hb

end Chain

/-! ## The widening of narrow words -/

section Widen

open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords (widenJ widenP widenP_regionTypes
  widenP_varTransports widenP_mapValExtends widenP_regionTransports exprBlock?_denote)

/-- **The stage lemma of the widening `widenJ` at the tree level**, the first stage of
    `narrowPrep`: at every handler of the calls of `jasminDialect` and every fuel, the tree
    with call events of `p` is related to the tree with call events of the widened program at
    the widened valuation, each call the event with the widened signature and arguments
    (`MapRE widenP`), answered by the widening of the source answer (`MapRA widenP`), the
    leaves related by the widening, and the failed source leaf `none`. -/
theorem ruttS_widenJ
    (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {q : NFProg jasminDialect (Γ.map NarrowWords.wideTy) (ts.map NarrowWords.wideTy)}
    (hq : widenJ p = some q) (V : Valuation Γ) :
    RuttS h₁ (MapRE widenP fun x => NarrowWords.transTy x)
      (MapRA widenP fun x => NarrowWords.transTy x)
      (OutRel fun x y => y = transArgs widenP.mapTy (fun x => NarrowWords.transTy x) x)
      (fun o => o = none) (nfProgTree fuel p V) (nfProgTree fuel q (NarrowWords.mapVal V)) :=
  map?_ruttS widenP (fun x => NarrowWords.transTy x) (fun V => NarrowWords.mapVal V)
    widenP_regionTypes (fun _ => True) widenP_varTransports
    (fun e _ blk hblk V => exprBlock?_denote e blk hblk V) widenP_mapValExtends
    widenP_regionTransports h₁ fuel p (NFProg.covered_of_forall _ (fun _ => trivial) p)
    (fun v => v) V (NarrowWords.mapVal V) (pullV_id _) q hq

end Widen

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain
