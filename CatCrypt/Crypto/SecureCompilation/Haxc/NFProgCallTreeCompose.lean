/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeNarrow
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeFlat

/-!
# The front, the chain and the back half of `compileA` composed at the level of call trees

The statement `NFProgCallTreeCalls.R3StatementF` relates the source call tree `nfTree` of the
entry of a module, at the tree table of the module, to the family of the target trees of the
calling body. The relation is assembled from three relations of call trees:

* the front, from `nfTree` of the entry to the call tree `treeAt linkReader` of the program of
  `nfDialect` that the translation `haxToNF` returns;
* the chain `extChainCore` followed by `narrowPrep`, from `treeAt linkReader` to the tree `mfTree`
  of the narrowed program (`NFProgCallTreeNarrow.ruttS_extChainCore_narrowPrep`), a relation by
  `RuttS` at the source handler of the leaf table of the builtins;
* the back half, from the call tree of the program of `jasminDialect` to the target trees
  (`NFProgCallTreeRefBack.ruttF_regionRef_word`), a relation by `RuttF`.

In the tree `treeAt linkReader` every leaf call of `nfDialect` is an event, among them the calls
of the builtins (field heads, reductions, word operations named by the call typing), which the
chain skips at the answer of the leaf table. In the tree `nfTree` at the tree table of a module
the only events are the calls of the linked functions; a builtin call is answered inside the
tree. A relation by `RuttS` from `nfTree` relates every target event to a source event, so the
target of the front is the tree `answerOut` in which the events outside a predicate (the calls
of names that are not linked) are answered by the handler of the leaf table, and the relation of
the chain carries over to that tree when every event it relates to a target event satisfies the
predicate (`RuttS.answerOut`).

## Main definitions

* `answerOut`: a tree with the events outside a predicate answered by a handler.
* `FrontRE`, `FrontRA`, `FrontRR`: the relations of events, answers and leaves of the front: a
  linked call and a leaf call of the same name at the encoded arguments and the result type of
  the linked function, answers related by the encoding, and a source value read back from the
  result of the program.

## Main results

* `interp_answerOut`: answering events by the handler of the interpretation keeps the
  interpretation.
* `RuttS.answerOut`: a relation whose related source events satisfy the predicate holds from the
  tree with the other events answered.
* `RuttF.imp`: `RuttF` is monotone in the relations of events and leaves and in the failed
  leaves, and antitone in the relation of answers.
* `ruttF_front_chain_back`: a relation of the front, a relation of the chain from the tree whose
  other events the front answers, and a relation of the back half compose into a relation of the
  source tree and the target family at the compositions of the relations.
* `ruttS_extChain_narrowPrep`: the chain `extChain` of the front followed by `narrowPrep`, from
  the call tree of the program of `nfDialect` to the tree `mfTree` of the narrowed program: the
  elimination of aborting branches and tuple flattening, then
  `NFProgCallTreeNarrow.ruttS_extChainCore_narrowPrep`.
* `frontRA_linkHandler`, `srcFail_of_frontRR`: the side conditions of the composition at the
  front, at the handler of the linked functions and the leaf table of the table of the linked
  functions.
* `r3f_consequence_compileA`: from `R3StatementF`, a source run of the entry of a module to a
  value that is not a control-flow value is read back from a target run of the decoded calling
  body of `compileA` under every handler meeting the separation contracts.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCompose

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (CompRE CompRA RuttS.trans)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF RuttS.trans_ruttF
  R3StatementF r3f_consequence)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (LeafCall leafSig leafHandler)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS HandlerMeetsC
  contractRAC)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect (NfTy)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
open CatCrypt.Crypto.Hax.ImpToNF (enc dec encAll tableOf)
open CatCrypt.Crypto.SecureCompilation.VIR (HVector)
open _root_.Hax
open _root_.Hax.InlineLocalClosures

/-! ## Answering the events outside a predicate -/

section AnswerOut

variable {E : EventSig} {R : Type}

/-- **A tree with the events outside a predicate answered**: an event `e` with `keep e` stays an
    event; an event with `keep e = false` is answered by the handler `h`, the tree continuing at
    that answer. -/
def answerOut (keep : E.Event → Bool) (h : ∀ e : E.Event, E.Resp e) :
    CallTree E R → CallTree E R
  | .ret r => .ret r
  | .vis e k =>
    if keep e then .vis e fun a => answerOut keep h (k a) else answerOut keep h (k (h e))

/-- Answering events by the handler of the interpretation keeps the interpretation. -/
theorem interp_answerOut (keep : E.Event → Bool) (h : ∀ e : E.Event, E.Resp e)
    (t : CallTree E R) : interp h (answerOut keep h t) = interp h t := by
  induction t with
  | ret r => rfl
  | vis e k ih =>
    by_cases hk : keep e = true
    · simp only [answerOut, hk, ite_true, interp_vis]
      exact ih _
    · simp only [answerOut, hk, Bool.false_eq_true, ite_false, interp_vis]
      exact ih _

/-- **A relation from the tree with the other events answered.** When every source event that
    `RE` relates to a target event satisfies `keep`, a relation by `RuttS` at the source handler
    `h₁` holds from the tree whose events outside `keep` are answered by `h₁`. -/
theorem RuttS.answerOut {E₂ : EventSig} {R₂ : Type} {h₁ : ∀ e : E.Event, E.Resp e}
    {RE : E.Event → E₂.Event → Prop}
    {RA : (e₁ : E.Event) → (e₂ : E₂.Event) → E.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R → R₂ → Prop} {Fail : R → Prop} (keep : E.Event → Bool)
    (hkeep : ∀ e₁ e₂, RE e₁ e₂ → keep e₁ = true) {t₁ : CallTree E R} {t₂ : CallTree E₂ R₂}
    (h : RuttS h₁ RE RA RR Fail t₁ t₂) :
    RuttS h₁ RE RA RR Fail (NFProgCallTreeCompose.answerOut keep h₁ t₁) t₂ := by
  induction h with
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
      exact ih

end AnswerOut

/-! ## Monotonicity and composition of `RuttF` -/

section Compose

variable {E₀ E₁ E₂ E₃ : EventSig} {R₀ R₁ R₂ R₃ : Type}

/-- **`RuttF` is monotone in the relations of events and leaves and in the failed leaves, and
    antitone in the relation of answers**, the answers compared at related events. -/
theorem RuttF.imp {h₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE RE' : E₁.Event → E₂.Event → Prop}
    {RA RA' : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR RR' : R₁ → R₂ → Prop} {Fail Fail' : R₁ → Prop}
    (hE : ∀ e₁ e₂, RE e₁ e₂ → RE' e₁ e₂)
    (hA : ∀ e₁ e₂, RE e₁ e₂ → ∀ a₁ a₂, RA' e₁ e₂ a₁ a₂ → RA e₁ e₂ a₁ a₂)
    (hR : ∀ r₁ r₂, RR r₁ r₂ → RR' r₁ r₂) (hF : ∀ r₁, Fail r₁ → Fail' r₁)
    {t₁ : CallTree E₁ R₁} {T : Nat → CallTree E₂ R₂} (h : RuttF h₁ RE RA RR Fail t₁ T) :
    RuttF h₁ RE' RA' RR' Fail' t₁ T := by
  induction h with
  | ret n hT h => exact .ret n hT (hR _ _ h)
  | fail h => exact .fail (hF _ h)
  | vis n hT he _ ih => exact .vis n hT (hE _ _ he) fun a₁ a₂ ha => ih a₁ a₂ (hA _ _ he _ _ ha)
  | skip _ ih => exact .skip ih

/-- **The front, the chain and the back half composed.** Let `t₀` be related by `RuttS` to the
    tree `t₁` with its events outside `keep` answered by `h₁` (the front), `t₁` be related by
    `RuttS` to `t₂` (the chain), every event the chain relates to a target event satisfy `keep`,
    and `t₂` be related by `RuttF` to the family `T` (the back half). Under the side conditions
    of `RuttS.trans` at the front and at the chain, `t₀` is related to `T` at the compositions of
    the relations. -/
theorem ruttF_front_chain_back {h₀ : ∀ e : E₀.Event, E₀.Resp e}
    {h₁ : ∀ e : E₁.Event, E₁.Resp e} {h₂ : ∀ e : E₂.Event, E₂.Resp e}
    {RE₁ : E₀.Event → E₁.Event → Prop} {RE₂ : E₁.Event → E₂.Event → Prop}
    {RE₃ : E₂.Event → E₃.Event → Prop}
    {RA₁ : (e₀ : E₀.Event) → (e₁ : E₁.Event) → E₀.Resp e₀ → E₁.Resp e₁ → Prop}
    {RA₂ : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RA₃ : (e₂ : E₂.Event) → (e₃ : E₃.Event) → E₂.Resp e₂ → E₃.Resp e₃ → Prop}
    {RR₁ : R₀ → R₁ → Prop} {RR₂ : R₁ → R₂ → Prop} {RR₃ : R₂ → R₃ → Prop}
    {F₀ : R₀ → Prop} {F₁ : R₁ → Prop} {F₂ : R₂ → Prop} (keep : E₁.Event → Bool)
    (hh₁ : ∀ e₀ e₁, RE₁ e₀ e₁ → RA₁ e₀ e₁ (h₀ e₀) (h₁ e₁))
    (hF₁ : ∀ r₀ r₁, RR₁ r₀ r₁ → F₁ r₁ → F₀ r₀)
    (hh₂ : ∀ e₁ e₂, RE₂ e₁ e₂ → RA₂ e₁ e₂ (h₁ e₁) (h₂ e₂))
    (hF₂ : ∀ r₁ r₂, RR₂ r₁ r₂ → F₂ r₂ → F₁ r₁)
    (hkeep : ∀ e₁ e₂, RE₂ e₁ e₂ → keep e₁ = true)
    {t₀ : CallTree E₀ R₀} {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂}
    {T : Nat → CallTree E₃ R₃}
    (hfront : RuttS h₀ RE₁ RA₁ RR₁ F₀ t₀ (answerOut keep h₁ t₁))
    (hchain : RuttS h₁ RE₂ RA₂ RR₂ F₁ t₁ t₂) (hback : RuttF h₂ RE₃ RA₃ RR₃ F₂ t₂ T) :
    RuttF h₀ (CompRE (CompRE RE₁ RE₂) RE₃)
      (CompRA (CompRE RE₁ RE₂) RE₃ (CompRA RE₁ RE₂ RA₁ RA₂) RA₃)
      (Relation.Comp (Relation.Comp RR₁ RR₂) RR₃) F₀ t₀ T := by
  have h02 := RuttS.trans hh₁ hF₁ hfront (RuttS.answerOut keep hkeep hchain)
  refine RuttS.trans_ruttF (fun e₀ e₂ he => ?_) (fun r₀ r₂ hr hf => ?_) h02 hback
  · obtain ⟨e₁, he₁, he₂⟩ := he
    intro e₁' he₁' he₂'
    exact ⟨h₁ e₁', hh₁ _ _ he₁', hh₂ _ _ he₂'⟩
  · obtain ⟨r₁, hr₁, hr₂⟩ := hr
    exact hF₁ _ _ hr₁ (hF₂ _ _ hr₂ hf)

end Compose

/-! ## The chain of the front at the tree level -/

section Chain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (regionExportableB)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (linkReader OutRel ExtRE ExtRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt (MapRE MapRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montEnv)

/-- The failed leaf `none` is related to every leaf by `OutRel`. -/
theorem outRel_none {α β : Type} (R : α → β → Prop) (o : Option β) : OutRel R none o :=
  fun _ ha => nomatch ha

/-- A source leaf related to the failed leaf `none` by the equality of values is failed. -/
theorem none_of_outRel_eq {α : Type} {r₀ r₁ : Option α} (h : OutRel (fun x y => y = x) r₀ r₁)
    (h1 : r₁ = none) : r₀ = none := by
  cases r₀ with
  | none => rfl
  | some a =>
    obtain ⟨b, hb, -⟩ := h a rfl
    rw [h1] at hb
    cases hb
open Ctxt (Var Valuation)

/-- **The steps of `extChain` followed by `narrowPrep` at the tree level.** The statement of
    `NFProgCallTreeNarrow.ruttS_extChainCore_narrowPrep` for the chain `extChain` of the front,
    which runs the elimination of aborting branches and tuple flattening before `extChainCore`,
    at a tree call environment in which every call of a procedure fails: both steps keep the
    events, the answers and the leaves of the tree (`refinesT_treeAt_abortElim_link`,
    `ruttS_treeAt_flatSame`). -/
theorem ruttS_extChain_narrowPrep {bi : Builtins} (hbi : SubTable bi) (D : List ExtDecl)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (a : Valuation (d := nfDialect) as),
      tE.call f as rs a = .ret none)
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
    (h : (extChain D Γ t).run p = some q) (hB : regionExportableB q = true)
    {q' : NFProg jasminDialect ((mapCtx (Γ.map catTy)).map NarrowWords.wideTy)
      ([mapTy (catTy t)].map NarrowWords.wideTy)} (hq' : NarrowWords.narrowPrep q = some q')
    (V : Valuation Γ) (hin : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V))
    (tf fuel : Nat) (hle : tf ≤ fuel) :
    RuttS (leafHandler (tableOf bi))
      (CompRE (CompRE ExtRE (MapRE catToJasmin fun x => ctTransTy x))
        (MapRE NarrowWords.widenP fun x => NarrowWords.transTy x))
      (CompRA (CompRE ExtRE (MapRE catToJasmin fun x => ctTransTy x))
        (MapRE NarrowWords.widenP fun x => NarrowWords.transTy x)
        (CompRA ExtRE (MapRE catToJasmin fun x => ctTransTy x) ExtRA
          (MapRA catToJasmin fun x => ctTransTy x))
        (MapRA NarrowWords.widenP fun x => NarrowWords.transTy x))
      (Relation.Comp
        (Relation.Comp (OutRel (VRelL [t]))
          (OutRel fun x y => y = transArgs catToJasmin.mapTy (fun x => ctTransTy x) x))
        (OutRel fun x y => y = transArgs NarrowWords.widenP.mapTy
          (fun x => NarrowWords.transTy x) x))
      (fun o => o = none)
      (treeAt linkReader tE tf p V)
      (mfTree fuel q' (NarrowWords.mapVal (ctMapValD (mapVal V)))) := by
  simp only [extChain, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨p₁, h1, p₂, h2, h3⟩ := h
  cases h1
  have R1 := NFProgCallTreeAbort.refinesT_treeAt_abortElim_link (leafHandler (tableOf bi)) tE tf
    p V
  have R2 := NFProgCallTreeFlat.ruttS_treeAt_flatSame (leafHandler (tableOf bi)) tE htE tf h2 V
  have R3 := NFProgCallTreeNarrow.ruttS_extChainCore_narrowPrep hbi D tE h₂ h₃ hh₂ hh₃ hinner h3
    hB hq' V hin tf fuel hle
  have R23 := NFProgCallTreeFlat.ruttS_eqTrans (F₀ := fun o => o = none)
    (F₁ := fun o => o = none) (fun _ _ h01 h1 => none_of_outRel_eq h01 h1) R2 R3
  have R123 := NFProgCallTreeFlat.ruttS_eqTrans (F₀ := fun o => o = none)
    (F₁ := fun o => o = none) (fun _ _ h01 h1 => h01.trans h1) R1 R23
  refine NFProgCallTreeExt.RuttS.mono ?_ R123
  rintro r₀ r₂ ⟨r₁, rfl, r₁', h01, h12⟩
  cases r₀ with
  | none =>
    exact ⟨none, ⟨none, outRel_none _ _, outRel_none _ _⟩, outRel_none _ _⟩
  | some a =>
    obtain ⟨b, rfl, rfl⟩ := h01 a rfl
    exact h12

end Chain

/-! ## The relations of the front -/

section Front

/-- **The event relation of the front**: a call of a linked function `l` of `m` and a leaf call
    of the same name, whose argument values encode to the source arguments, at the result type of
    `l`. -/
def FrontRE (m : HaxModule) (e₀ : linkSig.Event) (e₁ : leafSig.Event) : Prop :=
  e₁.name = LinkCall.name e₀ ∧ LinkCall.args e₀ = encAll e₁.argTys e₁.args
    ∧ ∃ l, m.linked.find? (·.name == LinkCall.name e₀) = some l ∧ e₁.ret = l.res

/-- **The answer relation of the front**: the source answer is the encoding of the answer of the
    leaf call. -/
def FrontRA (e₀ : linkSig.Event) (e₁ : leafSig.Event) (a₀ : linkSig.Resp e₀)
    (a₁ : leafSig.Resp e₁) : Prop :=
  (a₀ : Option Value) = a₁.map (enc e₁.ret)

/-- **The leaf relation of the front**: a source value that is not a control-flow value is the
    encoding of the result of the program. -/
def FrontRR (t : NfTy) (r₀ : Outcome × Env)
    (o : Option (HVector NfTy.denote [t])) : Prop :=
  ∀ v, r₀.1 = .val v → v.isControlFlow = false →
    ∃ y, o = some (HVector.cons y .nil) ∧ v = enc t y

/-- **The front at the handlers of the linked functions.** At events related by `FrontRE`, the
    answer of the handler of the linked functions of `m` and the answer of the leaf table of the
    table of the linked functions over `bi` are related by `FrontRA`. -/
theorem frontRA_linkHandler (m : HaxModule) (bi : Builtins) {e₀ : linkSig.Event}
    {e₁ : leafSig.Event} (he : FrontRE m e₀ e₁) :
    FrontRA e₀ e₁ (linkHandler m e₀) (leafHandler (tableOf (m.linkTable bi)) e₁) := by
  obtain ⟨n₁, as₁, r₁, xs₁⟩ := e₁
  obtain ⟨hn, ha, l, hl, hr⟩ := he
  dsimp only at hn ha hr
  subst hr
  have h0 : linkHandler m e₀ = l.sem (LinkCall.args e₀) := by
    simp only [linkHandler, hl]
    rfl
  have h1 : leafHandler (tableOf (m.linkTable bi)) ⟨n₁, as₁, l.res, xs₁⟩
      = (l.sem (LinkCall.args e₀)).bind (dec l.res) := by
    change (m.linkTable bi n₁ (encAll as₁ xs₁)).bind (dec l.res) = _
    rw [← ha, hn]
    simp only [HaxModule.linkTable, CatCrypt.Crypto.Hax.linkBi_of_find_some _ _ hl]
  show (linkHandler m e₀ : Option Value) = _
  rw [h0, h1]
  cases hs : l.sem (LinkCall.args e₀) with
  | none => rfl
  | some v =>
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (l.sem_res _ v hs)
    rw [Option.bind_some, hy, Option.map_some, ← CatCrypt.Crypto.Hax.ImpToNF.dec_sound _ _ _ hy]

/-- A source leaf related by `FrontRR` to the failed leaf `none` is a failed source leaf. -/
theorem srcFail_of_frontRR {t : NfTy} {r₀ : Outcome × Env} (h : FrontRR t r₀ none) :
    srcFail r₀ := by
  intro v hv
  cases hc : v.isControlFlow with
  | true => rfl
  | false =>
    obtain ⟨y, hy, -⟩ := h v hv hc
    cases hy

end Front

/-! ## The consequence at the bytes of `compileA` -/

/-- **The consequence of `R3StatementF` at the bytes of `compileA`.** For a module whose linked
    functions are linked kernels with distinct names, the bytes of `compileA` decode to a calling
    body `pc` followed by the region of the kernel blocks, with a symbol map `sym`, such that from
    every entry state satisfying `σ.Regions` and every source environment `σ` reads off it, under
    every target handler meeting the separation contracts of the linked functions, a run of the
    entry of the module at its table to a value that is not a control-flow value is read back by
    `σ` from the leaf of the target tree of `pc` under the handler at some target fuel. -/
theorem r3f_consequence_compileA (hR : R3StatementF) {m : HaxModule} {σ : AbiLayout}
    {fname : String} {P : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lprog}
    {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hnd : (m.linked.map (·.name)).Nodup)
    (hk : ∀ l ∈ m.linked, RegionLinkCall.LinkedKernel l) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      X86Backend.LprogBytesDecode.decodeLprog bytes =
          some (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ (h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e), HandlerMeetsC m h₂ →
        ∀ (fuelC fuel : Nat) (v : Value) (env' : Env),
          (denoteSpine (m.table CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel m.entry.erase).run env
            = (.val v, env') → v.isControlFlow = false →
          ∃ fuelT s', interp h₂ (targetTree aMachine pc sym (linkRead m) fuelT 0 sa) = some s'
            ∧ σ.ResultOf sa s' v := by
  obtain ⟨pc, Q, sym, hd, hrel⟩ := hR m σ fname P bytes hc hnd hk
  refine ⟨pc, Q, sym, hd, fun sa hreg env henv h₂ hh fuelC fuel v env' hrun hcf => ?_⟩
  refine r3f_consequence m σ sa h₂ hh (hrel sa hreg env henv fuelC fuel) (env' := env') ?_ hcf
  rw [interp_nfTree_table]
  exact hrun

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCompose
