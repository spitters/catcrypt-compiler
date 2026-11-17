/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallAns
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheckAns

/-!
# The image of a calling body cut at its calls, at the answers of the callees

`NFProgCallTreeCallsSite.ImgUp` relates a source call tree, after a call of the image, to the
image state after the step `Glue` of the summary of the callee, so the state after the call
carries the value of the summary. This module states the same relation at the answer of the
callee: after a call of the symbol `f`, ending in the return state `sc` of a run of the run
relation `X f`, the source continuation is related to the image state after the step
`LprogCallCutAns.GlueA` at the word `ρ f sc` that the result reader `ρ` reads off `sc`. The
steps of the call sites are the steps `ImageAddrCallAns.SiteStepA` at that reader, and the
relation with the target trees is `NFProgCallTreeOracle.RuttFA` at a skip predicate `Sk`: a
source event that the image does not perform is continued at every answer that `Sk` admits.

At the kind `CalleeKind.ins` of every called symbol, the steps of the call sites hold at the
interface `LinkedFn.frameSig` of the frame contract and the reader of the result register
(`ruttF_of_contractsA`); no summary value and no meaning of a callee enter the relation.

## Main definitions

* `SegSimA`: `NFProgCallTreeCallsBack.SegSim` with skipped source events continued at every
  answer of a skip predicate.
* `ImgUpA`: a relation between source call trees and image states carried by the segments of
  the image and the steps of its call sites at the answers of the callees.
* `RefCarriedA`, `RefImgUpA`: a relation carried by the cut programs of a reference body under a
  simulation `CutSimIA` at the steps `GlueA`, and the relation with image states it induces.

## Main results

* `ruttFA_of_segSimA`: a simulation cut at the calls gives `RuttFA` with the target family.
* `segSimA_iff_segSim`: at the answers of a pure handler, `SegSimA` is `SegSim`.
* `segSim_of_imgUpA`, `ruttF_of_imgUpA`: a relation carried by the image gives the simulation
  cut at the calls and the relation `RuttFA` with the target trees.
* `imgUpA_of_imgUp`: a relation `ImgUp` whose summary steps are the steps `GlueA` at the answers
  of the callees is a relation `ImgUpA` at the answers of the source handler.
* `ruttF_of_contractsA`: the relation from the checks of the image with callees of the kind
  `CalleeKind.ins` at the frame contract.
* `imgUp_of_refCarriedA`: a relation carried by the cut programs of the reference induces a
  relation carried by the image.
* `ruttF_calleeBodyA`, `ruttF_calleeBody_refA`: the calling body of the back half against the
  target trees, from a relation carried by its image or by its reference.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSiteAns

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport hiding regName
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (evalInstrPMemFk)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
  (SegTo Glue CutRun IsSite IsCut IsCutRev PcFree FnStable entryPos segTo_of_cutRun)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCutAns (GlueA CutSimIA glueLaws_glueA)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (Halted atPc goto)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr Params retOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallAns (SiteStepA siteStepA_ins)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind CallAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSig CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls
  (RuttF targetTree_of_haltsNoCall targetTree_of_reaches_call)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack (callEvent SegSim)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsImg
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSite
  (SegSimR UpInv ImgUp segSimR_of_segExactR)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle (RuttFA ruttFA_iff_ruttF)
open CatCrypt.Crypto.Hax (LinkedFn)

/-! ## 1. Simulations cut at the calls, with skips at a predicate -/

section Seg

variable {σ : Type} (M : Machine σ) (prog : List RInstr) (sym : Nat → String)
  (rd : String → σ → List _root_.Hax.Value)
  {E₁ : EventSig} {R₁ : Type} (Sk : (e : E₁.Event) → E₁.Resp e → Prop)
  (RE : E₁.Event → (kSig σ).Event → Prop)
  (RA : (e₁ : E₁.Event) → (e₂ : (kSig σ).Event) → E₁.Resp e₁ → (kSig σ).Resp e₂ → Prop)
  (RR : R₁ → Option σ → Prop) (Fail : R₁ → Prop)

/-- **A simulation of source call trees by the target program cut at its calls, with skips at
    the predicate `Sk`.** The clauses of `NFProgCallTreeCallsBack.SegSim`, with a source event
    that the target does not perform continued at every answer that `Sk` admits, each related
    to the same index and state. -/
def SegSimA (Inv : CallTree E₁ R₁ → Nat → σ → Prop) : Prop :=
  ∀ t₁ pc s, Inv t₁ pc s →
    (∃ r₁, t₁ = .ret r₁ ∧ (Fail r₁ ∨ ∃ s', HaltsNoCall M prog pc s s' ∧ RR r₁ (some s')))
    ∨ ∃ e₁ k₁, t₁ = .vis e₁ k₁ ∧
      ((∃ pc' tg s', Reaches M prog pc s pc' s' ∧ prog[pc']? = some (.call tg)
          ∧ RE e₁ (callEvent M sym rd pc' tg s')
          ∧ ∀ a₁ a₂, RA e₁ (callEvent M sym rd pc' tg s') a₁ a₂ →
            (∃ r, k₁ a₁ = .ret r ∧ Fail r)
            ∨ ∃ sc, a₂ = some sc ∧ Inv (k₁ a₁) (pc' + 1) (retOps.foldl M.exec sc))
        ∨ ∀ a, Sk e₁ a → Inv (k₁ a) pc s)

/-- **A simulation cut at the calls with skips at `Sk` gives the relation `RuttFA` with the
    target family.** Every source tree related by `Inv` to an index and a state is related by
    `RuttFA Sk` to the family of the target trees from them. -/
theorem ruttFA_of_segSimA {Inv : CallTree E₁ R₁ → Nat → σ → Prop}
    (hS : SegSimA M prog sym rd Sk RE RA RR Fail Inv) :
    ∀ (t₁ : CallTree E₁ R₁) (pc : Nat) (s : σ), Inv t₁ pc s →
      RuttFA Sk RE RA RR Fail t₁ fun n => targetTree M prog sym rd n pc s := by
  intro t₁
  induction t₁ with
  | ret r₁ =>
    intro pc s hI
    rcases hS _ pc s hI with ⟨r, hr, hf | ⟨s', hh, hR⟩⟩ | ⟨e₁, k₁, he, -⟩
    · cases hr; exact .fail hf
    · cases hr
      obtain ⟨n, hn⟩ := targetTree_of_haltsNoCall M prog sym rd hh
      exact .ret n (hn 0) hR
    · cases he
  | vis e₁ k₁ ih =>
    intro pc s hI
    rcases hS _ pc s hI with ⟨r, hr, -⟩ | ⟨e, k, he, hc | hk⟩
    · cases hr
    · cases he
      obtain ⟨pc', tg, s', hr, hcall, hE, hA⟩ := hc
      obtain ⟨n, hn⟩ := targetTree_of_reaches_call M prog sym rd hr hcall
      refine .vis n hn hE fun a₁ a₂ ha => ?_
      rcases hA a₁ a₂ ha with ⟨r, hr, hf⟩ | ⟨sc, rfl, hI'⟩
      · rw [hr]; exact .fail hf
      · exact ih a₁ _ _ hI'
    · cases he
      exact .skip fun a ha => ih a pc s (hk a ha)

/-- **At the answers of a pure handler, `SegSimA` is `SegSim`.** -/
theorem segSimA_iff_segSim (h₁ : ∀ e : E₁.Event, E₁.Resp e)
    {Inv : CallTree E₁ R₁ → Nat → σ → Prop} :
    SegSimA M prog sym rd (fun e a => a = h₁ e) RE RA RR Fail Inv
      ↔ NFProgCallTreeCallsBack.SegSim M prog sym rd h₁ RE RA RR Fail Inv := by
  simp only [SegSimA, NFProgCallTreeCallsBack.SegSim, forall_eq]

end Seg

/-! ## 2. Source trees carried by the image at the answers of the callees -/

section Up

variable {E₁ : EventSig} {R₁ : Type} (Sk : (e : E₁.Event) → E₁.Resp e → Prop)
  (RE : E₁.Event → (kSig AState).Event → Prop)
  (RA : (e₁ : E₁.Event) → (e₂ : (kSig AState).Event) → E₁.Resp e₁ → (kSig AState).Resp e₂ →
    Prop)
  (RR : R₁ → Option AState → Prop) (Fail : R₁ → Prop)
  (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
  (base : String → BitVec 64) (rsp : BitVec 64) (body : Lcmd) (E : Nat → List String)
  (X : String → CalleeRun) (ρ : String → AState → BitVec 64) (I : LprogIsa.Isa)
  (T : LprogIsa.ProcTable) (P : LprogM)
  (prog : List RInstr) (pos : Nat → Nat) (tgt : String → Nat) (sym : Nat → String)
  (rd : String → AState → List _root_.Hax.Value) (Fin : LstateMF → AState → Prop)

/-- **A relation between source call trees and image states carried by the image at the
    answers of the callees.** The clauses of `ImgUp`, with two changes. After a segment of the
    image to a call at `p` of a symbol `f`, at every answer that `RA` relates to a source
    answer, the source continuation is a failed leaf, or the answer is a return state `sc` of a
    run of `X f` from the entry state of the call and the source continuation is related by
    `Up` to a state after the step `GlueA` at `p` at the word `ρ f sc`. A source event that the
    image does not perform is continued at every answer that `Sk` admits, related to the same
    image state. -/
def ImgUpA (Up : CallTree E₁ R₁ → LstateMF → Prop) : Prop :=
  ∀ t₁ s, Up t₁ s →
    (∃ r₁, t₁ = .ret r₁ ∧
      (Fail r₁ ∨ ∃ t, SegTo I T P s none t ∧ ∀ sA, Fin t sA → RR r₁ (some sA)))
    ∨ ∃ e₁ k₁, t₁ = .vis e₁ k₁ ∧
      ((∃ p u, SegTo I T P s (some p) u ∧
          ∀ bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
          ∀ sa sA, ImgRelF frame slotArr base body (E p) u sa → ACorr rsp sA sa →
            sa.reg.lpc = p →
            RE e₁ (callEvent aMachine sym rd (pos p) (tgt f) sA)
            ∧ ∀ a₁ a₂, RA e₁ (callEvent aMachine sym rd (pos p) (tgt f) sA) a₁ a₂ →
              (∃ r, k₁ a₁ = .ret r ∧ Fail r)
              ∨ ∃ sc tr, a₂ = some sc
                ∧ X f (entryOf (pos p + 1) sA) tr sc
                ∧ ∃ v, GlueA T P p u (ρ f sc) v ∧ Up (k₁ a₁) v)
        ∨ ∀ a, Sk e₁ a → Up (k₁ a) s)

/-- **A relation carried by the image at the answers of the callees gives the simulation cut at
    the calls of the decoded program.** The hypotheses of `segSim_of_imgUp`, with each step
    `GlueA T P` at a call of a symbol `f` at the word `w` the write of `w` to a destination
    `dst` with the step of the site (`SiteStepA`) of `X f`, `c f` and the reader `ρ f` at the
    names `E p` and `E (p + 1)`. A relation `Up` carried by the image (`ImgUpA`) gives the
    simulation `SegSimA` of the source trees by `prog` at the invariant `UpInv`. -/
theorem segSim_of_imgUpA {c : String → CalleeSig} {L : Nat → Bool}
    (hLc : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → L (p + 1) = false)
    (hcl : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → p + 1 < body.length)
    (hsim : SegSimR frame slotArr base rsp body P.lfn E L prog pos tgt (SegTo I T P) Fin)
    (hStep : ∀ p u w v, GlueA T P p u w v → u.prog.base.reg.lpc = p →
      ∀ bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      ∃ dst, v = LprogIsa.retWord dst w u
        ∧ SiteStepA frame slotArr base rsp body (X f) (c f) (ρ f) (E p) (E (p + 1)) dst u)
    {Up : CallTree E₁ R₁ → LstateMF → Prop}
    (hUp : ImgUpA Sk RE RA RR Fail frame slotArr base rsp body E X ρ I T P pos tgt sym rd Fin
      Up) :
    SegSimA aMachine prog sym rd Sk RE RA RR Fail
      (UpInv frame slotArr base rsp body E P pos L Up) := by
  rintro t₁ pc sA ⟨s, sa, hU, hfn, hlen, hL, hI, hA, rfl⟩
  rcases hUp t₁ s hU with ⟨r₁, rfl, hf | ⟨t, hseg, hR⟩⟩ | ⟨e₁, k₁, rfl, hc | hk⟩
  · exact .inl ⟨r₁, rfl, .inl hf⟩
  · obtain ⟨sA', hh, hfin⟩ := hsim.toEnd s sa sA t hfn hlen hL hI hA hseg
    exact .inl ⟨r₁, rfl, .inr ⟨sA', hh, hR sA' hfin⟩⟩
  · obtain ⟨p, u, hseg, hcall⟩ := hc
    obtain ⟨sa1, sA1, hI1, hc1, hpc1, ⟨bi, ra, ⟨f, l⟩, hb, hbi, hprog⟩, hreach⟩ :=
      hsim.toCall s sa sA p u hfn hlen hL hI hA hseg
    obtain ⟨hfu, hpu⟩ : u.prog.lfn = P.lfn ∧ u.prog.base.reg.lpc = p := by
      obtain ⟨_, _, hat, _⟩ := hseg
      exact hat
    obtain ⟨hRE, hRA⟩ := hcall bi ra f l hb hbi sa1 sA1 hI1 hc1 hpc1
    refine .inr ⟨e₁, k₁, rfl, .inl ⟨pos p, tgt f, sA1, hreach, hprog, hRE, fun a₁ a₂ ha => ?_⟩⟩
    rcases hRA a₁ a₂ ha with hf | ⟨sc, tr, rfl, hX, v, hg, hU'⟩
    · exact .inl hf
    refine .inr ?_
    obtain ⟨dst, rfl, hst⟩ := hStep _ _ _ _ hg hpu bi ra f l hb hbi
    have hfv : (LprogIsa.retWord dst (ρ f sc) u).prog.lfn = P.lfn :=
      (LprogIsa.lfn_retRes dst (.word (ρ f sc)) u).trans hfu
    obtain ⟨u', zf, hag, hrel⟩ := hI1
    obtain ⟨-, hall⟩ := hst.1 u' hag sa1 zf sA1 hrel hc1
      ⟨bi, ra, (f, l), by rw [hpc1]; exact hb, hbi⟩ (pos p + 1)
    obtain ⟨sa2, hpc2, hA2, w, zf', hag2, hrel2⟩ := hall tr sc hX
    refine ⟨sc, rfl, LprogIsa.retWord dst (ρ f sc) u, sa2, hU', hfv, ?_, ?_, ?_, hA2, ?_⟩
    · rw [hpc2, hpc1]; exact hcl _ bi ra _ hb hbi
    · rw [hpc2, hpc1]; exact hLc _ bi ra _ hb hbi
    · rw [hpc2, hpc1]
      exact ⟨w, zf', ((hag.retWord dst (ρ f sc)).trans hag2).mono hst.2, hrel2⟩
    · rw [hpc2, hpc1, hsim.pos_call _ bi ra _ hb hbi]
  · exact .inr ⟨e₁, k₁, rfl, .inr fun a ha => ⟨s, sa, hk a ha, hfn, hlen, hL, hI, hA, rfl⟩⟩

/-- **A source tree related to an image state at the start of a segment is related by `RuttFA`
    to the family of the target trees** from the index of the position of that state and the
    byte state corresponding to it, under the hypotheses of `segSim_of_imgUpA`. -/
theorem ruttF_of_imgUpA {c : String → CalleeSig} {L : Nat → Bool}
    (hLc : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → L (p + 1) = false)
    (hcl : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → p + 1 < body.length)
    (hsim : SegSimR frame slotArr base rsp body P.lfn E L prog pos tgt (SegTo I T P) Fin)
    (hStep : ∀ p u w v, GlueA T P p u w v → u.prog.base.reg.lpc = p →
      ∀ bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      ∃ dst, v = LprogIsa.retWord dst w u
        ∧ SiteStepA frame slotArr base rsp body (X f) (c f) (ρ f) (E p) (E (p + 1)) dst u)
    {Up : CallTree E₁ R₁ → LstateMF → Prop}
    (hUp : ImgUpA Sk RE RA RR Fail frame slotArr base rsp body E X ρ I T P pos tgt sym rd Fin
      Up)
    {t₁ : CallTree E₁ R₁} {s : LstateMF} (hU : Up t₁ s) (hfn : s.prog.lfn = P.lfn)
    {sa : LstateA} {sA : AState} (hlen : sa.reg.lpc < body.length) (hL : L sa.reg.lpc = false)
    (hI : ImgRelF frame slotArr base body (E sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    RuttFA Sk RE RA RR Fail t₁ fun n => targetTree aMachine prog sym rd n (pos sa.reg.lpc) sA :=
  ruttFA_of_segSimA aMachine prog sym rd Sk RE RA RR Fail
    (segSim_of_imgUpA Sk RE RA RR Fail frame slotArr base rsp body E X ρ I T P prog pos tgt sym
      rd Fin hLc hcl hsim hStep hUp) t₁ _ sA ⟨s, sa, hU, hfn, hlen, hL, hI, hA, rfl⟩

/-- **A relation carried by the image at the summary steps is carried at the answers of the
    callees** when each summary step at a call of `f` is the step `GlueA` at the word that `ρ f`
    reads off every return state of `X f`: a relation `ImgUp` at the source handler `h₁` is a
    relation `ImgUpA` at the skip predicate of the answers of `h₁`. -/
theorem imgUpA_of_imgUp (h₁ : ∀ e : E₁.Event, E₁.Resp e)
    (hρ : ∀ p u v, Glue T P p u v → ∀ bi ra f l, body[p]? = some bi →
      bi.li_i = .Lcall ra (f, l) → ∀ sA tr sc, X f (entryOf (pos p + 1) sA) tr sc →
        GlueA T P p u (ρ f sc) v)
    {Up : CallTree E₁ R₁ → LstateMF → Prop}
    (h : ImgUp h₁ RE RA RR Fail frame slotArr base rsp body E X I T P pos tgt sym rd Fin Up) :
    ImgUpA (fun e a => a = h₁ e) RE RA RR Fail frame slotArr base rsp body E X ρ I T P pos tgt
      sym rd Fin Up := by
  intro t₁ s hU
  rcases h t₁ s hU with hr | ⟨e₁, k₁, rfl, ⟨p, u, v, hseg, hg, hcall⟩ | hk⟩
  · exact .inl hr
  · refine .inr ⟨e₁, k₁, rfl, .inl ⟨p, u, hseg, fun bi ra f l hb hbi sa sA hI hA hpc => ?_⟩⟩
    obtain ⟨hRE, hRA⟩ := hcall bi ra f l hb hbi sa sA hI hA hpc
    refine ⟨hRE, fun a₁ a₂ ha => ?_⟩
    rcases hRA a₁ a₂ ha with hf | ⟨sc, tr, h1, h2, h3⟩
    · exact .inl hf
    · exact .inr ⟨sc, tr, h1, h2, v, hρ p u v hg bi ra f l hb hbi sA tr sc h2, h3⟩
  · exact .inr ⟨e₁, k₁, rfl, .inr fun a ha => by subst ha; exact hk⟩

end Up

/-! ## 3. The image of a calling body at the frame contracts of its callees -/

/-- **The image of a calling body of the wide class against the target trees, with callees at the
    frame contract.** The hypotheses of `NFProgCallTreeCallsChecks.ruttF_of_contracts`, with
    every called symbol `f` of the kind `CalleeKind.ins (lf f) (insK f) (resK f)` and its run
    relation `X f` meeting the interface `LinkedFn.frameSig` of the frame contract of `lf f`. A
    source tree related by a relation `Up` carried by the image at the answers of the callees
    (`ImgUpA` at the reader of the result register of `resK f`) to an image state related up to
    the dead names of its position to an address state at a position where `liveW` is false,
    which corresponds to the byte state `sA`, is related by `RuttFA Sk` to the family of the
    target trees of `prog` from the index of that position and `sA`. No summary value and no
    meaning of a callee enter. -/
theorem ruttF_of_contractsA {E₁ : EventSig} {R₁ : Type} (Sk : (e : E₁.Event) → E₁.Resp e → Prop)
    (RE : E₁.Event → (kSig AState).Event → Prop)
    (RA : (e₁ : E₁.Event) → (e₂ : (kSig AState).Event) → E₁.Resp e₁ →
      (kSig AState).Resp e₂ → Prop)
    (RR : R₁ → Option AState → Prop) (Fail : R₁ → Prop) (sym : Nat → String)
    (rd : String → AState → List _root_.Hax.Value)
    {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {kind : String → CalleeKind} {lf : String → LinkedFn}
    {insK : String → List (String × ArgKind)} {resK : String → String}
    (hkind : ∀ f, CalledIn body f → kind f = .ins (lf f) (insK f) (resK f))
    {X : String → CalleeRun}
    (hX : ∀ f, CalledIn body f →
      CalleeSpec (X f) ((lf f).frameSig ((insK f).map (·.1)) (some (resK f))))
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) {site : Nat → String × List String}
    (hOk : ∀ f, CalledIn body f → (kind f).Ok frame slotArr base rsp body site f G)
    {ds : List X86Backend.PhysAbiShape.DShape} (hcls : printedAddrCWB G body = true)
    (hshapes : X86Backend.DecodeGen.shapesOf (Params.ofBody body) body = some ds)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (symBase : String → Option Int) {prog : List RInstr}
    (tgtI : X86Backend.LprogBytesDecode.Item → Option (Nat × Nat))
    (K : String → Nat)
    (hK : ∀ it f j t, it.target = none → it.sym = some f → tgtI it = some (j, t) → j = K f)
    (hP : X86Backend.LprogBytesLinkReloc.expectedRelocMap
      (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      tgtI
      (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
        = some prog)
    {D : DeadTab} (hbits : bitsDeadB frame D body = true)
    (hdead : callDeadSymB (fun f => (kind f).sig) (fun f => (kind f).isOut) site D.dead body
      = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {fn : String} {pr : Nat → LprogIsa.ProcSummary}
    (hsit : SitesOf T (callImg slotArr site body) pr site)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr site body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      X86Backend.LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    {Up : CallTree E₁ R₁ → LstateMF → Prop}
    (hUp : ImgUpA Sk RE RA RR Fail frame slotArr base rsp body D.dead X
      (fun f sc => sc.regs (phys (resK f))) I T
      (singletonProgM fn (callImg slotArr site body)) (X86Backend.DecodePrintedCFG.posOf ds) K
      sym rd Fin Up)
    {t₁ : CallTree E₁ R₁} {s : LstateMF} (hU : Up t₁ s)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    RuttFA Sk RE RA RR Fail t₁ fun n =>
      targetTree aMachine prog sym rd n (X86Backend.DecodePrintedCFG.posOf ds sa.reg.lpc) sA := by
  have hCF := callFacts_of_printedAddrCWB hcls hshapes
  have hB := byteSegR_of_linked hCF
    (X86Backend.LprogBytesLinkReloc.linkedProg_of_itemsMapL symBase hCF.toLinkFacts tgtI K hK
      prog hP) rsp hfr
  have hsim := segSimR_of_segExactR hD (fun _ h => (liveW_false_spec h).1) hbits
    (segExactR_callImg hsep hphys hgate hsites hcond hB hI site T fn) hB.halt hfin hFin
  refine ruttF_of_imgUpA Sk RE RA RR Fail frame slotArr base rsp body D.dead X
    (fun f sc => sc.regs (phys (resK f))) I T (singletonProgM fn (callImg slotArr site body))
    prog (X86Backend.DecodePrintedCFG.posOf ds) K sym rd Fin
    (c := fun f => (lf f).frameSig ((insK f).map (·.1)) (some (resK f)))
    (fun _ _ _ _ hb hbi => liveW_succ_call hflags hCF.carry hb hbi)
    (lt_of_call_imgGateCBW hgate) hsim ?_ hUp hU hfn hlen hL hI0 hA
  intro p u w v hg hpc bi ra f l hb hbi
  have hcf : CalledIn body f := ⟨p, bi, ra, l, hb, hbi⟩
  obtain ⟨i, pr', dst, srcs, hi, hq, rfl⟩ := hg
  obtain ⟨-, rfl, -⟩ := hsit p i pr' dst srcs hi hq
  have hk := hOk f hcf
  have hsub0 := (callDeadSymB_spec hdead hb hbi).2
  rw [hkind f hcf] at hk
  have hsub : ∀ r ∈ (D.dead p).filter (fun r => r != (site p).1)
      ++ exemptC ((lf f).frameSig ((insK f).map (·.1)) (some (resK f))), r ∈ D.dead (p + 1) := by
    intro r hr
    apply hsub0
    simp only [hkind f hcf, deadOut, CalleeKind.isOut, CalleeKind.sig] at hr ⊢
    exact hr
  exact ⟨(site p).1, rfl, siteStepA_ins hsep hphys (hX f hcf) hS hk ⟨bi, ra, l, hb, hbi⟩
    hsub hpc⟩

/-! ## 4. A reference body cut at its calls, at the answers of the callees -/

/-- **A shadow instruction of a call of a symbol of `T` has the step at every answer**, from every
    state. -/
theorem glueA_of_isSite {T : LprogIsa.ProcTable} {fn : String} {B : List LinstrRM} {p : Nat}
    (h : IsSite T B (some p)) (u : LstateMF) (w : BitVec 64) :
    ∃ v, GlueA T (singletonProgM fn B) p u w v := by
  obtain ⟨i, hi, hp⟩ := h
  obtain ⟨⟨pr, dst, srcs⟩, hq⟩ := Option.isSome_iff_exists.mp hp
  exact ⟨_, i, pr, dst, srcs, hi, hq, rfl⟩

section Ref

variable {E₁ : EventSig} {R₁ : Type} (Sk : (e : E₁.Event) → E₁.Resp e → Prop)
  (RE : E₁.Event → (kSig AState).Event → Prop)
  (RA : (e₁ : E₁.Event) → (e₂ : (kSig AState).Event) → E₁.Resp e₁ → (kSig AState).Resp e₂ →
    Prop)
  (RR : R₁ → Option AState → Prop) (Fail : R₁ → Prop)
  (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
  (base : String → BitVec 64) (rsp : BitVec 64) (body : Lcmd) (E : Nat → List String)
  (X : String → CalleeRun) (ρ : String → AState → BitVec 64) (pos : Nat → Nat)
  (tgt : String → Nat) (sym : Nat → String)
  (rd : String → AState → List _root_.Hax.Value) (Fin : LstateMF → AState → Prop)
  {I : LprogIsa.Isa} {T : LprogIsa.ProcTable} {outs : List String} {fn : String}
  {B B' : List LinstrRM} {cut cut' : Option Nat → Option Nat → List LinstrRM}
  (sim : CutSimIA I T outs fn B B' cut cut' (GlueA T (singletonProgM fn B))
    (GlueA T (singletonProgM fn B')))

/-- **A relation between source call trees and states of `B` carried by its cut programs at the
    answers of the callees.** The clauses of `NFProgCallTreeCallsRef.RefCarried` under a
    simulation `CutSimIA` at the steps `GlueA`, with two changes. After a halting run of the cut
    program from `e` to the shadow instruction at `p`, at every image state at the call `q` that
    the simulation relates to the call state of `B`, the conditions of `ImgUpA` hold with each
    source continuation a failed leaf or related, at the entry `some p`, to a state of `B` after
    the step `GlueA` at `p` at the word `ρ f sc` of the return state `sc` of the callee. A
    source event that `B` does not perform is continued at every answer that `Sk` admits. -/
def RefCarriedA (RefUp : CallTree E₁ R₁ → Option Nat → LstateMF → Prop) : Prop :=
  ∀ t₁ e s, RefUp t₁ e s →
    (∃ r₁, t₁ = .ret r₁ ∧ (Fail r₁ ∨ ∃ t, CutRun I fn (cut e none) s t
      ∧ ∀ t', Obs outs t t' → ∀ sA, Fin t' sA → RR r₁ (some sA)))
    ∨ ∃ e₁ k₁, t₁ = .vis e₁ k₁ ∧
      ((∃ p u, IsSite T B (some p) ∧ CutRun I fn (cut e (some p)) s u ∧
          ∀ u' q, sim.Q (some p) u u' → sim.site (some p) = some q →
          ∀ bi ra f l, body[q]? = some bi → bi.li_i = .Lcall ra (f, l) →
          ∀ sa sA, ImgRelF frame slotArr base body (E q) (goto u' q) sa → ACorr rsp sA sa →
            sa.reg.lpc = q →
            RE e₁ (callEvent aMachine sym rd (pos q) (tgt f) sA)
            ∧ ∀ a₁ a₂, RA e₁ (callEvent aMachine sym rd (pos q) (tgt f) sA) a₁ a₂ →
              (∃ r, k₁ a₁ = .ret r ∧ Fail r)
              ∨ ∃ sc tr, a₂ = some sc
                ∧ X f (entryOf (pos q + 1) sA) tr sc
                ∧ ∃ v, GlueA T (singletonProgM fn B) p u (ρ f sc) v
                  ∧ RefUp (k₁ a₁) (some p) v)
        ∨ ∀ a, Sk e₁ a → RefUp (k₁ a) e s)

/-- The relation between source call trees and image states induced by a relation with the
    states of `B` under a simulation `CutSimIA`: a state of `B` at an entry `e` related to the
    source tree and by `R e` to a state of the function, both entries sites, the image state
    being that state at the entry position of the site of `e`. -/
def RefImgUpA (RefUp : CallTree E₁ R₁ → Option Nat → LstateMF → Prop) (t₁ : CallTree E₁ R₁)
    (s' : LstateMF) : Prop :=
  ∃ e s s₀, RefUp t₁ e s ∧ sim.R e s s₀ ∧ s₀.prog.lfn = fn ∧ IsSite T B e
    ∧ IsSite T B' (sim.site e) ∧ s' = goto s₀ (entryPos (sim.site e))

/-- **A relation carried by the cut programs of `B` at the answers of the callees induces a
    relation carried by the image.** Under the hypotheses of
    `NFProgCallTreeCallsRef.imgUp_of_refCarried` with a simulation `CutSimIA` at the steps
    `GlueA`, a relation `RefUp` carried by the cut programs of `B` (`RefCarriedA`) induces the
    relation `RefImgUpA` carried by the image (`ImgUpA`). -/
theorem imgUp_of_refCarriedA {pos' : Option Nat → Option Nat → Nat → Nat} (hI : PcFree I)
    (hR : I.RefusesProcs T) (hS : FnStable I)
    (hcut' : ∀ e x, IsSite T B' e → IsSite T B' x →
      IsCut T fn B' e x (cut' e x) (pos' e x) ∧ IsCutRev T B' x (cut' e x) (pos' e x))
    {RefUp : CallTree E₁ R₁ → Option Nat → LstateMF → Prop}
    (hC : RefCarriedA Sk RE RA RR Fail frame slotArr base rsp body E X ρ pos tgt sym rd Fin sim
      RefUp) :
    ImgUpA Sk RE RA RR Fail frame slotArr base rsp body E X ρ I T (singletonProgM fn B') pos tgt
      sym rd Fin (RefImgUpA sim RefUp) := by
  have hle : ∀ e, IsSite T B' e → entryPos e ≤ B'.length := by
    intro e he
    cases e with
    | none => exact Nat.zero_le _
    | some p =>
        obtain ⟨i, hi, -⟩ := he
        exact (List.getElem?_eq_some_iff.mp hi).1
  rintro t₁ s' ⟨e, s, s₀, hU, hRs, hfn, hB, he, rfl⟩
  rcases hC t₁ e s hU with ⟨r₁, rfl, hf | ⟨t, hrun, hfin⟩⟩ | ⟨e₁, k₁, rfl, hc | hk⟩
  · exact .inl ⟨r₁, rfl, .inl hf⟩
  · obtain ⟨u', hrun', hQ⟩ := sim.seg e none s s₀ t hB trivial hfn hRs hrun
    rw [sim.site_none] at hrun'
    obtain ⟨hc, hv⟩ := hcut' (sim.site e) none he trivial
    obtain ⟨q, hseg⟩ := segTo_of_cutRun hI hR hS hc hv hfn (hle _ he) hrun'
    have ho : Obs outs t u' := sim.fin _ _ hQ
    exact .inl ⟨r₁, rfl, .inr ⟨_, hseg, hfin _ ⟨ho.1, ho.2.1, ho.2.2⟩⟩⟩
  · obtain ⟨p, u, hp, hrun, hcall⟩ := hc
    obtain ⟨u', hrun', hQ⟩ := sim.seg e (some p) s s₀ u hB hp hfn hRs hrun
    obtain ⟨v0, hg0⟩ := glueA_of_isSite (fn := fn) hp u 0
    obtain ⟨q, v0', hsite, hglue0, -⟩ := sim.glue p u u' 0 v0 hQ hg0
    have hq : IsSite T B' (some q) := (glueLaws_glueA T fn B').site _ _ _ _ hglue0
    rw [hsite] at hrun'
    obtain ⟨hc, hv⟩ := hcut' (sim.site e) (some q) he hq
    obtain ⟨q', hseg⟩ := segTo_of_cutRun hI hR hS hc hv hfn (hle _ he) hrun'
    have hat : atPc (singletonProgM fn B') q (goto u' q') := by
      obtain ⟨_, _, hat, _⟩ := hseg
      exact hat
    have hqq : q' = q := hat.2
    subst hqq
    refine .inr ⟨e₁, k₁, rfl, .inl ⟨q', goto u' q', hseg,
      fun bi ra f l hb hbi sa sA hIr hA hpc => ?_⟩⟩
    obtain ⟨hRE, hRA⟩ := hcall u' q' hQ hsite bi ra f l hb hbi sa sA hIr hA hpc
    refine ⟨hRE, fun a₁ a₂ ha => ?_⟩
    rcases hRA a₁ a₂ ha with hf | ⟨sc, tr, h1, h2, v, hg, hU'⟩
    · exact .inl hf
    obtain ⟨q2, v', hsite2, hglue', hR'⟩ := sim.glue p u u' (ρ f sc) v hQ hg
    rw [hsite] at hsite2
    obtain rfl := Option.some.inj hsite2
    have hg' := hglue'.goto q'
    have hfn' : v'.prog.lfn = fn := (hg'.atPc_succ hat).1
    exact .inr ⟨sc, tr, h1, h2, goto v' (q' + 1), hg', some p, v, v', hU', hR', hfn', hp,
      by rw [hsite]; exact hq, by rw [hsite]; rfl⟩
  · exact .inr ⟨e₁, k₁, rfl, .inr fun a ha => ⟨e, s, s₀, hk a ha, hRs, hfn, hB, he, rfl⟩⟩

end Ref

/-- **A relation with a family is a relation with every family that is that family after some
    fuel**, for `RuttFA`. -/
theorem RuttFA.shift {E₁ E₂ : EventSig} {R₁ R₂ : Type} {Sk : (e : E₁.Event) → E₁.Resp e → Prop}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {t₁ : CallTree E₁ R₁}
    {T₀ T₁ : Nat → CallTree E₂ R₂} (j : Nat) (hT : ∀ m, T₀ (j + m) = T₁ m)
    (h : RuttFA Sk RE RA RR Fail t₁ T₁) : RuttFA Sk RE RA RR Fail t₁ T₀ := by
  induction h generalizing T₀ with
  | ret n hn hR => exact .ret (j + n) (by rw [hT, hn]) hR
  | fail hf => exact .fail hf
  | vis n hn he hk ih => exact .vis (j + n) (fun m => by rw [Nat.add_assoc, hT, hn]) he hk
  | skip hk ih => exact .skip fun a ha => ih a ha hT

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSiteAns

/-! ## 5. The calling body of the back half at the frame contracts of its callees -/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSiteAns

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotRen slotArrOf
  slotArrOf_some)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody
  cellBody_getElem?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (ProcTable ProcSummary)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiReg abiBase)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle (RuttFA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCutAns (GlueA CutSimIA)
open CatCrypt.Crypto.Hax (LinkedFn)

/-- **The calling body of the back half against the target trees, at the frame contracts of its
    callees.** The hypotheses of `NFProgCallTreeCallsLinked.ruttF_calleeBody`, with each function
    `c` of `T` of the kind `CalleeKind.ins (lf c.name) (insK c.name) (resK c.name)` and its run
    relation `X c.name` meeting the interface `LinkedFn.frameSig` of the frame contract of
    `lf c.name`. From every entry state `sa` satisfying `σ.Regions`, the calling body has a
    caller program `pc` and shapes `ds` such that every source call tree related, by a relation
    `Up` carried by the image of `b` at the answers of the callees (`ImgUpA` at the reader of the
    result register of `resK f`), to the entry state of the image is related by `RuttFA Sk` to
    the family of the target trees of `pc` from index `0` and `sa`. -/
theorem ruttF_calleeBodyA {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
    {bytes : List (BitVec 8)} {w m : Nat} {r : Exported} {cert : List (String × String)}
    (hbs : calleeBytes (some T) b = some bytes)
    (hg : regionCoB σ exportReg b (.stackArr w m) r.code r.res cert (some T) a.fname = true)
    {d : CoParts}
    (hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCodeT (some T) r.code) r.res cert
      (some T) = d)
    (kind : String → CalleeKind) (lf : String → LinkedFn)
    (insK : String → List (String × ArgKind)) (resK : String → String) (X : String → CalleeRun)
    (hK : ∀ c ∈ T.fns, (kind c.name).Top c
      ∧ kind c.name = .ins (lf c.name) (insK c.name) (resK c.name)
      ∧ CalleeSpec (X c.name)
        ((lf c.name).frameSig ((insK c.name).map (·.1)) (some (resK c.name))))
    {PT : ProcTable} (hTc : ∀ c ∈ T.fns, PT c.name = some (kind c.name).summary)
    (sa : AState) (hreg : σ.Regions sa) :
    ∃ (pc : List RInstr) (ds : List X86Backend.PhysAbiShape.DShape),
      calleeProg T b = some pc
      ∧ X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
      ∧ ∀ {E₁ : EventSig} {R₁ : Type} (Sk : (e : E₁.Event) → E₁.Resp e → Prop)
        (RE : E₁.Event → (kSig AState).Event → Prop)
        (RA : (e₁ : E₁.Event) → (e₂ : (kSig AState).Event) → E₁.Resp e₁ →
          (kSig AState).Resp e₂ → Prop)
        (RR : R₁ → Option AState → Prop) (Fail : R₁ → Prop) (sym : Nat → String)
        (rd : String → AState → List _root_.Hax.Value) (Up : CallTree E₁ R₁ → LstateMF → Prop),
        ImgUpA Sk RE RA RR Fail (X86Backend.ImageAddrRoute.frameE b sa)
          (slotRen (slotArrOf σ exportReg) (renOf d.ps))
          (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) (X86Backend.DecodePrintedCFG.frameRsp b sa)
          b (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg)
            (renOf d.ps)) (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b)
            d.outs).dead X (fun f sc => sc.regs (phys (resK f)))
          X86Backend.CheckedIsaCall.x86IsaK PT
          (singletonProgM a.fname (X86Backend.ImageAddrCall.callImg
            (slotRen (slotArrOf σ exportReg) (renOf d.ps))
            (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b))
          (X86Backend.DecodePrintedCFG.posOf ds) (fun f => pc.length + T.entryIdx (T.symPos f))
          sym rd (FinT σ sa d.ps) Up →
        ∀ t₁, Up t₁ (entryImg σ b sa d.ps a.fname) →
        RuttFA Sk RE RA RR Fail t₁ fun n => targetTree aMachine pc sym rd n 0 sa := by
  -- The summaries of the procedure table at the symbols of the table and elsewhere.
  have hTf : ∀ f c, T.lookup f = some c → PT f = some (kind f).summary := by
    intro f c hc
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    exact hTc c hcm
  -- The conjuncts of the gate.
  have hg' := hg
  simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, hce⟩, hren⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, himg⟩⟩ := hg'
  have hcells : d.cells = [] := List.isEmpty_iff.mp hce
  rw [hcells] at himg
  have himg0 := himg
  have RF := X86Backend.ImageAddrRoute.renB_spec hren
  have hU := fun j (hj : j < σ.args.length) => (RF.unr j hj).2
  obtain ⟨hsep, -, hacorr, hpc0, -⟩ := renImage_entry_nil himg0 hU sa hreg a.fname []
  have hrelF := fun X => (renImage_entry_nil himg0 hU sa hreg a.fname X).2.1
  simp only [renImageB, X86Backend.ImageAddrRouteW.slotArrC_nil, Bool.and_eq_true] at himg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hphys⟩, himgT⟩, -⟩, hent⟩, -⟩, -⟩ := himg
  obtain ⟨-, -, hcls, hgate⟩ := calleeImgBT_some himgT
  have hcellsE : d.cells = regionCells σ exportReg d.ps b (d.fused.drop d.pre.length) := by
    rw [← hd]; rfl
  have hcb0 : cellBody (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b = b :=
    cellBody_of_cellArrsOf_nil _ (cellArrsOf_nil_of_regionCells_nil (hcellsE ▸ hcells))
  rw [hcb0] at hphys hrelF
  have hfm : X86Backend.ImageStraightCells.frameMarkC [] b
      = X86Backend.ImageAddrFrame.frameMark (X86Backend.ImageAddrFrame.frameNames b) := rfl
  rw [hcb0, hfm] at hgate
  -- The checks of the calling body.
  have hok := calleeBodyBT_spec.mp hcb
  have hsites := hok.callSites
  have hdead := hok.dead
  have hflags := hok.flags
  have hcond := hok.condLive
  have hseg := hok.deadSeg
  have hlive := hok.live0
  have hroomB := hok.stackRoom
  have hnn := hok.frameNonneg
  have hcode := hok.code
  simp only [calleeDeadBT, Bool.and_eq_true] at hdead
  obtain ⟨hdo, hparB⟩ := hdead
  have hl : b.getLast?.any (fun r => X86Backend.DecodePrinted.isRetB r.li_i) = true := by
    have h1 := hcls
    simp only [X86Backend.ImageAddrCallW.printedAddrCWB, Bool.and_eq_true] at h1
    exact h1.1.1.1.2
  have hcall : ∀ {q : Nat} {bi : Linstr} {ra : Option String} {f : String} {l : LLabel},
      b[q]? = some bi → bi.li_i = .Lcall ra (f, l) → ∃ c, T.lookup f = some c :=
    fun hb hbi => lookup_of_call hok.decode hl hb hbi
  -- The dead names at the interfaces and the result kinds of the kinds.
  have hdead' : X86Backend.ImageAddrCall.callDeadSymB (fun f => (kind f).sig)
      (fun f => (kind f).isOut) (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
      (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b) d.outs).dead b
      = true := by
    refine (callDeadSymB_congr_exempt fun q bi ra f l hb hbi => ?_).trans hdo
    obtain ⟨c, hc⟩ := hcall hb hbi
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    obtain ⟨-, -, -, -, hout, hclob, hres, -⟩ := (hK c hcm).1.facts
    refine ⟨?_, ?_, rfl⟩
    · simp only [CalleeTab.sigOf, hc]
      unfold X86Backend.ImageAddrCall.exemptC
      rw [hclob, hres]
    · simp only [CalleeTab.outOf, hc, Option.any_some, hout]
      cases c.res <;> rfl
  -- The summaries at the call sites of the image.
  have hsit : X86Backend.ImageAddrCall.SitesOf PT
      (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b)
      (fun q => (kind ((callSymAt b q).getD "")).summary)
      (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) :=
    X86Backend.ImageAddrCall.sitesOf_callImg _ hsites fun q bi ra f l hb hbi => by
      obtain ⟨c, hc⟩ := hcall hb hbi
      simp only [callSymAt_eq_some.mpr ⟨bi, ra, l, hb, hbi⟩, Option.getD_some]
      exact hTf f c hc
  -- The caller separation at the renamed slot map.
  have E := X86Backend.ImageAddrRoute.entryB_spec hent sa
  have hun : ∀ q A n, slotArrOf σ exportReg q = some (A, n) →
      X86Backend.ImageAddrRoute.unren d.ps (renOf d.ps A) = A := by
    intro q A n hq
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some hq
    exact (RF.unr j (List.getElem?_eq_some_iff.mp hj).1).2
  have hS0 := X86Backend.CalleeStackRoom.callerSep_of_regions E.rs hreg hroomB hnn
    (slotArr := slotArrOf σ exportReg) E.len
  have hS : X86Backend.ImageAddrCall.CallerSep (X86Backend.ImageAddrRoute.frameE b sa)
      (slotRen (slotArrOf σ exportReg) (renOf d.ps)) (X86Backend.ImageAddrRouteW.baseR σ sa d.ps)
      (X86Backend.DecodePrintedCFG.frameRsp b sa) T.frame := by
    refine ⟨hS0.frames, fun q A' n j hq hj x hx => ?_⟩
    obtain ⟨A, hA, rfl⟩ := X86Backend.ImageAddrRoute.slotRen_some hq
    have hb : X86Backend.ImageAddrRouteW.baseR σ sa d.ps (renOf d.ps A)
        = abiBase (abiReg σ) sa A := by
      simp only [X86Backend.ImageAddrRouteW.baseR, hun q A n hA]
    rw [hb] at hx
    exact hS0.cells q A n j hA hj x hx
  -- The hypotheses of the calls of each symbol at its kind.
  have hgateW :=
    (imgGateCBW_frameMark b (X86Backend.DecodePrintedCFG.frameRsp b sa) _).trans hgate
  have hgateI := X86Backend.ImageAddrCallW.imgGateW_of_imgGateCBW hgateW
  have hOk : ∀ f, X86Backend.ImageAddrCall.CalledIn b f →
      (kind f).Ok (X86Backend.ImageAddrRoute.frameE b sa)
        (slotRen (slotArrOf σ exportReg) (renOf d.ps)) (X86Backend.ImageAddrRouteW.baseR σ sa d.ps)
        (X86Backend.DecodePrintedCFG.frameRsp b sa) b
        (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) f T.frame := by
    rintro f ⟨q, bi, ra, l, hb, hbi⟩
    obtain ⟨c, hc⟩ := hcall hb hbi
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    exact (hK c hcm).1.ok hsep hgateI hS hparB hcode hc (CalleeTab.frame_le hcm)
  -- The end of the run: the words of the arrays of the slot map at their bases.
  let Fin : LstateMF → AState → Prop := fun t sA => ∀ q A n,
    slotRen (slotArrOf σ exportReg) (renOf d.ps) q = some (A, n) →
      ∃ arr, t.prog.base.getArr A 64 n = some arr
        ∧ ∀ j (hj : j < n), read64 sA.mem
          (cellAt (X86Backend.ImageAddrRouteW.baseR σ sa d.ps A) j) = arr ⟨j, hj⟩
  have hfin : ∀ t0 sa0 zf sA, X86Backend.ImageAddrSim.ImgRel
      (X86Backend.ImageAddrRoute.frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
      (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b t0 sa0 zf →
      X86Backend.LprogBytesLinkReloc.FinLea (X86Backend.DecodePrintedCFG.frameRsp b sa)
        (X86Backend.LprogBytesDecode.Params.ofBody b).frame sa0 sA → Fin t0 sA := by
    rintro t0 sa0 zf sA hrel ⟨sB, hcB, rfl⟩ q A n hq
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A n hq
    refine ⟨arr, h1, fun j hj => ?_⟩
    rw [(X86Backend.DecodePrinted.evalInstrA_leaFrame sB _).2,
      ← X86Backend.DecodePrintedAddr.read64_eq_of_agree hcB.mem (hsep.red q A n j hq hj)]
    exact h2 j hj
  have hFin : ∀ t1 t2 sA, X86Backend.ImageAddrCall.AgreeOffF
      ((deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b) d.outs).dead
        t1.prog.base.reg.lpc) t1 t2 →
      Fin t2 sA → Fin t1 sA := by
    intro t1 t2 sA hag hF2 q A n hq
    obtain ⟨arr, h1, h2⟩ := hF2 q A n hq
    exact ⟨arr, by rw [X86Backend.ImageAddrSim.getArr_congr hag.arr]; exact h1, h2⟩
  have hbne : b ≠ [] := by
    intro hb
    simp [X86Backend.ImageAddrCallW.printedAddrCWB, hb] at hcls
  have hlen : (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc < b.length := by
    rw [hpc0]
    exact List.length_pos_iff.mpr hbne
  -- The bytes of the calling body.
  obtain ⟨hbytes, hne, ds, prog, hss, hbr, hP, hprog, hp0⟩ := calleeBytes_tab hbs
  have hLv : X86Backend.ImageAddrCallW.liveW
      (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg)
        (renOf d.ps)) (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
        b) d.outs) (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b
      (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc = false := by
    rw [hpc0]
    exact X86Backend.ImageAddrCallW.liveW_zero (by simpa using hlive)
      (X86Backend.ImageAddrCallW.callFacts_of_printedAddrCWB hcls hss).carry
  have hbits : X86Backend.ImageAddrCallW.bitsDeadB (X86Backend.ImageAddrRoute.frameE b sa)
      (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg)
        (renOf d.ps)) (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
        b) d.outs) b = true :=
    (bitsDeadB_frameMark b _ _).trans hok.bitsDead
  have hlenP := X86Backend.LprogBytesLinkReloc.expectedRelocMap_length _ _ _ _ hP
  refine ⟨prog, ds, hprog, hss, fun Sk RE RA RR Fail sym rd Up hUp t₁ hU => ?_⟩
  have hR := ruttF_of_contractsA Sk RE RA RR Fail sym rd hsep hphys hgateW hsites
    (kind := kind) (lf := lf) (insK := insK) (resK := resK) (X := X)
    (fun f ⟨_, bi, ra, l, hb, hbi⟩ => by
      obtain ⟨c, hc⟩ := hcall hb hbi
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
      exact (hK c hcm).2.1)
    (fun f ⟨_, bi, ra, l, hb, hbi⟩ => by
      obtain ⟨c, hc⟩ := hcall hb hbi
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
      exact (hK c hcm).2.2)
    hS hOk hcls hss (fun q hq => X86Backend.ImageAddrFrame.frameIn_eq q hq) (calleeSym T b) _
    (fun f => prog.length + T.entryIdx (T.symPos f))
    (fun it f j t _ hs ht => by
      simp only [X86Backend.LprogBytesLinkReloc.symTgt, hs, Option.bind_some,
        CalleeTab.linkMap, Option.some.injEq, Prod.mk.injEq] at ht
      rw [← ht.1, hlenP])
    hP hbits hdead' hflags hcond hsit X86Backend.CheckedIsaCall.x86IsaK_checked
    (X86Backend.CheckedIsaCall.deadSteps_x86K hseg) hfin hFin hUp hU rfl hlen hLv
    (hrelF _) hacorr
  have hpos : X86Backend.DecodePrintedCFG.posOf ds 0 = 0 + 1 := by
    simp [X86Backend.DecodePrintedCFG.posOf]
  rw [hpc0, hpos] at hR
  have hstep : X86Backend.RInstrSemantics.step aMachine prog 0 sa = some (.go (0 + 1)
      (Ascent.AddrMem.evalInstrA sa (X86Backend.PhysAbiShape.leaFrame
        (-(Int.ofNat (X86Backend.LprogBytesDecode.Params.ofBody b).frame))))) := by
    simp only [X86Backend.RInstrSemantics.step, hp0]
    rfl
  obtain ⟨j, hj⟩ := NFProgCallTreeCalls.targetTree_of_reaches aMachine prog sym rd
    (X86Backend.RInstrSemantics.Reaches.single hstep)
  exact RuttFA.shift j hj hR

/-- **The calling body of the back half against the target trees, from its reference, at the
    frame contracts of its callees.** Under the hypotheses of `ruttF_calleeBodyA`, at every
    simulation `sim` of the cut programs of the reference `d.ref` of the calling body by those of
    its image at the steps `GlueA` (`CalleeSegCheckAns.segSimA_of_checks`), on the checked x86
    instruction set with the procedures of `PT`, at the label `freshLabel` of both: every source
    call tree related to the entry state of the reference by a relation carried by the cut
    programs of the reference at the answers of the callees (`RefCarriedA`) is related by
    `RuttFA Sk` to the family of the target trees of the caller program from index `0` and
    `sa`. -/
theorem ruttF_calleeBody_refA {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
    {bytes : List (BitVec 8)} {w m : Nat} {r : Exported} {cert : List (String × String)}
    (hbs : calleeBytes (some T) b = some bytes)
    (hg : regionCoB σ exportReg b (.stackArr w m) r.code r.res cert (some T) a.fname = true)
    {d : CoParts}
    (hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCodeT (some T) r.code) r.res cert
      (some T) = d)
    (kind : String → CalleeKind) (lf : String → LinkedFn)
    (insK : String → List (String × ArgKind)) (resK : String → String) (X : String → CalleeRun)
    (hK : ∀ c ∈ T.fns, (kind c.name).Top c
      ∧ kind c.name = .ins (lf c.name) (insK c.name) (resK c.name)
      ∧ CalleeSpec (X c.name)
        ((lf c.name).frameSig ((insK c.name).map (·.1)) (some (resK c.name))))
    {PT : ProcTable} (hTc : ∀ c ∈ T.fns, PT c.name = some (kind c.name).summary)
    (sa : AState) (hreg : σ.Regions sa) :
    ∃ (pc : List RInstr) (ds : List X86Backend.PhysAbiShape.DShape),
      calleeProg T b = some pc
      ∧ X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
      ∧ ∀ {E₁ : EventSig} {R₁ : Type} (Sk : (e : E₁.Event) → E₁.Resp e → Prop)
        (RE : E₁.Event → (kSig AState).Event → Prop)
        (RA : (e₁ : E₁.Event) → (e₂ : (kSig AState).Event) → E₁.Resp e₁ →
          (kSig AState).Resp e₂ → Prop)
        (RR : R₁ → Option AState → Prop) (Fail : R₁ → Prop) (sym : Nat → String)
        (rd : String → AState → List _root_.Hax.Value)
        (sim : CutSimIA X86Backend.CheckedIsaCall.x86IsaK PT d.outs a.fname d.ref
          (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
            (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b)
          (LprogCallCut.cutAt a.fname (freshLabel (d.ref ++
            X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
              (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b)) d.ref)
          (LprogCallCut.cutAt a.fname (freshLabel (d.ref ++
            X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
              (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b))
            (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
              (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b))
          (GlueA PT (singletonProgM a.fname d.ref))
          (GlueA PT (singletonProgM a.fname
            (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
              (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b))))
        (RefUp : CallTree E₁ R₁ → Option Nat → LstateMF → Prop),
        RefCarriedA Sk RE RA RR Fail (X86Backend.ImageAddrRoute.frameE b sa)
          (slotRen (slotArrOf σ exportReg) (renOf d.ps))
          (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) (X86Backend.DecodePrintedCFG.frameRsp b sa)
          b (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg)
            (renOf d.ps)) (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b)
            d.outs).dead X (fun f sc => sc.regs (phys (resK f)))
          (X86Backend.DecodePrintedCFG.posOf ds)
          (fun f => pc.length + T.entryIdx (T.symPos f)) sym rd (FinT σ sa d.ps) sim RefUp →
        ∀ t₁, RefUp t₁ none (entryImg σ b sa d.ps a.fname) →
        RuttFA Sk RE RA RR Fail t₁ fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨pc, ds, hpc, hds, hR⟩ :=
    ruttF_calleeBodyA hbs hg hd kind lf insK resK X hK hTc sa hreg
  refine ⟨pc, ds, hpc, hds, fun Sk RE RA RR Fail sym rd sim RefUp hC t₁ hU => ?_⟩
  -- The checks of the calling body.
  have hg' := hg
  simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := hg'
  have hok := calleeBodyBT_spec.mp hcb
  have hsymB : X86Backend.ImageAddrCall.bodyCallSymsB (fun g => T.names.contains g) b
      = true := by
    have h1 := bodyCallSymsB_of_decodeSites hok.decode
    rwa [CalleeTab.lookup_isSome] at h1
  have hsi := RegionLinkCompose.callSymsB_callImg
    (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) hok.callSites hsymB
  have hT' : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length := by
    intro f c hc
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    obtain ⟨har, -⟩ := (hK c hcm).1.facts
    exact ⟨_, hTc c hcm, har⟩
  have hDi := RegionLinkCompose.calleeTab_domEqT hT' hsi
  have hcutI := RegionLinkCompose.calleeCutB_of_domEq hok.cutImg hDi
  have hcut' := cuts_of_calleeCutB (fn := a.fname) hcutI fun i hi => List.mem_append_right _ hi
  refine hR Sk RE RA RR Fail sym rd (RefImgUpA sim RefUp)
    (imgUp_of_refCarriedA Sk RE RA RR Fail _ _ _ _ b _ X _ _ _ sym rd _ sim
      X86Backend.CheckedIsaCall.x86IsaK_pcFree (X86Backend.CheckedIsaCall.x86IsaK_refusesProcs PT)
      X86Backend.CheckedIsaCall.fnStable_x86IsaK hcut' hC) t₁
    ⟨none, _, _, hU, sim.init _, rfl, trivial, by rw [sim.site_none]; trivial, ?_⟩
  rw [sim.site_none]
  rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSiteAns
