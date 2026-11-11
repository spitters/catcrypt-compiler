/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsImg
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack

/-!
# The image of a calling body cut at its calls, against the target trees

The simulation of the image of a calling body by its decoded program holds segment by segment
(`NFProgCallTreeCallsImg`), and the step of a call site relates the image state after the call
to every return state of the callee that the run relation of its kind admits
(`ImageAddrCall.ResStep`). A relation `Up` between source call trees and image states at the
start of a segment that the segments of the image and the steps of its call sites carry, with
the events of the source matched at each call, then gives a simulation of the source trees by
the decoded program cut at its calls (`NFProgCallTreeCallsBack.SegSim`), hence a relation by
`RuttF` with the family of the target trees.

## Main definitions

* `SegSimR`: the simulation of a segment of the image by a path of the decoded program, up to
  the dead names of each position.
* `ImgUp`: a relation between source call trees and image states carried by the segments and
  the call sites of the image.

## Main results

* `segSimR_of_segExactR`: the simulation of a segment up to dead names from `SegExactR`.
* `segSim_of_imgUp`: a relation carried by the image gives the simulation cut at the calls.
* `ruttF_of_imgUp`: a source tree related to an image state at the start of the body is
  related by `RuttF` to the family of the target trees from the index of that state.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSite

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport hiding regName
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (stepA)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (evalInstrPMemFk)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (RunChain SegTo Glue runChain_of_run)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (Steps Halted atPc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
  (RInstr Params ShapeOK Shape)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (remoteSym)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc (RelocShapeOK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (calleeSavedToSave frameSize)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys isRetB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
  (instrOKB condPrevB frameRsp isCondB LoadSafeAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
  (ACorrW widenS widenCell lvm_of_getW instrOKWB carryPrevB castPosB SafeWN WideSafeAt CellSafeAt
    NarrowInv CarryReq narrowIn narrowIn_zero narrowIn_succ narrowStep narrowInv_step classifyK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameIn bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkW
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
  (CalleeRun CalleeSig CalleeSpec HaltsO)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsImg

/-! ## Segments up to dead names -/

/-- A path of steps followed by a halting path without call is a halting path without call. -/
theorem reachesHalts {σ : Type} {M : Machine σ} {prog : List RInstr} {pc pc' : Nat}
    {s s' s'' : σ} (h : Reaches M prog pc s pc' s') (h' : HaltsNoCall M prog pc' s' s'') :
    HaltsNoCall M prog pc s s'' := by
  obtain ⟨q, hr, hret⟩ := h'
  exact ⟨q, h.trans hr, hret⟩

/-- **The simulation of one segment of the image by a path of the decoded program**, the
    statement of `ImageAddrCall.SegSim` with paths: from an image state in the function `fn`
    related, up to the dead names of its position and the flags, to an address state that
    corresponds to a byte state, at a position where no flag is live, a segment to the call at
    position `p` reaches, by a path from the index of the start to the index of the call, an
    image state related up to the dead names of `p` to an address state at `p`; a segment to an
    end state gives a halting path without call to a byte state that satisfies `Fin` with the end
    state. -/
structure SegSimR (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) (rsp : BitVec 64)
    (body : Lcmd) (fn : String) (E : Nat → List String) (L : Nat → Bool)
    (prog : List RInstr) (pos : Nat → Nat) (tgt : String → Nat)
    (Seg : LstateMF → Option Nat → LstateMF → Prop) (Fin : LstateMF → AState → Prop) :
    Prop where
  /-- A segment to a call. -/
  toCall : ∀ s sa sA p u, s.prog.lfn = fn → sa.reg.lpc < body.length →
    L sa.reg.lpc = false →
    ImgRelF frame slotArr base body (E sa.reg.lpc) s sa →
    ACorr rsp sA sa → Seg s (some p) u →
    ∃ sa' sA', ImgRelF frame slotArr base body (E p) u sa' ∧ ACorr rsp sA' sa'
      ∧ sa'.reg.lpc = p
      ∧ (∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t
          ∧ prog[pos p]? = some (.call (tgt t.1)))
      ∧ Reaches aMachine prog (pos sa.reg.lpc) sA (pos p) sA'
  /-- A segment to an end state. -/
  toEnd : ∀ s sa sA t, s.prog.lfn = fn → sa.reg.lpc < body.length →
    L sa.reg.lpc = false →
    ImgRelF frame slotArr base body (E sa.reg.lpc) s sa →
    ACorr rsp sA sa → Seg s none t →
    ∃ sA', HaltsNoCall aMachine prog (pos sa.reg.lpc) sA sA' ∧ Fin t sA'
  /-- The index after a call. -/
  pos_call : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
    pos (p + 1) = pos p + 1

/-- **The simulation `SegSimR` of a segment up to dead names, from `SegExactR`**, under the
    hypotheses of `ImageAddrCallW.segSim_of_segExactW` with the closing return a halting path
    without call. -/
theorem segSimR_of_segExactR {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} {D : DeadTab} {L : Nat → Bool} {prog : List RInstr} {pos : Nat → Nat} {tgt : String → Nat} {I : LprogIsa.Isa}
    {T : LprogIsa.ProcTable} {fn : String} {B : List LinstrRM} {FinA : LstateA → AState → Prop}
    {Fin : LstateMF → AState → Prop} (hD : DeadSteps D I (singletonProgM fn B))
    (hLD : ∀ k, L k = false → D.live k = false)
    (hbits : bitsDeadB frame D body = true)
    (hX : SegExactR frame slotArr base rsp body fn L prog pos tgt
      (SegTo I T (singletonProgM fn B)))
    (hhalt : ∀ sa sA, sa.reg.lpc + 1 = body.length → ACorr rsp sA sa →
      ∃ sA', HaltsNoCall aMachine prog (pos sa.reg.lpc) sA sA' ∧ FinA sa sA')
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf → FinA sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA) :
    SegSimR frame slotArr base rsp body fn D.dead L prog pos tgt
      (SegTo I T (singletonProgM fn B)) Fin := by
  refine ⟨fun s sa sA p u hfn hlen hL hI hA hseg => ?_,
    fun s sa sA t hfn hlen hL hI hA hseg => ?_, hX.pos_call⟩
  · obtain ⟨s', zf, hag, hrel⟩ := deadAgree_of_imgRelF (hLD _ hL) hI
    obtain ⟨n, hn, hat, i, hi, hproc⟩ := hseg
    obtain ⟨u', hn', hagu⟩ := hD n s s' u hag hn
    have hat' : atPc (singletonProgM fn B) p u' :=
      ⟨hagu.off.fn.symm.trans hat.1, hagu.off.pc.symm.trans hat.2⟩
    obtain ⟨sa', zf', sA', hrel', hA', ⟨bi, ra, t', hb, hbi, hprog⟩, hk⟩ :=
      hX.toCall s' sa zf sA p u' (hag.off.fn.symm.trans hfn) hlen hL hrel hA
        ⟨n, hn', hat', i, hi, hproc⟩
    have hpu : u.prog.base.reg.lpc = p := hat.2
    have hpa : sa'.reg.lpc = p := hrel'.pc.trans (hagu.off.pc.symm.trans hpu)
    obtain ⟨⟨u'', zf'', hag2, hrel2⟩, hA2⟩ := imgRelF_of_imgRelW (E := D.dead p) hrel' hA'
      (by rw [hpa]; exact bitsDeadB_call hbits hb hbi)
    refine ⟨widenS sA' sa', sA', ⟨u'', zf'', ?_, hrel2⟩, hA2, hpa,
      ⟨bi, ra, t', hb, hbi, hprog⟩, hk⟩
    have := hagu.off
    rw [hpu] at this
    exact (this.trans hag2).mono fun r hr => by simpa using hr
  · obtain ⟨s', zf, hag, hrel⟩ := deadAgree_of_imgRelF (hLD _ hL) hI
    obtain ⟨n, hn, hhalt0⟩ := hseg
    obtain ⟨t', hn', hagt⟩ := hD n s s' t hag hn
    have hhalt' : Halted (singletonProgM fn B) t' := by
      unfold Halted findInstrMem at hhalt0 ⊢
      rw [← hagt.off.fn]
      exact (congrArg (fun q => if t.prog.lfn = fn then B[q]? else none) hagt.off.pc.symm).trans
        hhalt0
    obtain ⟨sa', zf', sA', hrel', hA', hend, hk⟩ :=
      hX.toEnd s' sa zf sA t' (hag.off.fn.symm.trans hfn) hlen hL hrel hA ⟨n, hn', hhalt'⟩
    have hpe : sa'.reg.lpc = body.length - 1 := by omega
    obtain ⟨⟨t'', zf'', hag2, hrel2⟩, hA2⟩ := imgRelF_of_imgRelW
      (E := D.dead (body.length - 1)) hrel' hA' (by rw [hpe]; exact bitsDeadB_last hbits)
    obtain ⟨sA'', hrun, hfa⟩ := hhalt (widenS sA' sa') sA' hend hA2
    refine ⟨sA'', reachesHalts hk hrun, hFin t t'' sA'' ?_ (hfin _ _ _ _ hrel2 hfa)⟩
    have hpt : t.prog.base.reg.lpc = body.length - 1 := by
      rw [hagt.off.pc, ← hrel'.pc, hpe]
    rw [hpt]
    have := hagt.off
    rw [hpt] at this
    exact (this.trans hag2).mono fun r hr => by simpa using hr


/-! ## Source trees carried by the image -/

section Up

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack (callEvent ruttF_of_segSim)

variable {E₁ : EventSig} {R₁ : Type} (h₁ : ∀ e : E₁.Event, E₁.Resp e)
  (RE : E₁.Event → (kSig AState).Event → Prop)
  (RA : (e₁ : E₁.Event) → (e₂ : (kSig AState).Event) → E₁.Resp e₁ → (kSig AState).Resp e₂ →
    Prop)
  (RR : R₁ → Option AState → Prop) (Fail : R₁ → Prop)
  (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
  (base : String → BitVec 64) (rsp : BitVec 64) (body : Lcmd) (E : Nat → List String)
  (X : String → CalleeRun) (I : LprogIsa.Isa) (T : LprogIsa.ProcTable) (P : LprogM)
  (prog : List RInstr) (pos : Nat → Nat) (tgt : String → Nat) (sym : Nat → String)
  (rd : String → AState → List _root_.Hax.Value) (Fin : LstateMF → AState → Prop)

/-- **A relation between source call trees and image states carried by the image.** From a
    source tree and an image state at the start of a segment related by `Up`: a failed source
    leaf; a source leaf whose value `RR` relates to every byte state that `Fin` relates to the
    end state of the segment of the image to its end; a source event and a segment of the image
    to a call at `p` of a symbol `f`, followed by the step `Glue` of the call to `v`, such that at
    every address state at `p` related up to the dead names of `p` to the image state at the call
    and every byte state corresponding to it, `RE` relates the source event to the linked event
    of the call of `tgt f` at the index `pos p`, and at every answer that `RA` relates to a source
    answer the source continuation is a failed leaf, or the answer is a return state of a run of
    `X f` from the entry state of the call at which the source continuation and `v` are related
    by `Up`; or a source event that the image does not
    perform, the source continuation at the answer of the source handler related to the same
    image state. -/
def ImgUp (Up : CallTree E₁ R₁ → LstateMF → Prop) : Prop :=
  ∀ t₁ s, Up t₁ s →
    (∃ r₁, t₁ = .ret r₁ ∧
      (Fail r₁ ∨ ∃ t, SegTo I T P s none t ∧ ∀ sA, Fin t sA → RR r₁ (some sA)))
    ∨ ∃ e₁ k₁, t₁ = .vis e₁ k₁ ∧
      ((∃ p u v, SegTo I T P s (some p) u ∧ Glue T P p u v ∧
          ∀ bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
          ∀ sa sA, ImgRelF frame slotArr base body (E p) u sa → ACorr rsp sA sa →
            sa.reg.lpc = p →
            RE e₁ (callEvent aMachine sym rd (pos p) (tgt f) sA)
            ∧ ∀ a₁ a₂, RA e₁ (callEvent aMachine sym rd (pos p) (tgt f) sA) a₁ a₂ →
              (∃ r, k₁ a₁ = .ret r ∧ Fail r)
              ∨ ∃ sc tr, a₂ = some sc
                ∧ X f (X86Backend.ImageCallProbe.entryOf (pos p + 1) sA) tr sc ∧ Up (k₁ a₁) v)
        ∨ Up (k₁ (h₁ e₁)) s)

/-- The invariant of the cut simulation from a relation carried by the image: a source tree
    related by `Up` to an image state in the function of `P`, which is related up to the dead
    names of its position to an address state at a position of the body where no flag is live,
    corresponding to the byte state at the index of that position. -/
def UpInv (L : Nat → Bool) (Up : CallTree E₁ R₁ → LstateMF → Prop) (t₁ : CallTree E₁ R₁)
    (pc : Nat) (sA : AState) : Prop :=
  ∃ s sa, Up t₁ s ∧ s.prog.lfn = P.lfn ∧ sa.reg.lpc < body.length ∧ L sa.reg.lpc = false
    ∧ ImgRelF frame slotArr base body (E sa.reg.lpc) s sa ∧ ACorr rsp sA sa
    ∧ pc = pos sa.reg.lpc

/-- **A relation carried by the image gives the simulation cut at the calls of the decoded
    program.** Let the segments `SegTo I T P` of the image have the simulation `SegSimR` at the
    dead names `E`, let no flag be live after a call and each call be followed by a position of
    the body, and let each step `Glue T P` at a call of a symbol `f` be a step of the site
    (`SiteStep`) of `X f` and `c f` at the names `E p` and `E (p + 1)`. Then a relation `Up`
    carried by the image (`ImgUp`) gives the simulation `SegSim` of the source trees by `prog`
    at the invariant `UpInv`. -/
theorem segSim_of_imgUp {c : String → CalleeSig} {L : Nat → Bool}
    (hLc : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → L (p + 1) = false)
    (hcl : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → p + 1 < body.length)
    (hsim : SegSimR frame slotArr base rsp body P.lfn E L prog pos tgt (SegTo I T P) Fin)
    (hStep : ∀ p u v, Glue T P p u v → u.prog.base.reg.lpc = p →
      ∀ bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      SiteStep frame slotArr base rsp body (X f) (c f) (E p) (E (p + 1)) u v)
    {Up : CallTree E₁ R₁ → LstateMF → Prop}
    (hUp : ImgUp h₁ RE RA RR Fail frame slotArr base rsp body E X I T P pos tgt sym rd Fin
      Up) :
    NFProgCallTreeCallsBack.SegSim aMachine prog sym rd h₁ RE RA RR Fail
      (UpInv frame slotArr base rsp body E P pos L Up) := by
  rintro t₁ pc sA ⟨s, sa, hU, hfn, hlen, hL, hI, hA, rfl⟩
  rcases hUp t₁ s hU with ⟨r₁, rfl, hf | ⟨t, hseg, hR⟩⟩ | ⟨e₁, k₁, rfl, hc | hk⟩
  · exact .inl ⟨r₁, rfl, .inl hf⟩
  · obtain ⟨sA', hh, hfin⟩ := hsim.toEnd s sa sA t hfn hlen hL hI hA hseg
    exact .inl ⟨r₁, rfl, .inr ⟨sA', hh, hR sA' hfin⟩⟩
  · obtain ⟨p, u, v, hseg, hglue, hcall⟩ := hc
    obtain ⟨sa1, sA1, hI1, hc1, hpc1, ⟨bi, ra, ⟨f, l⟩, hb, hbi, hprog⟩, hreach⟩ :=
      hsim.toCall s sa sA p u hfn hlen hL hI hA hseg
    obtain ⟨hfu, hpu⟩ : u.prog.lfn = P.lfn ∧ u.prog.base.reg.lpc = p := by
      obtain ⟨_, _, hat, _⟩ := hseg
      exact hat
    have hst := hStep _ _ _ hglue hpu bi ra f l hb hbi
    obtain ⟨hRE, hRA⟩ := hcall bi ra f l hb hbi sa1 sA1 hI1 hc1 hpc1
    refine .inr ⟨e₁, k₁, rfl, .inl ⟨pos p, tgt f, sA1, hreach, hprog, hRE, fun a₁ a₂ ha => ?_⟩⟩
    rcases hRA a₁ a₂ ha with hf | ⟨sc, tr, rfl, hX, hU'⟩
    · exact .inl hf
    refine .inr ?_
    obtain ⟨dst, x, rfl, hres, hsub⟩ := hst
    have hfv : (LprogIsa.retRes dst x u).prog.lfn = P.lfn :=
      (LprogIsa.lfn_retRes dst x u).trans hfu
    obtain ⟨u', zf, hag, hrel⟩ := hI1
    obtain ⟨-, hall⟩ := hres u' hag sa1 zf sA1 hrel hc1
      ⟨bi, ra, (f, l), by rw [hpc1]; exact hb, hbi⟩ (pos p + 1)
    obtain ⟨sa2, hpc2, hA2, w, zf', hag2, hrel2⟩ := hall tr sc hX
    refine ⟨sc, rfl, LprogIsa.retRes dst x u, sa2, hU', hfv, ?_, ?_, ?_, hA2, ?_⟩
    · rw [hpc2, hpc1]; exact hcl _ bi ra _ hb hbi
    · rw [hpc2, hpc1]; exact hLc _ bi ra _ hb hbi
    · rw [hpc2, hpc1]
      exact ⟨w, zf', ((hag.retRes dst x).trans hag2).mono hsub, hrel2⟩
    · rw [hpc2, hpc1, hsim.pos_call _ bi ra _ hb hbi]
  · exact .inr ⟨e₁, k₁, rfl, .inr ⟨s, sa, hk, hfn, hlen, hL, hI, hA, rfl⟩⟩

/-- **A source tree related to an image state at the start of a segment is related by `RuttF` to
    the family of the target trees** from the index of the position of that state and the byte
    state corresponding to it, under the hypotheses of `segSim_of_imgUp`. -/
theorem ruttF_of_imgUp {c : String → CalleeSig} {L : Nat → Bool}
    (hLc : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → L (p + 1) = false)
    (hcl : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → p + 1 < body.length)
    (hsim : SegSimR frame slotArr base rsp body P.lfn E L prog pos tgt (SegTo I T P) Fin)
    (hStep : ∀ p u v, Glue T P p u v → u.prog.base.reg.lpc = p →
      ∀ bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      SiteStep frame slotArr base rsp body (X f) (c f) (E p) (E (p + 1)) u v)
    {Up : CallTree E₁ R₁ → LstateMF → Prop}
    (hUp : ImgUp h₁ RE RA RR Fail frame slotArr base rsp body E X I T P pos tgt sym rd Fin
      Up)
    {t₁ : CallTree E₁ R₁} {s : LstateMF} (hU : Up t₁ s) (hfn : s.prog.lfn = P.lfn)
    {sa : LstateA} {sA : AState} (hlen : sa.reg.lpc < body.length) (hL : L sa.reg.lpc = false)
    (hI : ImgRelF frame slotArr base body (E sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    RuttF h₁ RE RA RR Fail t₁ fun n => targetTree aMachine prog sym rd n (pos sa.reg.lpc) sA :=
  ruttF_of_segSim aMachine prog sym rd h₁ RE RA RR Fail
    (segSim_of_imgUp h₁ RE RA RR Fail frame slotArr base rsp body E X I T P prog pos tgt sym rd
      Fin hLc hcl hsim hStep hUp) t₁ _ sA ⟨s, sa, hU, hfn, hlen, hL, hI, hA, rfl⟩

end Up

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSite
