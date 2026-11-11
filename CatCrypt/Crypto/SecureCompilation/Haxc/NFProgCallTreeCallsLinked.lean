/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsChecks
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsRef
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkRoute

/-!
# The calling body of the back half against the target trees

The back half compiles a program with `call`s at a table `T` of linked functions to a printed
calling body `b`, whose image `ImageAddrCall.callImg` at the slot map of the layout is checked
against the reference of the region export (`regionCoB`). From the checks of the gate and the
bytes of the calling body alone, without a run of the source, the relation of the image with
the decoded program of the calling body holds at the target trees
(`NFProgCallTreeCallsChecks.ruttF_of_contracts`): every source call tree related to the entry
state of the image by a relation carried by the image (`ImgUp`) is related by `RuttF` to the
family of the target trees of the caller program from index `0` and the entry state. This is the
part of `RegionLinkCall.regionBack_correct_linked_multi` after the image run, with the calls of
the image cut at their sites.

With the simulation of the cut programs of the reference of the calling body by those of its
image (`NFProgCallTreeCallsRef`), a relation carried by the cut programs of the reference gives
the same conclusion.

## Main definitions

* `FinT`, `entryImg`: the end condition of a run of the image of a calling body and the entry
  state of the image.

## Main results

* `ruttF_calleeBody`: the relation of the calling body of the back half with the target trees
  of its caller program, at every relation carried by its image.
* `cuts_of_calleeCutB`: the cut programs of a body that passes `calleeCutB` are cuts that halt
  only at their exits.
* `ruttF_calleeBody_ref`: the same relation at every relation carried by the cut programs of the
  reference, under every simulation of the cut programs of the reference by those of the image.
* `contractRun`, `sContract_contractRun`: the run relation of a contract, which admits every
  return state the contract admits, meets the contract when some run relation does.
* `contractRun_of_contractRAC`: an answer of the separation contracts at a defined meaning is a
  return state of the run relation of the contract.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (reloadOf accArr dstHitB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotRen slotArrOf
  slotArrOf_some)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody cellMove
  cellBody_getElem?)


open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (ProcTable ProcSummary)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (HaltsC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiReg abiBase)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (keepCheckB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee (wordSummary wordSig)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (NFCT)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel (regionPre)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind CallAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArrChain (InsLayout insSummary
  insSummary_retWord)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee (WordLayout OutLayout outSig
  outSummary ParamAt readIns readIns_entry)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (WordCallee FootBelow CallerSep
  exemptC)
open CatCrypt.Crypto.SecureCompilation.SepLogic (SContract)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall (guarded)

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSite (ImgUp)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsChecks (ruttF_of_contracts RuttF.shift)

/-- The end of a run of the image of a calling body: the words of the arrays of the renamed slot
    map at their bases are the arrays of the image state. -/
def FinT (σ : AbiLayout) (sa : AState) (ps : List (String × String)) (t : LstateMF)
    (sA : AState) : Prop :=
  ∀ q A n, slotRen (slotArrOf σ exportReg) (renOf ps) q = some (A, n) →
    ∃ arr, t.prog.base.getArr A 64 n = some arr
      ∧ ∀ j (hj : j < n), read64 sA.mem
        (cellAt (X86Backend.ImageAddrRouteW.baseR σ sa ps A) j) = arr ⟨j, hj⟩

/-- The entry state of the image of a calling body: the entry state `entryV` of the layout at
    the frame of the body and the renaming `ps`, in the function `fn`. -/
def entryImg (σ : AbiLayout) (b : Lcmd) (sa : AState) (ps : List (String × String))
    (fn : String) : LstateMF :=
  ⟨⟨X86Backend.ImageAddrRoute.entryV σ (X86Backend.ImageAddrRoute.frameE b sa) sa
      (X86Backend.ImageAddrRoute.unren ps), fn⟩, false⟩

/-- **The calling body of the back half against the target trees.** Let the printed calling body
    `b` have the bytes `bytes` at the table `T` and pass, with the webbed export `r` and the
    certificate `cert`, the gate `regionCoB` at `T` and the function name `a.fname`, with the parts
    `d`. Let each function `c` of `T` have a kind `kind c.name` whose top hypotheses it meets and
    whose specification the run relation `X c.name` meets, and let the procedure table `PT` give
    the symbol of each function of `T` the summary of its kind. From every entry state `sa` satisfying `σ.Regions`, the
    calling body has a caller program `pc` and shapes `ds` such that every source call tree
    related, by a relation `Up` carried by the image of `b` (`ImgUp` at the dead names of the image,
    the run relations `X`, the checked x86 instruction set with the procedures of `PT`, the index
    `posOf ds`, the call targets of `T` after `pc` and the end `FinT`), to the entry state of the
    image is related by `RuttF` to the family of the target trees of `pc` from index `0` and
    `sa`. -/
theorem ruttF_calleeBody {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
    {bytes : List (BitVec 8)} {w m : Nat} {r : Exported} {cert : List (String × String)}
    (hbs : calleeBytes (some T) b = some bytes)
    (hg : regionCoB σ exportReg b (.stackArr w m) r.code r.res cert (some T) a.fname = true)
    {d : CoParts}
    (hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCodeT (some T) r.code) r.res cert
      (some T) = d)
    (kind : String → CalleeKind) (X : String → CalleeRun)
    (hK : ∀ c ∈ T.fns, (kind c.name).Top c ∧ (kind c.name).Spec (X c.name))
    {PT : ProcTable} (hTc : ∀ c ∈ T.fns, PT c.name = some (kind c.name).summary)
    (sa : AState) (hreg : σ.Regions sa) :
    ∃ (pc : List RInstr) (ds : List X86Backend.PhysAbiShape.DShape),
      calleeProg T b = some pc
      ∧ X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
      ∧ ∀ {E₁ : EventSig} {R₁ : Type} (h₁ : ∀ e : E₁.Event, E₁.Resp e)
        (RE : E₁.Event → (kSig AState).Event → Prop)
        (RA : (e₁ : E₁.Event) → (e₂ : (kSig AState).Event) → E₁.Resp e₁ →
          (kSig AState).Resp e₂ → Prop)
        (RR : R₁ → Option AState → Prop) (Fail : R₁ → Prop) (sym : Nat → String)
        (rd : String → AState → List _root_.Hax.Value) (Up : CallTree E₁ R₁ → LstateMF → Prop),
        ImgUp h₁ RE RA RR Fail (X86Backend.ImageAddrRoute.frameE b sa)
          (slotRen (slotArrOf σ exportReg) (renOf d.ps))
          (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) (X86Backend.DecodePrintedCFG.frameRsp b sa)
          b (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg)
            (renOf d.ps)) (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b)
            d.outs).dead X X86Backend.CheckedIsaCall.x86IsaK PT
          (singletonProgM a.fname (X86Backend.ImageAddrCall.callImg
            (slotRen (slotArrOf σ exportReg) (renOf d.ps))
            (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b))
          (X86Backend.DecodePrintedCFG.posOf ds) (fun f => pc.length + T.entryIdx (T.symPos f))
          sym rd (FinT σ sa d.ps) Up →
        ∀ t₁, Up t₁ (entryImg σ b sa d.ps a.fname) →
        RuttF h₁ RE RA RR Fail t₁ fun n => targetTree aMachine pc sym rd n 0 sa := by
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
  have hpr : ∀ q f, X86Backend.ImageAddrCallMeets.CallAt b f q →
      (kind ((callSymAt b q).getD "")).summary = (kind f).summary := by
    rintro q f ⟨bi, ra, l, hb, hbi⟩
    simp only [callSymAt_eq_some.mpr ⟨bi, ra, l, hb, hbi⟩, Option.getD_some]
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
  refine ⟨prog, ds, hprog, hss, fun h₁ RE RA RR Fail sym rd Up hUp t₁ hU => ?_⟩
  have hR := ruttF_of_contracts h₁ RE RA RR Fail sym rd hsep hphys hgateW hsites
    (kind := kind) (X := X)
    (fun f ⟨_, bi, ra, l, hb, hbi⟩ => by
      obtain ⟨c, hc⟩ := hcall hb hbi
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
      exact (hK c hcm).2)
    hS hOk hcls hss (fun q hq => X86Backend.ImageAddrFrame.frameIn_eq q hq) (calleeSym T b) _
    (fun f => prog.length + T.entryIdx (T.symPos f))
    (fun it f j t _ hs ht => by
      simp only [X86Backend.LprogBytesLinkReloc.symTgt, hs, Option.bind_some,
        CalleeTab.linkMap, Option.some.injEq, Prod.mk.injEq] at ht
      rw [← ht.1, hlenP])
    hP hbits hdead' hflags hcond hsit hpr X86Backend.CheckedIsaCall.x86IsaK_checked
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
  exact RuttF.shift j hj hR

open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsRef (RefCarried RefImgUp
  imgUp_of_refCarried)

/-- **The cut programs of a body that passes `calleeCutB` are cuts that halt only at their
    exits**, at the label `freshLabel A` of a list `A` holding every instruction of the body. -/
theorem cuts_of_calleeCutB {PT : ProcTable} {fn : String} {A B : List JasminLsemMem.LinstrRM}
    (h : calleeCutB PT (freshLabel A) B = true) (hsub : ∀ i ∈ B, i ∈ A) :
    ∀ e x, LprogCallCut.IsSite PT B e → LprogCallCut.IsSite PT B x →
      LprogCallCut.IsCut PT fn B e x (LprogCallCut.cutAt fn (freshLabel A) B e x)
          (LprogCallCut.cutPos B e)
        ∧ LprogCallCut.IsCutRev PT B x (LprogCallCut.cutAt fn (freshLabel A) B e x)
          (LprogCallCut.cutPos B e) := by
  intro e x he hx
  simp only [calleeCutB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hok, hrev⟩ := h
  have hB := LprogCallCut.jumpLabel_ne_of_isCutRev
    (LprogCallCut.isCutRev_of_isCutRevB (hrev none List.mem_cons_self none List.mem_cons_self))
    (findLabelMem_freshLabel hsub)
  exact ⟨LprogCallCut.isCut_cutAt_of_cutOkB hok hB fn he hx,
    LprogCallCut.isCutRev_cutAt_rename hB
      (hrev e (LprogCallCut.mem_of_isSite he) x (LprogCallCut.mem_of_isSite hx))⟩

/-- **The calling body of the back half against the target trees, from its reference.** Under
    the hypotheses of `ruttF_calleeBody`, at every simulation `sim` of the cut programs of the
    reference `d.ref` of the calling body by those of its image, on the checked x86 instruction
    set with the procedures of `PT`, at the label `freshLabel` of both: every source call tree
    related to the entry state of the reference by a relation carried by the cut programs of the
    reference (`RefCarried`) is related by `RuttF` to the family of the target trees of the
    caller program from index `0` and `sa`. -/
theorem ruttF_calleeBody_ref {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
    {bytes : List (BitVec 8)} {w m : Nat} {r : Exported} {cert : List (String × String)}
    (hbs : calleeBytes (some T) b = some bytes)
    (hg : regionCoB σ exportReg b (.stackArr w m) r.code r.res cert (some T) a.fname = true)
    {d : CoParts}
    (hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCodeT (some T) r.code) r.res cert
      (some T) = d)
    (kind : String → CalleeKind) (X : String → CalleeRun)
    (hK : ∀ c ∈ T.fns, (kind c.name).Top c ∧ (kind c.name).Spec (X c.name))
    {PT : ProcTable} (hTc : ∀ c ∈ T.fns, PT c.name = some (kind c.name).summary)
    (sa : AState) (hreg : σ.Regions sa) :
    ∃ (pc : List RInstr) (ds : List X86Backend.PhysAbiShape.DShape),
      calleeProg T b = some pc
      ∧ X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
      ∧ ∀ {E₁ : EventSig} {R₁ : Type} (h₁ : ∀ e : E₁.Event, E₁.Resp e)
        (RE : E₁.Event → (kSig AState).Event → Prop)
        (RA : (e₁ : E₁.Event) → (e₂ : (kSig AState).Event) → E₁.Resp e₁ →
          (kSig AState).Resp e₂ → Prop)
        (RR : R₁ → Option AState → Prop) (Fail : R₁ → Prop) (sym : Nat → String)
        (rd : String → AState → List _root_.Hax.Value)
        (sim : LprogCallCut.CutSimI X86Backend.CheckedIsaCall.x86IsaK PT d.outs a.fname d.ref
          (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
            (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b)
          (LprogCallCut.cutAt a.fname (freshLabel (d.ref ++
            X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
              (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b)) d.ref)
          (LprogCallCut.cutAt a.fname (freshLabel (d.ref ++
            X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
              (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b))
            (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
              (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b)))
        (RefUp : CallTree E₁ R₁ → Option Nat → LstateMF → Prop),
        RefCarried h₁ RE RA RR Fail (X86Backend.ImageAddrRoute.frameE b sa)
          (slotRen (slotArrOf σ exportReg) (renOf d.ps))
          (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) (X86Backend.DecodePrintedCFG.frameRsp b sa)
          b (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg)
            (renOf d.ps)) (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b)
            d.outs).dead X (X86Backend.DecodePrintedCFG.posOf ds)
          (fun f => pc.length + T.entryIdx (T.symPos f)) sym rd (FinT σ sa d.ps) sim RefUp →
        ∀ t₁, RefUp t₁ none (entryImg σ b sa d.ps a.fname) →
        RuttF h₁ RE RA RR Fail t₁ fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨pc, ds, hpc, hds, hR⟩ := ruttF_calleeBody hbs hg hd kind X hK hTc sa hreg
  refine ⟨pc, ds, hpc, hds, fun h₁ RE RA RR Fail sym rd sim RefUp hC t₁ hU => ?_⟩
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
  refine hR h₁ RE RA RR Fail sym rd (RefImgUp sim RefUp)
    (imgUp_of_refCarried h₁ RE RA RR Fail _ _ _ _ b _ X _ _ sym rd _ sim
      X86Backend.CheckedIsaCall.x86IsaK_pcFree (X86Backend.CheckedIsaCall.x86IsaK_refusesProcs PT)
      X86Backend.CheckedIsaCall.fnStable_x86IsaK hcut' hC) t₁
    ⟨none, _, _, hU, sim.init _, rfl, trivial, by rw [sim.site_none]; trivial, ?_⟩
  rw [sim.site_none]
  rfl

/-! ## The run relation of a contract -/

section ContractRun

open CatCrypt.Crypto.SecureCompilation.SepLogic

variable {σ' : Type} {L : Type} [Footprinted σ' L] {Tr : Type} {α : Type}

/-- **The run relation of a contract**: the runs with the trace `tr₀` from a state to a state that
    satisfies the postcondition and keeps the locations outside the write set at every logical
    variable whose precondition holds at the entry state. -/
def contractRun (C : ContractSpec σ' L α) (tr₀ : Tr) (s : σ') (tr : Tr) (s' : σ') : Prop :=
  tr = tr₀ ∧ ∀ a, (C.pre a).holds s →
    (C.post a).holds s' ∧ Footprinted.AgreeOn (C.writes a s)ᶜ s s'

/-- **A contract met by some run relation is met by its run relation.** -/
theorem sContract_contractRun {C : ContractSpec σ' L α} {Y : σ' → Tr → σ' → Prop}
    (hY : SContract Y C) (tr₀ : Tr) : SContract (contractRun C tr₀) C where
  halts a s hs := by
    obtain ⟨t, s', hr⟩ := hY.halts a s hs
    exact ⟨tr₀, s', rfl, fun b hb => ⟨hY.post b s t s' hb hr, hY.keep b s t s' hb hr⟩⟩
  post a s t s' hs hr := (hr.2 a hs).1
  keep a s t s' hs hr := (hr.2 a hs).2
  ct _ _ _ _ t₁ t₂ _ _ _ _ _ h₁ h₂ := h₁.1.trans h₂.1.symm

/-- **An answer of the separation contracts at a defined meaning is a run of the contract.** At
    an answer related by `contractRAC` whose source answer is a value, the target answer is a
    return state of the run relation of the contract of the linked function from the entry state
    of the call, at every trace. -/
theorem contractRun_of_contractRAC {m : CatCrypt.Crypto.Hax.HaxModule} {e₁ : linkSig.Event}
    {e₂ : (kSig AState).Event} {a₁ : linkSig.Resp e₁} {a₂ : (kSig AState).Resp e₂}
    {l : CatCrypt.Crypto.Hax.LinkedFn}
    (hl : m.linked.find? (·.name == LinkCall.name e₁) = some l)
    (h : RegionLinkContract.contractRAC m e₁ e₂ a₁ a₂) {v : _root_.Hax.Value}
    (hv : (a₁ : Option _root_.Hax.Value) = some v) {Tr : Type} (tr₀ : Tr) :
    ∃ s', (a₂ : Option AState) = some s'
      ∧ contractRun l.contract tr₀ (KCall.entry e₂) tr₀ s' := by
  obtain ⟨l', hl', -, hall⟩ := h
  rw [hl] at hl'
  obtain rfl := Option.some.inj hl'
  obtain ⟨s', hs', -, -, hc⟩ := hall v hv
  exact ⟨s', hs', rfl, hc⟩

end ContractRun

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked
