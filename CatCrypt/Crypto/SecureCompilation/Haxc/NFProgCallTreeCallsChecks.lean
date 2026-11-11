/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSite
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets

/-!
# The image of a calling body against the target trees, from the checks of the image

The relation by `RuttF` of a source call tree with the family of the target trees of the
decoded program of a calling body of the wide class, from a relation `ImgUp` carried by its
image, under the Boolean checks of the image and the relocated item list of the body: the
statement of `ImageAddrCallW.haltsO_of_linkedChecksS` and of
`ImageAddrCallMeets.haltsO_of_contracts` with a relation of call trees in place of a run under
an oracle. The callees enter through the steps of their call sites only, which relate the image
after a call to every return state the run relation of the kind of the callee admits; no
callee run is chosen and no specification of the callee is needed beyond those steps.

## Main results

* `RuttF.shift`: a relation with a family is a relation with every family that is that family
  after some fuel.
* `ruttF_of_linkedChecksS`: the relation from the checks of the image at the steps of its call
  sites.
* `ruttF_of_contracts`: the relation with the steps of the call sites given by the kinds of
  the called symbols.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsChecks

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)

/-- **A relation with a family is a relation with every family that is that family after some
    fuel.** -/
theorem RuttF.shift {E₁ E₂ : EventSig} {R₁ R₂ : Type} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {t₁ : CallTree E₁ R₁}
    {T₀ T₁ : Nat → CallTree E₂ R₂} (j : Nat) (hT : ∀ m, T₀ (j + m) = T₁ m)
    (h : RuttF h₁ RE RA RR Fail t₁ T₁) : RuttF h₁ RE RA RR Fail t₁ T₀ := by
  induction h generalizing T₀ with
  | ret n hn hR => exact .ret (j + n) (by rw [hT, hn]) hR
  | fail hf => exact .fail hf
  | vis n hn he hk ih => exact .vis (j + n) (fun m => by rw [Nat.add_assoc, hT, hn]) he hk
  | skip hk ih => exact .skip (ih hT)

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

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind CallAt)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsImg
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSite

/-- **The image of a calling body of the wide class against the target trees, from checks.**
    Under the hypotheses of `ImageAddrCallW.haltsO_of_linkedChecksS` without a callee
    specification and an oracle, a source tree related by a relation `Up` carried by the image
    (`ImgUp` at the index `posOf ds` and the target map `K`) to an image state related up to the
    dead names of its position to an address state at a position where `liveW` is false, which
    corresponds to the byte state `sA`, is related by `RuttF` to the family of the target trees
    of `prog` from the index of that position and `sA`. -/
theorem ruttF_of_linkedChecksS {E₁ : EventSig} {R₁ : Type} (h₁ : ∀ e : E₁.Event, E₁.Resp e)
    (RE : E₁.Event → (kSig AState).Event → Prop)
    (RA : (e₁ : E₁.Event) → (e₂ : (kSig AState).Event) → E₁.Resp e₁ →
      (kSig AState).Resp e₂ → Prop)
    (RR : R₁ → Option AState → Prop) (Fail : R₁ → Prop) (sym : Nat → String)
    (rd : String → AState → List _root_.Hax.Value)
    {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {X : String → CalleeRun} {c : String → CalleeSig}
    {G : Nat} {ds : List X86Backend.PhysAbiShape.DShape} (hcls : printedAddrCWB G body = true)
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
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {fn : String} {site : Nat → String × List String} {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr site body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      X86Backend.LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (hStep : ∀ p u v, Glue T (singletonProgM fn (callImg slotArr site body)) p u v →
      u.prog.base.reg.lpc = p → ∀ bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      SiteStep frame slotArr base rsp body (X f) (c f) (D.dead p) (D.dead (p + 1)) u v)
    {Up : CallTree E₁ R₁ → LstateMF → Prop}
    (hUp : ImgUp h₁ RE RA RR Fail frame slotArr base rsp body D.dead X I T
      (singletonProgM fn (callImg slotArr site body)) (X86Backend.DecodePrintedCFG.posOf ds) K
      sym rd Fin Up)
    {t₁ : CallTree E₁ R₁} {s : LstateMF} (hU : Up t₁ s)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    RuttF h₁ RE RA RR Fail t₁ fun n =>
      targetTree aMachine prog sym rd n (X86Backend.DecodePrintedCFG.posOf ds sa.reg.lpc) sA := by
  have hCF := callFacts_of_printedAddrCWB hcls hshapes
  have hB := byteSegR_of_linked hCF
    (X86Backend.LprogBytesLinkReloc.linkedProg_of_itemsMapL symBase hCF.toLinkFacts tgtI K hK
      prog hP) rsp hfr
  have hsim := segSimR_of_segExactR hD (fun _ h => (liveW_false_spec h).1) hbits
    (segExactR_callImg hsep hphys hgate hsites hcond hB hI site T fn) hB.halt hfin hFin
  exact ruttF_of_imgUp h₁ RE RA RR Fail frame slotArr base rsp body D.dead X I T
    (singletonProgM fn (callImg slotArr site body)) prog (X86Backend.DecodePrintedCFG.posOf ds) K
    sym rd Fin (fun _ _ _ _ hb hbi => liveW_succ_call hflags hCF.carry hb hbi)
    (lt_of_call_imgGateCBW hgate) hsim hStep hUp hU hfn hlen hL hI0 hA

/-- **The image of a calling body against the target trees, with callees of several kinds.**
    `ruttF_of_linkedChecksS` with the step of each call site given by the kind `kind f` of the
    symbol `f` of the call (`CalleeKind.siteStep`), under the hypotheses of
    `ImageAddrCallMeets.haltsO_of_contracts` without an oracle: the run relation of each called
    symbol meets the specification of its kind and the hypotheses of its calls at its kind, the
    caller is separated at the frame bound `G`, the dead names pass `callDeadSymB` at the
    interfaces and the result kinds, and the shadow instruction at each position `p` has the
    summary `pr p` of the kind of the symbol of the call at `p`. -/
theorem ruttF_of_contracts {E₁ : EventSig} {R₁ : Type} (h₁ : ∀ e : E₁.Event, E₁.Resp e)
    (RE : E₁.Event → (kSig AState).Event → Prop)
    (RA : (e₁ : E₁.Event) → (e₂ : (kSig AState).Event) → E₁.Resp e₁ →
      (kSig AState).Resp e₂ → Prop)
    (RR : R₁ → Option AState → Prop) (Fail : R₁ → Prop) (sym : Nat → String)
    (rd : String → AState → List _root_.Hax.Value)
    {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {kind : String → CalleeKind} {X : String → CalleeRun}
    (hXk : ∀ f, CalledIn body f → (kind f).Spec (X f)) {G : Nat}
    (hS : CallerSep frame slotArr base rsp G) {site : Nat → String × List String}
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
    (hpr : ∀ p f, CallAt body f p → pr p = (kind f).summary)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr site body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      X86Backend.LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    {Up : CallTree E₁ R₁ → LstateMF → Prop}
    (hUp : ImgUp h₁ RE RA RR Fail frame slotArr base rsp body D.dead X I T
      (singletonProgM fn (callImg slotArr site body)) (X86Backend.DecodePrintedCFG.posOf ds) K
      sym rd Fin Up)
    {t₁ : CallTree E₁ R₁} {s : LstateMF} (hU : Up t₁ s)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    RuttF h₁ RE RA RR Fail t₁ fun n =>
      targetTree aMachine prog sym rd n (X86Backend.DecodePrintedCFG.posOf ds sa.reg.lpc) sA :=
  ruttF_of_linkedChecksS h₁ RE RA RR Fail sym rd hsep hphys hgate hsites
    (c := fun f => (kind f).sig) hcls hshapes hfr symBase tgtI K hK hP hbits hflags hcond hI hD
    hfin hFin
    (fun p _ _ hg hpc bi ra f l hb hbi =>
      CalleeKind.siteStep hsep hphys (hXk f ⟨p, bi, ra, l, hb, hbi⟩) hS
        (hOk f ⟨p, bi, ra, l, hb, hbi⟩) ⟨bi, ra, l, hb, hbi⟩
        (callDeadSymB_spec hdead hb hbi).1 (callDeadSymB_spec hdead hb hbi).2 hsit
        (hpr p f ⟨bi, ra, l, hb, hbi⟩) hpc hg)
    hUp hU hfn hlen hL hI0 hA

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsChecks
