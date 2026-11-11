/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefCarried
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChecked

/-!
# The reference of a calling body carries the call tree of its program

The relation of the call tree of a program and the entry state of the reference `d.ref` of its
calling body, on the bounds-checked machine
(`NFProgCallTreeRefChecked.tsim_regionRef_checked`), is a relation carried by the cut programs of
`d.ref` (`NFProgCallTreeCallsRef.RefCarried`) at the entries of their cuts
(`NFProgCallTreeRefCarried.refCarried_of_tsim`): the cut checks of `d.ref` hold at every table
that gives each symbol of the callees a summary of its arity, and at the end state the arrays of
the result slots read back the source result at the byte states of the end condition `FinT`.

## Main definitions

* `imgOf`: the image of a calling body at a table of callees.

## Main results

* `refCarried_regionRef`: the relation `RefUpT` is carried by the cut programs of the reference
  of a calling body, and holds of the call tree of its program at the image entry.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBody

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

open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
  (CutSimI CutRun IsSite IsCut IsCutRev PcFree FnStable entryPos segTo_of_cutRun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (goto)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack (callEvent)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSite (ImgUp)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiReg abiBase)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall eventEnv treeAt
  pureReader)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsRef (RefCarried)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked (FinT entryImg)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefCarried (RefUpT refCarried_of_tsim
  noneFail_treeAt)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose (calleeTab_domEqT
  calleeCutB_of_domEq)


/-- The image of a calling body at a table of callees. -/
abbrev imgOf (σ : AbiLayout) (T : CalleeTab) (b : Lcmd) (ps : List (String × String)) :
    List LinstrRM :=
  X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf ps))
    (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf ps)) b) b

/-- **The reference of a calling body carries the call tree of its program.** Under the
    hypotheses of `NFProgCallTreeRefChain.tsim_regionRef` at the register names `exportReg`, let
    each symbol of `T` have a summary in `PT` of its arity, and let `sim` simulate the cut
    programs of `d.ref` by those of its image on the bounds-checked machine with the procedures of
    `PT`. With the end condition `Post` of `tsim_regionRef` and the relation `RR` of a value of
    the program and a byte state that reads back its result, the relation `RefUpT` holds of the call
    tree of the program at the image entry and is carried by the cut programs of `d.ref`, under the
    two conditions at the calls of events of `G`: the summary of `PT` steps at every call site of
    `d.ref` or the source handler `h₁` fails at the event, and at
    every image call related to a call state of `d.ref` the source event and the call event of the
    image are related by `RE`, and every pair of answers that `RA` relates is the failed answer or
    a callee answer of `X` whose source answer the step of the summary writes. -/
theorem refCarried_regionRef {σ : AbiLayout} {fn : String}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) {r0 r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r0) (ht : ∃ w m, t = .stackArr w m)
    {ex : List String} {T : CalleeTab}
    (hw : regionWebs ex r0 (calleeAAT (some T)) (calleeAOT (some T)) = r) {b : Lcmd}
    {cert : List (String × String)}
    (hg : regionCoB σ exportReg b t r.code r.res cert (some T) fn = true) {d : CoParts}
    (hd : regionCoParts σ exportReg b t (calleeCodeT (some T) r.code) r.res cert (some T) = d)
    {G : NFCall jasminDialect → Prop} (hGT : ∀ e, G e → EvOK T e)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) (hG : AllEv G (treeAt pureReader eventEnv fuel p V))
    {PT : LprogIsa.ProcTable}
    (hT' : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length)
    (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (RE : (nfCallSig jasminDialect).Event → (kSig AState).Event → Prop)
    (RA : (e₁ : (nfCallSig jasminDialect).Event) → (e₂ : (kSig AState).Event) →
      (nfCallSig jasminDialect).Resp e₁ → (kSig AState).Resp e₂ → Prop)
    (E : Nat → List String) (X : String → CalleeRun) (pos : Nat → Nat) (tgt : String → Nat)
    (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value)
    {cut' : Option Nat → Option Nat → List LinstrRM}
    (sim : CutSimI X86Backend.CheckedIsaCall.x86IsaK PT d.outs fn d.ref (imgOf σ T b d.ps)
      (LprogCallCut.cutAt fn (freshLabel (d.ref ++ imgOf σ T b d.ps)) d.ref) cut')
    (hglue : ∀ (ev : NFCall jasminDialect) (u : LstateMF) (q : Nat), G ev →
      NFProgCallTreeExport.CallSite (singletonProgM fn d.ref) ev u →
      atPc (singletonProgM fn d.ref) q u →
        (∃ v, Glue PT (singletonProgM fn d.ref) q u v) ∨ h₁ ev = none)
    (hsite : ∀ (ev : NFCall jasminDialect) (u : LstateMF) (p : Nat), G ev →
      NFProgCallTreeExport.CallSite (singletonProgM fn d.ref) ev u →
      atPc (singletonProgM fn d.ref) p u →
      ∀ u' q v', sim.Q (some p) u u' → sim.site (some p) = some q →
      Glue PT (singletonProgM fn (imgOf σ T b d.ps)) q u' v' →
      ∀ bi ra f l, b[q]? = some bi → bi.li_i = .Lcall ra (f, l) →
      ∀ sa₁ sA, ImgRelF (frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
          (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b (E q) (goto u' q) sa₁ →
        ACorr (frameRsp b sa) sA sa₁ → sa₁.reg.lpc = q →
        RE ev (callEvent aMachine sym rd (pos q) (tgt f) sA)
        ∧ ∀ a₁ a₂, RA ev (callEvent aMachine sym rd (pos q) (tgt f) sA) a₁ a₂ →
          a₁ = none ∨ ∃ sc tr, a₂ = some sc
            ∧ X f (X86Backend.ImageCallProbe.entryOf (pos q + 1) sA) tr sc
            ∧ ∀ v, Glue PT (singletonProgM fn d.ref) p u v →
              CallRet (singletonProgM fn d.ref) ev u a₁ v) :
    let Post : Ctxt.Valuation (d := jasminDialect) [t] → LstateMF → Prop := fun v u =>
      (∀ sa' : AState,
        (∀ q A n, slotArrOf σ exportReg q = some (A, n) →
          ∃ arr, u.prog.base.getArr (renOf d.ps A) 64 n = some arr
            ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa A) j) = arr ⟨j, hj⟩) →
        σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
        ∧ u.prog.base.lpc = d.ref.length ∧ u.prog.lfn = fn
    RefCarried h₁ RE RA
        (NFProgCallTreeExt.OutRel fun v sA => σ.ResultOf sa sA (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
        (fun r => r = none) (frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) (frameRsp b sa) b E X pos tgt sym rd
        (FinT σ sa d.ps) sim (RefUpT PT fn d.ref G Post)
      ∧ RefUpT PT fn d.ref G Post (treeAt pureReader eventEnv fuel p V) none
        (entryImg σ b sa d.ps fn) := by
  intro Post
  have hT0 := NFProgCallTreeRefChecked.tsim_regionRef_checked hp hr ht hw hg hd hGT sa V hV hreg
    fuel hG
  -- The checks of the calling body.
  have hg' := hg
  simp only [regionCoB, regionCopy_some_callee, regionOut, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, -⟩, hren⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := hg'
  have hok := calleeBodyBT_spec.mp hcb
  have RF := renB_spec hren
  have hun : ∀ q A n, slotArrOf σ exportReg q = some (A, n) → unren d.ps (renOf d.ps A) = A := by
    intro q A n h
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some h
    exact (RF.unr j (List.getElem?_eq_some_iff.mp hj).1).2
  have hDr := calleeTab_domEqT hT' hok.symsRef
  have hcut := calleeCutB_of_domEq hok.cutRef hDr
  have hPT : ∀ (k : Nat) (dst f : String) (srcs : List LOperand) (tag : MemTag),
      d.ref[k]? = some (LprogIsa.callShadow dst f srcs, tag) → (PT f).isSome = true := by
    intro k dst f srcs tag hk
    have h1 := NFProgCallTreeRefChecked.tab_of_callSymsB hok.symsRef k dst f srcs tag hk
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (by simpa [CalleeTab.tab] using h1)
    obtain ⟨pr, hpr, -⟩ := hT' f c hc
    rw [hpr]
    rfl
  refine ⟨refCarried_of_tsim h₁ RE RA _ _ _ _ b E X pos tgt sym rd _ sim hcut
    (fun i hi => List.mem_append_left _ hi) hPT ?_ hglue hsite, rfl, rfl, trivial,
    Nat.zero_le _, hG, noneFail_treeAt fuel p V, hT0⟩
  intro v u ⟨hP, hpc, hfn⟩
  refine ⟨hfn, le_of_eq hpc.symm, fun t' hO sA hF w hw' => ?_⟩
  obtain rfl := Option.some.inj hw'
  refine ⟨sA, rfl, hP sA fun q A n hq => ?_⟩
  have hq' : slotRen (slotArrOf σ exportReg) (renOf d.ps) q = some (renOf d.ps A, n) := by
    simp only [slotRen, hq, Option.map_some]
  obtain ⟨arr, harr, hrd⟩ := hF q _ n hq'
  refine ⟨arr, ?_, fun j hj => ?_⟩
  · rw [← harr]
    exact getArr_of_larr_eq _ _ (by rw [hO.2.1])
  · rw [← hrd j hj]
    show _ = read64 _ (cellAt (abiBase (abiReg σ) sa (unren d.ps (renOf d.ps A))) j)
    rw [hun q A n hq]

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBody
