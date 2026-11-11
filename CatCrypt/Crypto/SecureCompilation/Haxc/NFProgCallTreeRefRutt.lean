/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBody
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont

/-!
# The calling body against the target trees, from its call tree

The calling body of the back half is related to the target trees of its caller program at every
relation carried by the cut programs of its reference
(`NFProgCallTreeCallsLinked.ruttF_calleeBody_ref`). The call tree of its program is one, at the
image entry (`NFProgCallTreeRefBody.refCarried_regionRef`), under the conditions at the calls of
the image. The call tree is then related by `RuttF` to the target trees, at the relation of a value
and a byte state that reads back its result. The tree `mfTree`, which answers the inner heads inside
the tree, is the call tree with call events for a program that calls no inner head.

## Main results

* `mfTree_eq_treeAt`: the tree `mfTree` of a program whose calls name no inner head is its call
  tree with call events.
* `ruttF_regionRef`, `ruttF_regionRef_mfTree`: the call tree and the tree `mfTree` of the program of
  a calling body against the target trees of its caller program.
* `ruttF_regionRef_seg`: the same at the simulation of the segment check of the gate, where the
  image state at a call agrees with the call state of the reference on the operands and the names
  live into the site, the arrays and the memory.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefRutt

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall eventEnv treeAt
  pureReader)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree mfEnv innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (callsToAny)

/-- **The tree `mfTree` of a program whose calls name no inner head is its call tree with call
    events.** -/
theorem mfTree_eq_treeAt {fs : List String} (hfs : ∀ f ∈ fs, innerHead f = false) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (h : callsToAny fs p = true) :
    ∀ V : Ctxt.Valuation Γ, mfTree fuel p V = treeAt pureReader eventEnv fuel p V := by
  induction p with
  | ret vs => intro V; rfl
  | var e k ih =>
      intro V
      show NFProgCallTree.obind _ _ = NFProgCallTree.obind _ _
      congr 1
      funext x
      exact ih h _
  | forLoop count inits body k ihb ihk =>
      intro V
      simp only [callsToAny, Bool.and_eq_true] at h
      show NFProgCallTree.obind (NFProgCallTree.ofoldl _ _ _) _
        = NFProgCallTree.obind (NFProgCallTree.ofoldl _ _ _) _
      congr 2
      · funext acc i
        exact ihb h.1 _
      · funext acc
        exact ihk h.2 _
  | ifThenElse cond thn els k iht ihe ihk =>
      intro V
      simp only [callsToAny, Bool.and_eq_true] at h
      show NFProgCallTree.obind _ _ = NFProgCallTree.obind _ _
      congr 1
      · split
        · exact iht h.1.1 V
        · exact ihe h.1.2 V
      · funext r
        exact ihk h.2 _
  | whileLoop inits body k ihb ihk =>
      intro V
      simp only [callsToAny, Bool.and_eq_true] at h
      show NFProgCallTree.obind (NFProgCallTree.owhileIter _ _ _) _
        = NFProgCallTree.obind (NFProgCallTree.owhileIter _ _ _) _
      congr 2
      · funext acc
        exact ihb h.1 _
      · funext acc
        exact ihk h.2 _
  | call f args k ih =>
      intro V
      simp only [callsToAny, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
      show NFProgCallTree.obind (mfEnv.call _ _ _ _) _
        = NFProgCallTree.obind (eventEnv.call _ _ _ _) _
      congr 1
      · simp only [mfEnv, hfs f h.1, Bool.false_eq_true, ite_false]
        rfl
      · funext r
        exact ih h.2 _


section Rutt

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (CutSimI Glue)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (ImgRelF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (atPc goto)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack (callEvent)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBody (imgOf refCarried_regionRef)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked (ruttF_calleeBody_ref)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)

/-- **The calling body against the target trees, from the call tree of its program.** Under the
    hypotheses of `NFProgCallTreeCallsLinked.ruttF_calleeBody` and of
    `NFProgCallTreeRefChain.tsim_regionRef`, the caller program `pc` and the shapes `ds` exist, and
    at every simulation `sim` of the cut programs of `d.ref` by those of its image, every call tree
    with call events of the program is related by `RuttF` at `RE`, `RA`, the relation `OutRel` of
    a value and a byte state that reads back its result, and the failed leaf, to the family of the
    target trees of `pc` from `sa`, under the two conditions at the calls of
    `NFProgCallTreeRefBody.refCarried_regionRef`. -/
theorem ruttF_regionRef {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
    {bytes : List (BitVec 8)} {w m : Nat} {r : Exported} {cert : List (String × String)}
    (hbs : calleeBytes (some T) b = some bytes)
    (hg : regionCoB σ exportReg b (.stackArr w m) r.code r.res cert (some T) a.fname = true)
    {d : CoParts}
    (hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCodeT (some T) r.code) r.res cert
      (some T) = d)
    (kind : String → CalleeKind) (X : String → CalleeRun)
    (hK : ∀ c ∈ T.fns, (kind c.name).Top c ∧ (kind c.name).Spec (X c.name))
    {PT : LprogIsa.ProcTable} (hTc : ∀ c ∈ T.fns, PT c.name = some (kind c.name).summary)
    (sa : AState) (hreg : σ.Regions sa)
    {Γ : Ctxt jasminDialect} {p : NFProg jasminDialect Γ [.stackArr w m]}
    (hp : RegionExportable p) {r0 : Exported}
    (hr : exportR Γ.length a.fname p Γ.length 0 = some r0) {ex : List String}
    (hw : regionWebs ex r0 (calleeAAT (some T)) (calleeAOT (some T)) = r)
    {G : NFCall jasminDialect → Prop} (hGT : ∀ e, G e → EvOK T e)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (fuel : Nat)
    (hG : AllEv G (treeAt pureReader eventEnv fuel p V)) :
    ∃ (pc : List RInstr) (ds : List X86Backend.PhysAbiShape.DShape),
      calleeProg T b = some pc
      ∧ X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
      ∧ ∀ (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
        (RE : (nfCallSig jasminDialect).Event → (kSig AState).Event → Prop)
        (RA : (e₁ : (nfCallSig jasminDialect).Event) → (e₂ : (kSig AState).Event) →
          (nfCallSig jasminDialect).Resp e₁ → (kSig AState).Resp e₂ → Prop)
        (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value)
        (sim : CutSimI X86Backend.CheckedIsaCall.x86IsaK PT d.outs a.fname d.ref
          (imgOf σ T b d.ps)
          (LprogCallCut.cutAt a.fname (freshLabel (d.ref ++ imgOf σ T b d.ps)) d.ref)
          (LprogCallCut.cutAt a.fname (freshLabel (d.ref ++ imgOf σ T b d.ps))
            (imgOf σ T b d.ps))),
        (∀ (ev : NFCall jasminDialect) (u : LstateMF) (q : Nat), G ev →
          NFProgCallTreeExport.CallSite (singletonProgM a.fname d.ref) ev u →
          atPc (singletonProgM a.fname d.ref) q u →
          (∃ v, Glue PT (singletonProgM a.fname d.ref) q u v) ∨ h₁ ev = none) →
        (∀ (ev : NFCall jasminDialect) (u : LstateMF) (p : Nat), G ev →
          NFProgCallTreeExport.CallSite (singletonProgM a.fname d.ref) ev u →
          atPc (singletonProgM a.fname d.ref) p u →
          ∀ u' q v', sim.Q (some p) u u' → sim.site (some p) = some q →
          Glue PT (singletonProgM a.fname (imgOf σ T b d.ps)) q u' v' →
          ∀ bi ra f l, b[q]? = some bi → bi.li_i = .Lcall ra (f, l) →
          ∀ sa₁ sA, ImgRelF (frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
              (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b
              ((deadTab (imgOf σ T b d.ps) d.outs).dead q) (goto u' q) sa₁ →
            ACorr (X86Backend.DecodePrintedCFG.frameRsp b sa) sA sa₁ → sa₁.reg.lpc = q →
            RE ev (callEvent aMachine sym rd (X86Backend.DecodePrintedCFG.posOf ds q)
              (pc.length + T.entryIdx (T.symPos f)) sA)
            ∧ ∀ a₁ a₂, RA ev (callEvent aMachine sym rd (X86Backend.DecodePrintedCFG.posOf ds q)
                (pc.length + T.entryIdx (T.symPos f)) sA) a₁ a₂ →
              a₁ = none ∨ ∃ sc tr, a₂ = some sc
                ∧ X f (X86Backend.ImageCallProbe.entryOf
                  (X86Backend.DecodePrintedCFG.posOf ds q + 1) sA) tr sc
                ∧ ∀ v, Glue PT (singletonProgM a.fname d.ref) p u v →
                  CallRet (singletonProgM a.fname d.ref) ev u a₁ v) →
        RuttF h₁ RE RA (NFProgCallTreeExt.OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (.stackArr w m)
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m)
                .here v)))
          (fun o => o = none) (treeAt pureReader eventEnv fuel p V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨pc, ds, hpc, hds, hR⟩ := ruttF_calleeBody_ref hbs hg hd kind X hK hTc sa hreg
  refine ⟨pc, ds, hpc, hds, fun h₁ RE RA sym rd sim hglue hsite => ?_⟩
  have hT' : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length := by
    intro f c hc
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    obtain ⟨har, -⟩ := (hK c hcm).1.facts
    exact ⟨_, hTc c hcm, har⟩
  obtain ⟨hC, hU⟩ := refCarried_regionRef hp hr ⟨w, m, rfl⟩ hw hg hd hGT sa V hV hreg fuel hG hT'
    h₁ RE RA _ X _ _ sym rd sim hglue hsite
  exact hR h₁ RE RA _ _ sym rd sim _ hC _ hU

/-- **The calling body against the target trees, from the tree `mfTree` of its program.** As
    `ruttF_regionRef`, for a program whose calls name symbols of the table of callees, none of
    which is an inner head: its tree `mfTree` is its call tree with call events
    (`mfTree_eq_treeAt`). -/
theorem ruttF_regionRef_mfTree {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
    {bytes : List (BitVec 8)} {w m : Nat} {r : Exported} {cert : List (String × String)}
    (hbs : calleeBytes (some T) b = some bytes)
    (hg : regionCoB σ exportReg b (.stackArr w m) r.code r.res cert (some T) a.fname = true)
    {d : CoParts}
    (hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCodeT (some T) r.code) r.res cert
      (some T) = d)
    (kind : String → CalleeKind) (X : String → CalleeRun)
    (hK : ∀ c ∈ T.fns, (kind c.name).Top c ∧ (kind c.name).Spec (X c.name))
    {PT : LprogIsa.ProcTable} (hTc : ∀ c ∈ T.fns, PT c.name = some (kind c.name).summary)
    (sa : AState) (hreg : σ.Regions sa)
    {Γ : Ctxt jasminDialect} {p : NFProg jasminDialect Γ [.stackArr w m]}
    (hp : RegionExportable p) {r0 : Exported}
    (hr : exportR Γ.length a.fname p Γ.length 0 = some r0) {ex : List String}
    (hw : regionWebs ex r0 (calleeAAT (some T)) (calleeAOT (some T)) = r)
    {G : NFCall jasminDialect → Prop} (hGT : ∀ e, G e → EvOK T e)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (fuel : Nat)
    (hG : AllEv G (treeAt pureReader eventEnv fuel p V))
    (hin : ∀ f ∈ T.names, innerHead f = false) (hcalls : callsToAny T.names p = true) :
    ∃ (pc : List RInstr) (ds : List X86Backend.PhysAbiShape.DShape),
      calleeProg T b = some pc
      ∧ X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
      ∧ ∀ (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
        (RE : (nfCallSig jasminDialect).Event → (kSig AState).Event → Prop)
        (RA : (e₁ : (nfCallSig jasminDialect).Event) → (e₂ : (kSig AState).Event) →
          (nfCallSig jasminDialect).Resp e₁ → (kSig AState).Resp e₂ → Prop)
        (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value)
        (sim : CutSimI X86Backend.CheckedIsaCall.x86IsaK PT d.outs a.fname d.ref
          (imgOf σ T b d.ps)
          (LprogCallCut.cutAt a.fname (freshLabel (d.ref ++ imgOf σ T b d.ps)) d.ref)
          (LprogCallCut.cutAt a.fname (freshLabel (d.ref ++ imgOf σ T b d.ps))
            (imgOf σ T b d.ps))),
        (∀ (ev : NFCall jasminDialect) (u : LstateMF) (q : Nat), G ev →
          NFProgCallTreeExport.CallSite (singletonProgM a.fname d.ref) ev u →
          atPc (singletonProgM a.fname d.ref) q u →
          (∃ v, Glue PT (singletonProgM a.fname d.ref) q u v) ∨ h₁ ev = none) →
        (∀ (ev : NFCall jasminDialect) (u : LstateMF) (p : Nat), G ev →
          NFProgCallTreeExport.CallSite (singletonProgM a.fname d.ref) ev u →
          atPc (singletonProgM a.fname d.ref) p u →
          ∀ u' q v', sim.Q (some p) u u' → sim.site (some p) = some q →
          Glue PT (singletonProgM a.fname (imgOf σ T b d.ps)) q u' v' →
          ∀ bi ra f l, b[q]? = some bi → bi.li_i = .Lcall ra (f, l) →
          ∀ sa₁ sA, ImgRelF (frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
              (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b
              ((deadTab (imgOf σ T b d.ps) d.outs).dead q) (goto u' q) sa₁ →
            ACorr (X86Backend.DecodePrintedCFG.frameRsp b sa) sA sa₁ → sa₁.reg.lpc = q →
            RE ev (callEvent aMachine sym rd (X86Backend.DecodePrintedCFG.posOf ds q)
              (pc.length + T.entryIdx (T.symPos f)) sA)
            ∧ ∀ a₁ a₂, RA ev (callEvent aMachine sym rd (X86Backend.DecodePrintedCFG.posOf ds q)
                (pc.length + T.entryIdx (T.symPos f)) sA) a₁ a₂ →
              a₁ = none ∨ ∃ sc tr, a₂ = some sc
                ∧ X f (X86Backend.ImageCallProbe.entryOf
                  (X86Backend.DecodePrintedCFG.posOf ds q + 1) sA) tr sc
                ∧ ∀ v, Glue PT (singletonProgM a.fname d.ref) p u v →
                  CallRet (singletonProgM a.fname d.ref) ev u a₁ v) →
        RuttF h₁ RE RA (NFProgCallTreeExt.OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (.stackArr w m)
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m)
                .here v)))
          (fun o => o = none) (mfTree fuel p V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  rw [mfTree_eq_treeAt hin fuel p hcalls V]
  exact ruttF_regionRef hbs hg hd kind X hK hTc sa hreg hp hr hw hGT V hV fuel hG

end Rutt


section Seg

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (CutSimI Glue)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (ImgRelF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck (segOutsAt siteMap
  segSim_of_checks)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (atPc goto)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack (callEvent)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBody (imgOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)

/-- **The calling body against the target trees, at the simulation of the segment check.** As
    `ruttF_regionRef`, at the simulation `CalleeSegCheck.segSim_of_checks` of the segment check
    of the gate carried to `PT`: at a call of `d.ref` at `p`, the image state at the
    corresponding site agrees with the call state on the registers of the operands and the
    names live into the site, the arrays and the memory. -/
theorem ruttF_regionRef_seg {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
    {bytes : List (BitVec 8)} {w m : Nat} {r : Exported} {cert : List (String × String)}
    (hbs : calleeBytes (some T) b = some bytes)
    (hg : regionCoB σ exportReg b (.stackArr w m) r.code r.res cert (some T) a.fname = true)
    {d : CoParts}
    (hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCodeT (some T) r.code) r.res cert
      (some T) = d)
    (kind : String → CalleeKind) (X : String → CalleeRun)
    (hK : ∀ c ∈ T.fns, (kind c.name).Top c ∧ (kind c.name).Spec (X c.name))
    {PT : LprogIsa.ProcTable} (hTc : ∀ c ∈ T.fns, PT c.name = some (kind c.name).summary)
    (sa : AState) (hreg : σ.Regions sa)
    {Γ : Ctxt jasminDialect} {p : NFProg jasminDialect Γ [.stackArr w m]}
    (hp : RegionExportable p) {r0 : Exported}
    (hr : exportR Γ.length a.fname p Γ.length 0 = some r0) {ex : List String}
    (hw : regionWebs ex r0 (calleeAAT (some T)) (calleeAOT (some T)) = r)
    {G : NFCall jasminDialect → Prop} (hGT : ∀ e, G e → EvOK T e)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (fuel : Nat)
    (hG : AllEv G (treeAt pureReader eventEnv fuel p V)) :
    ∃ (pc : List RInstr) (ds : List X86Backend.PhysAbiShape.DShape),
      calleeProg T b = some pc
      ∧ X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
      ∧ ∀ (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
        (RE : (nfCallSig jasminDialect).Event → (kSig AState).Event → Prop)
        (RA : (e₁ : (nfCallSig jasminDialect).Event) → (e₂ : (kSig AState).Event) →
          (nfCallSig jasminDialect).Resp e₁ → (kSig AState).Resp e₂ → Prop)
        (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value),
        (∀ (ev : NFCall jasminDialect) (u : LstateMF) (q : Nat), G ev →
          NFProgCallTreeExport.CallSite (singletonProgM a.fname d.ref) ev u →
          atPc (singletonProgM a.fname d.ref) q u →
          (∃ v, Glue PT (singletonProgM a.fname d.ref) q u v) ∨ h₁ ev = none) →
        (∀ (ev : NFCall jasminDialect) (u : LstateMF) (p : Nat), G ev →
          NFProgCallTreeExport.CallSite (singletonProgM a.fname d.ref) ev u →
          atPc (singletonProgM a.fname d.ref) p u →
          ∀ u' q v', Obs (segOutsAt d.ref (insTab d.ref d.outs) d.outs (some p)) u u' →
          u'.prog.lfn = u.prog.lfn → siteMap PT d.ref (imgOf σ T b d.ps) (some p) = some q →
          Glue PT (singletonProgM a.fname (imgOf σ T b d.ps)) q u' v' →
          ∀ bi ra f l, b[q]? = some bi → bi.li_i = .Lcall ra (f, l) →
          ∀ sa₁ sA, ImgRelF (frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
              (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b
              ((deadTab (imgOf σ T b d.ps) d.outs).dead q) (goto u' q) sa₁ →
            ACorr (X86Backend.DecodePrintedCFG.frameRsp b sa) sA sa₁ → sa₁.reg.lpc = q →
            RE ev (callEvent aMachine sym rd (X86Backend.DecodePrintedCFG.posOf ds q)
              (pc.length + T.entryIdx (T.symPos f)) sA)
            ∧ ∀ a₁ a₂, RA ev (callEvent aMachine sym rd (X86Backend.DecodePrintedCFG.posOf ds q)
                (pc.length + T.entryIdx (T.symPos f)) sA) a₁ a₂ →
              a₁ = none ∨ ∃ sc tr, a₂ = some sc
                ∧ X f (X86Backend.ImageCallProbe.entryOf
                  (X86Backend.DecodePrintedCFG.posOf ds q + 1) sA) tr sc
                ∧ ∀ v, Glue PT (singletonProgM a.fname d.ref) p u v →
                  CallRet (singletonProgM a.fname d.ref) ev u a₁ v) →
        RuttF h₁ RE RA (NFProgCallTreeExt.OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (.stackArr w m)
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m)
                .here v)))
          (fun o => o = none) (treeAt pureReader eventEnv fuel p V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨pc, ds, hpc, hds, hR⟩ := ruttF_regionRef hbs hg hd kind X hK hTc sa hreg hp hr hw hGT
    V hV fuel hG
  refine ⟨pc, ds, hpc, hds, fun h₁ RE RA sym rd hglue hsite => ?_⟩
  -- The checks of the calling body.
  have hg' := hg
  simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := hg'
  have hok := calleeBodyBT_spec.mp hcb
  have hT : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length
      ∧ (pr.RetWord ∨ ∀ q, callSymAt b q = some f →
        (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b q).1
          ∈ (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b q).2) := by
    intro f c hc
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    obtain ⟨har, -, -, -, -, -, -, hres⟩ := (hK c hcm).1.facts
    exact ⟨_, hTc c hcm, har, hres.imp id fun h q _ => h _ _ q⟩
  have hsymB : X86Backend.ImageAddrCall.bodyCallSymsB (fun g => T.names.contains g) b
      = true := by
    have h1 := bodyCallSymsB_of_decodeSites hok.decode
    rwa [CalleeTab.lookup_isSome] at h1
  have hsi := callSymsB_callImg (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
    hok.callSites hsymB
  have hT' : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length :=
    fun f c hc => let ⟨pr, hpr, ha, _⟩ := hT f c hc; ⟨pr, hpr, ha⟩
  have hDr := calleeTab_domEqT hT' hok.symsRef
  have hDi := calleeTab_domEqT hT' hsi
  have hres' : ∀ (p : Nat) (d' f : String) (xs : List String) (pr' : LprogIsa.ProcSummary),
      X86Backend.CalleeSegCheck.shadowAt d.ref p = some (d', f, xs.map LOperand.reg) →
      PT f = some pr' → pr'.RetWord ∨ d' ∈ xs := by
    intro p d' f xs pr' hp hf
    have hfT : T.names.contains f = true := by
      unfold X86Backend.CalleeSegCheck.shadowAt at hp
      cases hr : d.ref[p]? with
      | none => simp [hr] at hp
      | some i =>
        simp only [hr, Option.bind_some] at hp
        have hm := List.all_eq_true.mp hok.symsRef i (List.mem_of_getElem? hr)
        simpa [hp] using hm
    have hs : (T.lookup f).isSome = true := by
      have h1 := congrFun T.lookup_isSome f
      rw [h1]
      exact hfT
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨pr, hpr, -, hres⟩ := hT f c hc
    rw [hpr] at hf
    cases hf
    refine hres.imp id fun hall => ?_
    obtain ⟨q, hq⟩ := shadowAt_img_of_calleeSegB hok.seg hp (by simp [CalleeTab.tab, hc])
    unfold X86Backend.CalleeSegCheck.shadowAt at hq
    cases hr : (imgOf σ T b d.ps)[q]? with
    | none => simp [hr] at hq
    | some i =>
      simp only [hr, Option.bind_some] at hq
      obtain ⟨⟨bi, ra, l, hb, hbi⟩, hx⟩ := shadowCall?_callImg _ hok.callSites hr hq
      have hcs : callSymAt b q = some f := callSymAt_eq_some.mpr ⟨bi, ra, l, hb, hbi⟩
      have hsite : siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b q
          = calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b q := by
        simp [siteFn, hcs, hc]
      simp only [Prod.mk.injEq, hsite] at hx
      obtain ⟨hd', -, hxs⟩ := hx
      have hxs' : xs = (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b q).2 :=
        List.map_injective_iff.mpr (fun _ _ h => LOperand.reg.inj h) hxs
      rw [hxs', hd']
      exact hall q hcs
  have hseg := (X86Backend.CallTableCongr.calleeSegB_congr hDr hDi).symm.trans hok.seg
  exact hR h₁ RE RA sym rd (segSim_of_checks hres' hseg) hglue
    (fun ev u p hev hsi hat u' q v' hQ hq => hsite ev u p hev hsi hat u' q v' hQ.1 hQ.2 hq)

end Seg

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefRutt
