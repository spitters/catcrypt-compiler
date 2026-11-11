/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefArgs

/-!
# The answers at the calls of a calling body

At a call of the reference of a calling body, the source answer and the answer of the image call
are related by `BackRA`: the source answer fails, or the summary of the procedure table computes it
on the argument words of the event and the target answer is a return state of the callee run. At
`BackRA` the condition of `NFProgCallTreeRefRutt.ruttF_regionRef_seg` on the answers holds, since
the step of the summary is then a state after the call at the source answer
(`NFProgCallTreeSeg.callRet_of_glue`), and the symbol of the image call is that of the event.

## Main definitions

* `BackRA`: the relation of the answers of a call event and of a linked call event of the image.

## Main results

* `answers_of_backRA`: at `BackRA`, every pair of answers is the failed answer or a callee answer
  whose source answer the step of the summary writes.
* `glue_of_summary`: the step of the summary at a call site, from the summary of the symbol of the
  event.
* `ruttF_regionRef_back`, `ruttF_regionRef_backS`: the call tree of the program of a calling body
  against the target trees at `RE` and `BackRA`, under the condition that the summary steps or
  the source handler fails at each call site of an event of `G` (given by the summary of the
  symbol of the event), and the relation `RE` at each image call of an event of `G`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (arrArgsOf wordsOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (Glue)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (atPc)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree (KCall kSig)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (CallOut CallRet)

/-- **The relation of the answers at a call**, at the procedure table `PT` and the callee runs
    `X`: the source answer fails, or it is a result `r` that the summary of the symbol of the event
    computes on the argument words of the event, at the arity and the array positions of the
    event and with a state after the call at every destination, and the target answer is a return
    state of the callee run of the symbol from the entry state of the linked call. -/
def BackRA (PT : LprogIsa.ProcTable) (X : String → CalleeRun) (ev : NFCall jasminDialect)
    (e₂ : (kSig AState).Event) (a₁ : (nfCallSig jasminDialect).Resp ev)
    (a₂ : (kSig AState).Resp e₂) : Prop :=
  a₁ = none ∨ ∃ r, a₁ = some r
    ∧ (∃ pr x, PT ev.name = some pr ∧ pr.arity = ev.argTys.length
      ∧ pr.arrArgs = arrArgsOf ev.argTys ∧ pr.result (wordsOf ev.args) = some x
      ∧ ∀ (dst : String) (u : LstateMF), CallOut dst ev.resTys r u (LprogIsa.retRes dst x u))
    ∧ ∃ sc tr, a₂ = some sc ∧ X ev.name e₂.entry tr sc

/-- **The answers at `BackRA`.** Every pair of answers of a call event `ev` at a call site `u` of
    `B` at `p` and of a linked call event with the entry state `sA` that `BackRA` relates is the
    failed answer, or a return state of the callee run of the symbol of `ev` from `sA` whose source
    answer the step of the summary of `PT` at `p` writes. -/
theorem answers_of_backRA {PT : LprogIsa.ProcTable} {X : String → CalleeRun} {fn : String}
    {B : List LinstrRM} {ev : NFCall jasminDialect} {u : LstateMF} {p : Nat}
    (hsi : NFProgCallTreeExport.CallSite (singletonProgM fn B) ev u)
    (hat : atPc (singletonProgM fn B) p u) {e₂ : (kSig AState).Event}
    {a₁ : (nfCallSig jasminDialect).Resp ev} {a₂ : (kSig AState).Resp e₂}
    (h : BackRA PT X ev e₂ a₁ a₂) :
    a₁ = none ∨ ∃ sc tr, a₂ = some sc ∧ X ev.name e₂.entry tr sc
      ∧ ∀ v, Glue PT (singletonProgM fn B) p u v → CallRet (singletonProgM fn B) ev u a₁ v := by
  rcases h with h | ⟨r, rfl, ⟨pr, x, hpr, har, haa, hx, hout⟩, sc, tr, hsc, hX⟩
  · exact Or.inl h
  · exact Or.inr ⟨sc, tr, hsc, hX, fun v hg =>
      NFProgCallTreeSeg.callRet_of_glue hpr har haa hx hout hsi hat hg⟩



/-- **The step of the summary at a call site.** If the summary of the symbol of a call event `ev`
    has the arity and the array positions of `ev`, and refuses the argument words of `ev` only where
    the source handler `h₁` fails at `ev`, the step of the summary at every call site of `ev` is
    defined, or `h₁` fails at `ev`. -/
theorem glue_of_summary {PT : LprogIsa.ProcTable} {fn : String} {B : List LinstrRM}
    (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    {ev : NFCall jasminDialect}
    (hsum : ∃ pr, PT ev.name = some pr ∧ pr.arity = ev.argTys.length
      ∧ pr.arrArgs = arrArgsOf ev.argTys ∧ (pr.result (wordsOf ev.args) = none → h₁ ev = none))
    {u : LstateMF} {q : Nat} (hsi : NFProgCallTreeExport.CallSite (singletonProgM fn B) ev u)
    (hat : atPc (singletonProgM fn B) q u) :
    (∃ v, Glue PT (singletonProgM fn B) q u v) ∨ h₁ ev = none := by
  obtain ⟨pr, hpr, har, haa, hnone⟩ := hsum
  obtain ⟨dst, srcs, tag, k, hat', hf, hlen, hrd⟩ := hsi
  obtain rfl : k = q := hat'.2.symm.trans hat.2
  cases hx : pr.result (wordsOf ev.args) with
  | none => exact Or.inr (hnone hx)
  | some x =>
      refine Or.inl ⟨LprogIsa.retRes dst x u, _, pr, dst, srcs, hf, ?_, ?_⟩
      · rw [LprogIsa.procCall?_callShadow, hpr]
        rfl
      · unfold LprogIsa.procStep
        rw [ite_eq_left (hlen.trans har.symm), haa, hrd]
        simp only [Option.bind_some, hx, Option.map_some]

section Corollary

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (CutSimI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (ImgRelF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck (segOutsAt siteMap)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (goto)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (eventEnv treeAt pureReader)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack (callEvent)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBody (imgOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)

/-- **The calling body against the target trees at the answer relation `BackRA`.** As
    `NFProgCallTreeRefRutt.ruttF_regionRef_seg` at `RA := BackRA PT X`: the answers at the calls
    are those of `answers_of_backRA`, the symbol of the image call is that of the event
    (`NFProgCallTreeRefArgs.callSym_eq`), and the condition at the image calls of events of `G` is
    the relation `RE` of the event and the call event of the image alone. -/
theorem ruttF_regionRef_back {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
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
              (pc.length + T.entryIdx (T.symPos f)) sA)) →
        RuttF h₁ RE (BackRA PT X) (NFProgCallTreeExt.OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (.stackArr w m)
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m)
                .here v)))
          (fun o => o = none) (treeAt pureReader eventEnv fuel p V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨pc, ds, hpc, hds, hR⟩ := NFProgCallTreeRefRutt.ruttF_regionRef_seg hbs hg hd kind X hK
    hTc sa hreg hp hr hw hGT V hV fuel hG
  refine ⟨pc, ds, hpc, hds, fun h₁ RE sym rd hglue hRE => ?_⟩
  -- The segment check at `PT` and the call sites of the body.
  have hg' := hg
  simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := hg'
  have hok := calleeBodyBT_spec.mp hcb
  have hT' : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length := by
    intro f c hc
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    obtain ⟨har, -⟩ := (hK c hcm).1.facts
    exact ⟨_, hTc c hcm, har⟩
  have hsymB : X86Backend.ImageAddrCall.bodyCallSymsB (fun g => T.names.contains g) b
      = true := by
    have h1 := bodyCallSymsB_of_decodeSites hok.decode
    rwa [CalleeTab.lookup_isSome] at h1
  have hsi := callSymsB_callImg (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
    hok.callSites hsymB
  have hseg := (X86Backend.CallTableCongr.calleeSegB_congr (calleeTab_domEqT hT' hok.symsRef)
    (calleeTab_domEqT hT' hsi)).symm.trans hok.seg
  refine hR h₁ RE (BackRA PT X) sym rd hglue fun ev u p hev hcs hat u' q v' hO hfn hq hg'' bi ra f
    l hb hbi sa₁ sA hrel hac hpcq => ⟨hRE ev u p hev hcs hat u' q v' hO hfn hq hg'' bi ra f l hb hbi
      sa₁ sA hrel hac hpcq, fun a₁ a₂ hra => ?_⟩
  obtain ⟨dst, srcs, tag, k, hat', hf, hlen, hrd⟩ := hcs
  obtain rfl : k = p := hat'.2.symm.trans hat.2
  obtain rfl := NFProgCallTreeRefArgs.callSym_eq hseg hok.callSites hf hq hb hbi
  exact answers_of_backRA ⟨dst, srcs, tag, k, hat', hf, hlen, hrd⟩ hat hra

/-- **The calling body against the target trees at the summaries of the events.** As
    `ruttF_regionRef_back`, with the condition on the step of the summary at the call sites given
    by the summary of the symbol of each event of `G`: it has the arity and the array positions of
    the event and refuses its argument words only where the source handler fails
    (`glue_of_summary`). -/
theorem ruttF_regionRef_backS {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
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
        (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value),
        (∀ ev, G ev → ∃ pr, PT ev.name = some pr ∧ pr.arity = ev.argTys.length
          ∧ pr.arrArgs = arrArgsOf ev.argTys
          ∧ (pr.result (wordsOf ev.args) = none → h₁ ev = none)) →
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
              (pc.length + T.entryIdx (T.symPos f)) sA)) →
        RuttF h₁ RE (BackRA PT X) (NFProgCallTreeExt.OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (.stackArr w m)
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m)
                .here v)))
          (fun o => o = none) (treeAt pureReader eventEnv fuel p V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨pc, ds, hpc, hds, hR⟩ := ruttF_regionRef_back hbs hg hd kind X hK hTc sa hreg hp hr hw
    hGT V hV fuel hG
  exact ⟨pc, ds, hpc, hds, fun h₁ RE sym rd hsum hRE =>
    hR h₁ RE sym rd (fun ev _ _ hev hsi hat => glue_of_summary h₁ (hsum ev hev) hsi hat) hRE⟩


/-- **The relation of a call event and a linked call event of the image at a table of callees**:
    the linked call names the symbol of the event, and the argument words of the event are the
    registers of the arguments of the callee of the symbol at the entry state of the linked
    call. -/
def BackRE (T : CalleeTab) (ev : NFCall jasminDialect) (e₂ : (kSig AState).Event) : Prop :=
  e₂.call.name = ev.name ∧ ∃ c, T.lookup ev.name = some c
    ∧ wordsOf ev.args = c.args.map fun a => e₂.entry.regs (X86Backend.DecodePrinted.phys a)

/-- **The calling body against the target trees at a table of word callees.** As
    `ruttF_regionRef_backS` at `RE := BackRE T`, for a table whose functions have a word result,
    no array argument and general-purpose argument names, where `sym` sends the entry of the code
    of each symbol of the table to the symbol: at an image call matched to a call of an event, the
    symbol is that of the event (`NFProgCallTreeRefArgs.callSym_eq`) and the argument words of the
    event are the registers of the arguments of the callee at its entry
    (`NFProgCallTreeRefArgs.eventArgs_entry`). The remaining condition is that of the summaries. -/
theorem ruttF_regionRef_word {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
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
    (hword : ∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none)
      ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true) :
    ∃ (pc : List RInstr) (ds : List X86Backend.PhysAbiShape.DShape),
      calleeProg T b = some pc
      ∧ X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
      ∧ ∀ (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
        (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value),
        (∀ ev, G ev → ∃ pr, PT ev.name = some pr ∧ pr.arity = ev.argTys.length
          ∧ pr.arrArgs = arrArgsOf ev.argTys
          ∧ (pr.result (wordsOf ev.args) = none → h₁ ev = none)) →
        (∀ f ∈ T.names, sym (pc.length + T.entryIdx (T.symPos f)) = f) →
        RuttF h₁ (BackRE T) (BackRA PT X) (NFProgCallTreeExt.OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (.stackArr w m)
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m)
                .here v)))
          (fun o => o = none) (treeAt pureReader eventEnv fuel p V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨pc, ds, hpc, hds, hR⟩ := ruttF_regionRef_backS hbs hg hd kind X hK hTc sa hreg hp hr hw
    hGT V hV fuel hG
  refine ⟨pc, ds, hpc, hds, fun h₁ sym rd hsum hsym => hR h₁ (BackRE T) sym rd hsum ?_⟩
  -- The checks of the calling body and the entry facts of the image.
  have hg' := hg
  simp only [regionCoB, regionCopy_some_callee, regionOut, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨⟨⟨⟨⟨⟨-, hcs⟩, -⟩, -⟩, -⟩, -⟩,
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, hce⟩, hren⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, himg⟩⟩ := hg'
  obtain ⟨codeC, hcode⟩ := Option.isSome_iff_exists.mp hcs
  have hcc : calleeCodeT (some T) r.code = codeC := by
    simp only [calleeCodeT, hcode, Option.getD_some]
  rw [hcc] at hd hren
  have hcells : d.cells = [] := List.isEmpty_iff.mp hce
  have hcellOuts : d.cellOuts = [] := by
    have h1 : d.cellOuts = d.cells.flatMap fun p =>
        if d.obs.contains p.1 then X86Backend.ImageAddrRouteW.outCells p.1 p.2 else [] := by
      rw [← hd]; rfl
    rw [h1, hcells]
    rfl
  rw [hcells, hcellOuts, List.append_nil] at himg
  have RF := renB_spec hren
  have hU : ∀ j, j < σ.args.length → unren d.ps (renOf d.ps (argName j)) = argName j :=
    fun j hj => (RF.unr j hj).2
  obtain ⟨hsep, -⟩ := renImage_entry_nil himg hU sa hreg a.fname []
  have hok := calleeBodyBT_spec.mp hcb
  have hT' : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length := by
    intro f c hc
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    obtain ⟨har, -⟩ := (hK c hcm).1.facts
    exact ⟨_, hTc c hcm, har⟩
  have hsymB : X86Backend.ImageAddrCall.bodyCallSymsB (fun g => T.names.contains g) b
      = true := by
    have h1 := bodyCallSymsB_of_decodeSites hok.decode
    rwa [CalleeTab.lookup_isSome] at h1
  have hsi := callSymsB_callImg (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
    hok.callSites hsymB
  have hseg := (X86Backend.CallTableCongr.calleeSegB_congr (calleeTab_domEqT hT' hok.symsRef)
    (calleeTab_domEqT hT' hsi)).symm.trans hok.seg
  have hdead := (Bool.and_eq_true_iff.mp hok.dead).1
  intro ev u p hev hcs' hat u' q v' hO hfn hq hg'' bi ra f l hb hbi sa₁ sA hrel hac hpcq
  obtain ⟨dst, srcs, tag, k, hat', hf, hlen, hrd⟩ := id hcs'
  obtain rfl : k = p := hat'.2.symm.trans hat.2
  obtain rfl := NFProgCallTreeRefArgs.callSym_eq hseg hok.callSites hf hq hb hbi
  -- The callee of the symbol.
  have hfT : T.names.contains ev.name = true := by
    have hm := List.all_eq_true.mp hok.symsRef _ (List.mem_of_getElem? hf)
    simpa [LprogIsa.shadowCall?_callShadow] using hm
  have hs : (T.lookup ev.name).isSome = true := by
    have h1 := congrFun T.lookup_isSome ev.name
    rw [h1]
    exact hfT
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨⟨r', hr'⟩, haa, hgp⟩ := hword c (CalleeTab.lookup_spec hc).1
  have hsite : siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b q
      = (c.resReg, c.args) := by
    rw [siteFn_of_callSym (callSymAt_eq_some.mpr ⟨bi, ra, l, hb, hbi⟩) hc,
      calleeSiteAt_of_reg hr' haa]
  have hw' : arrArgsOf ev.argTys = fun _ => none := by
    rw [(hGT ev hev).1]
    simp [calleeAAT, hc, haa]
  have hargs := NFProgCallTreeRefArgs.eventArgs_entry hseg hok.callSites hdead hsep hcs' hat hw' hO
    hq (by rw [hsite]; exact hgp) hrel hac (X86Backend.DecodePrintedCFG.posOf ds q + 1)
  rw [hsite] at hargs
  have hmem : ev.name ∈ T.names := by simpa using hfT
  exact ⟨hsym ev.name hmem, c, hc, hargs⟩

end Corollary

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack
