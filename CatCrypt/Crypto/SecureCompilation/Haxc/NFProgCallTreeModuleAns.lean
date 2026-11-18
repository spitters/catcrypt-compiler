/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBackAns
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeModule
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSAComp

/-!
# The statement at the separation contracts for a module, at the answers of the callees

`NFProgCallTreeModule.r3FG_of_front` gives the conclusion of `R3StatementFG` at a module from the
relation of the front, through the back half at the answer relation `BackRA`, in which the source
answer of a call is computed by the summary of the procedure table. This module gives the same
composition at the answers of the callees: the back half is
`NFProgCallTreeRefBackAns.ruttF_regionRef_backA` at the answer relation `BackRAA`, whose source
answer is the word of the result register of the return state of the callee run, the run relation
of a callee is the run relation of the frame contract `LinkedFn.frameContract`, and every relation
is `RuttSA` or `RuttFA` at a skip predicate. The relation of the chain at a skip predicate `Sk₁` of
the leaf events is a hypothesis (`ChainSA`), which the relation of the chain at the leaf handler
discharges (`chainSA_leaf`); the front is related at a skip predicate `Sk₀` of the source events.

The answers of the separation contracts at an answer predicate (`contractRACA`) are related by the
composed answer relation from the read-back `ResultOf` of the result of a linked function alone
(`compRA_of_contractRACA`): no meaning of a linked function and no summary enters. The events of
the narrowed program are asked to satisfy `EvOK` only.

## Main definitions

* `ChainSA`: the chain `extChain` followed by `narrowPrep` relates the call trees at a skip
  predicate of the leaf events.

## Main results

* `ruttF_regionRef_wordA`: the calling body against the target trees at a table of word callees,
  at `BackRE` and `BackRAA`.
* `ruttF_regionBack_targetA`: the same at a result of `regionBack`, with the decoding of the bytes.
* `chainSA_leaf`: the chain at the skip predicate of the leaf handler.
* `RuttFA.answerOut`, `RuttFA.and_target`: answering the events outside `keep` and restricting to
  target events of a predicate.
* `ruttF_extChain_targetA`: the chain composed with the back half.
* `ruttF_front_targetDA`: the front composed with the chain and the back half.
* `compRA_of_contractRACA`: the answers of the separation contracts at an answer predicate are
  related by the composed answer relation.
* `ruttF_contracts_targetDA`: the composed call trees at `contractREG` and `contractRACA`.
* `r3FA_of_front`: the relation of the call trees of a module at `contractRACA`, from the front.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeModuleAns

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (ImgRelF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck (segOutsAt siteMap)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc (regionProg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (atPc goto)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (tableOf entryCtx EntryVals enc dec)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn wordVal)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry OutTy)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv nfCallSig NFCall treeAt
  pureReader eventEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig leafHandler linkReader
  OutRel ExtRE ExtRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt (MapRE MapRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (CompRE CompRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvent (IsCallEv AllEvT encAll_wordsOf
  ins_scalar_of_arrArgs)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBody (imgOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack (callEvent)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack (BackRE)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBackAns (BackRAA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA (RuttSA ruttSA_iff_ruttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSAComp (RuttSA.trans_ruttFA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle (RuttFA AnsPred contractRACA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCompose (answerOut FrontRE FrontRA
  FrontRR)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (ChainRE ChainRA ChainRR
  eq_none_of_outRel mfTree_castProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTarget (symOf symOf_entry)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeR3 (keepL)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTyped (FrontRET frontRET_types)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeAnswer (length_encAll arrArgsOf_words)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked (contractRun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnFrame (calleeSpec_contractRun_frame)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose
open _root_.Hax

/-! ## 1. The back half at a table of word callees -/

/-- **The calling body against the target trees at a table of word callees, at the answers of
    the callees.** As `NFProgCallTreeRefBack.ruttF_regionRef_word`, from
    `NFProgCallTreeRefBackAns.ruttF_regionRef_backA` at `RE := BackRE T`: at the kinds `.ins` of
    the functions of `T` and run relations meeting the interface of the frame contract, the call
    tree of the program is related by `RuttFA` at every skip predicate to the target trees at the
    answer relation `BackRAA`, whose word is that of the result register `resK f`. No condition
    on the summaries at the events remains. -/
theorem ruttF_regionRef_wordA {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
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
      ∧ ∀ (Sk : (e : (nfCallSig jasminDialect).Event) → (nfCallSig jasminDialect).Resp e → Prop)
        (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value),
        (∀ f ∈ T.names, sym (pc.length + T.entryIdx (T.symPos f)) = f) →
        RuttFA Sk (BackRE T) (BackRAA (fun f sc => sc.regs (phys (resK f))) X)
          (OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (.stackArr w m)
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m)
                .here v)))
          (fun o => o = none) (treeAt pureReader eventEnv fuel p V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨pc, ds, hpc, hds, hR⟩ := NFProgCallTreeRefBackAns.ruttF_regionRef_backA hbs hg hd kind
    lf insK resK X hK hTc sa hreg hp hr hw hGT V hV fuel hG
  refine ⟨pc, ds, hpc, hds, fun Sk sym rd hsym => hR Sk (BackRE T) sym rd ?_⟩
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
  intro ev u p hev hcs' hat u' q hO hfn hq bi ra f l hb hbi sa₁ sA hrel hac hpcq
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

/-- **The back half at a result of `regionBack`, with the decoding of the bytes, at the answers
    of the callees.** The statement of `NFProgCallTreeTarget.ruttF_regionBack_target` with the
    back half of `ruttF_regionRef_wordA`: at the kinds `.ins` and run relations meeting the
    interface of the frame contract, the relation `RuttFA` at every skip predicate and the answer
    relation `BackRAA`; the table of callees is moreover nonempty. -/
theorem ruttF_regionBack_targetA {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData} {P : Lprog}
    {bytes : List (BitVec 8)} (h : regionBack σ a p linked = some (P, bytes))
    (hcf : p.callFree = false) :
    ∃ (T : CalleeTab) (b : Lcmd) (pc : List RInstr),
      T.fns.Sublist linked ∧ calleeBytes (some T) b = some bytes ∧ calleeProg T b = some pc
      ∧ callsToAny T.names p = true ∧ T.names.Nodup ∧ T.fns ≠ []
      ∧ (∀ q : CalleeData → List RInstr, (∀ c ∈ T.fns, decodeLprog c.bytes = some (q c)) →
        decodeLprog bytes = some (pc ++ shiftProg pc.length (regionProg (T.regionEntries q)))
        ∧ ∀ f ∈ T.names, symOf T pc.length (pc.length + T.entryIdx (T.symPos f)) = f)
      ∧ ∀ (kind : String → CalleeKind) (lf : String → LinkedFn)
        (insK : String → List (String × ArgKind)) (resK : String → String)
        (X : String → CalleeRun),
        (∀ c ∈ T.fns, (kind c.name).Top c
          ∧ kind c.name = .ins (lf c.name) (insK c.name) (resK c.name)
          ∧ CalleeSpec (X c.name)
            ((lf c.name).frameSig ((insK c.name).map (·.1)) (some (resK c.name)))) →
        ∀ {PT : LprogIsa.ProcTable}, (∀ c ∈ T.fns, PT c.name = some (kind c.name).summary) →
        (∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none)
          ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true) →
        ∀ (sa : AState), σ.Regions sa → ∀ (V : Ctxt.Valuation Γ), AbiValOf σ sa V →
        ∀ (fuel : Nat) {G : NFCall jasminDialect → Prop}, (∀ e, G e → EvOK T e) →
        AllEv G (treeAt pureReader eventEnv fuel p V) →
        ∀ (Sk : (e : (nfCallSig jasminDialect).Event) → (nfCallSig jasminDialect).Resp e → Prop)
          (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value),
        (∀ f ∈ T.names, sym (pc.length + T.entryIdx (T.symPos f)) = f) →
        RuttFA Sk (BackRE T) (BackRAA (fun f sc => sc.regs (phys (resK f))) X)
          (OutRel fun v sA =>
            σ.ResultOf sa sA (denVal t
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
          (fun o => o = none) (treeAt pureReader eventEnv fuel p V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨T, r0, hr0, hcT, ⟨w, m, rfl⟩, hB, r, b, cert, hwb, hbs, hg, -, -⟩ :=
    regionBack_spec_tab h hcf
  have hp : RegionExportable p := regionExportableB_sound hB
  obtain ⟨-, hneB, ds, pc, -, -, -, hpc, -⟩ := calleeBytes_tab hbs
  have hnd : T.names.Nodup := by
    have hg' := hg
    simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
    obtain ⟨⟨⟨⟨⟨⟨hnd0, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg'
    exact of_decide_eq_true hnd0
  obtain ⟨hpr, hnoc⟩ := regionCoB_callee hg
  have hrs : ∀ i ∈ b, ∀ f, X86Backend.LprogBytes.remoteSym i.li_i = some f → f ∈ T.names := by
    have hg' := hg
    simp only [regionCoB, renImageB, Option.all_some, Bool.and_eq_true] at hg'
    obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := hg'
    exact remoteSym_mem_names hpr (calleeBodyBT_spec.mp hb).decode
  have hne := regionCallee_fns_ne_nil hcT
  refine ⟨T, b, pc, regionCallee_sublist hcT, hbs, hpc, callsToAny_of_regionCallee hr0 hcT, hnd,
    hne, fun q hdecq => ?_,
    fun kind lf insK resK X hK PT hTc hword sa hreg V hV fuel G hGT hG Sk sym rd hsym => ?_⟩
  · have hnoq : ∀ c ∈ T.fns, ∀ tg, RInstr.call tg ∉ q c := fun c hc => hnoc c hc _ (hdecq c hc)
    have hR := T.regionBlocks hne q hdecq hneB hnoq T.names (fun _ h => h)
    obtain ⟨pr', hp', hd⟩ := calleeBytes_decode hbs hpr hrs hR.decode
    rw [hpc, Option.some.injEq] at hp'
    subst hp'
    exact ⟨hd, symOf_entry hnd hneB hR.decode pc.length⟩
  · obtain ⟨pc', ds', hpc', -, hR⟩ := ruttF_regionRef_wordA (a := a) hbs hg rfl kind lf insK resK
      X hK hTc sa hreg hp hr0 hwb hGT V hV fuel hG hword
    rw [hpc] at hpc'
    obtain rfl := Option.some.inj hpc'
    exact hR Sk sym rd hsym

/-! ## 2. The chain at a skip predicate -/

/-- **The chain at a skip predicate of the leaf events**: when the program `p` the chain
    `extChain` returns on `p0` passes the gate `regionExportableB`, at every narrowed program `q'`
    of `p` and every valuation in range, the call tree of `p0` at `linkReader` and the tree
    `mfTree` of `q'` are related by `RuttSA Sk` at the relations of the chain. -/
def ChainSA (Sk : (e : leafSig.Event) → leafSig.Resp e → Prop)
    (tE : TreeCallEnv leafSig nfDialect) {Γ : Ctxt nfDialect} {t : NfTy}
    (p0 : NFProg nfDialect Γ [t])
    (p : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) : Prop :=
  regionExportableB p = true →
    ∀ (q' : NFProg jasminDialect ((mapCtx (Γ.map catTy)).map NarrowWords.wideTy)
      ([mapTy (catTy t)].map NarrowWords.wideTy)), NarrowWords.narrowPrep p = some q' →
    ∀ (V : Ctxt.Valuation Γ), (∀ (s : NfTy) (v : Ctxt.Var Γ s), InRange s (v.lookup V)) →
    ∀ (tf fuel : Nat), tf ≤ fuel →
      RuttSA Sk ChainRE ChainRA (ChainRR t) (fun o => o = none) (treeAt linkReader tE tf p0 V)
        (mfTree fuel q' (NarrowWords.mapVal (ctMapValD (mapVal V))))

/-- **The chain at the skip predicate of the leaf handler**, from
    `NFProgCallTreeCompose.ruttS_extChain_narrowPrep`. -/
theorem chainSA_leaf {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (D : List ExtDecl)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (a : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs a = .ret none)
    (h₂ : ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e)
    (h₃ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hh₂ : ∀ e₁ e₂, ExtRE e₁ e₂ → ExtRA e₁ e₂ (leafHandler (tableOf bi) e₁) (h₂ e₂))
    (hh₃ : ∀ e₁ e₂, MapRE catToJasmin (fun x => ctTransTy x) e₁ e₂ →
      MapRA catToJasmin (fun x => ctTransTy x) e₁ e₂ (h₂ e₁) (h₃ e₂))
    (hinner : ∀ (f : String) (as rs : List JasminTy)
      (x : Ctxt.Valuation (d := jasminDialect) as), innerHead f = true →
        h₃ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    {Γ : Ctxt nfDialect} {t : NfTy} {p0 : NFProg nfDialect Γ [t]}
    {p : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]}
    (hp : (extChain D Γ t).run p0 = some p) :
    ChainSA (fun e a => a = leafHandler (tableOf bi) e) tE p0 p :=
  fun hB _ hq' V hin tf fuel hle => ruttSA_iff_ruttS.mpr
    (NFProgCallTreeCompose.ruttS_extChain_narrowPrep hbi D tE htE h₂ h₃ hh₂ hh₃ hinner hp hB hq'
      V hin tf fuel hle)

/-! ## 3. Answering events outside `keep`, and target events of a predicate -/

section RuttFA

variable {E₁ E₂ : EventSig} {R₁ R₂ : Type}

/-- **Answering the source events outside `keep` by a handler whose answers the skip predicate
    admits keeps `RuttFA`**, when every source event related to a target event is kept. -/
theorem RuttFA.answerOut {Sk : (e : E₁.Event) → E₁.Resp e → Prop}
    {h₁ : ∀ e : E₁.Event, E₁.Resp e} {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} (keep : E₁.Event → Bool)
    (hkeep : ∀ e₁ e₂, RE e₁ e₂ → keep e₁ = true) (hS : ∀ e, keep e = false → Sk e (h₁ e))
    {t₁ : CallTree E₁ R₁} {T : Nat → CallTree E₂ R₂} (h : RuttFA Sk RE RA RR Fail t₁ T) :
    RuttFA Sk RE RA RR Fail (answerOut keep h₁ t₁) T := by
  induction h with
  | ret n hT h => exact .ret n hT h
  | fail h => exact .fail h
  | @vis e₁ e₂ k₁ T K n hT he _ ih =>
    simp only [NFProgCallTreeCompose.answerOut, hkeep _ _ he, ite_true]
    exact .vis n hT he ih
  | @skip e₁ k₁ T _ ih =>
    by_cases hk : keep e₁ = true
    · simp only [NFProgCallTreeCompose.answerOut, hk, ite_true]
      exact .skip ih
    · simp only [NFProgCallTreeCompose.answerOut, hk, Bool.false_eq_true, ite_false]
      exact ih _ (hS e₁ (by simpa using hk))

/-- **A relation with a family of trees whose events satisfy a predicate** holds at the event
    relation restricted to target events that satisfy the predicate. -/
theorem RuttFA.and_target {Sk : (e : E₁.Event) → E₁.Resp e → Prop}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {P : E₂.Event → Prop} {t₁ : CallTree E₁ R₁}
    {T : Nat → CallTree E₂ R₂} (h : RuttFA Sk RE RA RR Fail t₁ T) :
    (∀ n, AllEvT P (T n)) → RuttFA Sk (fun e₁ e₂ => RE e₁ e₂ ∧ P e₂) RA RR Fail t₁ T := by
  induction h with
  | ret n hT h => exact fun _ => .ret n hT h
  | fail h => exact fun _ => .fail h
  | @vis e₁ e₂ k₁ T K n hT he _ ih =>
    intro hP
    have h0 := hP (n + 0)
    rw [hT 0] at h0
    refine .vis n hT ⟨he, h0.1⟩ fun a₁ a₂ ha => ih a₁ a₂ ha fun m => ?_
    have hm := hP (n + m)
    rw [hT m] at hm
    exact hm.2 a₂
  | skip _ ih => exact fun hP => .skip fun a ha => ih a ha hP

end RuttFA

/-! ## 4. The chain and the front composed with the back half -/

/-- **The call tree of the program of `nfDialect` against the target trees of the calling body of
    `compileRegion`, with the decoding of the bytes, at the answers of the callees.** As
    `NFProgCallTreeAssembly.ruttF_extChain_target`, with the chain at a skip predicate `Sk₁` of the
    leaf events (`ChainSA`) every answer of which has an answer related by the chain, and the
    back half of `ruttF_regionBack_targetA`. The relation is `RuttFA Sk₁` at the answer relation
    `BackRAA` of the back half. -/
theorem ruttF_extChain_targetA (tE : TreeCallEnv leafSig nfDialect)
    (Sk₁ : (e : leafSig.Event) → leafSig.Resp e → Prop)
    (hhC : ∀ e₁ e₂, ChainRE e₁ e₂ → ∀ a₁, Sk₁ e₁ a₁ → ∃ a₂, ChainRA e₁ e₂ a₁ a₂)
    {σ : AbiLayout} {t : NfTy} {p0 : NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    {p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy t)]}
    (hchain : ChainSA Sk₁ tE p0 p) {a : AbiNames} {linked : List CalleeData}
    {P : Lprog} {bytes : List (BitVec 8)} (h1 : compileRegion σ a p linked = some (P, bytes))
    (hcf : p.callFree = false) :
    ∃ (q : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
        ([mapTy (catTy t)].map NarrowWords.wideTy)) (T : CalleeTab) (b : Lcmd) (pc : List RInstr),
      NarrowWords.narrowPrep p = some q
      ∧ T.fns.Sublist linked ∧ calleeBytes (some T) b = some bytes ∧ calleeProg T b = some pc
      ∧ T.names.Nodup ∧ T.fns ≠ []
      ∧ (∀ qb : CalleeData → List RInstr, (∀ c ∈ T.fns, decodeLprog c.bytes = some (qb c)) →
        decodeLprog bytes = some (pc ++ shiftProg pc.length (regionProg (T.regionEntries qb)))
        ∧ ∀ f ∈ T.names, symOf T pc.length (pc.length + T.entryIdx (T.symPos f)) = f)
      ∧ ∀ (kind : String → CalleeKind) (lf : String → LinkedFn)
        (insK : String → List (String × ArgKind)) (resK : String → String)
        (X : String → CalleeRun),
        (∀ c ∈ T.fns, (kind c.name).Top c
          ∧ kind c.name = .ins (lf c.name) (insK c.name) (resK c.name)
          ∧ CalleeSpec (X c.name)
            ((lf c.name).frameSig ((insK c.name).map (·.1)) (some (resK c.name)))) →
        ∀ {PT : LprogIsa.ProcTable}, (∀ c ∈ T.fns, PT c.name = some (kind c.name).summary) →
        (∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none)
          ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true) →
        (∀ f ∈ T.names, innerHead f = false) →
        ∀ (sa : AState), σ.Regions sa → ∀ (env : _root_.Hax.Env), σ.EnvOf sa env →
        ∀ (V : Ctxt.Valuation (entryCtx (abiEntry σ))), EntryVals env (abiEntry σ) V →
        ∀ (tf fuel : Nat), tf ≤ fuel → ∀ {G : NFCall jasminDialect → Prop},
        (∀ e, G e → EvOK T e) →
        AllEv G (mfTree fuel q (NarrowWords.mapVal (ctMapValD (mapVal V)))) →
        ∀ (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value),
        (∀ f ∈ T.names, sym (pc.length + T.entryIdx (T.symPos f)) = f) →
        RuttFA Sk₁ (CompRE ChainRE (BackRE T))
          (CompRA ChainRE (BackRE T) ChainRA (BackRAA (fun f sc => sc.regs (phys (resK f))) X))
          (Relation.Comp (ChainRR t) (OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (NarrowWords.wideTy (mapTy (catTy t)))
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [NarrowWords.wideTy (mapTy (catTy t))])
                (t := NarrowWords.wideTy (mapTy (catTy t))) .here v))))
          (fun o => o = none) (treeAt linkReader tE tf p0 V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨hB, q, hq, hb, hcfq, -⟩ := compileRegion_ctx (nfCtx_wide σ) h1
  have hcf' := hcfq.trans hcf
  obtain ⟨T, b, pc, hsub, hbs, hpc, hcalls, hnd, hne, hdec, hR⟩ :=
    ruttF_regionBack_targetA hb hcf'
  refine ⟨q, T, b, pc, hq, hsub, hbs, hpc, hnd, hne, hdec,
    fun kind lf insK resK X hK PT hTc hword hin sa hreg env henv V hV
    tf fuel hle G hGT hG sym rd hsym => ?_⟩
  have hW : NarrowWords.mapVal (ctMapValD (mapVal V)) ≍ ctMapValD (mapVal V) :=
    NarrowWords.mapVal_heq_of_wide (nfCtx_wide σ) _
  have hmf : mfTree fuel q (NarrowWords.mapVal (ctMapValD (mapVal V)))
      = treeAt pureReader eventEnv fuel (NarrowWords.castProg (nfCtx_wide σ) rfl q)
        (ctMapValD (mapVal V)) := by
    rw [← mfTree_castProg fuel (nfCtx_wide σ) q _ _ hW.symm]
    exact NFProgCallTreeRefRutt.mfTree_eq_treeAt hin fuel _ hcalls _
  have hch := hchain hB q hq V (NFToRoute.inRange_entry henv V hV) tf fuel hle
  have hback := hR kind lf insK resK X hK hTc hword sa hreg (ctMapValD (mapVal V))
    (NFToRoute.abiValOf_mapVal henv V hV) fuel hGT (hmf ▸ hG) (fun _ _ => True) sym rd hsym
  refine RuttSA.trans_ruttFA (fun e₁ e₂ he a₁ ha₁ => ?_) (fun r₀ r₁ hr hf => ?_)
    (hmf ▸ hch) hback
  · obtain ⟨a₂, ha₂⟩ := hhC e₁ e₂ he a₁ ha₁
    exact ⟨a₂, trivial, ha₂⟩
  · obtain ⟨m₁, ⟨m₀, h1, h2⟩, h3⟩ := hr
    subst hf
    exact eq_none_of_outRel h1 (eq_none_of_outRel h2 (eq_none_of_outRel h3 rfl))

/-- **The front composed with the chain and the back half, with the decoding of the bytes, at the
    answers of the callees.** As `NFProgCallTreeModule.ruttF_front_targetD`, with the chain at a
    skip predicate `Sk₁` of the leaf events (`ChainSA`) that admits the answers of the leaf table
    at the events outside the linked functions, and the front at a skip predicate `Sk₀` of the
    source events every answer of which at an event related to a leaf call has an answer of `Sk₁`
    related by `FrontRA`. Every source tree related by the front to the call tree of the program
    of `haxToNF` with the other calls answered by the leaf table is related by `RuttFA Sk₀` to the
    target trees of the calling body, at the answer relation `BackRAA` of the back half. -/
theorem ruttF_front_targetDA {m : HaxModule} {σ : AbiLayout}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    {p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]}
    {a : AbiNames} {linked : List CalleeData} {P : Lprog} {bytes : List (BitVec 8)}
    (h1 : compileRegion σ a p linked = some (P, bytes)) (hcf : p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect) (Sk₁ : (e : leafSig.Event) → leafSig.Resp e → Prop)
    (hchain : ChainSA Sk₁ tE q.2 p)
    (hhC : ∀ e₁ e₂, ChainRE e₁ e₂ → ∀ a₁, Sk₁ e₁ a₁ → ∃ a₂, ChainRA e₁ e₂ a₁ a₂)
    (hS : ∀ e, keepL m e = false →
      Sk₁ e (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e))
    (Sk₀ : (e : linkSig.Event) → linkSig.Resp e → Prop)
    (hhF : ∀ e₀ e₁, FrontRET m e₀ e₁ → ∀ a₀, Sk₀ e₀ a₀ → ∃ a₁, Sk₁ e₁ a₁ ∧ FrontRA e₀ e₁ a₀ a₁)
    (hlinked : linked = m.linked.filterMap LinkedFn.calleeData) :
    ∃ (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
        ([mapTy (catTy q.1)].map NarrowWords.wideTy)) (T : CalleeTab) (b : Lcmd)
        (pc : List RInstr),
      NarrowWords.narrowPrep p = some q'
      ∧ T.fns.Sublist linked ∧ calleeBytes (some T) b = some bytes ∧ calleeProg T b = some pc
      ∧ T.names.Nodup ∧ T.fns ≠ []
      ∧ (∀ qb : CalleeData → List RInstr, (∀ c ∈ T.fns, decodeLprog c.bytes = some (qb c)) →
        decodeLprog bytes = some (pc ++ shiftProg pc.length (regionProg (T.regionEntries qb)))
        ∧ ∀ f ∈ T.names, symOf T pc.length (pc.length + T.entryIdx (T.symPos f)) = f)
      ∧ ∀ (kind : String → CalleeKind) (lf : String → LinkedFn)
        (insK : String → List (String × ArgKind)) (resK : String → String)
        (X : String → CalleeRun),
        (∀ c ∈ T.fns, (kind c.name).Top c
          ∧ kind c.name = .ins (lf c.name) (insK c.name) (resK c.name)
          ∧ CalleeSpec (X c.name)
            ((lf c.name).frameSig ((insK c.name).map (·.1)) (some (resK c.name)))) →
        ∀ {PT : LprogIsa.ProcTable}, (∀ c ∈ T.fns, PT c.name = some (kind c.name).summary) →
        (∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none)
          ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true) →
        (∀ f ∈ T.names, innerHead f = false) →
        ∀ (sa : AState), σ.Regions sa → ∀ (env : Env), σ.EnvOf sa env →
        ∀ (V : Ctxt.Valuation (entryCtx (abiEntry σ))), EntryVals env (abiEntry σ) V →
        ∀ (tf : Nat) {G : NFCall jasminDialect → Prop}, (∀ e, G e → EvOK T e) →
        AllEv G (mfTree tf q' (NarrowWords.mapVal (ctMapValD (mapVal V)))) →
        ∀ (sym : Nat → String) (rd : String → AState → List Value),
        (∀ f ∈ T.names, sym (pc.length + T.entryIdx (T.symPos f)) = f) →
        ∀ (t₀ : CallTree linkSig (Outcome × Env)),
        RuttSA Sk₀ (FrontRET m) FrontRA (FrontRR q.1) srcFail t₀
          (answerOut (keepL m) (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)))
            (treeAt linkReader tE tf q.2 V)) →
        RuttFA Sk₀ (CompRE (FrontRET m) (CompRE ChainRE (BackRE T)))
          (CompRA (FrontRET m) (CompRE ChainRE (BackRE T)) FrontRA
            (CompRA ChainRE (BackRE T) ChainRA (BackRAA (fun f sc => sc.regs (phys (resK f))) X)))
          (Relation.Comp (FrontRR q.1) (Relation.Comp (ChainRR q.1) (OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (NarrowWords.wideTy (mapTy (catTy q.1)))
              (Ctxt.Var.lookup (d := jasminDialect)
                (Γ := [NarrowWords.wideTy (mapTy (catTy q.1))])
                (t := NarrowWords.wideTy (mapTy (catTy q.1))) .here v)))))
          srcFail t₀ fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨q', T, b, pc, hq', hsub, hbs, hpc, hnd, hne, hdec, hR⟩ :=
    ruttF_extChain_targetA tE Sk₁ hhC hchain h1 hcf
  refine ⟨q', T, b, pc, hq', hsub, hbs, hpc, hnd, hne, hdec,
    fun kind lf insK resK X hK PT hTc hword hin sa hreg env
    henv V hV tf G hGT hG sym rd hsym t₀ hfront => ?_⟩
  have hback := hR kind lf insK resK X hK hTc hword hin sa hreg env henv V hV tf tf le_rfl hGT hG
    sym rd hsym
  refine RuttSA.trans_ruttFA hhF
    (fun r₀ r₁ hr hf => by subst hf; exact NFProgCallTreeCompose.srcFail_of_frontRR hr)
    hfront (RuttFA.answerOut (keepL m) (fun e₁ e₂ he => ?_) hS hback)
  obtain ⟨e₄, hC, -, c, hc, -⟩ := he
  obtain ⟨hcm, hcn⟩ := CalleeTab.lookup_spec hc
  rw [hlinked] at hsub
  obtain ⟨l, hl, hlc⟩ := List.mem_filterMap.mp (hsub.subset hcm)
  have hn : l.name = e₁.name := by
    rw [← (CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1, hcn,
      NFProgCallTreeModule.chainRE_name hC]
  exact List.any_eq_true.mpr ⟨l, hl, by simp [hn]⟩

/-! ## 5. The separation contracts at an answer predicate -/

/-- A word of 64 bits read back as a source integer decodes to the word. -/
theorem dec_word_int_toNat (w : BitVec 64) : dec (.word 64) (.int (w.toNat : Int)) = some w := by
  simp [dec, w.isLt]

/-- **The answers of the separation contracts at an answer predicate are related by the composed
    answer relation.** Let the linked functions of `m` have distinct names, each be a linked
    kernel, the functions of the table `T` be among their data, each with a register result and
    no array position, and the leaf calls the front relates to source calls have word and integer
    arguments and a word result. Let `lf` and `resK` send the symbol of each function of `T` to
    its linked function and its result register. Answers related by `contractRACA A m` are related
    by the composition of the answer relations of the front, the chain and the back half at the
    answers of the callees, `BackRAA` at the word of the result register and the run relations of
    the frame contracts. The value answer is the read-back `ResultOf` of the result register; no
    meaning of a linked function enters. -/
theorem compRA_of_contractRACA {A : AnsPred} {m : HaxModule} {T : CalleeTab}
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hsub : T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData))
    (hword : ∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none))
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (lf : String → LinkedFn) (resK : String → String)
    (hlf : ∀ c ∈ T.fns, ∀ l ∈ m.linked, l.calleeData = some c →
      lf c.name = l ∧ resK c.name = c.resReg)
    (tr₀ : List CTLeak)
    {e₀ : linkSig.Event} {e₅ : (kSig AState).Event} {a₀ : linkSig.Resp e₀}
    {a₅ : (kSig AState).Resp e₅} (hc : contractRACA A m e₀ e₅ a₀ a₅) :
    CompRA (FrontRET m) (CompRE ChainRE (fun e₄ e₅ => BackRE T e₄ e₅ ∧ IsCallEv (linkRead m) e₅))
      FrontRA (CompRA ChainRE (fun e₄ e₅ => BackRE T e₄ e₅ ∧ IsCallEv (linkRead m) e₅)
        ChainRA (BackRAA (fun f sc => sc.regs (phys (resK f)))
          (fun f => contractRun (lf f).frameContract tr₀))) e₀ e₅ a₀ a₅ := by
  intro e₁ hFT hCB
  obtain ⟨-, hret, -⟩ := frontRET_types hpar hFT
  have hF := hFT.1
  obtain ⟨l, hl, -, hall⟩ := id hc
  obtain ⟨n₁, as₁, r₁, xs₁⟩ := e₁
  dsimp only at hret
  subst hret
  obtain ⟨hn1, -, l', hl', -⟩ := hF
  dsimp only at hn1
  rw [hl] at hl'
  obtain rfl := Option.some.inj hl'
  -- The callee of the call in `T`, and the register of its result.
  obtain ⟨e₄₀, hC₀, ⟨-, c, hc5, -⟩, -⟩ := hCB
  have hn₄ : e₄₀.name = LinkCall.name e₀ := (NFProgCallTreeModule.chainRE_name hC₀).trans hn1
  rw [hn₄] at hc5
  obtain ⟨hcm, hcn⟩ := CalleeTab.lookup_spec hc5
  obtain ⟨l', hl'm, hlc⟩ := List.mem_filterMap.mp (hsub.subset hcm)
  have hll : l' = l := by
    have h1 := find?_name_of_nodup hnd hl'm
    rw [← (CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1, hcn, hl] at h1
    exact (Option.some.inj h1).symm
  subst hll
  obtain ⟨⟨r, hres⟩, -⟩ := hword c hcm
  obtain ⟨htop, -, -, -⟩ := (hk l' hl'm).kind_facts hlc
  have hkind : kernelKind l' c = .ins l' c.ins c.resReg := by
    simp only [kernelKind, hres]
  rw [hkind] at htop
  obtain ⟨-, hL, -⟩ := htop
  have hval : ∀ v, (a₀ : Option Value) = some v → ∃ s', (a₅ : Option AState) = some s'
      ∧ v = .int (s'.regs (phys c.resReg)).toNat
      ∧ contractRun l'.frameContract () (KCall.entry e₅) () s' := by
    intro v hv
    obtain ⟨s', hs', hres', hrun, -⟩ := hall v hv
    refine ⟨s', hs', ?_, hrun⟩
    simpa [AbiLayout.ResultOf, hL.result, ResultKind.read] using hres'
  refine ⟨(a₀ : Option Value).bind (dec (.word 64)), ?_, ?_⟩
  · -- The source answer is the encoding of the answer of the leaf call.
    change (a₀ : Option Value) = ((a₀ : Option Value).bind (dec (.word 64))).map (enc (.word 64))
    cases ha : (a₀ : Option Value) with
    | none => rfl
    | some v =>
      obtain ⟨s', -, rfl, -⟩ := hval v ha
      rw [Option.bind_some, dec_word_int_toNat, Option.map_some]
      rfl
  · intro e₄ hC hB
    obtain ⟨e₃, ⟨e₂, hE, hM⟩, hW⟩ := id hC
    obtain ⟨n₂, as₂, rs₂, xs₂⟩ := e₂
    obtain ⟨hn2, has2, hrs2, -⟩ := hE
    dsimp only at hn2 has2 hrs2
    subst hrs2
    subst has2
    subst hM
    subst hW
    refine ⟨((a₀ : Option Value).bind (dec (.word 64))).map fun y =>
      transArgs NarrowWords.widenP.mapTy (fun x => NarrowWords.transTy x)
        (transArgs catToJasmin.mapTy (fun x => ctTransTy x)
          (HVector.cons y .nil : Ctxt.Valuation (d := catCryptDialect) [catTy (.word 64)])), ?_, ?_⟩
    · -- The answers of the chain: the word, transported.
      generalize (a₀ : Option Value).bind (dec (.word 64)) = a₁
      intro e₃' hA' hW'
      obtain ⟨e₂', hE', hM'⟩ := hA'
      obtain ⟨n₂', as₂', rs₂', xs₂'⟩ := e₂'
      obtain ⟨-, has2', hrs2', -⟩ := hE'
      dsimp only at has2' hrs2'
      subst hrs2'
      subst has2'
      subst hM'
      refine ⟨a₁.map fun y => transArgs catToJasmin.mapTy (fun x => ctTransTy x)
        (HVector.cons y .nil : Ctxt.Valuation (d := catCryptDialect) [catTy (.word 64)]),
        fun e₂'' hE'' hM'' => ?_, fun y hy => ?_⟩
      · obtain ⟨n₂'', as₂'', rs₂'', xs₂''⟩ := e₂''
        obtain ⟨-, has2'', hrs2'', -⟩ := hE''
        dsimp only at has2'' hrs2''
        subst hrs2''
        subst has2''
        refine ⟨a₁.map fun y => (HVector.cons y .nil :
          Ctxt.Valuation (d := catCryptDialect) [catTy (.word 64)]), fun y hy => ?_,
          fun y hy => ?_⟩
        · refine ⟨y, ?_, rfl⟩
          rw [hy]
          rfl
        · cases a₁ with
          | none => cases hy
          | some y₀ =>
            cases hy
            rfl
      · cases a₁ with
        | none => cases hy
        | some y₀ =>
          cases hy
          rfl
    · -- The answer of the back half: the word of the result register, the frame run.
      obtain ⟨⟨-, c', hc5', -⟩, -⟩ := hB
      dsimp only at hc5' hn2
      have hn₀ : n₂ = LinkCall.name e₀ := hn2.trans hn1
      rw [hn₀, hc5] at hc5'
      obtain rfl := Option.some.inj hc5'
      obtain ⟨hlf1, hlf2⟩ := hlf c hcm l' hl'm hlc
      cases hav : (a₀ : Option Value) with
      | none =>
        left
        rfl
      | some v =>
        right
        obtain ⟨s', hs', rfl, hrun⟩ := hval v hav
        refine ⟨transArgs NarrowWords.widenP.mapTy (fun x => NarrowWords.transTy x)
          (transArgs catToJasmin.mapTy (fun x => ctTransTy x)
            (HVector.cons (s'.regs (phys c.resReg)) .nil :
              Ctxt.Valuation (d := catCryptDialect) [catTy (.word 64)])),
          s', tr₀, ?_, hs', ?_, ?_⟩
        · rw [Option.bind_some, dec_word_int_toNat]
          rfl
        · change contractRun (lf n₂).frameContract tr₀ _ tr₀ s'
          rw [hn₀, ← hcn, hlf1]
          exact ⟨rfl, hrun.2⟩
        · intro dst u
          dsimp only
          rw [hn₀, ← hcn, hlf2]
          rfl

/-- **The composed call trees of a module at the separation contracts at an answer predicate,
    with the decoding of the bytes.** As `NFProgCallTreeModule.ruttF_contracts_targetD`, at the
    hypotheses of `ruttF_front_targetDA` on the chain and the front: every source tree related by
    the front at the skip predicate `Sk₀` to the call tree of the program of `haxToNF` is related
    by `RuttFA Sk₀` to the target trees of the calling body at the linked reader, at
    `contractREG`, `contractRACA A`, `resRel` and `srcFail`, for every answer predicate `A`. The
    kinds are `moduleKind`, the run relations are those of the frame contracts, and the events of
    the narrowed program are asked to satisfy a predicate within `EvOK` only. -/
theorem ruttF_contracts_targetDA {m : HaxModule} {σ : AbiLayout}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : haxToNF σ m = some q)
    {p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]}
    {a : AbiNames} {linked : List CalleeData} {P : Lprog} {bytes : List (BitVec 8)}
    (h1 : compileRegion σ a p linked = some (P, bytes)) (hcf : p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect) (Sk₁ : (e : leafSig.Event) → leafSig.Resp e → Prop)
    (hchain : ChainSA Sk₁ tE q.2 p)
    (hhC : ∀ e₁ e₂, ChainRE e₁ e₂ → ∀ a₁, Sk₁ e₁ a₁ → ∃ a₂, ChainRA e₁ e₂ a₁ a₂)
    (hS : ∀ e, keepL m e = false →
      Sk₁ e (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e))
    (Sk₀ : (e : linkSig.Event) → linkSig.Resp e → Prop)
    (hhF : ∀ e₀ e₁, FrontRET m e₀ e₁ → ∀ a₀, Sk₀ e₀ a₀ → ∃ a₁, Sk₁ e₁ a₁ ∧ FrontRA e₀ e₁ a₀ a₁)
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hlinked : linked = m.linked.filterMap LinkedFn.calleeData)
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (A : AnsPred) (tr₀ : List CTLeak) :
    ∃ (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
        ([mapTy (catTy q.1)].map NarrowWords.wideTy)) (T : CalleeTab) (b : Lcmd)
        (pc : List RInstr),
      NarrowWords.narrowPrep p = some q'
      ∧ T.fns.Sublist linked ∧ calleeBytes (some T) b = some bytes ∧ calleeProg T b = some pc
      ∧ T.names.Nodup
      ∧ (∀ qb : CalleeData → List RInstr, (∀ c ∈ T.fns, decodeLprog c.bytes = some (qb c)) →
        decodeLprog bytes = some (pc ++ shiftProg pc.length (regionProg (T.regionEntries qb)))
        ∧ ∀ f ∈ T.names, symOf T pc.length (pc.length + T.entryIdx (T.symPos f)) = f)
      ∧ ((∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none)
          ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true) →
        (∀ f ∈ T.names, innerHead f = false) →
        ∀ (sa : AState), σ.Regions sa → ∀ (env : Env), σ.EnvOf sa env →
        ∀ (V : Ctxt.Valuation (entryCtx (abiEntry σ))), EntryVals env (abiEntry σ) V →
        ∀ (tf : Nat) {G : NFCall jasminDialect → Prop}, (∀ e, G e → EvOK T e) →
        AllEv G (mfTree tf q' (NarrowWords.mapVal (ctMapValD (mapVal V)))) →
        ∀ (sym : Nat → String),
        (∀ f ∈ T.names, sym (pc.length + T.entryIdx (T.symPos f)) = f) →
        ∀ (t₀ : CallTree linkSig (Outcome × Env)),
        RuttSA Sk₀ (FrontRET m) FrontRA (FrontRR q.1) srcFail t₀
          (answerOut (keepL m) (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)))
            (treeAt linkReader tE tf q.2 V)) →
        RuttFA Sk₀ (contractREG m) (contractRACA A m) (resRel σ sa) srcFail t₀
          fun n => targetTree aMachine pc sym (linkRead m) n 0 sa) := by
  obtain ⟨q', T, b, pc, hq', hsub, hbs, hpc, hnd', hne, hdec, hR⟩ :=
    ruttF_front_targetDA h1 hcf tE Sk₁ hchain hhC hS Sk₀ hhF hlinked
  have hout : OutTy q.1 := outTy_of_outTyB q.1 (haxToNF_eq_some_res hq)
  subst hlinked
  refine ⟨q', T, b, pc, hq', hsub, hbs, hpc, hnd', hdec,
    fun hword hin sa hreg env henv V hV tf G hGT hG sym hsym t₀ hfront => ?_⟩
  obtain ⟨c₀, hc₀⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨l₀, -, -⟩ := List.mem_filterMap.mp (hsub.subset hc₀)
  -- The linked function, the argument kinds and the result register of a symbol.
  let lf : String → LinkedFn := fun f => (m.linked.find? (·.name == f)).getD l₀
  let insK : String → List (String × ArgKind) := fun f => ((lf f).calleeData.map (·.ins)).getD []
  let resK : String → String := fun f => ((lf f).calleeData.map (·.resReg)).getD ""
  have hfind : ∀ c ∈ T.fns, ∀ l ∈ m.linked, l.calleeData = some c →
      m.linked.find? (·.name == c.name) = some l := by
    intro c _ l hl hlc
    rw [(CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1]
    exact find?_name_of_nodup hnd hl
  have hlf : ∀ c ∈ T.fns, ∀ l ∈ m.linked, l.calleeData = some c →
      lf c.name = l ∧ resK c.name = c.resReg ∧ insK c.name = c.ins := by
    intro c hc l hl hlc
    have h1 : lf c.name = l := by simp only [lf, hfind c hc l hl hlc, Option.getD_some]
    refine ⟨h1, ?_, ?_⟩
    · simp only [resK, h1, hlc, Option.map_some, Option.getD_some]
    · simp only [insK, h1, hlc, Option.map_some, Option.getD_some]
  have hK : ∀ c ∈ T.fns, (moduleKind m.linked (.ins l₀ [] "") c.name).Top c
      ∧ moduleKind m.linked (.ins l₀ [] "") c.name = .ins (lf c.name) (insK c.name) (resK c.name)
      ∧ CalleeSpec (contractRun (lf c.name).frameContract tr₀)
        ((lf c.name).frameSig ((insK c.name).map (·.1)) (some (resK c.name))) := by
    intro c hc
    obtain ⟨l, hl, hlc⟩ := List.mem_filterMap.mp (hsub.subset hc)
    obtain ⟨h1, h2, h3⟩ := hlf c hc l hl hlc
    obtain ⟨⟨r, hres⟩, -, -⟩ := hword c hc
    have hkk : moduleKind m.linked (.ins l₀ [] "") c.name = .ins l c.ins c.resReg := by
      simp [moduleKind, hfind c hc l hl hlc, hlc, kernelKind, hres]
    obtain ⟨htop, -, -, -⟩ := (hk l hl).kind_facts hlc
    rw [hkk, h1, h2, h3]
    refine ⟨?_, rfl, calleeSpec_contractRun_frame _ _ _ _⟩
    simpa [kernelKind, hres] using htop
  have H := hR (moduleKind m.linked (.ins l₀ [] "")) lf insK resK
    (fun f => contractRun (lf f).frameContract tr₀) hK
    (PT := NFProgCallTreeKinds.summaryOf m.linked (.ins l₀ [] "")) (fun _ _ => rfl) hword hin sa
    hreg env henv V hV tf hGT hG sym (linkRead m) hsym t₀ hfront
  have H' := RuttFA.and_target H
    (fun n => NFProgCallTreeEvent.allEvT_targetTree pc sym (linkRead m) n 0 sa)
  have hword' : ∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none) :=
    fun c hc => ⟨(hword c hc).1, (hword c hc).2.1⟩
  refine NFProgCallTreeOracle.RuttFA.imp (fun _ _ h => h) (fun e₀ e₅ he => ?_)
    (fun e₀ e₅ a₀ a₅ he ha => ?_) (fun r₀ r₅ hr => NFProgCallTreeResult.resRel_of_comp hout hr)
    (fun _ h => h) H'
  · obtain ⟨⟨e₁, h1, e₄, h4, h5⟩, hIs⟩ := he
    exact NFProgCallTreeTyped.contractREG_of_compT hnd hk hsub hword' hpar
      ⟨e₁, h1, e₄, h4, h5, hIs⟩
  · obtain ⟨-, hIs⟩ := he
    have hC := compRA_of_contractRACA hnd hk hsub hword' hpar lf resK
      (fun c hc l hl hlc => ⟨(hlf c hc l hl hlc).1, (hlf c hc l hl hlc).2.1⟩) tr₀ ha
    intro e₁ hF hCB
    obtain ⟨e₄, h4, h5⟩ := hCB
    obtain ⟨a₁, hFA, hrest⟩ := hC e₁ hF ⟨e₄, h4, h5, hIs⟩
    exact ⟨a₁, hFA, fun e₄' h4' h5' => hrest e₄' h4' ⟨h5', hIs⟩⟩

/-- **The relation of the call trees of a module at the separation contracts at an answer
    predicate, from the front.** As `NFProgCallTreeModule.r3FG_of_front` at the answers of the
    callees: under the shape conditions of `r3FG_of_front` on `m`, the chain of the program of
    `haxToNF` at a skip predicate `Sk₁` (`ChainSA`) whose answers have answers related by the
    chain and which admits the answers of the leaf table outside the linked functions, the events
    of the narrowed program within `EvOK`, and the front at a skip predicate `Sk₀` whose answers at
    an event related to a leaf call have answers of `Sk₁` related by `FrontRA`, the source call
    tree of the entry is related by `RuttFA Sk₀` to the target trees of the calling body at
    `contractREG` and `contractRACA A`, for every answer predicate `A`. At `Sk₀ := SkipAns A m` it
    is the conclusion of `NFProgCallTreeOracle.R3StatementFA A` at `m`. -/
theorem r3FA_of_front {m : HaxModule} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none)
    (hcf : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect) (Sk₁ : (e : leafSig.Event) → leafSig.Resp e → Prop)
    (hchain : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → ChainSA Sk₁ tE q.2 p)
    (hhC : ∀ e₁ e₂, ChainRE e₁ e₂ → ∀ a₁, Sk₁ e₁ a₁ → ∃ a₂, ChainRA e₁ e₂ a₁ a₂)
    (hS : ∀ e, keepL m e = false →
      Sk₁ e (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e))
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (hword : ∀ c ∈ m.linked.filterMap LinkedFn.calleeData, (∃ r, c.res = .reg r)
      ∧ c.arrArgs = (fun _ => none) ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true)
    (hin : ∀ l ∈ m.linked, innerHead l.name = false)
    (hev : ∀ (T : CalleeTab), T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData) →
      ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
        (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)])
        (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
          ([mapTy (catTy q.1)].map NarrowWords.wideTy)), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → NarrowWords.narrowPrep p = some q' →
      ∀ (tf : Nat) (V : Ctxt.Valuation (entryCtx (abiEntry σ))),
        AllEv (EvOK T) (mfTree tf q' (NarrowWords.mapVal (ctMapValD (mapVal V)))))
    (Sk₀ : (e : linkSig.Event) → linkSig.Resp e → Prop)
    (hhF : ∀ e₀ e₁, FrontRET m e₀ e₁ → ∀ a₀, Sk₀ e₀ a₀ → ∃ a₁, Sk₁ e₁ a₁ ∧ FrontRA e₀ e₁ a₀ a₁)
    (hfront : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]),
      haxToNF σ m = some q → ∀ (sa : AState), σ.Regions sa → ∀ (env : Env), σ.EnvOf sa env →
      ∀ (fuelC fuel : Nat), ∃ (V : Ctxt.Valuation (entryCtx (abiEntry σ))) (tf : Nat),
        EntryVals env (abiEntry σ) V
        ∧ RuttSA Sk₀ (FrontRET m) FrontRA (FrontRR q.1) srcFail
          (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel m.entry.erase env)
          (answerOut (keepL m) (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)))
            (treeAt linkReader tE tf q.2 V)))
    (A : AnsPred) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel,
          RuttFA Sk₀ (contractREG m) (contractRACA A m) (resRel σ sa) srcFail
            (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel
              m.entry.erase env)
            (fun fuelT => targetTree aMachine pc sym (linkRead m) fuelT 0 sa) := by
  have hca : compileARegion m σ fname = some (P, bytes) := by
    rw [← pairTailOf_none_compileA_eq hpt fname hn]
    exact hc
  have hca' := (NFEntry.compileR_eq_bind haxEntry m σ fname
    (m.linked.filterMap LinkedFn.calleeData)).symm.trans hca
  obtain ⟨q, hq, hca⟩ := Option.bind_eq_some_iff.mp hca'
  obtain ⟨p, hp, h1⟩ := Option.bind_eq_some_iff.mp hca
  obtain ⟨q', T, b, pc, hq', hsub, hbs, hpc, hndT, hdec, hR⟩ :=
    ruttF_contracts_targetDA hq h1 (hcf q p hq hp) tE Sk₁ (hchain q p hq hp) hhC hS Sk₀ hhF
      hnd hk rfl hpar A []
  obtain ⟨hdB, hsym⟩ := hdec _ (NFProgCallTreeModule.decode_moduleBlock hnd hk hsub)
  refine ⟨pc, regionProg (T.regionEntries fun c => moduleBlock m.linked c.name),
    symOf T pc.length, hdB, fun sa hreg env henv fuelC fuel => ?_⟩
  have hne : narrowEntry m σ sa = sa := by simp [narrowEntry, hn]
  rw [hne] at henv
  obtain ⟨V, tf, hV, hfr⟩ := hfront q hq sa hreg env henv fuelC fuel
  have hwordT : ∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none)
      ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true :=
    fun c hcT => hword c (hsub.subset hcT)
  have hinT : ∀ f ∈ T.names, innerHead f = false := by
    intro f hf
    obtain ⟨c, hcT, rfl⟩ := List.mem_map.mp hf
    obtain ⟨l, hl, hlc⟩ := List.mem_filterMap.mp (hsub.subset hcT)
    rw [(CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1]
    exact hin l hl
  exact hR hwordT hinT sa hreg env henv V hV tf (G := EvOK T) (fun _ he => he)
    (hev T hsub q p q' hq hp hq' tf V) (symOf T pc.length) hsym _ hfr

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeModuleAns
