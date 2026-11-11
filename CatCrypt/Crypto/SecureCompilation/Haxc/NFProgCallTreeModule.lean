/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeAssembly
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTyped

/-!
# The statement at the guarded contracts for a module, from the front

`R3StatementFG` relates, for a module compiled by `compileA`, the source call tree of the entry to
the target trees of the decoded calling body at `contractREG`, `contractRAC` and `resRel`. For a
module without narrow parameters read at their widths and without a pair tail, `compileA` is the
region back half on the chain of the program of `haxToNF` (`pairTailOf_none_compileA_eq`,
`NFEntry.compileR_eq_bind`). When that program has a `call` and the linked functions of the module
are linked kernels with distinct names, word and integer parameters, a word result, register
results, no array positions and general-purpose argument names, the conclusion of `R3StatementFG`
for the module follows from the relation `FrontRET` of the front between the source call tree of the
entry and the call tree of the program of `haxToNF`, under the conditions of the intermediate
handlers and of the events of the narrowed program (`r3FG_of_front`). A call the chain relates to a
call of the back half is a call of a linked function, since the back half calls the symbols of its
table, which are the names of linked functions, and the chain keeps the names of calls
(`chainRE_name`). The bytes decode to the calling body followed by the region of the decoded blocks
of the kernels, and the symbol map is `symOf`.

## Main results

* `chainRE_name`: the chain keeps the name of a call.
* `ruttF_front_targetD`, `ruttF_contracts_targetD`: the compositions of the front `FrontRET` and
  the passage to the separation contracts at every list of declarations of the chain.
* `decode_moduleBlock`: the code of the data of a linked kernel decodes to its block.
* `r3FG_of_front`: the conclusion of `R3StatementFG` at a module, from the relation of the front.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeModule



open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (tableOf entryCtx EntryVals)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv nfCallSig NFCall treeAt)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig leafHandler linkReader
  OutRel ExtRE ExtRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt (MapRE MapRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (CompRE CompRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack (BackRE BackRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCompose (answerOut FrontRE FrontRA
  FrontRR)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (ChainRE ChainRA ChainRR)
open _root_.Hax

open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeR3 (keepL)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeKinds (contractRunOf summaryOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (contractRAC)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (OutTy)
open CatCrypt.Crypto.Hax (LinkedFn)

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc (regionProg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTarget (symOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (eq_none_of_outRel mfTree_castProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (pureReader eventEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContracts (R3StatementFG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTyped (FrontRET)


/-- The chain keeps the name of a call. -/
theorem chainRE_name {e₁ : leafSig.Event} {e₄ : (nfCallSig jasminDialect).Event}
    (h : ChainRE e₁ e₄) : e₄.name = e₁.name := by
  obtain ⟨e₃, ⟨e₂, hE, hM⟩, hW⟩ := h
  rw [hW, hM]
  exact hE.1

/-- **The front composed with the chain and the back half, with the decoding of the bytes, at
    every list of declarations of the chain.** Let `haxToNF` return `q` on the module `m`, the
    chain `extChain D` return `p` on `q`, and `compileRegion` return a result on `p` at the data of
    the linked functions of `m`, which has a `call`. Under the conditions of
    `NFProgCallTreeRegion.ruttF_extChain_compileRegion` at the table of the linked functions of `m`,
    every source tree related by the front (`FrontRET`, `FrontRA`, `FrontRR`, the failed source leaf
    `srcFail`) to the call tree of `q` at `linkReader` with the other calls answered by the leaf
    table is related by `RuttF` to the target trees of the calling body, at the compositions of the
    relations of the front, of the chain and of the back half. -/
theorem ruttF_front_targetD {m : HaxModule} {D : List ExtDecl} {σ : AbiLayout}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : haxToNF σ m = some q)
    {p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]}
    (hp : (extChain D _ q.1).run q.2
      = some p)
    {a : AbiNames} {linked : List CalleeData} {P : Lprog} {bytes : List (BitVec 8)}
    (h1 : compileRegion σ a p linked = some (P, bytes)) (hcf : p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (x : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs x = .ret none)
    (h₂ : ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e)
    (h₃ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hh₂ : ∀ e₁ e₂, ExtRE e₁ e₂ → ExtRA e₁ e₂
      (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁) (h₂ e₂))
    (hh₃ : ∀ e₁ e₂, MapRE catToJasmin (fun x => ctTransTy x) e₁ e₂ →
      MapRA catToJasmin (fun x => ctTransTy x) e₁ e₂ (h₂ e₁) (h₃ e₂))
    (hinner : ∀ (f : String) (as rs : List JasminTy) (x : Ctxt.Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₃ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    (hhC : ∀ e₁ e₂, ChainRE e₁ e₂ → ChainRA e₁ e₂
      (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁) (h₃ e₂))
    (hlinked : linked = m.linked.filterMap LinkedFn.calleeData) :
    ∃ (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
        ([mapTy (catTy q.1)].map NarrowWords.wideTy)) (T : CalleeTab) (b : Lcmd)
        (pc : List RInstr),
      NarrowWords.narrowPrep p = some q'
      ∧ T.fns.Sublist linked ∧ calleeBytes (some T) b = some bytes ∧ calleeProg T b = some pc
      ∧ T.names.Nodup
      ∧ (∀ qb : CalleeData → List RInstr, (∀ c ∈ T.fns, decodeLprog c.bytes = some (qb c)) →
        decodeLprog bytes = some (pc ++ shiftProg pc.length (regionProg (T.regionEntries qb)))
        ∧ ∀ f ∈ T.names, symOf T pc.length (pc.length + T.entryIdx (T.symPos f)) = f)
      ∧ (∀ (kind : String → CalleeKind) (X : String → CalleeRun),
        (∀ c ∈ T.fns, (kind c.name).Top c ∧ (kind c.name).Spec (X c.name)) →
        ∀ {PT : LprogIsa.ProcTable}, (∀ c ∈ T.fns, PT c.name = some (kind c.name).summary) →
        (∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none)
          ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true) →
        (∀ f ∈ T.names, innerHead f = false) →
        ∀ (sa : AState), σ.Regions sa → ∀ (env : Env), σ.EnvOf sa env →
        ∀ (V : Ctxt.Valuation (entryCtx (abiEntry σ))), EntryVals env (abiEntry σ) V →
        ∀ (tf : Nat) {G : NFCall jasminDialect → Prop}, (∀ e, G e → EvOK T e) →
        AllEv G (mfTree tf q' (NarrowWords.mapVal (ctMapValD (mapVal V)))) →
        ∀ (sym : Nat → String) (rd : String → AState → List Value),
        (∀ ev, G ev → ∃ pr, PT ev.name = some pr ∧ pr.arity = ev.argTys.length
          ∧ pr.arrArgs = arrArgsOf ev.argTys
          ∧ (pr.result (wordsOf ev.args) = none → h₃ ev = none)) →
        (∀ f ∈ T.names, sym (pc.length + T.entryIdx (T.symPos f)) = f) →
        ∀ (t₀ : CallTree linkSig (Outcome × Env)),
        RuttS (linkHandler m) (FrontRET m) FrontRA (FrontRR q.1) srcFail t₀
          (answerOut (keepL m) (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)))
            (treeAt linkReader tE tf q.2 V)) →
        RuttF (linkHandler m) (CompRE (FrontRET m) (CompRE ChainRE (BackRE T)))
          (CompRA (FrontRET m) (CompRE ChainRE (BackRE T)) FrontRA
            (CompRA ChainRE (BackRE T) ChainRA (BackRA PT X)))
          (Relation.Comp (FrontRR q.1) (Relation.Comp (ChainRR q.1) (OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (NarrowWords.wideTy (mapTy (catTy q.1)))
              (Ctxt.Var.lookup (d := jasminDialect)
                (Γ := [NarrowWords.wideTy (mapTy (catTy q.1))])
                (t := NarrowWords.wideTy (mapTy (catTy q.1))) .here v)))))
          srcFail t₀ fun n => targetTree aMachine pc sym rd n 0 sa) := by
  obtain ⟨hfs, -, hlk, -⟩ := haxToNF_eq_some hq
  have hbi : SubTable (m.linkTable CatCrypt.Crypto.Hax.hax64WExit) :=
    subTable_linkBi _ CatCrypt.Crypto.Hax.hax64WExit_subTable
      fun l hl => not_catName_of_linkNameOk (hlk l hl)
  obtain ⟨q', T, b, pc, hq', hsub, hbs, hpc, hnd, hdec, hR⟩ :=
    NFProgCallTreeAssembly.ruttF_extChain_target hbi D tE htE h₂ h₃ hh₂ hh₃ hinner
      hhC hp h1 hcf
  refine ⟨q', T, b, pc, hq', hsub, hbs, hpc, hnd, hdec,
    fun kind X hK PT hTc hword hin sa hreg env
    henv V hV tf G hGT hG sym rd hsum hsym t₀ hfront => ?_⟩
  have hback := hR kind X hK hTc hword hin sa hreg env henv V hV tf tf le_rfl hGT hG sym rd hsum
    hsym
  exact NFProgCallTreeCalls.RuttS.trans_ruttF
    (fun e₀ e₁ he => NFProgCallTreeCompose.frontRA_linkHandler m _ he.1)
    (fun r₀ r₁ hr hf => by subst hf; exact NFProgCallTreeCompose.srcFail_of_frontRR hr)
    hfront (NFProgCallTreeR3.RuttF.answerOut (keepL m) (fun e₁ e₂ he => by
      obtain ⟨e₄, hC, -, c, hc, -⟩ := he
      obtain ⟨hcm, hcn⟩ := CalleeTab.lookup_spec hc
      rw [hlinked] at hsub
      obtain ⟨l, hl, hlc⟩ := List.mem_filterMap.mp (hsub.subset hcm)
      have hn : l.name = e₁.name := by
        rw [← (CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1, hcn, chainRE_name hC]
      exact List.any_eq_true.mpr ⟨l, hl, by simp [hn]⟩) hback)

/-- **The composed call trees of a module at the separation contracts, with the decoding of the
    bytes, at every list of declarations of the chain.** Under the hypotheses of
    `NFProgCallTreeR3.ruttF_front_compileRegion`, at a module whose linked functions have distinct
    names and are linked kernels whose data are the linked data of `compileRegion`, at a result
    type the back half reads back, and at linked functions with word and integer parameters and a
    word result: every source tree related by the front `FrontRET` to the call tree of the program
    of `haxToNF` is related by `RuttF` to the target trees of the calling body at the linked
    reader, at `contractREG`, `contractRAC`, `resRel` and `srcFail`, at the kinds `moduleKind`,
    the run relations of the contracts and the procedure table of the summaries of the kinds. -/
theorem ruttF_contracts_targetD {m : HaxModule} {D : List ExtDecl} {σ : AbiLayout}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : haxToNF σ m = some q)
    {p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]}
    (hp : (extChain D _ q.1).run q.2
      = some p)
    {a : AbiNames} {linked : List CalleeData} {P : Lprog} {bytes : List (BitVec 8)}
    (h1 : compileRegion σ a p linked = some (P, bytes)) (hcf : p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (x : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs x = .ret none)
    (h₂ : ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e)
    (h₃ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hh₂ : ∀ e₁ e₂, ExtRE e₁ e₂ → ExtRA e₁ e₂
      (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁) (h₂ e₂))
    (hh₃ : ∀ e₁ e₂, MapRE catToJasmin (fun x => ctTransTy x) e₁ e₂ →
      MapRA catToJasmin (fun x => ctTransTy x) e₁ e₂ (h₂ e₁) (h₃ e₂))
    (hinner : ∀ (f : String) (as rs : List JasminTy) (x : Ctxt.Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₃ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    (hhC : ∀ e₁ e₂, ChainRE e₁ e₂ → ChainRA e₁ e₂
      (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁) (h₃ e₂))
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hlinked : linked = m.linked.filterMap LinkedFn.calleeData) (hout : OutTy q.1)
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (d : CalleeKind) (tr₀ : List CTLeak) :
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
        (∀ ev, G ev → ∃ pr, summaryOf m.linked d ev.name = some pr ∧ pr.arity = ev.argTys.length
          ∧ pr.arrArgs = arrArgsOf ev.argTys
          ∧ (pr.result (wordsOf ev.args) = none → h₃ ev = none)) →
        (∀ f ∈ T.names, sym (pc.length + T.entryIdx (T.symPos f)) = f) →
        ∀ (t₀ : CallTree linkSig (Outcome × Env)),
        RuttS (linkHandler m) (FrontRET m) FrontRA (FrontRR q.1) srcFail t₀
          (answerOut (keepL m) (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)))
            (treeAt linkReader tE tf q.2 V)) →
        RuttF (linkHandler m) (contractREG m) (contractRAC m) (resRel σ sa) srcFail t₀
          fun n => targetTree aMachine pc sym (linkRead m) n 0 sa) := by
  obtain ⟨q', T, b, pc, hq', hsub, hbs, hpc, hnd', hdec, hR⟩ := ruttF_front_targetD
    hq hp h1 hcf tE htE h₂ h₃ hh₂ hh₃ hinner hhC hlinked
  subst hlinked
  refine ⟨q', T, b, pc, hq', hsub, hbs, hpc, hnd', hdec,
    fun hword hin sa hreg env henv V hV tf G hGT hG
    sym hsum hsym t₀ hfront => ?_⟩
  obtain ⟨hK, hTc⟩ := NFProgCallTreeKinds.kinds_of_linked hnd hk hsub d tr₀
  have H := hR (moduleKind m.linked d) (contractRunOf m.linked tr₀) hK hTc hword hin sa hreg
    env henv V hV tf hGT hG sym (linkRead m) hsum hsym t₀ hfront
  have H' := NFProgCallTreeEvent.RuttF.and_target H
    (fun n => NFProgCallTreeEvent.allEvT_targetTree pc sym (linkRead m) n 0 sa)
  have hword' : ∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none) :=
    fun c hc => ⟨(hword c hc).1, (hword c hc).2.1⟩
  refine NFProgCallTreeCompose.RuttF.imp (fun e₀ e₅ he => ?_) (fun e₀ e₅ he a₀ a₅ ha => ?_)
    (fun r₀ r₅ hr => NFProgCallTreeResult.resRel_of_comp hout hr) (fun _ h => h) H'
  · obtain ⟨⟨e₁, h1, e₄, h4, h5⟩, hIs⟩ := he
    exact NFProgCallTreeTyped.contractREG_of_compT hnd hk hsub hword' hpar
      ⟨e₁, h1, e₄, h4, h5, hIs⟩
  · obtain ⟨-, hIs⟩ := he
    have hC := NFProgCallTreeTyped.compRA_of_contractRACT hnd hk hsub hword' hpar d tr₀ ha
    intro e₁ hF hCB
    obtain ⟨e₄, h4, h5⟩ := hCB
    obtain ⟨a₁, hFA, hrest⟩ := hC e₁ hF ⟨e₄, h4, h5, hIs⟩
    exact ⟨a₁, hFA, fun e₄' h4' h5' => hrest e₄' h4' ⟨h5', hIs⟩⟩

/-- **The code of the data of a linked kernel decodes to its block.** At a module whose linked
    functions have distinct names and are linked kernels, the code of each function of a table
    among their data decodes to the block `moduleBlock` of its symbol. -/
theorem decode_moduleBlock {m : HaxModule} (hnd : (m.linked.map (·.name)).Nodup)
    (hk : ∀ l ∈ m.linked, LinkedKernel l) {T : CalleeTab}
    (hsub : T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData)) :
    ∀ c ∈ T.fns, decodeLprog c.bytes = some (moduleBlock m.linked c.name) := by
  intro c hc
  obtain ⟨l, hl, hlc⟩ := List.mem_filterMap.mp (hsub.subset hc)
  have he := CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc
  have hf : m.linked.find? (·.name == c.name) = some l := by
    rw [he.2.1]
    exact find?_name_of_nodup hnd hl
  obtain ⟨q, hq, -⟩ := (hk l hl).contract_code hlc
  have hb : moduleBlock m.linked c.name = (decodeLprog l.bytes).getD [] := by
    simp [moduleBlock, hf]
  rw [hb, ← he.2.2.2.2.2.1, hq]
  rfl

/-- The events of the narrowed program the back half asks for, at the table `T`: events that
    `EvOK T` admits and whose symbol has a summary of the arity and the array positions of the
    event that refuses its argument words only where the handler `h₃` fails. -/
def GoodEv (m : HaxModule) (d : CalleeKind) (T : CalleeTab)
    (h₃ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (ev : NFCall jasminDialect) : Prop :=
  EvOK T ev ∧ ∃ pr, summaryOf m.linked d ev.name = some pr ∧ pr.arity = ev.argTys.length
    ∧ pr.arrArgs = arrArgsOf ev.argTys ∧ (pr.result (wordsOf ev.args) = none → h₃ ev = none)

/-- **The conclusion of `R3StatementFG` at a module, from the front.** Let `compileA` compile the
    module `m`, without narrow parameters read at their widths and without a pair tail, whose
    linked functions have distinct names, are linked kernels with word and integer parameters and
    a word result, and have data with register results, no array positions and general-purpose
    argument names, none an inner head. Let the program of `haxToNF` run through the chain to a
    program with a `call`. Under the conditions on the intermediate handlers `h₂`, `h₃` and on the
    events of the narrowed program (`GoodEv`), the relation `FrontRET` of the front gives the
    conclusion of `R3StatementFG` for `m`. -/
theorem r3FG_of_front {m : HaxModule} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none)
    (hcf : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (x : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs x = .ret none)
    (h₂ : ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e)
    (h₃ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hh₂ : ∀ e₁ e₂, ExtRE e₁ e₂ → ExtRA e₁ e₂
      (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁) (h₂ e₂))
    (hh₃ : ∀ e₁ e₂, MapRE catToJasmin (fun x => ctTransTy x) e₁ e₂ →
      MapRA catToJasmin (fun x => ctTransTy x) e₁ e₂ (h₂ e₁) (h₃ e₂))
    (hinner : ∀ (f : String) (as rs : List JasminTy) (x : Ctxt.Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₃ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    (hhC : ∀ e₁ e₂, ChainRE e₁ e₂ → ChainRA e₁ e₂
      (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁) (h₃ e₂))
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (hword : ∀ c ∈ m.linked.filterMap LinkedFn.calleeData, (∃ r, c.res = .reg r)
      ∧ c.arrArgs = (fun _ => none) ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true)
    (hin : ∀ l ∈ m.linked, innerHead l.name = false) (d : CalleeKind) (tr₀ : List CTLeak)
    (hev : ∀ (T : CalleeTab), T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData) →
      ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
        (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)])
        (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
          ([mapTy (catTy q.1)].map NarrowWords.wideTy)), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → NarrowWords.narrowPrep p = some q' →
      ∀ (tf : Nat) (V : Ctxt.Valuation (entryCtx (abiEntry σ))),
        AllEv (GoodEv m d T h₃) (mfTree tf q' (NarrowWords.mapVal (ctMapValD (mapVal V)))))
    (hfront : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]),
      haxToNF σ m = some q → ∀ (sa : AState), σ.Regions sa → ∀ (env : Env), σ.EnvOf sa env →
      ∀ (fuelC fuel : Nat), ∃ (V : Ctxt.Valuation (entryCtx (abiEntry σ))) (tf : Nat),
        EntryVals env (abiEntry σ) V
        ∧ RuttS (linkHandler m) (FrontRET m) FrontRA (FrontRR q.1) srcFail
          (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel m.entry.erase env)
          (answerOut (keepL m) (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)))
            (treeAt linkReader tE tf q.2 V))) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel,
          RuttF (linkHandler m) (contractREG m) (contractRAC m) (resRel σ sa) srcFail
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
  have hout : OutTy q.1 := outTy_of_outTyB q.1 (haxToNF_eq_some_res hq)
  obtain ⟨q', T, b, pc, hq', hsub, hbs, hpc, hndT, hdec, hR⟩ :=
    ruttF_contracts_targetD hq hp h1 (hcf q p hq hp) tE htE h₂ h₃ hh₂ hh₃
      hinner hhC hnd hk rfl hout hpar d tr₀
  obtain ⟨hdB, hsym⟩ := hdec _ (decode_moduleBlock hnd hk hsub)
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
  exact hR hwordT hinT sa hreg env henv V hV tf (G := GoodEv m d T h₃) (fun _ he => he.1)
    (hev T hsub q p q' hq hp hq' tf V) (symOf T pc.length) (fun _ he => he.2) hsym _ hfr

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeModule
