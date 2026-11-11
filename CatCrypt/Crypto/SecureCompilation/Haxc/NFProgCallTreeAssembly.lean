/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContracts

/-!
# The composed call trees of a module with the decoding of its bytes

`NFProgCallTreeContracts.ruttF_contracts_compileRegion` relates a source tree related by the front
to the target trees of the calling body of a result of `compileRegion`, at a symbol map given with
its condition. `R3StatementF` also asks the decoding of the bytes into the calling body followed by
the region of the callees, and its target trees are formed at a symbol map it provides. At the
back half of `NFProgCallTreeTarget.ruttF_regionBack_target`, which gives the decoding of the bytes
and the symbol map `symOf` with the same calling body, the compositions of the chain
(`ruttF_extChain_target`), of the front (`ruttF_front_target`) and the passage to the separation
contracts (`ruttF_contracts_target`) carry the decoding and the symbol map.

## Main results

* `ruttF_extChain_target`, `ruttF_front_target`, `ruttF_contracts_target`: the compositions of
  `NFProgCallTreeRegion.ruttF_extChain_compileRegion`, `NFProgCallTreeR3.ruttF_front_compileRegion`
  and `NFProgCallTreeContracts.ruttF_contracts_compileRegion` with the decoding of the bytes and the
  symbol map `symOf`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeAssembly


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

/-- **The call tree of the program of `nfDialect` against the target trees of the calling body of
    `compileRegion`, with the decoding of the bytes.** Let the chain `extChain D` return `p` on
    the program `p0` of `nfDialect` at
    the entry context of `σ`, and `compileRegion` return a result on `p`, which has a `call`. There
    are the narrowed program `q`, the table `T` of callees, the printed body `b` with the bytes of
    the result and the calling body `pc`, such that from every entry state `sa` satisfying
    `σ.Regions` and every valuation of the entry read off a source environment of `sa`, the call
    tree of `p0` at `linkReader`, at a tree call environment in which every call of a procedure
    fails, is related by `RuttF` to the target trees of `pc` from `sa`, at the compositions of the
    relations of the chain and of the back half, under the conditions of both: the handlers of
    the intermediate trees, no inner head among the callees, and the conditions of
    `ruttF_regionBack_word` at the call tree of the program `regionBack` compiles. -/
theorem ruttF_extChain_target {bi : _root_.Hax.Builtins} (hbi : SubTable bi)
    (D : List ExtDecl)
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
    (hhC : ∀ e₁ e₂, ChainRE e₁ e₂ → ChainRA e₁ e₂ (leafHandler (tableOf bi) e₁) (h₃ e₂))
    {σ : AbiLayout} {t : NfTy} {p0 : NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    {p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy t)]}
    (hp : (extChain D _ t).run p0 = some p) {a : AbiNames} {linked : List CalleeData}
    {P : Lprog} {bytes : List (BitVec 8)} (h1 : compileRegion σ a p linked = some (P, bytes))
    (hcf : p.callFree = false) :
    ∃ (q : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
        ([mapTy (catTy t)].map NarrowWords.wideTy)) (T : CalleeTab) (b : Lcmd) (pc : List RInstr),
      NarrowWords.narrowPrep p = some q
      ∧ T.fns.Sublist linked ∧ calleeBytes (some T) b = some bytes ∧ calleeProg T b = some pc
      ∧ T.names.Nodup
      ∧ (∀ qb : CalleeData → List RInstr, (∀ c ∈ T.fns, decodeLprog c.bytes = some (qb c)) →
        decodeLprog bytes = some (pc ++ shiftProg pc.length (regionProg (T.regionEntries qb)))
        ∧ ∀ f ∈ T.names, symOf T pc.length (pc.length + T.entryIdx (T.symPos f)) = f)
      ∧ ∀ (kind : String → CalleeKind) (X : String → CalleeRun),
        (∀ c ∈ T.fns, (kind c.name).Top c ∧ (kind c.name).Spec (X c.name)) →
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
        (∀ ev, G ev → ∃ pr, PT ev.name = some pr ∧ pr.arity = ev.argTys.length
          ∧ pr.arrArgs = arrArgsOf ev.argTys
          ∧ (pr.result (wordsOf ev.args) = none → h₃ ev = none)) →
        (∀ f ∈ T.names, sym (pc.length + T.entryIdx (T.symPos f)) = f) →
        RuttF (leafHandler (tableOf bi)) (CompRE ChainRE (BackRE T))
          (CompRA ChainRE (BackRE T) ChainRA (BackRA PT X))
          (Relation.Comp (ChainRR t) (OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (NarrowWords.wideTy (mapTy (catTy t)))
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [NarrowWords.wideTy (mapTy (catTy t))])
                (t := NarrowWords.wideTy (mapTy (catTy t))) .here v))))
          (fun o => o = none) (treeAt linkReader tE tf p0 V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨hB, q, hq, hb, hcfq, -⟩ := compileRegion_ctx (nfCtx_wide σ) h1
  have hcf' := hcfq.trans hcf
  obtain ⟨T, b, pc, hsub, hbs, hpc, hcalls, hnd, hdec, hR⟩ :=
    NFProgCallTreeTarget.ruttF_regionBack_target hb hcf'
  refine ⟨q, T, b, pc, hq, hsub, hbs, hpc, hnd, hdec,
    fun kind X hK PT hTc hword hin sa hreg env henv V hV
    tf fuel hle G hGT hG sym rd hsum hsym => ?_⟩
  have hW : NarrowWords.mapVal (ctMapValD (mapVal V)) ≍ ctMapValD (mapVal V) :=
    NarrowWords.mapVal_heq_of_wide (nfCtx_wide σ) _
  have hmf : mfTree fuel q (NarrowWords.mapVal (ctMapValD (mapVal V)))
      = treeAt pureReader eventEnv fuel (NarrowWords.castProg (nfCtx_wide σ) rfl q)
        (ctMapValD (mapVal V)) := by
    rw [← mfTree_castProg fuel (nfCtx_wide σ) q _ _ hW.symm]
    exact NFProgCallTreeRefRutt.mfTree_eq_treeAt hin fuel _ hcalls _
  have hchain := NFProgCallTreeCompose.ruttS_extChain_narrowPrep hbi D tE htE h₂ h₃ hh₂ hh₃
    hinner hp hB hq V (NFToRoute.inRange_entry henv V hV) tf fuel hle
  have hback := hR kind X hK hTc hword sa hreg (ctMapValD (mapVal V))
    (NFToRoute.abiValOf_mapVal henv V hV) fuel hGT (hmf ▸ hG) h₃ sym rd hsum hsym
  refine NFProgCallTreeCalls.RuttS.trans_ruttF hhC (fun r₀ r₁ hr hf => ?_) (hmf ▸ hchain) hback
  obtain ⟨m₁, ⟨m₀, h1, h2⟩, h3⟩ := hr
  subst hf
  exact eq_none_of_outRel h1 (eq_none_of_outRel h2 (eq_none_of_outRel h3 rfl))

/-- **The front composed with the chain and the back half, with the decoding of the bytes.** Let
    `haxToNF` return `q` on the
    module `m`, the chain `extChain` at the declared procedures of `m` return `p` on `q`, and
    `compileRegion` return a result on `p`, which has a `call`. Under the conditions of
    `NFProgCallTreeRegion.ruttF_extChain_compileRegion` at the table of the linked functions of `m`,
    and when every event the chain relates to a target event is a call of a linked function of `m`,
    every source tree related by the front (`FrontRE`, `FrontRA`, `FrontRR`, the failed source leaf
    `srcFail`) to the call tree of `q` at `linkReader` with the other calls answered by the leaf
    table is related by `RuttF` to the target trees of the calling body, at the compositions of the
    relations of the front, of the chain and of the back half. -/
theorem ruttF_front_target {m : HaxModule} {σ : AbiLayout}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : haxToNF σ m = some q)
    {p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]}
    (hp : (extChain (linkedDecls m (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) _ q.1).run q.2
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
      (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁) (h₃ e₂)) :
    ∃ (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
        ([mapTy (catTy q.1)].map NarrowWords.wideTy)) (T : CalleeTab) (b : Lcmd)
        (pc : List RInstr),
      NarrowWords.narrowPrep p = some q'
      ∧ T.fns.Sublist linked ∧ calleeBytes (some T) b = some bytes ∧ calleeProg T b = some pc
      ∧ T.names.Nodup
      ∧ (∀ qb : CalleeData → List RInstr, (∀ c ∈ T.fns, decodeLprog c.bytes = some (qb c)) →
        decodeLprog bytes = some (pc ++ shiftProg pc.length (regionProg (T.regionEntries qb)))
        ∧ ∀ f ∈ T.names, symOf T pc.length (pc.length + T.entryIdx (T.symPos f)) = f)
      ∧ ((∀ e₁ e₂, ChainRE e₁ e₂ → keepL m e₁ = true) →
        ∀ (kind : String → CalleeKind) (X : String → CalleeRun),
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
        RuttS (linkHandler m) (FrontRE m) FrontRA (FrontRR q.1) srcFail t₀
          (answerOut (keepL m) (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)))
            (treeAt linkReader tE tf q.2 V)) →
        RuttF (linkHandler m) (CompRE (FrontRE m) (CompRE ChainRE (BackRE T)))
          (CompRA (FrontRE m) (CompRE ChainRE (BackRE T)) FrontRA
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
    ruttF_extChain_target hbi
      (linkedDecls m (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) tE htE h₂ h₃ hh₂ hh₃ hinner
      hhC hp h1 hcf
  refine ⟨q', T, b, pc, hq', hsub, hbs, hpc, hnd, hdec,
    fun hkeep kind X hK PT hTc hword hin sa hreg env
    henv V hV tf G hGT hG sym rd hsum hsym t₀ hfront => ?_⟩
  have hback := hR kind X hK hTc hword hin sa hreg env henv V hV tf tf le_rfl hGT hG sym rd hsum
    hsym
  exact NFProgCallTreeCalls.RuttS.trans_ruttF
    (fun e₀ e₁ he => NFProgCallTreeCompose.frontRA_linkHandler m _ he)
    (fun r₀ r₁ hr hf => by subst hf; exact NFProgCallTreeCompose.srcFail_of_frontRR hr)
    hfront (NFProgCallTreeR3.RuttF.answerOut (keepL m) (fun e₁ e₂ he => by
      obtain ⟨e', he', -⟩ := he
      exact hkeep _ _ he') hback)

/-- **The composed call trees of a module at the separation contracts, with the decoding of the
    bytes.** Under the hypotheses of
    `NFProgCallTreeR3.ruttF_front_compileRegion`, at a module whose linked functions have distinct
    names and are linked kernels whose data are the linked data of `compileRegion`, at a result
    type the back half reads back, and when the leaf calls the front relates to source calls have
    word and integer arguments, as many as the parameters of the linked function, and a word
    result: every source tree related by the front to the call tree of the program of `haxToNF` is
    related by `RuttF` to the target trees of the calling body at the linked reader, at
    `contractREG`, `contractRAC`, `resRel` and `srcFail`, at the kinds `moduleKind`, the run
    relations of the contracts and the procedure table of the summaries of the kinds. -/
theorem ruttF_contracts_target {m : HaxModule} {σ : AbiLayout}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : haxToNF σ m = some q)
    {p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]}
    (hp : (extChain (linkedDecls m (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) _ q.1).run q.2
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
    (hty : ∀ e₀ e₁, FrontRE m e₀ e₁ → (∀ a ∈ e₁.argTys, a = .word 64 ∨ a = .int)
      ∧ e₁.ret = .word 64)
    (hlen : ∀ e₀ e₁ l, FrontRE m e₀ e₁ → m.linked.find? (·.name == LinkCall.name e₀) = some l →
      e₁.argTys.length = l.params.length)
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
      ∧ ((∀ e₁ e₂, ChainRE e₁ e₂ → keepL m e₁ = true) →
        (∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none)
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
        RuttS (linkHandler m) (FrontRE m) FrontRA (FrontRR q.1) srcFail t₀
          (answerOut (keepL m) (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)))
            (treeAt linkReader tE tf q.2 V)) →
        RuttF (linkHandler m) (contractREG m) (contractRAC m) (resRel σ sa) srcFail t₀
          fun n => targetTree aMachine pc sym (linkRead m) n 0 sa) := by
  obtain ⟨q', T, b, pc, hq', hsub, hbs, hpc, hnd', hdec, hR⟩ := ruttF_front_target
    hq hp h1 hcf tE htE h₂ h₃ hh₂ hh₃ hinner hhC
  subst hlinked
  refine ⟨q', T, b, pc, hq', hsub, hbs, hpc, hnd', hdec,
    fun hkeep hword hin sa hreg env henv V hV tf G hGT hG
    sym hsum hsym t₀ hfront => ?_⟩
  obtain ⟨hK, hTc⟩ := NFProgCallTreeKinds.kinds_of_linked hnd hk hsub d tr₀
  have H := hR hkeep (moduleKind m.linked d) (contractRunOf m.linked tr₀) hK hTc hword hin sa hreg
    env henv V hV tf hGT hG sym (linkRead m) hsum hsym t₀ hfront
  have H' := NFProgCallTreeEvent.RuttF.and_target H
    (fun n => NFProgCallTreeEvent.allEvT_targetTree pc sym (linkRead m) n 0 sa)
  have hword' : ∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none) :=
    fun c hc => ⟨(hword c hc).1, (hword c hc).2.1⟩
  have hty' : ∀ e₀ e₁, FrontRE m e₀ e₁ → ∀ a ∈ e₁.argTys, a = .word 64 ∨ a = .int :=
    fun e₀ e₁ h => (hty e₀ e₁ h).1
  refine NFProgCallTreeCompose.RuttF.imp (fun e₀ e₅ he => ?_) (fun e₀ e₅ he a₀ a₅ ha => ?_)
    (fun r₀ r₅ hr => NFProgCallTreeResult.resRel_of_comp hout hr) (fun _ h => h) H'
  · obtain ⟨⟨e₁, h1, e₄, h4, h5⟩, hIs⟩ := he
    exact NFProgCallTreeEvent.contractREG_of_comp hnd hk hsub hword' hty'
      ⟨e₁, h1, e₄, h4, h5, hIs⟩
  · obtain ⟨-, hIs⟩ := he
    have hC := NFProgCallTreeAnswer.compRA_of_contractRAC hnd hk hsub hword' hty hlen d tr₀ ha
    intro e₁ hF hCB
    obtain ⟨e₄, h4, h5⟩ := hCB
    obtain ⟨a₁, hFA, hrest⟩ := hC e₁ hF ⟨e₄, h4, h5, hIs⟩
    exact ⟨a₁, hFA, fun e₄' h4' h5' => hrest e₄' h4' ⟨h5', hIs⟩⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeAssembly
