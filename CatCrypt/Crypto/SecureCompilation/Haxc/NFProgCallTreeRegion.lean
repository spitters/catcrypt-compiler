/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract

/-!
# The back half at a result of `regionBack`

`NFProgCallTreeRefBack.ruttF_regionRef_word` relates the call tree of a program of `jasminDialect`
to the target trees of its calling body from the parts of the region export: the export, the webs,
the printed body and its gate. A result of `regionBack` on a program with a `call` has these parts
(`RegionLinkCall.regionBack_spec_tab`), the program passes the gate `regionExportableB` and is its
own legalisation, so the relation holds at every result of `regionBack`
(`ruttF_regionBack_word`), with the conditions on the table of callees, the summaries, the events
and the symbol map left to the caller.

The chain `extChain` followed by `narrowPrep` relates the call tree of the program of
`nfDialect` to the tree `mfTree` of the narrowed program
(`NFProgCallTreeCompose.ruttS_extChain_narrowPrep`), which is the call tree with call events of the
program `regionBack` compiles when no callee is an inner head (`mfTree_eq_treeAt`), up to the cast
of its context, which the widening keeps. Composed with the back half, the call tree of the
program of `nfDialect` is related by `RuttF` to the target trees of the calling body of every
result of `compileRegion` on the chain of the program (`ruttF_extChain_compileRegion`).

## Main results

* `ruttF_regionBack_word`: the call tree of a program with a `call` against the target trees of
  the calling body of a result of `regionBack` at a table of word callees.
* `mfTree_castProg`: the tree `mfTree` of a program cast along an equal context is the tree of the
  program at the heterogeneously equal valuation.
* `ruttF_extChain_compileRegion`: the call tree of the program of `nfDialect` against the target
  trees of the calling body of a result of `compileRegion` on its chain.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall treeAt pureReader
  eventEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack (BackRE BackRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree innerHead)

/-- **The back half at a result of `regionBack`.** For a result of `regionBack σ a p linked` on a
    program `p` with a `call`, the result type is a word array, the back half finds a table `T`
    among the linked data, and a printed body `b` with the bytes of the result and the calling
    body `pc`, such that the call tree of `p` from a valuation `σ` reads off an entry state is
    related by `RuttF` to the target trees of `pc` from that state, at the event relation
    `BackRE T` and the answer relation `BackRA PT X`, under the conditions of
    `NFProgCallTreeRefBack.ruttF_regionRef_word`: the kinds and the runs of the callees, the
    summaries of `PT`, word callees, the events of the tree, the summary condition and the symbol
    map. -/
theorem ruttF_regionBack_word {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData} {P : Lprog}
    {bytes : List (BitVec 8)} (h : regionBack σ a p linked = some (P, bytes))
    (hcf : p.callFree = false) :
    ∃ (T : CalleeTab) (b : Lcmd) (pc : List RInstr),
      T.fns.Sublist linked ∧ calleeBytes (some T) b = some bytes ∧ calleeProg T b = some pc
      ∧ callsToAny T.names p = true
      ∧ ∀ (kind : String → CalleeKind) (X : String → CalleeRun),
        (∀ c ∈ T.fns, (kind c.name).Top c ∧ (kind c.name).Spec (X c.name)) →
        ∀ {PT : LprogIsa.ProcTable}, (∀ c ∈ T.fns, PT c.name = some (kind c.name).summary) →
        (∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none)
          ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true) →
        ∀ (sa : AState), σ.Regions sa → ∀ (V : Ctxt.Valuation Γ), AbiValOf σ sa V →
        ∀ (fuel : Nat) {G : NFCall jasminDialect → Prop}, (∀ e, G e → EvOK T e) →
        AllEv G (treeAt pureReader eventEnv fuel p V) →
        ∀ (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
          (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value),
        (∀ ev, G ev → ∃ pr, PT ev.name = some pr ∧ pr.arity = ev.argTys.length
          ∧ pr.arrArgs = arrArgsOf ev.argTys
          ∧ (pr.result (wordsOf ev.args) = none → h₁ ev = none)) →
        (∀ f ∈ T.names, sym (pc.length + T.entryIdx (T.symPos f)) = f) →
        RuttF h₁ (BackRE T) (BackRA PT X) (NFProgCallTreeExt.OutRel fun v sA =>
            σ.ResultOf sa sA (denVal t
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
          (fun o => o = none) (treeAt pureReader eventEnv fuel p V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨T, r0, hr0, hcT, ⟨w, m, rfl⟩, hB, r, b, cert, hwb, hbs, hg, -, -⟩ :=
    regionBack_spec_tab h hcf
  have hp : RegionExportable p := regionExportableB_sound hB
  obtain ⟨-, -, ds, pc, -, -, -, hpc, -⟩ := calleeBytes_tab hbs
  refine ⟨T, b, pc, regionCallee_sublist hcT, hbs, hpc, callsToAny_of_regionCallee hr0 hcT,
    fun kind X hK PT hTc hword sa hreg V hV fuel G hGT hG h₁ sym rd hsum hsym => ?_⟩
  obtain ⟨pc', ds', hpc', -, hR⟩ := NFProgCallTreeRefBack.ruttF_regionRef_word (a := a) hbs hg rfl
    kind X hK hTc sa hreg hp hr0 hwb hGT V hV fuel hG hword
  rw [hpc] at hpc'
  obtain rfl := Option.some.inj hpc'
  exact hR h₁ sym rd hsum hsym

/-- A leaf related by `OutRel` to the failed leaf `none` is the failed leaf. -/
theorem eq_none_of_outRel {α β : Type} {R : α → β → Prop} {o : Option α} {o' : Option β}
    (h : NFProgCallTreeExt.OutRel R o o') (h' : o' = none) : o = none := by
  cases o with
  | none => rfl
  | some a =>
    obtain ⟨b, hb, -⟩ := h a rfl
    rw [h'] at hb
    cases hb

/-- **A program cast along an equal context has the tree of the program**, at heterogeneously
    equal valuations. -/
theorem mfTree_castProg (fuel : Nat) {Γ Γ' : Ctxt jasminDialect} {ts : List JasminTy}
    (h : Γ = Γ') (q : NFProg jasminDialect Γ ts) (W : Ctxt.Valuation Γ')
    (W' : Ctxt.Valuation Γ) (hW : W ≍ W') :
    mfTree fuel (NarrowWords.castProg h rfl q) W = mfTree fuel q W' := by
  subst h
  cases hW
  rfl

section Chain

open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (tableOf entryCtx EntryVals)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig leafHandler linkReader
  OutRel ExtRE ExtRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt (MapRE MapRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (CompRE CompRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montEnv)

/-- The event relation of the chain `extChain` followed by `narrowPrep`. -/
abbrev ChainRE : leafSig.Event → (nfCallSig jasminDialect).Event → Prop :=
  CompRE (CompRE ExtRE (MapRE catToJasmin fun x => ctTransTy x))
    (MapRE NarrowWords.widenP fun x => NarrowWords.transTy x)

/-- The answer relation of the chain `extChain` followed by `narrowPrep`. -/
abbrev ChainRA : (e₁ : leafSig.Event) → (e₂ : (nfCallSig jasminDialect).Event) →
    leafSig.Resp e₁ → (nfCallSig jasminDialect).Resp e₂ → Prop :=
  CompRA (CompRE ExtRE (MapRE catToJasmin fun x => ctTransTy x))
    (MapRE NarrowWords.widenP fun x => NarrowWords.transTy x)
    (CompRA ExtRE (MapRE catToJasmin fun x => ctTransTy x) ExtRA
      (MapRA catToJasmin fun x => ctTransTy x))
    (MapRA NarrowWords.widenP fun x => NarrowWords.transTy x)

/-- The leaf relation of the chain `extChain` followed by `narrowPrep` at the result type `t`. -/
abbrev ChainRR (t : NfTy) : Option (Ctxt.Valuation (d := nfDialect) [t]) →
    Option (Ctxt.Valuation (d := jasminDialect) ([mapTy (catTy t)].map NarrowWords.wideTy)) →
    Prop :=
  Relation.Comp
    (Relation.Comp (OutRel (VRelL [t]))
      (OutRel fun x y => y = transArgs catToJasmin.mapTy (fun x => ctTransTy x) x))
    (OutRel fun x y => y = transArgs NarrowWords.widenP.mapTy (fun x => NarrowWords.transTy x) x)

/-- **The call tree of the program of `nfDialect` against the target trees of the calling body of
    `compileRegion`.** Let the chain `extChain D` return `p` on the program `p0` of `nfDialect` at
    the entry context of `σ`, and `compileRegion` return a result on `p`, which has a `call`. There
    are the narrowed program `q`, the table `T` of callees, the printed body `b` with the bytes of
    the result and the calling body `pc`, such that from every entry state `sa` satisfying
    `σ.Regions` and every valuation of the entry read off a source environment of `sa`, the call
    tree of `p0` at `linkReader`, at a tree call environment in which every call of a procedure
    fails, is related by `RuttF` to the target trees of `pc` from `sa`, at the compositions of the
    relations of the chain and of the back half, under the conditions of both: the handlers of
    the intermediate trees, no inner head among the callees, and the conditions of
    `ruttF_regionBack_word` at the call tree of the program `regionBack` compiles. -/
theorem ruttF_extChain_compileRegion {bi : _root_.Hax.Builtins} (hbi : SubTable bi)
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
  obtain ⟨T, b, pc, hsub, hbs, hpc, hcalls, hR⟩ := ruttF_regionBack_word hb hcf'
  refine ⟨q, T, b, pc, hq, hsub, hbs, hpc, fun kind X hK PT hTc hword hin sa hreg env henv V hV
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

end Chain

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion
