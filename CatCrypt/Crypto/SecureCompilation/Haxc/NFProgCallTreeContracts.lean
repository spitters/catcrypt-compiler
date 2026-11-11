/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeAnswer

/-!
# The composed call trees of a module at the separation contracts

`NFProgCallTreeR3.ruttF_front_compileRegion` relates a source tree related by the front to the call
tree of the program of `haxToNF` to the target trees of the calling body at the compositions of the
relations of the front, the chain and the back half. At a module whose linked functions are linked
kernels with distinct names, scalar parameters and word results, at the kinds `moduleKind` of the
kernels, the run relations of their contracts and the procedure table of their summaries
(`NFProgCallTreeKinds.kinds_of_linked`), and at the linked reader `linkRead`, the compositions
pass to the relations of `R3StatementF`: the events of the target trees are calls of the linked
reader (`NFProgCallTreeEvent.allEvT_targetTree`), at which the composed event relation implies
`contractREG` (`NFProgCallTreeEvent.contractREG_of_comp`); `contractRAC` implies the composed
answer relation (`NFProgCallTreeAnswer.compRA_of_contractRAC`); and the composed relation of the
leaves implies `resRel` (`NFProgCallTreeResult.resRel_of_comp`). The source tree is then related by
`RuttF` to the target trees at `contractREG`, `contractRAC` and `resRel`
(`ruttF_contracts_compileRegion`).

## Main definitions

* `HandlerMeetsCG`, `R3StatementFG`: the target handlers meeting the separation contracts at the
  guarded event relation, and `R3StatementF` at `contractREG` in place of `contractRE`.

## Main results

* `ruttF_contracts_compileRegion`: a source tree related by the front to the call tree of the
  program of `haxToNF` is related by `RuttF` to the target trees of the calling body of a result
  of `compileRegion` on its chain, at `contractREG`, `contractRAC`, `resRel` and `srcFail`.
* `handlerMeetsCG_of_handlerMeetsC`, `r3StatementFG_of_r3StatementF`: a handler meeting the
  separation contracts meets them at the guarded event relation, and `R3StatementF` implies
  `R3StatementFG`.
* `r3fg_consequence`: from `R3StatementFG`, under every target handler meeting the separation
  contracts, a source run to a value that is not a control-flow value is read back from a target
  run.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContracts

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

/-- **The composed call trees of a module at the separation contracts.** Under the hypotheses of
    `NFProgCallTreeR3.ruttF_front_compileRegion`, at a module whose linked functions have distinct
    names and are linked kernels whose data are the linked data of `compileRegion`, at a result
    type the back half reads back, and when the leaf calls the front relates to source calls have
    word and integer arguments, as many as the parameters of the linked function, and a word
    result: every source tree related by the front to the call tree of the program of `haxToNF` is
    related by `RuttF` to the target trees of the calling body at the linked reader, at
    `contractREG`, `contractRAC`, `resRel` and `srcFail`, at the kinds `moduleKind`, the run
    relations of the contracts and the procedure table of the summaries of the kinds. -/
theorem ruttF_contracts_compileRegion {m : HaxModule} {σ : AbiLayout}
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
  obtain ⟨q', T, b, pc, hq', hsub, hbs, hpc, hR⟩ := NFProgCallTreeR3.ruttF_front_compileRegion
    hq hp h1 hcf tE htE h₂ h₃ hh₂ hh₃ hinner hhC
  subst hlinked
  refine ⟨q', T, b, pc, hq', hsub, hbs, hpc, fun hkeep hword hin sa hreg env henv V hV tf G hGT hG
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

/-! ## The statement at the guarded event relation -/

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (HandlerMeetsC)

/-- A target handler meets the separation contracts of the linked functions of `m` at the guarded
    event relation `contractREG`. -/
def HandlerMeetsCG (m : HaxModule) (h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e) :
    Prop :=
  ∀ e₁ e₂, contractREG m e₁ e₂ → contractRAC m e₁ e₂ (linkHandler m e₁) (h₂ e₂)

/-- **A handler meeting the separation contracts meets them at the guarded event relation.** At a
    call where the meaning is defined, `contractREG` is `contractRE`; where it is undefined, the
    source handler answers `none` and `contractRAC` asks nothing of the target answer. -/
theorem handlerMeetsCG_of_handlerMeetsC {m : HaxModule}
    {h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e} (h : HandlerMeetsC m h₂) :
    HandlerMeetsCG m h₂ := by
  intro e₁ e₂ he
  obtain ⟨hc, l, hl, hpre, ha⟩ := he
  have hlh : linkHandler m e₁ = l.sem (LinkCall.args e₁) := by
    simp only [linkHandler, hl]
    rfl
  cases hs : l.sem (LinkCall.args e₁) with
  | some v => exact h e₁ e₂ ⟨hc, l, hl, hpre (by rw [hs]; rfl), ha⟩
  | none =>
    refine ⟨l, hl, ?_, fun v hv => ?_⟩
    · show linkHandler m e₁ = _
      rw [hlh]
    · have : linkHandler m e₁ = some v := hv
      rw [hlh, hs] at this
      cases this

/-- **The call trees of `compileA` related at the guarded event relation.** The statement
    `R3StatementF` with `contractREG`, which requires the precondition of a linked function at the
    entry of a call only where its meaning is defined at the arguments, in place of
    `contractRE`. -/
def R3StatementFG : Prop :=
  ∀ (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)), compileA m σ fname = some (P, bytes) →
    (m.linked.map (·.name)).Nodup → (∀ l ∈ m.linked, LinkedKernel l) →
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      X86Backend.LprogBytesDecode.decodeLprog bytes =
          some (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel,
          RuttF (linkHandler m) (contractREG m) (contractRAC m) (resRel σ sa) srcFail
            (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel
              m.entry.erase env)
            (fun fuelT => targetTree aMachine pc sym (linkRead m) fuelT 0 sa)

/-- **`R3StatementF` implies `R3StatementFG`**: `contractRE` implies `contractREG`. -/
theorem r3StatementFG_of_r3StatementF (h : NFProgCallTreeCalls.R3StatementF) : R3StatementFG := by
  intro m σ fname P bytes hc hnd hk
  obtain ⟨pc, Q, sym, hd, hrel⟩ := h m σ fname P bytes hc hnd hk
  exact ⟨pc, Q, sym, hd, fun sa hreg env henv fuelC fuel =>
    NFProgCallTreeCompose.RuttF.imp
      (fun _ _ he => NFProgCallTreeContract.contractREG_of_contractRE he)
      (fun _ _ _ _ _ ha => ha) (fun _ _ h => h) (fun _ h => h)
      (hrel sa hreg env henv fuelC fuel)⟩

/-- **The consequence of `R3StatementFG`**: from a source tree and the target family related by
    `RuttF` at the guarded separation contracts, under every target handler meeting the separation
    contracts, a source run under the meanings of the linked functions to a value that is not a
    control-flow value is read back by `σ` from the leaf of the target family at some fuel. -/
theorem r3fg_consequence (m : HaxModule) (σ : AbiLayout) (sa : AState)
    (h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e) (hh : HandlerMeetsC m h₂)
    {t₁ : CallTree linkSig (Outcome × Env)} {T : Nat → CallTree (kSig AState) (Option AState)}
    (hr : RuttF (linkHandler m) (contractREG m) (contractRAC m) (resRel σ sa) srcFail t₁ T)
    {v : Value} {env' : Env} (hv : interp (linkHandler m) t₁ = (.val v, env'))
    (hcf : v.isControlFlow = false) :
    ∃ fuelT s', interp h₂ (T fuelT) = some s' ∧ σ.ResultOf sa s' v := by
  rcases NFProgCallTreeCalls.interp_ruttF h₂ (handlerMeetsCG_of_handlerMeetsC hh) hr with
    hf | ⟨n, hR⟩
  · rw [hv] at hf
    have := hf v rfl
    rw [hcf] at this
    exact absurd this (by simp)
  · obtain ⟨s', hs', hres⟩ := hR v (by rw [hv]) hcf
    exact ⟨n, s', hs', hres⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContracts
