/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerInstance

/-!
# Robust compilation over the handlers of the linked functions from a source run

`HandlerRC` bounds the robust compilation of the calling body by `ε + δ`, with `δ` a bound of the
failure weight of the source read-back. A run of the source relation `HaxModule.Runs` at the
table `hax64WExit` from the entry state `narrowEntry m σ sa` fixes a source environment, a callee
fuel and a fuel at which the call tree of the entry, interpreted under the handler of the linked
functions, is the point mass at the leaf of the run (`NFCallTree.interp_nfTree_table`). There the
source read-back returns the value of the run and does not fail, so `δ = 0`.

## Main results

* `readBack_srcRead_of_runs`: from a source run, an environment and fuels at which the source
  read-back is the point mass at the value of the run.
* `HandlerRC.of_runs`: from a source run, robust compilation at the bound `ε` of the failure
  weight of the target alone, and at `0` for a target that does not fail.
* `haxc_rcH_of_runs`: `haxc_rcH` with the conclusion `HandlerRC.of_runs` at every source run.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerSourceRun

open scoped ENNReal
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Crypto.RCGate
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
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (tableOf entryCtx entryEnvOf crateBi)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn hax64WExit)
open CatCrypt.Crypto.Hax.NFInline (crateOp)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv nfCallSig)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig leafHandler)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt (MapRE MapRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (ChainRE ChainRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeModule (GoodEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodCall
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerInstance
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open _root_.Hax

/-- **The source read-back of a source run.** A run of the source relation `HaxModule.Runs` at
    the table `hax64WExit` from the state `sa` to the value `v` gives an environment `env` that
    `σ` reads off `sa`, a callee fuel `fuelC` and a fuel `fuel` at which the source read-back of
    the call tree of the entry, interpreted under the handler of the linked functions, is the
    point mass at `v`. -/
theorem readBack_srcRead_of_runs {m : HaxModule} {σ : AbiLayout} {sa : AState} {v : Value}
    (h : HaxModule.Runs hax64WExit σ m sa v) :
    ∃ env fuelC fuel, σ.EnvOf sa env ∧
      readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
        (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)) = SPComp.pure v := by
  obtain ⟨env, fuel, fuelC, env', hE, hrun, hcf⟩ := h
  refine ⟨env, fuelC, fuel, hE, ?_⟩
  rw [readBack, interpSP_pure, SPComp.pure_bind, interp_nfTree_table, hrun]
  simp [srcRead, hcf, optSP]

/-- **The source read-back of a source run does not fail**: at the environment and fuels of
    `readBack_srcRead_of_runs`, its failure weight is `0` at every heap. -/
theorem readBack_srcRead_none_of_runs {m : HaxModule} {σ : AbiLayout} {sa : AState} {v : Value}
    (h : HaxModule.Runs hax64WExit σ m sa v) :
    ∃ env fuelC fuel, σ.EnvOf sa env ∧
      ∀ s, readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
        (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)) s none = 0 := by
  obtain ⟨env, fuelC, fuel, hE, hrb⟩ := readBack_srcRead_of_runs h
  refine ⟨env, fuelC, fuel, hE, fun s => ?_⟩
  rw [hrb]
  simp [SPComp.pure, SDistr.pure_apply_none]

/-- **Robust compilation over the handlers of the linked functions from a source run.** Let
    `HandlerRC` hold at the calling body `pc`, and let the source relation run from the entry
    state `narrowEntry m σ sa` of an entry state `sa` of the domain to the value `v`. Then there
    are a source environment `σ` reads off `narrowEntry m σ sa` and fuels at which the source
    read-back does not fail, robust compilation holds over the coupled handlers at every bound
    `ε` of the failure weight of the target, and at `0` when the target does not fail. -/
theorem HandlerRC.of_runs {m : HaxModule} {σ : AbiLayout} {pc : List RInstr}
    {sym : Nat → String} (h : HandlerRC m σ pc sym) {sa : AState} (hs : σ.Regions sa)
    {v : Value} (hr : HaxModule.Runs hax64WExit σ m (narrowEntry m σ sa) v) :
    ∃ env fuelC fuel, σ.EnvOf (narrowEntry m σ sa) env ∧
      (∀ s, readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
        (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)) s none = 0) ∧
      (∀ ε : ℝ≥0∞,
        (∀ h₂, HandlerCoupledCG m eqPre h₂ → ∀ s, interpTargetω m pc sym sa h₂ s none ≤ ε) →
        RobustCompilationH (HandlerCoupledCG m eqPre) ε
          (fun h₂ (_ : Unit) => readBack (fun s' => some (σ.result.read sa s'))
            (interpTargetω m pc sym sa h₂))
          (fun _ (_ : Unit) => readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
            (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)))) ∧
      ((∀ h₂, HandlerCoupledCG m eqPre h₂ → ∀ s, interpTargetω m pc sym sa h₂ s none = 0) →
        RobustCompilationH (HandlerCoupledCG m eqPre) 0
          (fun h₂ (_ : Unit) => readBack (fun s' => some (σ.result.read sa s'))
            (interpTargetω m pc sym sa h₂))
          (fun _ (_ : Unit) => readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
            (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)))) := by
  obtain ⟨env, fuelC, fuel, hE, h0⟩ := readBack_srcRead_none_of_runs hr
  refine ⟨env, fuelC, fuel, hE, h0, fun ε hε => ?_, fun hl => h.zero hs hE fuelC fuel hl h0⟩
  simpa using h sa hs env hE fuelC fuel ε 0 hε fun s => (h0 s).le

/-- **Robust compilation from the source runs** at the calling body `pc`: at every entry state
    `sa` of the domain and every value `v` to which the source relation runs from
    `narrowEntry m σ sa`, the conclusion of `HandlerRC.of_runs`. -/
def HandlerRCRuns (m : HaxModule) (σ : AbiLayout) (pc : List RInstr) (sym : Nat → String) :
    Prop :=
  ∀ (sa : AState), σ.Regions sa → ∀ v, HaxModule.Runs hax64WExit σ m (narrowEntry m σ sa) v →
    ∃ env fuelC fuel, σ.EnvOf (narrowEntry m σ sa) env ∧
      (∀ s, readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
        (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)) s none = 0) ∧
      (∀ ε : ℝ≥0∞,
        (∀ h₂, HandlerCoupledCG m eqPre h₂ → ∀ s, interpTargetω m pc sym sa h₂ s none ≤ ε) →
        RobustCompilationH (HandlerCoupledCG m eqPre) ε
          (fun h₂ (_ : Unit) => readBack (fun s' => some (σ.result.read sa s'))
            (interpTargetω m pc sym sa h₂))
          (fun _ (_ : Unit) => readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
            (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)))) ∧
      ((∀ h₂, HandlerCoupledCG m eqPre h₂ → ∀ s, interpTargetω m pc sym sa h₂ s none = 0) →
        RobustCompilationH (HandlerCoupledCG m eqPre) 0
          (fun h₂ (_ : Unit) => readBack (fun s' => some (σ.result.read sa s'))
            (interpTargetω m pc sym sa h₂))
          (fun _ (_ : Unit) => readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
            (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env))))

/-- `HandlerRC` gives robust compilation from the source runs. -/
theorem HandlerRC.runs {m : HaxModule} {σ : AbiLayout} {pc : List RInstr} {sym : Nat → String}
    (h : HandlerRC m σ pc sym) : HandlerRCRuns m σ pc sym :=
  fun _ hs _ hr => HandlerRC.of_runs h hs hr

/-- **Robust compilation over the handlers of the linked functions from the source runs, for the
    hax compiler.** Under the hypotheses of `haxc_rcH`, the bytes of `compileA` decode to a
    calling body `pc` followed by the shifted linked code `Q`, the decoded program satisfies the
    gate conclusion and robust compilation at `0` of `haxc_rc_proved_all`, and `HandlerRCRuns`
    holds at `pc`: at every entry state of the domain from whose entry state `narrowEntry` the
    source relation runs, there are a source environment and fuels at which the source read-back
    does not fail, and robust compilation holds over the coupled handlers at every bound `ε` of
    the failure weight of the target, and at `0` when the target does not fail. -/
theorem haxc_rcH_of_runs (s : _root_.Hax.FnSecrecy) {m : HaxModule} {σ : AbiLayout}
    {fname : String}
    {P : Lprog} {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none)
    (hcf : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]), haxToNF σ m = some q →
      (extChain (linkedDecls m hax64WExit) _ q.1).run q.2 = some p → p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (x : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs x = .ret none)
    (h₂ : ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e)
    (h₃ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hh₂ : ∀ e₁ e₂, NFProgCallTreeExt.ExtRE e₁ e₂ → NFProgCallTreeExt.ExtRA e₁ e₂
      (leafHandler (tableOf (m.linkTable hax64WExit)) e₁) (h₂ e₂))
    (hh₃ : ∀ e₁ e₂, MapRE catToJasmin (fun x => ctTransTy x) e₁ e₂ →
      MapRA catToJasmin (fun x => ctTransTy x) e₁ e₂ (h₂ e₁) (h₃ e₂))
    (hinner : ∀ (f : String) (as rs : List JasminTy) (x : Ctxt.Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₃ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    (hhC : ∀ e₁ e₂, ChainRE e₁ e₂ → ChainRA e₁ e₂
      (leafHandler (tableOf (m.linkTable hax64WExit)) e₁) (h₃ e₂))
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (hword : ∀ c ∈ m.linked.filterMap LinkedFn.calleeData, (∃ r, c.res = .reg r)
      ∧ c.arrArgs = (fun _ => none) ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true)
    (hin : ∀ l ∈ m.linked, innerHead l.name = false) (d : CalleeKind) (tr₀ : List CTLeak)
    (hev : ∀ (T : CalleeTab), T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData) →
      ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
        (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)])
        (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
          ([mapTy (catTy q.1)].map NarrowWords.wideTy)), haxToNF σ m = some q →
      (extChain (linkedDecls m hax64WExit) _ q.1).run q.2 = some p →
      NarrowWords.narrowPrep p = some q' →
      ∀ (tf : Nat) (V : Ctxt.Valuation (entryCtx (abiEntry σ))),
        AllEv (GoodEv m d T h₃) (mfTree tf q' (NarrowWords.mapVal (ctMapValD (mapVal V)))))
    (hspine : NFCallTreeInlineSpine.spineArgsOk m.entry.erase = true)
    (hfs : ∀ f ∈ m.fns, NFCallTreeInlineSpine.spineArgsOk f.texpr.erase = true)
    (hint : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg nfDialect (entryCtx (abiEntry σ)) [q.1]), haxToNF σ m = some q →
      nfSrcProgC (m.prepared nfBody ++ m.linkedFns) σ (bindConsts σ.consts m.entry)
        = some ⟨q.1, p⟩ → ∀ o, p.HasOp o → NFCallTreeFrontModule.OpOk IntArgFree o)
    (hgood : ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → NFCallTreeFrontModule.OpOk (NFCallTreeFrontModule.GoodCall m) o)
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true) (F fuelC : Nat)
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry (pairStage m σ).2))),
      (pairStage m σ).2.Regions sa → AbiValOf (pairStage m σ).2 sa
        (ctMapValD (mapVal V)) →
      ∃ v env', (denote' (crateBi ((pairStage m σ).1.prepared nfBody)
        ((pairStage m σ).1.linkTable hax64WExit) fuelC (pairStage m σ).1.depth) F
        (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry))).run
          (entryEnvOf (abiEntry (pairStage m σ).2) V) = (.val v, env'))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      (GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ)
          (haxcTgtRes σ (pc ++ shiftProg pc.length Q)) (haxcLeakRun (pc ++ shiftProg pc.length Q)) ∧
        RobustCompilation 0
          (realObs (Pre := σ.Regions) (srcRun := haxcSrcRun m σ)
            (leakRun := haxcLeakRun (pc ++ shiftProg pc.length Q))
            (haxcTgtRes σ (pc ++ shiftProg pc.length Q)))
          (idealObs (pubOf σ))) ∧
      HandlerRCRuns m σ pc sym := by
  obtain ⟨pc, Q, sym, hd, hg, hH⟩ := haxc_rcH s hc hnd hk hn hpt hcf tE htE h₂ h₃ hh₂ hh₃ hinner
    hhC hpar hword hin d tr₀ hev hspine hfs hint hgood hck F fuelC hterm hL hnds
  exact ⟨pc, Q, sym, hd, hg, HandlerRC.runs hH⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerSourceRun
