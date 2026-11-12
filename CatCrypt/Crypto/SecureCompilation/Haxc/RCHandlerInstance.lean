/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
public import CatCrypt.Crypto.SecureCompilation.Haxc.RCInstance
public import CatCryptCore.Crypto.RCHandler

/-!
# Robust compilation over the handlers of the linked functions

For a result of `compileA`, the source call tree of the entry and the target trees of the calling
body are related by `RuttF` at the separation contracts (`r3FG_of_shape_int`). Interpreted in
`SPComp` under a target handler coupled with the meanings of the linked functions on these
contracts (`HandlerCoupledCG`), the values read back from the source and from the target are at
statistical distance at most the failure weight `ε` of the target plus the failure weight `δ` of
the source read-back (`sdist_readBack_contract`). This module states the consequence as robust
compilation over the class of such handlers (`RobustCompilationH`), together with the gate
conclusion and the robust compilation of `haxc_rc_proved_all`.

## Main definitions

* `HandlerRC`: robust compilation over the handlers meeting the separation contracts, at every
  entry state of the domain, every source environment, every fuel, and every pair of bounds of the
  failure weights.

## Main results

* `HandlerRC.zero`: at bound `0` when the target interpretation and the source read-back do not
  fail.
* `haxc_rcH`: for a result of `compileA` under the hypotheses of `r3FG_of_shape_int` and
  `haxc_rc_proved_all`, the decoding of the bytes, the conclusion of `haxc_rc_proved_all` and
  `HandlerRC`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerInstance

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
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (contractRAC)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeModule (GoodEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSP
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodCall
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open _root_.Hax

/-- **Robust compilation over the handlers meeting the separation contracts.** At every entry
    state `sa` of the domain of `σ`, every source environment `env` of the narrowed entry, and every
    fuel, let `ε` bound the failure weight of the target interpretation under every handler
    coupled at equal heaps with the meanings of the linked functions of `m` on the separation
    contracts, and `δ` the failure weight of the source read-back. Then replacing the value the
    source run reads back (`srcRead`) by the value `σ` reads back from the return state of the
    calling body `pc` is robust compilation at `ε + δ` over this class of handlers. -/
def HandlerRC (m : HaxModule) (σ : AbiLayout) (pc : List RInstr) (sym : Nat → String) : Prop :=
  ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
    ∀ (fuelC fuel : Nat) (ε δ : ℝ≥0∞),
      (∀ h₂, HandlerCoupledCG m eqPre h₂ → ∀ s, interpTargetω m pc sym sa h₂ s none ≤ ε) →
      (∀ s, readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
        (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)) s none ≤ δ) →
      RobustCompilationH (HandlerCoupledCG m eqPre) (ε + δ)
        (fun h₂ (_ : Unit) => readBack (fun s' => some (σ.result.read sa s'))
          (interpTargetω m pc sym sa h₂))
        (fun _ (_ : Unit) => readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
          (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)))

/-- **Robust compilation at bound `0`** over the handlers meeting the separation contracts, when
    the target interpretation does not fail under any of them and the source read-back does not
    fail. -/
theorem HandlerRC.zero {m : HaxModule} {σ : AbiLayout} {pc : List RInstr} {sym : Nat → String}
    (h : HandlerRC m σ pc sym) {sa : AState} (hs : σ.Regions sa) {env : Env}
    (he : σ.EnvOf (narrowEntry m σ sa) env) (fuelC fuel : Nat)
    (hl : ∀ h₂, HandlerCoupledCG m eqPre h₂ → ∀ s, interpTargetω m pc sym sa h₂ s none = 0)
    (hsrc : ∀ s, readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
        (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)) s none = 0) :
    RobustCompilationH (HandlerCoupledCG m eqPre) 0
      (fun h₂ (_ : Unit) => readBack (fun s' => some (σ.result.read sa s'))
        (interpTargetω m pc sym sa h₂))
      (fun _ (_ : Unit) => readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
        (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env))) := by
  simpa using h sa hs env he fuelC fuel 0 0 (fun h₂ hh s => (hl h₂ hh s).le) fun s => (hsrc s).le

/-- **Robust compilation over the handlers of the linked functions, for the hax compiler.** Let
    `compileA` compile the module `m` to `(P, bytes)` under the hypotheses of
    `r3FG_of_shape_int` and those of `haxc_rc_proved_all`, among them the termination `hterm` of
    the source run. The bytes decode to a calling body `pc` followed by the shifted linked code
    `Q`; the decoded program satisfies the gate conclusion and robust compilation at `0` of
    `haxc_rc_proved_all`; and `HandlerRC` holds at `pc`: robust compilation at `ε + δ` over the
    target handlers coupled with the meanings of the linked functions on the separation
    contracts, for bounds `ε` of the failure weight of the target and `δ` of the failure weight
    of the source read-back. -/
theorem haxc_rcH (s : _root_.Hax.FnSecrecy) {m : HaxModule} {σ : AbiLayout} {fname : String}
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
      HandlerRC m σ pc sym := by
  obtain ⟨pc, Q, sym, hd, hrel⟩ := r3FG_of_shape_int hc hnd hk hn hpt hcf tE htE h₂ h₃ hh₂ hh₃
    hinner hhC hpar hword hin d tr₀ hev hspine hfs hint hgood
  refine ⟨pc, Q, sym, hd, haxc_rc_proved_all s m σ fname P bytes hc hck F fuelC hterm hL hnds hd
    hnd hk, ?_⟩
  intro sa hsa env henv fC fuel ε δ hε hδ
  refine (robustCompilationH_iff_sdist _ _ _ _).mpr fun h hh => ?_
  rw [sdist_sym]
  exact sdist_readBack_contract hh (hrel sa hsa env henv fC fuel) (hε h hh) hδ

end CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerInstance
