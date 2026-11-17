/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RCInstance

/-!
# Robust compilation of the hax compiler with termination per entry state

The joint theorems `haxc_gate_proved_all` and `haxc_rc_proved_all` (`Haxc/RCInstance.lean`)
take the run hypothesis `hterm` at one pair of fuels `F fuelC`, uniform over the entry states.
The hypothesis feeds only the constant-time conjunct, through the termination of the
translation (`haxToNF_leakRunL`), whose conclusion holds at every target fuel from some fuel
on and so depends on no source fuel. The theorems of this module take the run hypothesis per
entry state: for each entry state from which the module has a source run, and each valuation
the layout reads off it, the body the front reads runs to a value at some pair of fuels of
that state. The constant-time argument `NFEntry.compileR_ct` combines the two target fuels of
a pair of states by their maximum.

## Main results

* `ct_of_compileARegion_perState`, `haxc_ct_proved_all_perState` — constant time of the
  bytes of `compileARegion` and `compileA` under the run hypothesis per entry state.
* `haxc_gate_proved_all_perState`, `haxc_rc_proved_all_perState` — the gate conclusion and
  robust compilation for a result of `compileA`, with the run hypothesis per entry state that
  has a source run.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.RCGate
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnvOf crateBi)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel)
open _root_.Hax (Value denote')
open CatCrypt.Crypto.Hax (hax64WExit HaxModule)

/-- **Constant time of the bytes of `compileARegion` with termination per entry state.** It is
    `ct_of_compileARegion` with the run hypothesis taken at a pair of fuels `F fuelC` chosen
    for each entry state and valuation: `haxToNF_leakRunL` at that pair gives termination of
    the translation at every target fuel from some fuel on, which is the termination premise
    of `NFEntry.compileR_ct`. -/
theorem ct_of_compileARegion_perState (s : _root_.Hax.FnSecrecy) (m : HaxModule)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileARegion m σ fname = some (P, bytes)) (Pre : AState → Prop)
    (hct : HaxToNFCTLOn s σ m (fun V => ∃ sa, σ.Regions sa ∧ Pre sa ∧
      AbiValOf σ sa (VIR.DialectToJasminComCorrect.ctMapValD
        (CatCrypt.Crypto.Hax.NFToCat.mapVal V))))
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry σ))), σ.Regions sa →
      Pre sa → AbiValOf σ sa
        (VIR.DialectToJasminComCorrect.ctMapValD (CatCrypt.Crypto.Hax.NFToCat.mapVal V)) →
      ∃ F fuelC v env', (denote' (crateBi (m.prepared nfBody) (m.linkTable hax64WExit) fuelC
        m.depth) F (nfBody (bindConsts σ.consts m.entry))).run (entryEnvOf (abiEntry σ) V) =
          (.val v, env'))
    (hL : PubLabelsOK σ (mapLabels (nfLabels s (abiEntry σ))))
    (hnds : σ.envNames.Nodup) {prog : List RInstr} (hd : decodeLprog bytes = some prog)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ Pre s₁ ∧ Pre s₂
        ∧ (∃ v, haxRunsW σ m s₁ v) ∧ (m.linked = [] ∨ ∃ v, haxRunsW σ m s₂ v))
      (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') := by
  have hq' : ∀ q, haxEntry.toNF σ m = some q → ∀ l ∈ m.linked, linkNameOk l.name = true :=
    fun q hq => (haxToNF_eq_some hq).2.2.1
  exact haxEntry.compileR_ct s m σ fname P bytes hc 0 Pre
    (fun q hq => subTable_linkBi _ CatCrypt.Crypto.Hax.hax64WExit_subTable
      fun l hl => not_catName_of_linkNameOk (hq' q hq l hl))
    (fun q hq => linkedDecls_ne_index (hq' q hq) _) hct
    (fun q hq sa V hR hP hV => by
      obtain ⟨F, fuelC, h⟩ := hterm sa V hR hP hV
      exact haxToNF_leakRunL σ F fuelC hq V h)
    hL hnds hd hnd hk

/-- **Constant time of the bytes of `compileA` with termination per entry state.** It is
    `haxc_ct_proved_all` with the run hypothesis taken at a pair of fuels chosen for each
    entry state and valuation, through `ct_of_compileARegion_perState` at the pair stage. -/
theorem haxc_ct_proved_all_perState (s : _root_.Hax.FnSecrecy) (m : HaxModule)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes)) (Pre : AState → Prop)
    (hct : HaxToNFCTLOn s (pairStage m σ).2 (pairStage m σ).1 (fun V => ∃ sa,
      (pairStage m σ).2.Regions sa ∧ Pre sa ∧
      AbiValOf (pairStage m σ).2 sa (VIR.DialectToJasminComCorrect.ctMapValD
        (CatCrypt.Crypto.Hax.NFToCat.mapVal V))))
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry (pairStage m σ).2))),
      (pairStage m σ).2.Regions sa → Pre sa → AbiValOf (pairStage m σ).2 sa
        (VIR.DialectToJasminComCorrect.ctMapValD (CatCrypt.Crypto.Hax.NFToCat.mapVal V)) →
      ∃ F fuelC v env', (denote' (crateBi ((pairStage m σ).1.prepared nfBody)
        ((pairStage m σ).1.linkTable hax64WExit) fuelC (pairStage m σ).1.depth)
        F (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry))).run
          (entryEnvOf (abiEntry (pairStage m σ).2) V) = (.val v, env'))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup) {prog : List RInstr}
    (hd : decodeLprog bytes = some prog)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ Pre s₁ ∧ Pre s₂
        ∧ (∃ v, haxRuns σ m s₁ v) ∧ (m.linked = [] ∨ ∃ v, haxRuns σ m s₂ v))
      (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') := by
  have hl := pairStage_linked m σ
  have hc' : compileARegion (pairStage m σ).1 (pairStage m σ).2 fname = some (P, bytes) := hc
  have hR := pairStage_regions m σ
  have hA := pairStage_pubAgree m σ
  have hrun : ∀ {sa v}, haxRuns σ m sa v →
      ∃ x, haxRunsW (pairStage m σ).2 (pairStage m σ).1 sa x := fun h => by
    obtain ⟨x, hx, -⟩ := haxRuns_pairStage h
    exact ⟨x, hx⟩
  rintro s₁ s₂ t₁ t₂ ⟨hag, h₁, h₂, hP₁, hP₂, ⟨v, hr⟩, hr₂⟩ hb₁ hb₂
  refine ct_of_compileARegion_perState s _ _ fname P bytes hc' Pre hct hterm hL hnds hd
    (hl ▸ hnd) (hl ▸ hk) s₁ s₂ t₁ t₂
    ⟨(hA s₁ s₂).2 hag, (hR s₁).2 h₁, (hR s₂).2 h₂, hP₁, hP₂, hrun hr, ?_⟩ hb₁ hb₂
  rcases hr₂ with h | ⟨v₂, h⟩
  · exact .inl (hl.trans h)
  · exact .inr (hrun h)

/-- **The gate conclusion of `compileA` with termination per entry state.** It is
    `haxc_gate_proved_all` with the uniform run hypothesis replaced by one per entry state:
    for every entry state satisfying the regions of the pair stage from which the module has a
    source run (`haxRuns σ m`), and every valuation the layout of the stage reads off it, the
    body the front reads runs to a value at some pair of fuels `F fuelC` of that state and
    valuation. Constant time is `haxc_ct_proved_all_perState` at the precondition that the
    module has a source run, which the constant-time conjunct of the gate conclusion supplies
    for both states. -/
theorem haxc_gate_proved_all_perState (s : _root_.Hax.FnSecrecy) (m : HaxModule)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true)
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry (pairStage m σ).2))),
      (pairStage m σ).2.Regions sa → (∃ v, haxRuns σ m sa v) → AbiValOf (pairStage m σ).2 sa
        (VIR.DialectToJasminComCorrect.ctMapValD (CatCrypt.Crypto.Hax.NFToCat.mapVal V)) →
      ∃ F fuelC v env', (denote' (crateBi ((pairStage m σ).1.prepared nfBody)
        ((pairStage m σ).1.linkTable hax64WExit) fuelC (pairStage m σ).1.depth) F
        (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry))).run
          (entryEnvOf (abiEntry (pairStage m σ).2) V) = (.val v, env'))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ) (haxcTgtRes σ prog)
      (haxcLeakRun prog) := by
  refine ⟨fun sa v hpre hsrc' => ?_,
    fun s₁ s₂ t₁ t₂ h h₁ h₂ =>
      haxc_ct_proved_all_perState s m σ fname P bytes hc (fun sa => ∃ v, haxRuns σ m sa v)
        (haxToNFCTLOn_of_haxToNFCTL _ (haxToNFCTL_of_haxToNFCTBL s _ _ hck))
        hterm hL hnds hd hnd hk s₁ s₂ t₁ t₂
        ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, h.2.2.2.1, .inr h.2.2.2.2⟩ h₁ h₂⟩
  obtain ⟨prog', hd', hv⟩ := haxc_correct_auto m σ fname P bytes hc sa hpre v hsrc' hnd hk
  rw [hd] at hd'
  cases hd'
  rcases hv with ⟨sa', hh, hR, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩
  · exact ⟨sa', hh, hR⟩
  · exact h

/-- **Robust compilation for the hax compiler with termination per entry state.** It is
    `haxc_rc_proved_all` with the uniform run hypothesis replaced by the run hypothesis of
    `haxc_gate_proved_all_perState`, one pair of fuels for each entry state from which the
    module has a source run and each valuation the layout reads off it: the gate conclusion,
    and distance `0` in every context between the real observation (the result read back from
    the halting run of `prog` and its leakage trace) and the ideal observation (the value of
    the source run and a trace simulated from `pubOf σ`), by `RCGate.rc_of_gate`. -/
theorem haxc_rc_proved_all_perState (s : _root_.Hax.FnSecrecy) (m : HaxModule)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true)
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry (pairStage m σ).2))),
      (pairStage m σ).2.Regions sa → (∃ v, haxRuns σ m sa v) → AbiValOf (pairStage m σ).2 sa
        (VIR.DialectToJasminComCorrect.ctMapValD (CatCrypt.Crypto.Hax.NFToCat.mapVal V)) →
      ∃ F fuelC v env', (denote' (crateBi ((pairStage m σ).1.prepared nfBody)
        ((pairStage m σ).1.linkTable hax64WExit) fuelC (pairStage m σ).1.depth) F
        (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry))).run
          (entryEnvOf (abiEntry (pairStage m σ).2) V) = (.val v, env'))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ) (haxcTgtRes σ prog)
        (haxcLeakRun prog) ∧
      RobustCompilation 0
        (realObs (Pre := σ.Regions) (srcRun := haxcSrcRun m σ) (leakRun := haxcLeakRun prog)
          (haxcTgtRes σ prog))
        (idealObs (pubOf σ)) := by
  have g := haxc_gate_proved_all_perState s m σ fname P bytes hc hck hterm hL hnds hd hnd hk
  exact ⟨g, rc_of_gate g (pubOf σ) (pubAgree_of_pubOf_eq σ)
    fun sa v w _ => haxcTgtRes_det σ prog sa v w⟩

end CatCrypt.Crypto.SecureCompilation.Haxc
