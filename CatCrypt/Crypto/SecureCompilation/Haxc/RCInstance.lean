/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import CatCrypt.Crypto.SecureCompilation.Haxc.CTPub
public import CatCrypt.Crypto.SecureCompilation.Haxc.CTRegions
public import CatCryptCore.Crypto.RCGate
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTStraight

/-!
# The instance of the gate conclusion for the hax compiler

The relations at which `RCGate.GateConclusion` is instantiated for a decoded program of the
hax compiler: entry states are `AState`, the precondition is `σ.Regions`, the public data are
`σ.PubAgree`, the source relation is `haxcSrcRun` (a run of the source reading of `te` from
an environment `σ` reads off the entry state, to a value that is not a control-flow value),
the target result relation is a halting run
of the decoded program whose exit state `σ` reads back, and the leakage relation is a
terminating `RunL` run under `ctRegime`. The public projection `pubOf σ` lists the values of
the public registers of `σ` and the words of its public array regions.

## Main definitions

* `haxcSrcRun`, `haxcTgtRes`, `haxcLeakRun` — the source, target result and leakage
  relations.
* `pubOf` — the public projection of an entry state.

## Main results

* `haxcTgtRes_det` — the target result relation is deterministic.
* `pubAgree_of_pubOf_eq` — entry states with equal public projections agree on the public
  data.
* `haxc_gate_proved_all`, `haxc_rc_proved_all` — the gate conclusion and robust
  compilation for a result of `compileA`, on a module whose linked functions are linked
  kernels with distinct names, from the level check `haxToNFCTBL` and termination of the
  source on the entry states under the table of the linked functions, through
  `haxc_ct_proved_all` and `haxc_correct_auto` of `ComposeCTStraight`. The robust
  compilation conjunct relates the target result and trace to the source value and a trace
  simulated from `pubOf σ` (`RCGate.rc_of_gate`); `RCGate.rhp_of_gate` gives the
  hyperproperty-preservation form of the same conclusion.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.RCGate
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open _root_.Hax (TExpr Value Env)
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Crypto.Hax (hax64WExit)
open scoped ENNReal

/-- The source relation of the module `m` under `σ`, the source semantics `haxRuns` of the hax
    front: a run of the source reading of the entry of `m`, at the table of `m`, from an
    environment `σ` reads off the entry state `sa` to a value `v` that is not a control-flow
    value. A single function is the module with no callee (a `TExpr` coerces), whose runs
    are those of its source reading at `hax64WExit` (`haxRuns_single`). -/
def haxcSrcRun (m : CatCrypt.Crypto.Hax.HaxModule) (σ : AbiLayout) (sa : AState)
    (v : Value) : Prop :=
  haxRuns σ m sa v

/-- The target result relation of `prog` under `σ`: a halting run from the entry state `sa`
    whose exit state `σ` reads back as `v`. -/
def haxcTgtRes (σ : AbiLayout) (prog : List RInstr) (sa : AState) (v : Value) : Prop :=
  ∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v

/-- The target result relation is deterministic: a halting run of a decoded program has one
    exit state, and `σ` reads one result back from it. -/
theorem haxcTgtRes_det (σ : AbiLayout) (prog : List RInstr) (sa : AState) (v w : Value)
    (hv : haxcTgtRes σ prog sa v) (hw : haxcTgtRes σ prog sa w) : v = w := by
  obtain ⟨s₁, h₁, rfl⟩ := hv
  obtain ⟨s₂, h₂, rfl⟩ := hw
  rw [halts_det h₁ h₂]

/-- The leakage relation of `prog`: a terminating run from index `0` under `ctRegime`, with no
    side condition, with leakage trace `t`. -/
def haxcLeakRun (prog : List RInstr) (s : AState) (t : List CTLeak) : Prop :=
  ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s'

/-- The public projection of an entry state under `σ`: the values of the public registers, and
    the words of each public array region at the address its register holds. -/
def pubOf (σ : AbiLayout) (s : AState) : List (BitVec 64) × List (List Value) :=
  (σ.pubRegs.map s.regs, σ.pubRegions.map fun p => wordsAt s.mem (s.regs p.1) p.2)

/-- Entry states with equal public projections agree on the public data of `σ`. -/
theorem pubAgree_of_pubOf_eq (σ : AbiLayout) (s₁ s₂ : AState)
    (h : pubOf σ s₁ = pubOf σ s₂) : σ.PubAgree s₁ s₂ := by
  have hall : ∀ x ∈ σ.pubRegs, s₁.regs x = s₂.regs x :=
    List.map_inj_left.mp (congrArg Prod.fst h)
  have hw := List.map_inj_left.mp (congrArg Prod.snd h)
  refine ⟨hall _ (List.mem_cons_self ..), fun a ha hp => hall _ ?_, fun a ha n hk hm => ?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, hp⟩, rfl⟩)
  · refine hw (a.reg, n) (List.mem_filterMap.mpr ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, ?_⟩)
    · simpa using hm
    · simp [AbiArg.region, hk]

section Gate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnvOf crateBi)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel)
open _root_.Hax (denote')
open CatCrypt.Crypto.Hax (HaxModule)

/-- **The gate conclusion of `compileA` from the proved chain, on a module.** Let the level
    check `haxToNFCTBL` in the leakage model with quiet declared calls accept the
    translation of the module `(pairStage m σ).1` of the pair stage of `m` (`m` itself
    without a pair tail) at the secrecy record `s` under the layout `(pairStage m σ).2` of
    the stage, let the body the front reads run at the fuel `F` under the table
    `linkTable hax64WExit` of the linked functions to a value from the environment of every
    valuation that the layout of the stage reads off an entry state satisfying its regions,
    and let the linked functions of `m` have distinct names (`hnd`) and be linked kernels
    (`hk`), both automatic on a module without linked functions. For every decoding `prog`
    of the bytes of a result, value correctness relative to `haxcSrcRun m σ` holds (both
    cases of `haxc_correct_auto`), and constant time from entry states satisfying
    `σ.Regions` from each of which the module has a source run holds by
    `haxc_ct_proved_all` at the precondition that holds everywhere. -/
theorem haxc_gate_proved_all (s : _root_.Hax.FnSecrecy) (m : HaxModule) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true) (F fuelC : Nat)
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry (pairStage m σ).2))),
      (pairStage m σ).2.Regions sa → AbiValOf (pairStage m σ).2 sa
        (VIR.DialectToJasminComCorrect.ctMapValD (CatCrypt.Crypto.Hax.NFToCat.mapVal V)) →
      ∃ v env', (denote' (crateBi ((pairStage m σ).1.prepared nfBody)
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
      haxc_ct_proved_all s m σ fname P bytes hc F fuelC (fun _ => True)
        (haxToNFCTLOn_of_haxToNFCTL _ (haxToNFCTL_of_haxToNFCTBL s _ _ hck))
        (fun sa V hR _ hV => hterm sa V hR hV) hL hnds hd hnd hk s₁ s₂ t₁ t₂
        ⟨h.1, h.2.1, h.2.2.1, trivial, trivial, h.2.2.2.1, .inr h.2.2.2.2⟩ h₁ h₂⟩
  obtain ⟨prog', hd', hv⟩ := haxc_correct_auto m σ fname P bytes hc sa hpre v hsrc' hnd hk
  rw [hd] at hd'
  cases hd'
  rcases hv with ⟨sa', hh, hR, -⟩ | ⟨-, -, -, -, -, -, h, -⟩
  · exact ⟨sa', hh, hR⟩
  · exact h

/-- **Robust compilation for the hax compiler from the proved chain, on a module.** For a
    result of `compileA` on the module `m`, whose source relation `haxcSrcRun m σ` answers a
    call of a function of the module by the run of the source reading of the extraction of
    the callee, and a call of a linked function by its meaning. Under the hypotheses of
    `haxc_gate_proved_all`, the level check `haxToNFCTBL`, the run hypothesis at the table
    `linkTable hax64WExit` and the linked functions of distinct names and linked kernels,
    every decoding `prog` of the bytes satisfies the gate conclusion, and on the entry
    states of the domain the real observation (the result `σ` reads back from the halting
    run of `prog`, and the leakage trace of `prog`) and the ideal observation (the value of
    the source run, and a trace simulated from `pubOf σ`) are at distance `0` in every
    context. The conjunct carries value correctness and constant time together; the
    constant-time part is `haxc_ct_proved_all`, and determinism of the target result is
    `haxcTgtRes_det`. The ideal trace is chosen by the choice simulator `RCGate.simLeak`
    (`Classical.epsilon`); the conjunct restates the gate conclusion and holds for every
    compiler that satisfies it with a deterministic target. -/
theorem haxc_rc_proved_all (s : _root_.Hax.FnSecrecy) (m : HaxModule) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true) (F fuelC : Nat)
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry (pairStage m σ).2))),
      (pairStage m σ).2.Regions sa → AbiValOf (pairStage m σ).2 sa
        (VIR.DialectToJasminComCorrect.ctMapValD (CatCrypt.Crypto.Hax.NFToCat.mapVal V)) →
      ∃ v env', (denote' (crateBi ((pairStage m σ).1.prepared nfBody)
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
  have g := haxc_gate_proved_all s m σ fname P bytes hc hck F fuelC hterm hL hnds hd hnd hk
  exact ⟨g, rc_of_gate g (pubOf σ) (pubAgree_of_pubOf_eq σ)
    fun sa v w _ => haxcTgtRes_det σ prog sa v w⟩

end Gate

end CatCrypt.Crypto.SecureCompilation.Haxc
