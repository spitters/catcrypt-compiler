/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulator
public import CatCryptCore.Crypto.UCCoupling
public import CatCrypt.Crypto.SecureCompilation.Haxc.HtermOfKinds
public import CatCrypt.Crypto.SecureCompilation.Haxc.ExportContract

/-!
# Reactive robust compilation of the hax compiler at the ABI view

The one-call robust compilation statement `haxc_rc_proved_all_of_checkB` relates one call of a
result of `compileA` to one run of its source. This module states the reactive form: the
compiled module and its source are reactive systems (`UCTransparent.Sys`) that answer one call
per event and keep the machine state between calls, and the target system realizes the source
system behind the per-call leakage simulator at distance `0` (`UCTransparent.RealizesSim`), for
every environment that chooses the calls adaptively.

These are robust-compilation statements in the sense of robust relational hyperproperty
preservation (RrHP), with the leakage simulator of the constant-time argument in the place of
the back-translation of target contexts. They are not UC security claims: the source system is
not an ideal functionality, and the simulator only replaces the leakage trace by one computed
from public data.

## Observation model

An event is an ABI call: an `AState` that supplies the register file, the flags and the memory
of the call's footprint `entryLocs σ` (the words of the pointer regions and the stack words of
the stack parameters). The entry state of the call is `abiEnter σ e t`: the registers and the
footprint of the event, and the memory of the kept state `t` elsewhere. A context observes,
per call, only the ABI view: whether the call is in the domain of the one-call statement (the
entry state satisfies `σ.Regions` and the source has a run), the result the layout reads back,
and the leakage trace. It does not read the memory of the kept state, so the contents of the
stack frame after a return (stack residue) are outside the view.

On the target side the kept state after a call is the exit state of the halting run
(`haltExit`); on the source side it is the entry state, since the source writes no memory. A
call outside the domain answers `none` on both sides and keeps the state.

## Main definitions

* `gateTgtSys`, `gateSrcSys` — the reactive target and source systems of a gate conclusion
  (`RCGate.GateConclusion`) at an entry map `enter : E → St → St`; one call is `RCGate.realObs`
  (target) or the value of the source run (source).
* `pairLeak`, `leakSimHybrid`, `leakSim` — the per-call leakage simulator: it forwards the call
  to the source and pairs the source value with the trace simulated from the public projection
  of the event; it is opaque from `srcView` to `leakView`.
* `entryLocs`, `abiEnter`, `haltExit` — the ABI footprint of a call, the entry state of a call
  from the kept state, and the exit state of a halting run.
* `haxcTgtSys`, `haxcSrcSys`, `haxcLeakSim` — the instances for a decoded result of
  `compileA`, at `haxcSrcRun`, `haxcTgtRes`, `haxcLeakRun` and `pubOf`.

## Main results

* `realizesSim_of_gate_dom` — a reactive target system realizes the reactive source system
  behind the leakage simulator at `Z.input.rounds * ε`, from a coupling at grade `ε` of each
  call in the domain with the answer of the source behind the simulator.
* `realizesSim_of_gate` — the reactive target system realizes the reactive source system
  behind the leakage simulator at distance `0`, from a gate conclusion whose entry relations do
  not depend on the kept state.
* `gateTgtSys_step_of_dom`, `leakSim_withSub_step_of_dom` — one call in the domain is the real
  observation (target) or the ideal observation (source behind the simulator).
* `haxcSrcRun_abiEnter`, `regions_abiEnter`, `pubOf_abiEnter` — the source run, the entry
  conditions and the public projection of an entry state depend only on the event.
* `haxc_rrc_proved_all_of_checkB` — reactive robust compilation at distance `0` for the modules
  of `haxc_rc_proved_all_of_checkB` (no callee, no linked function, kind checker accepts).
* `haxc_rrc_one_call` — one call of the two reactive systems is the real and the ideal
  observation of `haxc_rc_proved_all_of_checkB`, and these satisfy `RobustCompilation 0`.

## References

* C. Abate, R. Blanco, D. Garg, C. Hrițcu, M. Patrignani, J. Thibault, *Journey beyond full
  abstraction: exploring robust property preservation for secure compilation*, CSF 2019 (RrHP).

## Search words

reactive robust compilation, RrHP, robust relational hyperproperty preservation, multi-call,
ABI view, leakage simulator, constant time, kept machine state, realization behind a simulator
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.RCGate
open CatCrypt.Crypto.UCTransparent
open CatCrypt.Crypto.UCCoupling (realizes_of_couplingApprox stepPost)
open CatCrypt.Relational
open scoped ENNReal

/-! ## Reactive systems of a gate conclusion -/

section Gate

variable {St E V Tr P : Type}

open Classical in
/-- **The reactive target system of a gate conclusion.** The state is the kept machine state;
    the event `e` enters at the state `enter e t`. In the domain of the one-call statement (the
    precondition, a source run and a terminating target run) the call answers the real
    observation `RCGate.realObs` (target result and leakage trace) and keeps the exit state
    `exit (enter e t)`; outside it the call answers `none` and keeps `t`. -/
noncomputable def gateTgtSys (enter : E → St → St) (Pre : St → Prop) (srcRun : St → V → Prop)
    (tgtRes : St → V → Prop) (leakRun : St → Tr → Prop) (exit : St → St) (init : St) :
    Sys St E (Option (V × Tr)) where
  init := init
  step t e :=
    if h : (Pre (enter e t) ∧ ∃ v, srcRun (enter e t) v) ∧ ∃ tr, leakRun (enter e t) tr then
      SPComp.map (fun o => (exit (enter e t), some o))
        (realObs (Pre := Pre) (srcRun := srcRun) (leakRun := leakRun) tgtRes ⟨enter e t, h⟩)
    else SPComp.pure (t, none)

open Classical in
/-- **The reactive source system.** The state is the kept machine state; the event `e` enters
    at the state `enter e u`. When the entry state satisfies the precondition and the source
    has a run, the call answers the value of a source run and keeps the entry state (the source
    writes no memory); otherwise it answers `none` and keeps `u`. -/
noncomputable def gateSrcSys (enter : E → St → St) (Pre : St → Prop) (srcRun : St → V → Prop)
    (init : St) : Sys St E (Option V) where
  init := init
  step u e :=
    if h : Pre (enter e u) ∧ ∃ v, srcRun (enter e u) v then
      SPComp.pure (enter e u, some (Classical.choose h.2))
    else SPComp.pure (u, none)

/-- The answer of the simulator: the source value paired with the stored trace. -/
def pairLeak (l : Option Tr) (o : Option V) : Option (V × Tr) :=
  o.bind fun v => l.map fun t => (v, t)

/-- **The per-call leakage simulator** as a multi-call simulator. On the event `e` it stores
    the trace `lk (pe e)` simulated from the public projection `pe e` of the event and forwards
    the event to the source; it answers the source value paired with the stored trace. -/
noncomputable def leakSimHybrid (pe : E → P) (lk : P → Tr) :
    MultiHybrid (Option Tr) E (Option (V × Tr)) E (Option V) where
  init := none
  fuel := 0
  start _ e := SPComp.pure (some (lk (pe e)), .inl e)
  resume l o := SPComp.pure (l, .inr (pairLeak l o))
  finish l o := SPComp.pure (l, pairLeak l o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- The public view of the outer interface: events with equal public projections, answers with
    equal leakage parts (and equal definedness). -/
def leakView (pe : E → P) : PubView E (Option (V × Tr)) :=
  PubView.ofProj pe (Option.map Prod.snd)

/-- The public view of the source interface: events with equal public projections, answers
    with equal definedness. -/
def srcView (pe : E → P) : PubView E (Option V) :=
  PubView.ofProj pe Option.isSome

/-- Answers of equal definedness, paired with the same trace, have equal leakage parts. -/
theorem map_snd_pairLeak (l : Option Tr) {o o' : Option V} (h : o.isSome = o'.isSome) :
    (pairLeak l o).map Prod.snd = (pairLeak l o').map Prod.snd := by
  cases o <;> cases o' <;> cases l <;> simp_all [pairLeak]

/-- The leakage simulator is opaque from `srcView pe` to `leakView pe`: its traces depend only
    on the public projections of the events. -/
theorem leakSimHybrid_opaque (pe : E → P) (lk : P → Tr) :
    (leakSimHybrid (V := V) pe lk).Opaque (leakView pe) (srcView pe) := by
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s s' e e' - he
    have he' : pe e = pe e' := he
    exact rHoare_ret fun _ _ h => ⟨h, by rw [he'], he'⟩
  · rintro s s' o o' rfl ho
    exact rHoare_ret fun _ _ h => ⟨h, rfl, map_snd_pairLeak s ho⟩
  · rintro s s' o o' rfl ho
    exact rHoare_ret fun _ _ h => ⟨h, rfl, map_snd_pairLeak s ho⟩

/-- **The per-call leakage simulator**, bundled with its opacity. -/
noncomputable def leakSim (pe : E → P) (lk : P → Tr) :
    Simulator E (Option (V × Tr)) E (Option V) (leakView pe) (srcView pe) :=
  Simulator.ofMultiHybrid (leakSimHybrid pe lk) (leakSimHybrid_opaque pe lk)

/-- One step of the leakage simulator over a system `X` is one step of `X`, its answer paired
    with the trace simulated from the event. -/
theorem leakSim_withSub_step (pe : E → P) (lk : P → Tr) {τ : Type} (X : Sys τ E (Option V))
    (l : Option Tr) (u : τ) (e : E) :
    ((leakSim pe lk).withSub X).step (l, u) e =
      SPComp.bind (X.step u e) fun q =>
        SPComp.pure ((some (lk (pe e)), q.1), pairLeak (some (lk (pe e))) q.2) := by
  simp [leakSim, Simulator.ofMultiHybrid, MultiHybrid.withSub, MultiHybrid.drive,
    leakSimHybrid, SPComp.pure_bind, SPComp.bind_assoc]

/-- Choice at equal predicates gives equal witnesses. -/
private theorem choose_congr_pred {p q : V → Prop} (h : p = q) (hp : ∃ v, p v)
    (hq : ∃ v, q v) : Classical.choose hp = Classical.choose hq := by
  subst h
  rfl

/-- **One target call in the domain is the real observation.** -/
theorem gateTgtSys_step_of_dom (enter : E → St → St) (Pre : St → Prop)
    (srcRun : St → V → Prop) (tgtRes : St → V → Prop) (leakRun : St → Tr → Prop)
    (exit : St → St) (init t : St) (e : E)
    (h : (Pre (enter e t) ∧ ∃ v, srcRun (enter e t) v) ∧ ∃ tr, leakRun (enter e t) tr) :
    (gateTgtSys enter Pre srcRun tgtRes leakRun exit init).step t e =
      SPComp.map (fun o => (exit (enter e t), some o))
        (realObs (Pre := Pre) (srcRun := srcRun) (leakRun := leakRun) tgtRes ⟨enter e t, h⟩) := by
  simp only [gateTgtSys, dite_eq_left h]

/-- **One call of the source behind the simulator in the domain is the ideal observation.**
    When the public projection of every entry state is that of its event, the answer is the
    ideal observation `RCGate.idealObs` of the entry state. -/
theorem leakSim_withSub_step_of_dom [Nonempty Tr] (enter : E → St → St) (Pre : St → Prop)
    (srcRun : St → V → Prop) (leakRun : St → Tr → Prop) (pub : St → P) (pe : E → P)
    (hpe : ∀ e t, pub (enter e t) = pe e) (init u : St) (l : Option Tr) (e : E)
    (h : (Pre (enter e u) ∧ ∃ v, srcRun (enter e u) v) ∧ ∃ tr, leakRun (enter e u) tr) :
    ((leakSim pe (simLeak Pre srcRun leakRun pub)).withSub
        (gateSrcSys enter Pre srcRun init)).step (l, u) e =
      SPComp.map (fun o => ((some (simLeak Pre srcRun leakRun pub (pe e)), enter e u), some o))
        (idealObs (Pre := Pre) (srcRun := srcRun) (leakRun := leakRun) pub ⟨enter e u, h⟩) := by
  rw [leakSim_withSub_step]
  simp only [gateSrcSys, dite_eq_left h.1, idealObs, srcOf, pairLeak, hpe, SPComp.map,
    SPComp.pure_bind, Option.bind_some, Option.map_some]
  rfl

/-- **Reactive robust compilation from per-call couplings.** Let the entry map `enter` give
    entry states whose precondition and source runs do not depend on the kept state, and let
    the gate conclusion give a target that has a leakage trace whenever it has a result. Let a
    reactive target system `T` answer `none` and keep its state outside the domain, and in the
    domain be coupled at grade `ε` with the answer that pairs the source value with the trace
    simulated from `pe e`. Then `T` realizes the reactive source system behind the leakage
    simulator `leakSim pe (simLeak …)` at `ε` per activation, `Z.input.rounds * ε` in all. -/
theorem realizesSim_of_gate_dom [Nonempty Tr] {Pre : St → Prop} {Pub : St → St → Prop}
    {srcRun : St → V → Prop} {tgtRes : St → V → Prop} {leakRun : St → Tr → Prop}
    (g : GateConclusion Pre Pub srcRun tgtRes leakRun) (pub : St → P)
    (hterm : ∀ s v, Pre s → tgtRes s v → ∃ tr, leakRun s tr)
    (enter : E → St → St) (pe : E → P)
    (hPre : ∀ e t u, Pre (enter e t) ↔ Pre (enter e u))
    (hsrc : ∀ e t u, srcRun (enter e t) = srcRun (enter e u))
    (T : Sys St E (Option (V × Tr))) (ε : ℝ≥0∞)
    (hin : ∀ t e (h : (Pre (enter e t) ∧ ∃ v, srcRun (enter e t) v) ∧
        ∃ tr, leakRun (enter e t) tr) (y : Option Tr × St),
      rHoareApprox ε eqPre (T.step t e)
        (SPComp.pure (y, some (srcOf (Pre := Pre) (srcRun := srcRun) (leakRun := leakRun)
          ⟨enter e t, h⟩, simLeak Pre srcRun leakRun pub (pe e))))
        (stepPost fun _ _ => True))
    (hout : ∀ t e, ¬ ((Pre (enter e t) ∧ ∃ v, srcRun (enter e t) v) ∧
        ∃ tr, leakRun (enter e t) tr) → T.step t e = SPComp.pure (t, none))
    (u₀ : St) :
    RealizesSim T (gateSrcSys enter Pre srcRun u₀) (leakSim pe (simLeak Pre srcRun leakRun pub))
      (fun _ Z => Z.input.rounds * ε) := by
  refine realizes_of_couplingApprox _ _ (fun _ _ => True) ε trivial ?_
  rintro t ⟨l, u⟩ e -
  rw [leakSim_withSub_step]
  by_cases hD : Pre (enter e u) ∧ ∃ v, srcRun (enter e u) v
  · have hp : Pre (enter e t) := (hPre e t u).2 hD.1
    obtain ⟨v, hv⟩ := hD.2
    have hv' : srcRun (enter e t) v := (hsrc e t u).symm ▸ hv
    have hT : (Pre (enter e t) ∧ ∃ v, srcRun (enter e t) v) ∧ ∃ tr, leakRun (enter e t) tr :=
      ⟨⟨hp, v, hv'⟩, hterm _ v hp (g.value _ _ hp hv')⟩
    simp only [gateSrcSys, dite_eq_left hD, SPComp.pure_bind, pairLeak, Option.bind_some,
      Option.map_some, ← choose_congr_pred (hsrc e t u) hT.1.2 hD.2]
    exact hin t e hT _
  · have hT : ¬ ((Pre (enter e t) ∧ ∃ v, srcRun (enter e t) v) ∧
        ∃ tr, leakRun (enter e t) tr) := fun h =>
      hD ⟨(hPre e t u).1 h.1.1, (hsrc e t u) ▸ h.1.2⟩
    simp only [hout t e hT, gateSrcSys, dite_eq_right hD, SPComp.pure_bind]
    exact rHoareApprox_mono_eps zero_le
      (rHoareApprox_of_rHoare (rHoare_ret fun _ _ hh => ⟨hh, trivial, rfl⟩))

/-- **Reactive robust compilation from a gate conclusion.** Let the compilation satisfy the
    gate conclusion, with a deterministic target result, a target that terminates with a
    leakage trace whenever it halts with a result, and public projections whose equality
    implies the public relation. Let the entry map `enter` give entry states whose
    precondition and source runs do not depend on the kept state, and whose public projection
    is the projection `pe e` of the event. Then the reactive target system realizes the
    reactive source system behind the leakage simulator `leakSim pe (simLeak …)` at distance
    `0`, for all initial kept states `t₀` and `u₀`. The answers are the ABI view (definedness,
    result, leakage trace); the kept state is not observed. -/
theorem realizesSim_of_gate [Nonempty Tr] {Pre : St → Prop} {Pub : St → St → Prop}
    {srcRun : St → V → Prop} {tgtRes : St → V → Prop} {leakRun : St → Tr → Prop}
    (g : GateConclusion Pre Pub srcRun tgtRes leakRun) (pub : St → P)
    (hpub : ∀ s₁ s₂, pub s₁ = pub s₂ → Pub s₁ s₂)
    (htgt : ∀ s v w, Pre s → tgtRes s v → tgtRes s w → v = w)
    (hterm : ∀ s v, Pre s → tgtRes s v → ∃ tr, leakRun s tr)
    (enter : E → St → St) (pe : E → P)
    (hPre : ∀ e t u, Pre (enter e t) ↔ Pre (enter e u))
    (hsrc : ∀ e t u, srcRun (enter e t) = srcRun (enter e u))
    (hpe : ∀ e t, pub (enter e t) = pe e) (exit : St → St) (t₀ u₀ : St) :
    RealizesSim (gateTgtSys enter Pre srcRun tgtRes leakRun exit t₀)
      (gateSrcSys enter Pre srcRun u₀) (leakSim pe (simLeak Pre srcRun leakRun pub))
      (fun _ _ => 0) := by
  have h := realizesSim_of_gate_dom g pub hterm enter pe hPre hsrc
    (gateTgtSys enter Pre srcRun tgtRes leakRun exit t₀) 0 (fun t e hT _ => ?_)
    (fun t e hT => by simp only [gateTgtSys, dite_eq_right hT]) u₀
  · simpa using h
  rw [gateTgtSys_step_of_dom enter Pre srcRun tgtRes leakRun exit t₀ t e hT,
    congrFun (realObs_eq_idealObs g pub hpub htgt) ⟨enter e t, hT⟩]
  simp only [idealObs, SPComp.map, SPComp.pure_bind, hpe]
  exact rHoareApprox_of_rHoare (rHoare_ret fun _ _ hh => ⟨hh, trivial, rfl⟩)

end Gate

/-! ## The instance of the hax compiler -/

section Instance

open CatCrypt.Crypto.SecureCompilation.SepLogic
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (Loc wordLocs wordsLocs regionWords loc
  agreeOn_iff read64_congr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL halts_runL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Haxc.CTTotality (WKind wKindSig)
open _root_.Hax (Value)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute

/-- The stack words of the stack parameters of `σ` at the register values `rv`: the word at
    `%rsp + 8 k` for each stack parameter carried by `stackArgReg k`. -/
def stackLocs (σ : AbiLayout) (rv : String → BitVec 64) : Set Loc :=
  ⋃ k ∈ {k : Nat | ∃ a ∈ σ.args, a.reg = stackArgReg k},
    wordLocs (rv "%rsp" + BitVec.ofNat 64 (8 * k))

/-- **The ABI footprint of a call** at the register values `rv`: the words of the pointer
    regions and the stack words of the stack parameters. -/
def entryLocs (σ : AbiLayout) (rv : String → BitVec 64) : Set Loc :=
  regionLocs σ rv ∪ stackLocs σ rv

open Classical in
/-- **The entry state of a call** with the event `e` from the kept state `t`: the registers and
    flags of `e`, the memory of `e` on the footprint `entryLocs σ e.regs`, and the memory of
    `t` elsewhere. -/
noncomputable def abiEnter (σ : AbiLayout) (e t : AState) : AState where
  regs := e.regs
  flags := e.flags
  mem a := if Loc.mem a ∈ entryLocs σ e.regs then e.mem a else t.mem a

/-- The entry state agrees with the event on the footprint. -/
theorem abiEnter_agreeOn (σ : AbiLayout) (e t : AState) :
    Footprinted.AgreeOn (entryLocs σ e.regs) (abiEnter σ e t) e := by
  rw [agreeOn_iff]
  rintro (r | f | a) hl
  · rfl
  · rfl
  · simp [loc, abiEnter, hl]

/-- The source run from an entry state is the source run from its event. -/
theorem haxcSrcRun_abiEnter (m : HaxModule) (σ : AbiLayout) (e t : AState) :
    haxcSrcRun m σ (abiEnter σ e t) = haxcSrcRun m σ e := by
  have h := abiEnter_agreeOn σ e t
  have hm : Footprinted.AgreeOn (regionLocs σ (abiEnter σ e t).regs) (abiEnter σ e t) e :=
    Footprinted.agreeOn_anti Set.subset_union_left h
  have hm' : Footprinted.AgreeOn (regionLocs σ e.regs) e (abiEnter σ e t) := by
    rw [agreeOn_iff] at h ⊢
    exact fun l hl => (h l (Or.inl hl)).symm
  funext v
  exact propext ⟨fun hs => haxRuns_congr (s := abiEnter σ e t) (t := e) (fun _ _ => rfl) hm hs,
    fun hs => haxRuns_congr (s := e) (t := abiEnter σ e t) (fun _ _ => rfl) hm' hs⟩

/-- The stack parameters are at entry in an entry state exactly when they are in its event. -/
theorem stackIn_abiEnter (σ : AbiLayout) (e t : AState) :
    σ.StackIn (abiEnter σ e t) ↔ σ.StackIn e := by
  have hw : ∀ a ∈ σ.args, ∀ k, a.reg = stackArgReg k →
      read64 (abiEnter σ e t).mem (e.regs "%rsp" + BitVec.ofNat 64 (8 * k)) =
        read64 e.mem (e.regs "%rsp" + BitVec.ofNat 64 (8 * k)) := fun a ha k hk =>
    read64_congr (Footprinted.agreeOn_anti
      (fun l hl => Or.inr (Set.mem_biUnion
        (show k ∈ {k : Nat | ∃ a ∈ σ.args, a.reg = stackArgReg k} from ⟨a, ha, hk⟩) hl))
      (abiEnter_agreeOn σ e t))
  constructor
  · intro h a ha k hk
    exact (h a ha k hk).trans (hw a ha k hk)
  · intro h a ha k hk
    exact (h a ha k hk).trans (hw a ha k hk).symm

/-- The entry conditions of an entry state are those of its event. -/
theorem regions_abiEnter (σ : AbiLayout) (e t : AState) :
    σ.Regions (abiEnter σ e t) ↔ σ.Regions e :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, (stackIn_abiEnter σ e t).1 h.2.2.2⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, (stackIn_abiEnter σ e t).2 h.2.2.2⟩⟩

/-- A public array region is a pointer region. -/
theorem mem_regions_of_mem_pubRegions {σ : AbiLayout} {p : String × Nat}
    (hp : p ∈ σ.pubRegions) : p ∈ σ.regions := by
  obtain ⟨a, ha, hr⟩ := List.mem_filterMap.1 hp
  exact List.mem_filterMap.2 ⟨a, (List.mem_filter.1 ha).1, hr⟩

/-- The public projection of an entry state is that of its event. -/
theorem pubOf_abiEnter (σ : AbiLayout) (e t : AState) :
    pubOf σ (abiEnter σ e t) = pubOf σ e := by
  unfold pubOf
  refine Prod.ext rfl (List.map_congr_left fun p hp => ?_)
  have hreg := mem_regions_of_mem_pubRegions hp
  simp only [wordsAt]
  refine List.map_congr_left fun j hj => ?_
  rw [read64_congr (Footprinted.agreeOn_anti ?_ (abiEnter_agreeOn σ e t))]
  · rfl
  intro l hl
  have h1 : l ∈ wordsLocs (regionWords (e.regs p.1) p.2) :=
    Set.mem_biUnion (t := wordLocs)
      (show e.regs p.1 + BitVec.ofNat 64 (8 * j) ∈ regionWords (e.regs p.1) p.2 from
        ⟨j, List.mem_range.1 hj, rfl⟩) hl
  exact Or.inl (Set.mem_iUnion₂.2 ⟨p, hreg, h1⟩)

/-- The exit state of a halting run of `prog` from `s`, when one exists (`halts_det` makes it
    unique); `s` otherwise. -/
noncomputable def haltExit (prog : List RInstr) (s : AState) : AState :=
  @Classical.epsilon AState ⟨s⟩ fun s' => Halts aMachine prog 0 s s'

/-- **The compiled module as a reactive system**: `gateTgtSys` at the entry map `abiEnter σ`,
    the target result relation `haxcTgtRes σ prog`, the leakage relation `haxcLeakRun prog`
    and the exit state `haltExit prog` of the halting run, from the kept state `t₀`. -/
noncomputable def haxcTgtSys (m : HaxModule) (σ : AbiLayout) (prog : List RInstr)
    (t₀ : AState) : Sys AState AState (Option (Value × List CTLeak)) :=
  gateTgtSys (abiEnter σ) σ.Regions (haxcSrcRun m σ) (haxcTgtRes σ prog) (haxcLeakRun prog)
    (haltExit prog) t₀

/-- **The source module as a reactive system**: `gateSrcSys` at the entry map `abiEnter σ` and
    the source relation `haxcSrcRun m σ`, from the kept state `u₀`. -/
noncomputable def haxcSrcSys (m : HaxModule) (σ : AbiLayout) (u₀ : AState) :
    Sys AState AState (Option Value) :=
  gateSrcSys (abiEnter σ) σ.Regions (haxcSrcRun m σ) u₀

/-- **The per-call leakage simulator of the hax compiler**: `leakSim` at the public projection
    `pubOf σ` of the event and the choice simulator `RCGate.simLeak` of the one-call
    statement. -/
noncomputable def haxcLeakSim (m : HaxModule) (σ : AbiLayout) (prog : List RInstr) :
    Simulator AState (Option (Value × List CTLeak)) AState (Option Value)
      (leakView (pubOf σ)) (srcView (pubOf σ)) :=
  leakSim (pubOf σ) (simLeak σ.Regions (haxcSrcRun m σ) (haxcLeakRun prog) (pubOf σ))

/-- A halting run of the decoded program to a result has a leakage trace. -/
theorem haxcLeakRun_of_tgtRes (σ : AbiLayout) (prog : List RInstr) (s : AState) (v : Value)
    (h : haxcTgtRes σ prog s v) : ∃ tr, haxcLeakRun prog s tr := by
  obtain ⟨s', hh, -⟩ := h
  obtain ⟨tr, htr⟩ := halts_runL ctRegime hh
  exact ⟨tr, s', htr⟩

/-- **Reactive robust compilation for the hax compiler from the kind checker.** Under the
    hypotheses of `haxc_rc_proved_all_of_checkB` (a module without callees and linked
    functions, the level check `haxToNFCTBL`, a run of the kind checker on the body of the pair
    stage), for every decoding `prog` of the bytes of the result, the compiled module as a
    reactive system realizes the source module as a reactive system behind the per-call
    leakage simulator `haxcLeakSim` at distance `0`, for all initial kept states. Each call is
    an ABI call (`abiEnter`); the context observes the ABI view of each call (definedness, the
    result `σ` reads back, the leakage trace) and not the memory of the kept state. This is a
    robust-compilation statement (RrHP at the ABI view), not a UC security claim. -/
theorem haxc_rrc_proved_all_of_checkB (s : _root_.Hax.FnSecrecy) (m : HaxModule)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true)
    (hfns : m.fns = []) (hlk : m.linked = []) {ko : Option WKind} {B : Nat}
    (hcheck : wKindSig.check (entryKindsB (pairStage m σ).2)
      (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry)) = some (ko, B))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog) (t₀ u₀ : AState) :
    RealizesSim (haxcTgtSys m σ prog t₀) (haxcSrcSys m σ u₀) (haxcLeakSim m σ prog)
      (fun _ _ => 0) :=
  realizesSim_of_gate
    (haxc_gate_proved_all_of_checkB s m σ fname P bytes hc hck hfns hlk hcheck hL hnds hd)
    (pubOf σ) (pubAgree_of_pubOf_eq σ) (fun s v w _ => haxcTgtRes_det σ prog s v w)
    (fun s v _ h => haxcLeakRun_of_tgtRes σ prog s v h) (abiEnter σ) (pubOf σ)
    (fun e t u => (regions_abiEnter σ e t).trans (regions_abiEnter σ e u).symm)
    (fun e t u => (haxcSrcRun_abiEnter m σ e t).trans (haxcSrcRun_abiEnter m σ e u).symm)
    (pubOf_abiEnter σ) (haltExit prog) t₀ u₀

/-- **One call of the reactive systems is the one-call statement.** Under the hypotheses of
    `haxc_rc_proved_all_of_checkB`: a call of the compiled module whose entry state lies in the
    domain answers the real observation `realObs` of that entry state; a call of the source
    behind the leakage simulator answers its ideal observation `idealObs (pubOf σ)`; and the two
    observations satisfy `RobustCompilation 0`, the conclusion of
    `haxc_rc_proved_all_of_checkB`. -/
theorem haxc_rrc_one_call (s : _root_.Hax.FnSecrecy) (m : HaxModule)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true)
    (hfns : m.fns = []) (hlk : m.linked = []) {ko : Option WKind} {B : Nat}
    (hcheck : wKindSig.check (entryKindsB (pairStage m σ).2)
      (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry)) = some (ko, B))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog) (t₀ u₀ : AState) :
    (∀ (t e : AState) (h : (σ.Regions (abiEnter σ e t) ∧
        ∃ v, haxcSrcRun m σ (abiEnter σ e t) v) ∧ ∃ tr, haxcLeakRun prog (abiEnter σ e t) tr),
      (haxcTgtSys m σ prog t₀).step t e =
        SPComp.map (fun o => (haltExit prog (abiEnter σ e t), some o))
          (realObs (Pre := σ.Regions) (srcRun := haxcSrcRun m σ) (leakRun := haxcLeakRun prog)
            (haxcTgtRes σ prog) ⟨abiEnter σ e t, h⟩)) ∧
    (∀ (l : Option (List CTLeak)) (u e : AState) (h : (σ.Regions (abiEnter σ e u) ∧
        ∃ v, haxcSrcRun m σ (abiEnter σ e u) v) ∧ ∃ tr, haxcLeakRun prog (abiEnter σ e u) tr),
      ((haxcLeakSim m σ prog).withSub (haxcSrcSys m σ u₀)).step (l, u) e =
        SPComp.map (fun o => ((some (simLeak σ.Regions (haxcSrcRun m σ) (haxcLeakRun prog)
            (pubOf σ) (pubOf σ e)), abiEnter σ e u), some o))
          (idealObs (Pre := σ.Regions) (srcRun := haxcSrcRun m σ) (leakRun := haxcLeakRun prog)
            (pubOf σ) ⟨abiEnter σ e u, h⟩)) ∧
    RobustCompilation 0
      (realObs (Pre := σ.Regions) (srcRun := haxcSrcRun m σ) (leakRun := haxcLeakRun prog)
        (haxcTgtRes σ prog))
      (idealObs (pubOf σ)) :=
  ⟨fun t e h => gateTgtSys_step_of_dom _ _ _ _ _ _ t₀ t e h,
    fun l u e h => leakSim_withSub_step_of_dom _ _ _ _ _ _ (pubOf_abiEnter σ) u₀ u l e h,
    (haxc_rc_proved_all_of_checkB s m σ fname P bytes hc hck hfns hlk hcheck hL hnds hd).2⟩

end Instance

end CatCrypt.Crypto.SecureCompilation.Haxc
