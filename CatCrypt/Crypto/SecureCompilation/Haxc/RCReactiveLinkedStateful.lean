/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerStateful
public import CatCrypt.Crypto.SecureCompilation.Haxc.RCReactiveLinkedState

/-!
# Reactive robust compilation of the hax compiler with stateful linked functions

`Haxc.RCReactiveLinkedState` states reactive robust compilation for linked functions answered
at a key drawn once per run. This module states it for linked functions answered by a stateful
oracle `O` (`RCHandlerStateful.StOracle`) whose handler state persists across activations: the
reactive systems hold the oracle state beside the kept machine state, the first activation
draws it by `O.init`, and each activation runs one call of the module with the linked calls
answered from the oracle state held and passes the final oracle state to the next activation
(`stSys`).

At the oracle state `x`, a call of the source runs the source tree of the entry under `O.step`
from `x` and answers its value with the final oracle state (`haxcStSrc`); a call of the compiled
module interprets the calling body under the stateful target handler `h₂` from `x`, keeping the
final handler state (`interpTargetStSω`). The domain of a call is that of `Haxc.RCReactive`
intersected with the entry states at which the source run from `x` does not fail
(`haxcStSrcRel`).

The coupling of the two runs keeps the two oracle states equal. Per activation, the couplings up
to failure of `RCHandlerStateful` at every fuel, with the final handler states related
(`RCHandlerStateful.relF_interpStS_ruttFA`, over the interpretation `interpStS` that keeps the
final handler state), bound the excess of the target over the source by zero and the
excess of the source over the target by the failure weight of the target; a sub-coupling along
the graph of the read-back then relates the two activations at that grade
(`rHoareApprox_graph_of_tvMargin`).

## Main definitions

* `haxcStSrcRel`, `haxcStSrc`, `haxcStTgtSys`, `haxcStSrcSys` — the hax instance of `stSys`,
  `gateTgtStepSt` and `gateSrcStepSt` (`RCReactiveLinkedState`).

## Main results

* A checked `example` derives `realizesSim_of_gate_run_keyed` of `RCReactiveLinkedState` as the
  instance of `realizesSim_of_gate_run_st` whose state is the key.
* `haxc_rrcHSt_of_ruttFA`, `haxc_rrcHSt` — reactive robust compilation for stateful linked
  functions.

## Search words

reactive robust compilation, stateful oracle, oracle state carried across activations, coupling
up to failure, graph sub-coupling, leakage simulator, keyed oracle instance
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open OmegaCompletePartialOrder
open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.RCGate
open CatCrypt.Crypto.UCTransparent
open CatCrypt.Crypto.UCCoupling (realizes_of_couplingApprox stepPost)
open CatCrypt.Relational
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerStateful
open scoped ENNReal

/-! ## Sub-couplings along the graph of a map -/

section Graph

variable {α β : Type}

open Classical in
/-- **A sub-coupling along the graph of a map.** When the image of `d₁` under `g` is dominated
    by `d₂` and the total excess of `d₂` over the image is at most `ε`, the two are related at
    grade `ε` by the graph of `g`. -/
theorem liftRApprox_graph {d₁ : SDistr α} {d₂ : SDistr β} {g : α → β} {ε : ℝ≥0∞}
    (hdom : ∀ b, ∑' a, (if g a = b then d₁ (some a) else 0) ≤ d₂ (some b))
    (hdef : ∑' b, (d₂ (some b) - ∑' a, (if g a = b then d₁ (some a) else 0)) ≤ ε) :
    liftRApprox ε (fun a b => g a = b) d₁ d₂ := by
  classical
  have hj : ∀ a b, (d₁.bind fun a => SDistr.pure (a, g a)) (some (a, b)) =
      if g a = b then d₁ (some a) else 0 := by
    intro a b
    rw [SDistr.bind_apply_some, tsum_eq_single a]
    · by_cases h : g a = b
      · simp [SDistr.pure_apply_some, h]
      · simp only [SDistr.pure_apply_some, h, ite_false]
        grind
    · intro a' ha'
      simp [SDistr.pure_apply_some, ha']
  refine ⟨⟨d₁.bind fun a => SDistr.pure (a, g a), fun a => ?_, fun b => ?_, ?_, ?_⟩, ?_⟩
  · simp only [hj]
    simp_all
  · simp only [hj]
    exact hdom b
  · simp only [hj]
    simp_all
  · simp only [hj]
    exact hdef
  · intro a b h
    rw [hj] at h
    by_contra hc
    simp [hc] at h

open Classical in
/-- The weight of a value under the read-back by a total map. -/
theorem readBack_some_apply_some (g : α → β) (c : SPComp α) (s : Heap) (q : β × Heap) :
    readBack (fun a => some (g a)) c s (some q) =
      ∑' p : α × Heap, (if (g p.1, p.2) = q then c s (some p) else 0) := by
  classical
  simp only [readBack, optSP, SPComp.bind]
  rw [SDistr.bind_apply_some]
  refine tsum_congr fun p => ?_
  by_cases hp : (g p.1, p.2) = q <;> simp [hp, SPComp.pure, SDistr.pure_apply_some]

/-- **An approximate coupling along the graph of a read-back.** When the read-back of `c₁` by
    `g` exceeds `c₂` nowhere and `c₂` exceeds it by at most `ε`, `c₁` and `c₂` are related at
    grade `ε` with the value of `c₂` the image of that of `c₁` at equal heaps. -/
theorem rHoareApprox_graph_of_tvMargin {c₁ : SPComp α} {c₂ : SPComp β} {g : α → β}
    {ε : ℝ≥0∞} (h₁ : ∀ s, tvMargin (readBack (fun a => some (g a)) c₁ s) (c₂ s) ≤ 0)
    (h₂ : ∀ s, tvMargin (c₂ s) (readBack (fun a => some (g a)) c₁ s) ≤ ε) :
    rHoareApprox ε eqPre c₁ c₂ (fun a s₁ b s₂ => g a = b ∧ s₁ = s₂) := by
  rintro s₀ s (rfl : s₀ = s)
  classical
  have key := liftRApprox_graph (ε := ε) (d₁ := c₁ s₀) (d₂ := c₂ s₀)
    (g := fun p => (g p.1, p.2)) ?_ ?_
  · refine liftRApprox_mono_rel (fun p q h => ?_) key
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact ⟨h1, h2⟩
  · intro b
    have h0 := tsum_eq_zero_iff.mp (le_antisymm (h₁ s₀) zero_le) b
    rw [readBack_some_apply_some] at h0
    convert tsub_eq_zero_iff_le.mp h0
  · have h0 := h₂ s₀
    unfold tvMargin at h0
    simp only [readBack_some_apply_some] at h0
    convert h0

end Graph

/-! ## Reactive systems carrying a state across activations -/

section CarriedState

variable {St E V Tr P X : Type}

/- The keyed statement as the instance whose carried state is the key: under the hypotheses of
`realizesSim_of_gate_run_keyed`, its conclusion follows from `realizesSim_of_gate_run_st` at the
source relations `gatedRun srcRun (srcK k)`, the target runs that return the key, and the source
computations `chooseSt`. -/
example [Nonempty Tr] {Pre : St → Prop}
    {Pub : St → St → Prop} {srcRun : St → V → Prop} {tgtRes : St → V → Prop}
    {leakRun : St → Tr → Prop}
    (g : GateConclusion Pre Pub srcRun tgtRes leakRun) (pub : St → P)
    (hpub : ∀ s₁ s₂, pub s₁ = pub s₂ → Pub s₁ s₂)
    (hterm : ∀ s v, Pre s → tgtRes s v → ∃ tr, leakRun s tr)
    (enter : E → St → St) (pe : E → P)
    (hPre : ∀ e t u, Pre (enter e t) ↔ Pre (enter e u))
    (hsrc : ∀ e t u, srcRun (enter e t) = srcRun (enter e u))
    (hpe : ∀ e t, pub (enter e t) = pe e) (kd : SPComp X) (srcK : X → St → V → Prop)
    (hsrcK : ∀ k e t u, srcK k (enter e t) = srcK k (enter e u))
    (run : X → St → SPComp St) (read : St → St → V) (ε : ℝ≥0∞)
    (hrun : ∀ k s v, Pre s → (∃ w, srcRun s w) → srcK k s v →
      sdist (fun _ : Unit => SPComp.map (read s) (run k s)) (fun _ : Unit => SPComp.pure v) ≤ ε)
    (t₀ u₀ : St) :
    RealizesSim
      (keyedSys kd (fun k =>
        (gateTgtSysRun enter Pre (gatedRun srcRun (srcK k)) leakRun (run k) read t₀).step) t₀)
      (keyedSys kd (fun k => (gateSrcSys enter Pre (gatedRun srcRun (srcK k)) u₀).step) u₀)
      (leakSim pe (simLeak Pre srcRun leakRun pub)) (fun _ Z => Z.input.rounds * ε) := by
  have hsrcX : ∀ k e t u, gatedRun srcRun (srcK k) (enter e t) =
      gatedRun srcRun (srcK k) (enter e u) := fun k e t u => by
    funext v
    simp only [gatedRun, hsrc e t u, hsrcK k e t u]
  rw [keyedSys_eq_stSys kd _ (gateTgtStepSt enter Pre (fun k => gatedRun srcRun (srcK k))
      leakRun (fun k s => SPComp.map (fun a => (a, k)) (run k s)) read) t₀ ?_,
    keyedSys_eq_stSys kd _ (gateSrcStepSt enter Pre (fun k => gatedRun srcRun (srcK k))
      (chooseSt fun k => gatedRun srcRun (srcK k))) u₀ ?_]
  · refine realizesSim_of_gate_run_st g pub hpub hterm enter pe hPre hpe kd _
      (fun _ _ _ h => h.1) hsrcX _ read _ (fun k e t u => ?_) ε (fun k s hp hv => ?_) t₀ u₀
    · unfold chooseSt
      beta_reduce
      rw [hsrcX k e t u]
    · have hv' := Classical.choose_spec hv
      simp only [chooseSt, dite_eq_left hv]
      refine rHoareApprox_conseq (fun _ _ h => h) ?_ le_rfl
        (rHoareApprox_map_pure_of_sdist (rel := fun a v => read s a = v)
          (y := (Classical.choose hv, k)) (F := fun a => (a, k))
          (h := hrun k s _ hp hv'.1 hv'.2) fun a ha => ⟨ha, rfl⟩)
      rintro ⟨a, k'⟩ h₁ ⟨v, k''⟩ h₂ ⟨hh, hr, hk⟩
      exact ⟨Prod.ext hr hk, hh⟩
  · intro k u e
    unfold gateSrcSys gateSrcStepSt chooseSt
    beta_reduce
    by_cases h : Pre (enter e u) ∧ ∃ v, gatedRun srcRun (srcK k) (enter e u) v
    · simp only [dite_eq_left h, ite_eq_left_of_eq_true _ _ (eq_true h), dite_eq_left h.2,
        SPComp.map, SPComp.pure_bind]
    · simp only [dite_eq_right h, ite_eq_right_of_eq_false _ _ (eq_false h), SPComp.map,
        SPComp.pure_bind]
  · intro k t e
    unfold gateTgtSysRun gateTgtStepSt
    beta_reduce
    by_cases h : (Pre (enter e t) ∧ ∃ v, gatedRun srcRun (srcK k) (enter e t) v) ∧
        ∃ tr, leakRun (enter e t) tr
    · simp only [dite_eq_left h, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp only [dite_eq_right h, SPComp.map, SPComp.pure_bind]

end CarriedState

/-! ## The instance of the hax compiler with stateful linked functions -/

section Instance

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed
open _root_.Hax (Value Env Outcome)
open CatCrypt.Crypto.Hax (HaxModule hax64WExit)

variable {m : HaxModule}

/-- **The source run under a stateful oracle, keeping the final oracle state**: interpret the
    source tree under `O.step` from the oracle state `x` and read back the value of the source
    leaf with the final oracle state. -/
noncomputable def stSrcS (O : StOracle m) (t : CallTree linkSig (Outcome × Env)) (x : O.St) :
    SPComp (Value × O.St) :=
  readBack (fun p => (srcRead p.1).map fun v => (v, p.2)) (interpSt O.step t x)

/-- **The witnesses of a source run from the oracle state `x`**: an environment read off the
    entry state `narrowEntry m σ sa` and fuels at which the source run under `O` from `x` does
    not fail. -/
def haxcStRuns (m : HaxModule) (σ : AbiLayout) (O : StOracle m) (x : O.St) (sa : AState)
    (w : Env × Nat × Nat) : Prop :=
  σ.EnvOf (narrowEntry m σ sa) w.1 ∧
    ∀ s, stSrcS O (nfTree (moduleTreeTable m hax64WExit w.2.1) w.2.2 m.entry.erase w.1) x s
      none = 0

/-- **The source relation at the oracle state `x`**: the source relation `haxcSrcRun` at the
    entry states from which a source run under `O` from `x` does not fail. -/
def haxcStSrcRel (m : HaxModule) (σ : AbiLayout) (O : StOracle m) (x : O.St) (sa : AState)
    (v : Value) : Prop :=
  haxcSrcRun m σ sa v ∧ ∃ w, haxcStRuns m σ O x sa w

open Classical in
/-- **The source computation of one call at the oracle state `x`**: the source run under `O`
    from `x` at chosen witnesses, keeping the final oracle state; failure where no witness
    exists. -/
noncomputable def haxcStSrc (m : HaxModule) (σ : AbiLayout) (O : StOracle m) (x : O.St)
    (sa : AState) : SPComp (Value × O.St) :=
  if h : ∃ w, haxcStRuns m σ O x sa w then
    stSrcS O (nfTree (moduleTreeTable m hax64WExit (Classical.choose h).2.1)
      (Classical.choose h).2.2 m.entry.erase (Classical.choose h).1) x
  else SPComp.fail

/-- **The interpretation of the target trees under a stateful target handler, keeping the
    final handler state**, from the entry state `sa` and the handler state `x`. -/
noncomputable def interpTargetStSω {S : Type} (m : HaxModule) (pc : List RInstr)
    (sym : Nat → String) (sa : AState)
    (h₂ : ∀ e : (kSig AState).Event, S → SPComp ((kSig AState).Resp e × S)) (x : S) :
    SPComp (AState × S) :=
  interpStSω h₂ (fun n => targetTree aMachine pc sym (linkRead m) n 0 sa)
    (fuelMono_targetTree aMachine pc sym (linkRead m) 0 sa) x

/-- **The compiled module with stateful linked functions**, as a reactive system: the oracle
    state is drawn by `O.init` at the first activation, and at the oracle state `x` a call
    interprets the calling body under `h₂` from `x`, answers the result `σ` reads back with the
    leakage trace of `prog`, and holds the return state and the final handler state. -/
noncomputable def haxcStTgtSys (m : HaxModule) (σ : AbiLayout) (pc : List RInstr)
    (sym : Nat → String) (O : StOracle m)
    (h₂ : ∀ e : (kSig AState).Event, O.St → SPComp ((kSig AState).Resp e × O.St))
    (prog : List RInstr) (t₀ : AState) :
    Sys (Option O.St × AState) AState (Option (Value × List CTLeak)) :=
  stSys O.init (gateTgtStepSt (abiEnter σ) σ.Regions (haxcStSrcRel m σ O) (haxcLeakRun prog)
    (fun x sa => interpTargetStSω m pc sym sa h₂ x) (fun sa s' => σ.result.read sa s')) t₀

/-- **The source module with stateful linked functions**, as a reactive system: the oracle state
    is drawn by `O.init` at the first activation, and at the oracle state `x` a call answers a
    value of the source run under `O` from `x` and holds the final oracle state. -/
noncomputable def haxcStSrcSys (m : HaxModule) (σ : AbiLayout) (O : StOracle m)
    (u₀ : AState) : Sys (Option O.St × AState) AState (Option Value) :=
  stSys O.init (gateSrcStepSt (abiEnter σ) σ.Regions (haxcStSrcRel m σ O) (haxcStSrc m σ O)) u₀

/-- The witnesses of a source run from the entry state of a call are those from its event. -/
theorem haxcStRuns_abiEnter (σ : AbiLayout) (O : StOracle m) (x : O.St) (e t : AState) :
    haxcStRuns m σ O x (abiEnter σ e t) = haxcStRuns m σ O x e := by
  funext w
  simp only [haxcStRuns, envOf_narrowEntry_abiEnter]

/-- The source relation at an oracle state from the entry state of a call is that from its
    event. -/
theorem haxcStSrcRel_abiEnter (σ : AbiLayout) (O : StOracle m) (x : O.St) (e t : AState) :
    haxcStSrcRel m σ O x (abiEnter σ e t) = haxcStSrcRel m σ O x e := by
  funext v
  unfold haxcStSrcRel
  rw [haxcSrcRun_abiEnter, haxcStRuns_abiEnter]

/-- The source computation at an oracle state from the entry state of a call is that from its
    event. -/
theorem haxcStSrc_abiEnter (σ : AbiLayout) (O : StOracle m) (x : O.St) (e t : AState) :
    haxcStSrc m σ O x (abiEnter σ e t) = haxcStSrc m σ O x e := by
  unfold haxcStSrc
  rw [haxcStRuns_abiEnter]

/-- **One call at an oracle state.** Let a source tree be related by `RuttFA` to the target
    trees of the calling body from `sa`, let the stateful target handler be coupled with `O`,
    let the source run from `x` not fail, and let `ε` bound the failure weight of the target
    interpretation from `x`. The target interpretation and the source run are related at grade
    `ε` with the read-back result equal to the source value and the final handler states
    equal. -/
theorem rHoareApprox_interpTargetStSω {σ : AbiLayout} {sa : AState} {pc : List RInstr}
    {sym : Nat → String} (O : StOracle m)
    {h₂ : ∀ e : (kSig AState).Event, O.St → SPComp ((kSig AState).Resp e × O.St)}
    (hc : HandlerCoupledSt O h₂) {t₁ : CallTree linkSig (Outcome × Env)}
    (h : RuttFA (SkipAns TypedAns m) (contractREG m) (contractRACA TypedAns m) (resRel σ sa)
      srcFail t₁ (fun n => targetTree aMachine pc sym (linkRead m) n 0 sa))
    {x : O.St} (hnf : ∀ s, stSrcS O t₁ x s none = 0) {ε : ℝ≥0∞}
    (hε : ∀ s, interpTargetStSω m pc sym sa h₂ x s none ≤ ε) :
    rHoareApprox ε eqPre (interpTargetStSω m pc sym sa h₂ x) (stSrcS O t₁ x)
      (fun a h₁ b h₂ => (σ.result.read sa a.1, a.2) = b ∧ h₁ = h₂) := by
  have hT := fuelMono_targetTree aMachine pc sym (linkRead m) 0 sa
  have hN : ∀ N, RelF eqPre (stSrcS O t₁ x)
      (readBack (fun a => some (σ.result.read sa a.1, a.2))
        (interpStS h₂ (targetTree aMachine pc sym (linkRead m) N 0 sa) x)) eqPost := fun N => by
    unfold stSrcS readBack
    refine RelF.bind (relF_interpStS_ruttFA hc O.skips (fun _ => srcFail_of_resRel_none) h hT N
      _ (fuelLe_refl _) x x rfl) fun p₁ y => ?_
    cases hv : srcRead p₁.1 with
    | none =>
      simp only [hv, Option.map_none]
      exact RelF.fail_left
    | some v =>
      simp only [hv, Option.map_some]
      refine RelF.ret fun s₁ s₂ hp => ?_
      rcases hp with hf | ⟨hR, hσ, hs⟩
      · rw [srcRead_of_srcFail hf] at hv
        cases hv
      · exact ⟨Prod.ext (read_of_resRel hR hv).symm hσ, hs⟩
  let C := interpStSChain h₂ (fun n => targetTree aMachine pc sym (linkRead m) n 0 sa) hT x
  let rb : AState × O.St → Option (Value × O.St) := fun a => some (σ.result.read sa a.1, a.2)
  have hω : interpTargetStSω m pc sym sa h₂ x = ωSup C := rfl
  have hC : ∀ N, C N = interpStS h₂ (targetTree aMachine pc sym (linkRead m) N 0 sa) x :=
    fun _ => rfl
  rw [hω]
  have key : ∀ s,
      tvMargin (stSrcS O t₁ x s) (readBack rb (ωSup C) s) ≤ readBack rb (ωSup C) s none ∧
      tvMargin (readBack rb (ωSup C) s) (stSrcS O t₁ x s) ≤ stSrcS O t₁ x s none :=
    fun s => tvMargin_le_of_iSup (d' := fun N => readBack rb (C N) s)
      (fun y => readBack_chain_mono rb C s y)
      (fun y => readBack_ωSup_apply_some rb C s y)
      (fun N => by rw [hC N]; exact tvMargin_le_none_of_relF (hN N) s)
      (fun N => by rw [hC N]; exact tvMargin_le_none_of_relF (hN N).symm_eq s)
  rw [← hω] at key ⊢
  clear_value C
  have h₁ : ∀ s, tvMargin (readBack rb (interpTargetStSω m pc sym sa h₂ x) s)
      (stSrcS O t₁ x s) ≤ 0 := fun s => (key s).2.trans (hnf s).le
  have h₂' : ∀ s, tvMargin (stSrcS O t₁ x s)
      (readBack rb (interpTargetStSω m pc sym sa h₂ x) s) ≤ ε := fun s => by
    refine (key s).1.trans ?_
    rw [readBack_some_apply_none]
    exact hε s
  exact rHoareApprox_graph_of_tvMargin h₁ h₂'

/-- **Reactive robust compilation with stateful linked functions.** Let the source trees of `m`
    be related by `RuttFA` to the target trees of the calling body `pc` at every entry state of
    the domain (the conclusion of `NFCallTreeR3TypedAns.r3FA_of_shape_int`), let the linked
    program `prog` satisfy the gate conclusion, let the stateful target handler `h₂` be coupled
    with the stateful oracle `O`, and let `ε` bound the failure weight of the target
    interpretation under `h₂` at every handler state and every entry state of the domain. Then
    the compiled module with the linked functions answered by `h₂` realizes the source module
    with the linked calls answered by `O`, both carrying the oracle state across activations,
    behind the per-call leakage simulator `haxcLeakSim`, at `Z.input.rounds * ε`, for all
    initial kept states. -/
theorem haxc_rrcHSt_of_ruttFA {σ : AbiLayout} {pc prog : List RInstr} {sym : Nat → String}
    (O : StOracle m)
    (hrel : ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
      ∀ fuelC fuel,
        RuttFA (SkipAns TypedAns m) (contractREG m) (contractRACA TypedAns m) (resRel σ sa)
          srcFail (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)
          (fun n => targetTree aMachine pc sym (linkRead m) n 0 sa))
    (g : GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ) (haxcTgtRes σ prog)
      (haxcLeakRun prog))
    {h₂ : ∀ e : (kSig AState).Event, O.St → SPComp ((kSig AState).Resp e × O.St)}
    (hh : HandlerCoupledSt O h₂) {ε : ℝ≥0∞}
    (hε : ∀ sa, σ.Regions sa → ∀ x s, interpTargetStSω m pc sym sa h₂ x s none ≤ ε)
    (t₀ u₀ : AState) :
    RealizesSim (haxcStTgtSys m σ pc sym O h₂ prog t₀) (haxcStSrcSys m σ O u₀)
      (haxcLeakSim m σ prog) (fun _ Z => Z.input.rounds * ε) := by
  refine realizesSim_of_gate_run_st g (pubOf σ) (pubAgree_of_pubOf_eq σ)
    (fun s v _ h => haxcLeakRun_of_tgtRes σ prog s v h) (abiEnter σ) (pubOf σ)
    (fun e t u => (regions_abiEnter σ e t).trans (regions_abiEnter σ e u).symm)
    (pubOf_abiEnter σ) O.init (haxcStSrcRel m σ O) (fun _ _ v h => ⟨v, h.1⟩)
    (fun x e t u => (haxcStSrcRel_abiEnter σ O x e t).trans
      (haxcStSrcRel_abiEnter σ O x e u).symm) _ _ (haxcStSrc m σ O)
    (fun x e t u => (haxcStSrc_abiEnter σ O x e t).trans (haxcStSrc_abiEnter σ O x e u).symm)
    ε (fun x sa hs hv => ?_) t₀ u₀
  obtain ⟨_, -, hD⟩ := hv
  obtain ⟨hE, hnf⟩ := Classical.choose_spec hD
  simp only [haxcStSrc, dite_eq_left hD]
  exact rHoareApprox_interpTargetStSω O hh (hrel sa hs _ hE _ _) hnf (hε sa hs x)

/-- **Reactive robust compilation of a result of `compileA` with stateful linked functions.**
    From a decoding of the bytes into a calling body `pc` followed by the shifted linked code
    `Q`, the gate conclusion of the linked program and the `RuttFA` relation of the source and
    target trees (the conclusion of `NFCallTreeR3TypedAns.r3FA_of_shape_int`): for every
    stateful oracle `O`, every stateful target handler `h₂` coupled with `O` and every bound `ε`
    of its failure weight, the compiled module realizes its source behind `haxcLeakSim` at
    `Z.input.rounds * ε`. -/
theorem haxc_rrcHSt {σ : AbiLayout} {bytes : List (BitVec 8)}
    (hrcS : ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ)
        (haxcTgtRes σ (pc ++ shiftProg pc.length Q)) (haxcLeakRun (pc ++ shiftProg pc.length Q)) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel,
          RuttFA (SkipAns TypedAns m) (contractREG m) (contractRACA TypedAns m) (resRel σ sa)
            srcFail (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)
            (fun n => targetTree aMachine pc sym (linkRead m) n 0 sa)) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      ∀ (O : StOracle m)
        (h₂ : ∀ e : (kSig AState).Event, O.St → SPComp ((kSig AState).Resp e × O.St)),
        HandlerCoupledSt O h₂ → ∀ ε : ℝ≥0∞,
        (∀ sa, σ.Regions sa → ∀ x s, interpTargetStSω m pc sym sa h₂ x s none ≤ ε) →
        ∀ t₀ u₀ : AState,
        RealizesSim (haxcStTgtSys m σ pc sym O h₂ (pc ++ shiftProg pc.length Q) t₀)
          (haxcStSrcSys m σ O u₀) (haxcLeakSim m σ (pc ++ shiftProg pc.length Q))
          (fun _ Z => Z.input.rounds * ε) := by
  obtain ⟨pc, Q, sym, hd, g, hrel⟩ := hrcS
  exact ⟨pc, Q, sym, hd, fun O h₂ hh ε hε t₀ u₀ =>
    haxc_rrcHSt_of_ruttFA O hrel g hh hε t₀ u₀⟩

/-- **The keyed oracle as a stateful oracle.** At the stateful oracle `keyedSt O` of a keyed
    oracle, whose handler state is the key drawn at the first activation and kept, and a target
    handler family coupled with `O`, the conclusion of `haxc_rrcHSt_of_ruttFA`. -/
theorem haxc_rrcHSt_keyedSt_of_ruttFA {σ : AbiLayout} {pc prog : List RInstr}
    {sym : Nat → String} (O : KeyedOracle m)
    (hrel : ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
      ∀ fuelC fuel,
        RuttFA (SkipAns TypedAns m) (contractREG m) (contractRACA TypedAns m) (resRel σ sa)
          srcFail (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)
          (fun n => targetTree aMachine pc sym (linkRead m) n 0 sa))
    (g : GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ) (haxcTgtRes σ prog)
      (haxcLeakRun prog))
    {h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hh : HandlerCoupledKeyed O h₂) {ε : ℝ≥0∞}
    (hε : ∀ sa, σ.Regions sa → ∀ x s,
      interpTargetStSω m pc sym sa (constSt h₂) x s none ≤ ε)
    (t₀ u₀ : AState) :
    RealizesSim (haxcStTgtSys m σ pc sym (keyedSt O) (constSt h₂) prog t₀)
      (haxcStSrcSys m σ (keyedSt O) u₀) (haxcLeakSim m σ prog)
      (fun _ Z => Z.input.rounds * ε) :=
  haxc_rrcHSt_of_ruttFA (keyedSt O) hrel g (handlerCoupledSt_keyedSt hh) hε t₀ u₀

end Instance

end CatCrypt.Crypto.SecureCompilation.Haxc
