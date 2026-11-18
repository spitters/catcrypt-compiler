/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RCReactive
public import CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerSourceRun

/-!
# Reactive robust compilation of the hax compiler with stateless linked functions

`Haxc.RCReactive` states reactive robust compilation at distance `0` for modules without
callees and linked functions. This module states it for modules whose linked functions are
answered by a stateless handler: a fixed Kleisli map `h₂` from the call events of the linked
functions to `SPComp`, coupled with the meanings `sem` of the linked functions on the separation
contracts (`HandlerCoupledCG`). One call of the compiled module interprets the calling body `pc`
under `h₂` from the entry state of the call (`interpTargetω`), reads the result back with `σ`, and
keeps the return state; the leakage trace is that of the linked program `prog`. The source system
and the per-call leakage simulator are those of `Haxc.RCReactive`.

The bound is per call the bound `ε` of the failure weight of the target interpretation under the
handlers of the class, the bound of `HandlerRC` at a source run (the source read-back then does
not fail), summed over the rounds of the run: `Z.input.rounds * ε`.

## Main definitions

* `gateTgtSysRun` — the reactive target system of a gate conclusion whose value is read back from
  a computation `run` of the return state.
* `haxcTgtSysH` — the compiled module with the linked functions answered by the handler `h₂`.

## Main results

* `liftRApprox_pure_right_of_mass`, `rHoareApprox_pure_right_of_mass` — an approximate coupling
  with a point mass from a bound on the mass outside the post-relation.
* `one_sub_mass_le_of_sdist_map` — a statistical distance `ε` between `map g c` and the point
  mass at `v` bounds the mass of `c` outside `g a = v` (at the initial heap) by `ε`.
* `rHoareApprox_map_pure_of_sdist` — one coupled activation against a point mass from that
  statistical distance.
* `realizesSim_of_gate_run` — the target system realizes the source system behind the leakage
  simulator at `Z.input.rounds * ε`, from a per-call statistical distance `ε` of the read-back
  values; an instance of `realizesSim_of_gate_dom`.
* `haxc_rrcH_of_handlerRC` — the instance for the hax compiler, from `HandlerRC` and the gate
  conclusion of the linked program; `haxc_rrcH_zero` its form at `0`.
* `haxc_rrcH` — from the conclusion of `haxc_rcH`.

## Search words

reactive robust compilation, RrHP, linked functions, stateless handler, per-call bound,
summed over rounds, leakage simulator, ABI view
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

/-! ## Approximate couplings with a point mass -/

section PointMass

variable {α β : Type}

open Classical in
/-- **A sub-coupling with a point mass.** When the mass of `d` on the elements related to `b` is
    at least `1 - ε`, `d` and the point mass at `b` are related at grade `ε`. -/
theorem liftRApprox_pure_right_of_mass {d : SDistr α} {b : β} {R : α → β → Prop} {ε : ℝ≥0∞}
    (h : 1 - ∑' a, (if R a b then d (some a) else 0) ≤ ε) :
    liftRApprox ε R d (SDistr.pure b) := by
  set M := ∑' a, (if R a b then d (some a) else 0) with hM
  set w : SDistr (α × β) := d.bind fun x => if R x b then SDistr.pure (x, b) else SDistr.fail
  have hjoint : ∀ a b', w (some (a, b')) = if R a b ∧ b' = b then d (some a) else 0 := by
    intro a b'
    rw [SDistr.bind_apply_some, tsum_eq_single a]
    · by_cases hb : b' = b
      · subst hb; by_cases hR : R a b' <;> simp [hR, SDistr.pure_apply_some, SDistr.fail_apply_some]
      · by_cases hR : R a b <;>
          simp [hR, hb, Ne.symm hb, SDistr.pure_apply_some, SDistr.fail_apply_some]
    · intro x hx
      by_cases hR : R x b <;> simp [hR, SDistr.pure_apply_some, SDistr.fail_apply_some, hx]
  have hrow : ∀ a, ∑' b', w (some (a, b')) = if R a b then d (some a) else 0 := by
    intro a
    simp_rw [hjoint]
    rw [tsum_eq_single b fun b' hb => by simp [hb]]
    simp
  have hcol : ∀ b', ∑' a, w (some (a, b')) = if b' = b then M else 0 := by
    intro b'
    simp_rw [hjoint]
    by_cases hb : b' = b <;> simp [hb, hM]
  have htot : ∑' a, d (some a) ≤ 1 := by
    have hone : d none + ∑' a, d (some a) = 1 := by
      rw [← SDistr.tsum_option_eq_add]; exact d.tsum_coe
    exact hone ▸ le_add_self
  have hM1 : M ≤ 1 :=
    (ENNReal.tsum_le_tsum fun a => by split_ifs <;> simp).trans htot
  have hsplit : ∑' a, (d (some a) - if R a b then d (some a) else 0) + M =
      ∑' a, d (some a) := by
    rw [hM, ← ENNReal.tsum_add]
    exact tsum_congr fun a => by split_ifs <;> simp
  refine ⟨⟨w, fun a => ?_, fun b' => ?_, ?_, ?_⟩, ?_⟩
  · rw [hrow]; split_ifs <;> simp
  · rw [hcol]; split_ifs with hb <;> simp [hb, SDistr.pure_apply_some, hM1]
  · simp_rw [hrow]
    refine le_trans ?_ h
    refine ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top ENNReal.one_ne_top hM1) ?_
    exact hsplit ▸ htot
  · simp_rw [hcol]
    rw [tsum_eq_single b fun b' hb => by simp [hb, SDistr.pure_apply_some, Ne.symm hb]]
    simpa [SDistr.pure_apply_some] using h
  · intro a b' hw
    rw [hjoint] at hw
    grind

/-- **A graded judgment against a point mass.** When, at every initial heap `s`, the mass of
    `c s` on the pairs related to `(b, s)` by `Ψ` is at least `1 - ε`, `c` and `pure b` are
    related at grade `ε` at equal initial heaps. -/
theorem rHoareApprox_pure_right_of_mass {c : SPComp α} {b : β} {Ψ : RPost α β} {ε : ℝ≥0∞}
    (h : ∀ s, 1 - ∑' p : α × Heap,
      (open Classical in if Ψ p.1 p.2 b s then c s (some p) else 0) ≤ ε) :
    rHoareApprox ε eqPre c (SPComp.pure b) Ψ := by
  rintro s s' (rfl : s = s')
  exact liftRApprox_pure_right_of_mass (R := fun (p : α × Heap) (q : β × Heap) => Ψ p.1 p.2 q.1 q.2)
    (h s)

open Classical in
/-- **The mass bound of a statistical distance to a point mass.** When `map g c` is at
    statistical distance at most `ε` from the point mass at `v`, the mass of `c s` on the pairs
    with value `g a = v` and final heap `s` is at least `1 - ε`. -/
theorem one_sub_mass_le_of_sdist_map {c : SPComp α} {g : α → β} {v : β} {ε : ℝ≥0∞}
    (h : sdist (fun _ : Unit => SPComp.map g c) (fun _ : Unit => SPComp.pure v) ≤ ε)
    (s : Heap) :
    1 - ∑' p : α × Heap, (if g p.1 = v ∧ p.2 = s then c s (some p) else 0) ≤ ε := by
  obtain ⟨w, hw⟩ := rHoareApprox_of_sdist h s s rfl
  have h1 : 1 - ∑' x, w.joint (some (x, (v, s))) ≤ ε := by
    refine le_trans ?_ w.right_deficit
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (v, s))
    simp [SPComp.pure, SDistr.pure_apply_some]
  have h2 : ∑' x, w.joint (some (x, (v, s))) ≤ (SPComp.map g c) s (some (v, s)) := by
    rw [tsum_eq_single (v, s) fun x hx => by
      by_contra h0
      exact hx (Prod.ext (hw x (v, s) h0).1 (hw x (v, s) h0).2)]
    exact (ENNReal.le_tsum (v, s)).trans (w.left_le (v, s))
  have h3 : (SPComp.map g c) s (some (v, s)) =
      ∑' p : α × Heap, (if g p.1 = v ∧ p.2 = s then c s (some p) else 0) := by
    simp only [SPComp.map, SPComp.bind, SPComp.pure]
    rw [SDistr.bind_apply_some]
    refine tsum_congr fun p => ?_
    by_cases hp : g p.1 = v ∧ p.2 = s <;> simp [hp, SDistr.pure_apply_some]
  exact le_trans (tsub_le_tsub_left (h2.trans h3.le) 1) h1

/-- **One activation against a point mass from a statistical distance.** Let `map g c` be at
    statistical distance at most `ε` from the point mass at `v`, and let every `a` with
    `g a = v` give a step `F a` whose state is related to that of `y` and whose output is that
    of `y`. Then `map F c` and `pure y` are related at grade `ε` by `stepPost rel`. -/
theorem rHoareApprox_map_pure_of_sdist {τ υ O : Type} {c : SPComp α} {g : α → β} {v : β}
    {F : α → τ × O} {y : υ × O} {rel : τ → υ → Prop} {ε : ℝ≥0∞}
    (hF : ∀ a, g a = v → rel (F a).1 y.1 ∧ (F a).2 = y.2)
    (h : sdist (fun _ : Unit => SPComp.map g c) (fun _ : Unit => SPComp.pure v) ≤ ε) :
    rHoareApprox ε eqPre (SPComp.map F c) (SPComp.pure y) (stepPost rel) := by
  have hpre : rHoareApprox ε eqPre c (SPComp.pure ())
      (fun a h₁ _ h₂ => g a = v ∧ h₁ = h₂) :=
    rHoareApprox_pure_right_of_mass fun s => by convert one_sub_mass_le_of_sdist_map h s
  rw [← SPComp.pure_bind () (fun _ => SPComp.pure y)]
  refine rHoareApprox_mono_eps (le_of_eq (add_zero ε)) (rHoareApprox_bind hpre fun a _ => ?_)
  refine rHoareApprox_of_rHoare (rHoare_ret fun _ _ hh => ?_)
  exact ⟨hh.2, (hF a hh.1).1, (hF a hh.1).2⟩

end PointMass

/-! ## Reactive target systems with a computed return state -/

section Gate

variable {St E V Tr P : Type}

open Classical in
/-- **The reactive target system of a gate conclusion with a computed return state.** In the
    domain of the one-call statement the call from the entry state `x = enter e t` runs the
    computation `run x` of the return state `s'`, answers the value `read x s'` with the leakage
    trace of `x`, and keeps `s'`; outside the domain it answers `none` and keeps `t`. -/
noncomputable def gateTgtSysRun (enter : E → St → St) (Pre : St → Prop) (srcRun : St → V → Prop)
    (leakRun : St → Tr → Prop) (run : St → SPComp St) (read : St → St → V) (init : St) :
    Sys St E (Option (V × Tr)) where
  init := init
  step t e :=
    if h : (Pre (enter e t) ∧ ∃ v, srcRun (enter e t) v) ∧ ∃ tr, leakRun (enter e t) tr then
      SPComp.map (fun s' => (s', some (read (enter e t) s',
        leakOf (Pre := Pre) (srcRun := srcRun) (leakRun := leakRun) ⟨enter e t, h⟩)))
        (run (enter e t))
    else SPComp.pure (t, none)

/-- **Reactive robust compilation from per-call statistical distances.** Let the gate
    conclusion give constant-time leakage, with public projections whose equality implies the
    public relation and a target that has a leakage trace whenever it has a result, and let
    the entry map `enter` give entry states whose precondition and
    source runs do not depend on the kept state and whose public projection is `pe e`. When at
    every entry state `i` of the domain the read-back value `map (read i) (run i)` is at
    statistical distance at most `ε` from the source value, the target system realizes the
    source system behind the leakage simulator at `ε` per activation, `Z.input.rounds * ε` in
    all. -/
theorem realizesSim_of_gate_run [Nonempty Tr] {Pre : St → Prop} {Pub : St → St → Prop}
    {srcRun : St → V → Prop} {tgtRes : St → V → Prop} {leakRun : St → Tr → Prop}
    (g : GateConclusion Pre Pub srcRun tgtRes leakRun) (pub : St → P)
    (hpub : ∀ s₁ s₂, pub s₁ = pub s₂ → Pub s₁ s₂)
    (hterm : ∀ s v, Pre s → tgtRes s v → ∃ tr, leakRun s tr)
    (enter : E → St → St) (pe : E → P)
    (hPre : ∀ e t u, Pre (enter e t) ↔ Pre (enter e u))
    (hsrc : ∀ e t u, srcRun (enter e t) = srcRun (enter e u))
    (hpe : ∀ e t, pub (enter e t) = pe e) (run : St → SPComp St) (read : St → St → V)
    (ε : ℝ≥0∞)
    (hrun : ∀ i : Dom Pre srcRun leakRun, sdist (fun _ : Unit => SPComp.map (read i.1) (run i.1))
      (fun _ : Unit => SPComp.pure (srcOf i)) ≤ ε)
    (t₀ u₀ : St) :
    RealizesSim (gateTgtSysRun enter Pre srcRun leakRun run read t₀)
      (gateSrcSys enter Pre srcRun u₀) (leakSim pe (simLeak Pre srcRun leakRun pub))
      (fun _ Z => Z.input.rounds * ε) := by
  refine realizesSim_of_gate_dom g pub hterm enter pe hPre hsrc _ ε (fun t e hT _ => ?_)
    (fun t e hT => by simp only [gateTgtSysRun, dite_eq_right hT]) u₀
  simp only [gateTgtSysRun, dite_eq_left hT]
  refine rHoareApprox_map_pure_of_sdist (h := hrun ⟨enter e t, hT⟩) fun s' hs' => ⟨trivial, ?_⟩
  rw [hs', leakOf_eq_simLeak g pub hpub, hpe]

end Gate

/-! ## The instance of the hax compiler with stateless linked functions -/

section Instance

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerInstance
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerSourceRun (readBack_srcRead_of_runs)
open _root_.Hax (Value)
open CatCrypt.Crypto.Hax (HaxModule)

/-- **The compiled module with the linked functions answered by the handler `h₂`**, as a
    reactive system: `gateTgtSysRun` at the entry map `abiEnter σ`, where a call interprets the
    calling body `pc` under `h₂` from its entry state (`interpTargetω`), answers the result `σ`
    reads back from the return state with the leakage trace of the linked program `prog`, and
    keeps the return state. -/
noncomputable def haxcTgtSysH (m : HaxModule) (σ : AbiLayout) (pc : List RInstr)
    (sym : Nat → String)
    (h₂ : ∀ e : (TargetCallTree.kSig AState).Event, SPComp ((TargetCallTree.kSig AState).Resp e))
    (prog : List RInstr) (t₀ : AState) : Sys AState AState (Option (Value × List CTLeak)) :=
  gateTgtSysRun (abiEnter σ) σ.Regions (haxcSrcRun m σ) (haxcLeakRun prog)
    (fun sa => interpTargetω m pc sym sa h₂) (fun sa s' => σ.result.read sa s') t₀

/-- **One call under a coupled handler from `HandlerRC`.** Let `ε` bound the failure weight of
    the target interpretation under every handler of the class at every entry state of the
    domain. At an entry state `sa` of the domain from which the source runs to `v`, the value
    read back from the interpretation of `pc` under a coupled handler `h₂` is at statistical
    distance at most `ε` from the point mass at `v`. -/
theorem sdist_interpTargetω_le_of_handlerRC {m : HaxModule} {σ : AbiLayout} {pc : List RInstr}
    {sym : Nat → String} (hRC : HandlerRC m σ pc sym)
    {h₂ : ∀ e : (TargetCallTree.kSig AState).Event, SPComp ((TargetCallTree.kSig AState).Resp e)}
    (hh : HandlerCoupledCG m eqPre h₂) {ε : ℝ≥0∞}
    (hε : ∀ sa, σ.Regions sa → ∀ h, HandlerCoupledCG m eqPre h → ∀ s,
      interpTargetω m pc sym sa h s none ≤ ε)
    {sa : AState} (hs : σ.Regions sa) {v : Value} (hv : haxcSrcRun m σ sa v) :
    sdist (fun _ : Unit => SPComp.map (fun s' => σ.result.read sa s')
        (interpTargetω m pc sym sa h₂))
      (fun _ : Unit => SPComp.pure v) ≤ ε := by
  obtain ⟨env, fuelC, fuel, hE, hrb⟩ := readBack_srcRead_of_runs hv
  have h0 := hRC sa hs env hE fuelC fuel ε 0 (hε sa hs) fun s => by
    rw [hrb]; simp [SPComp.pure, SDistr.pure_apply_none]
  have h1 := (robustCompilationH_iff_sdist _ _ _ _).mp h0 h₂ hh
  rw [hrb, add_zero] at h1
  exact h1

/-- **Reactive robust compilation with stateless linked functions.** Let `HandlerRC` hold at
    the calling body `pc`, let the linked program `prog` satisfy the gate conclusion, and let
    `ε` bound the failure weight of the target interpretation under every handler coupled with
    the meanings of the linked functions, at every entry state of the domain. For every such
    handler `h₂`, the compiled module with the linked functions answered by `h₂` realizes the
    source module behind the per-call leakage simulator `haxcLeakSim` at `ε` per call,
    `Z.input.rounds * ε` in all, for all initial kept states. The observation is the ABI view of
    each call (definedness, the result `σ` reads back, the leakage trace). -/
theorem haxc_rrcH_of_handlerRC {m : HaxModule} {σ : AbiLayout} {pc prog : List RInstr}
    {sym : Nat → String} (hRC : HandlerRC m σ pc sym)
    (g : GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ) (haxcTgtRes σ prog)
      (haxcLeakRun prog))
    {h₂ : ∀ e : (TargetCallTree.kSig AState).Event, SPComp ((TargetCallTree.kSig AState).Resp e)}
    (hh : HandlerCoupledCG m eqPre h₂) {ε : ℝ≥0∞}
    (hε : ∀ sa, σ.Regions sa → ∀ h, HandlerCoupledCG m eqPre h → ∀ s,
      interpTargetω m pc sym sa h s none ≤ ε)
    (t₀ u₀ : AState) :
    RealizesSim (haxcTgtSysH m σ pc sym h₂ prog t₀) (haxcSrcSys m σ u₀) (haxcLeakSim m σ prog)
      (fun _ Z => Z.input.rounds * ε) := by
  refine realizesSim_of_gate_run g (pubOf σ) (pubAgree_of_pubOf_eq σ)
    (fun s v _ h => haxcLeakRun_of_tgtRes σ prog s v h) (abiEnter σ) (pubOf σ)
    (fun e t u => (regions_abiEnter σ e t).trans (regions_abiEnter σ e u).symm)
    (fun e t u => (haxcSrcRun_abiEnter m σ e t).trans (haxcSrcRun_abiEnter m σ e u).symm)
    (pubOf_abiEnter σ) (fun sa => interpTargetω m pc sym sa h₂)
    (fun sa s' => σ.result.read sa s') ε (fun i => ?_) t₀ u₀
  exact sdist_interpTargetω_le_of_handlerRC hRC hh hε i.2.1.1 (Classical.choose_spec i.2.1.2)

/-- **Reactive robust compilation at `0` with stateless linked functions**: under the
    hypotheses of `haxc_rrcH_of_handlerRC`, when the target interpretation does not fail under
    any handler of the class at any entry state of the domain. -/
theorem haxc_rrcH_zero {m : HaxModule} {σ : AbiLayout} {pc prog : List RInstr}
    {sym : Nat → String} (hRC : HandlerRC m σ pc sym)
    (g : GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ) (haxcTgtRes σ prog)
      (haxcLeakRun prog))
    {h₂ : ∀ e : (TargetCallTree.kSig AState).Event, SPComp ((TargetCallTree.kSig AState).Resp e)}
    (hh : HandlerCoupledCG m eqPre h₂)
    (hε : ∀ sa, σ.Regions sa → ∀ h, HandlerCoupledCG m eqPre h → ∀ s,
      interpTargetω m pc sym sa h s none = 0)
    (t₀ u₀ : AState) :
    RealizesSim (haxcTgtSysH m σ pc sym h₂ prog t₀) (haxcSrcSys m σ u₀) (haxcLeakSim m σ prog)
      (fun _ _ => 0) := by
  simpa using haxc_rrcH_of_handlerRC hRC g hh (ε := 0)
    (fun sa hs h hh' s => (hε sa hs h hh' s).le) t₀ u₀

/-- **Reactive robust compilation of a result of `compileA` with stateless linked functions.**
    From the conclusion of `haxc_rcH` (the bytes decode to a calling body `pc` followed by the
    shifted linked code `Q`, the gate conclusion of the linked program, and `HandlerRC` at
    `pc`): for every handler `h₂` coupled with the meanings of the linked functions and every
    bound `ε` of the failure weight of the target interpretation under the handlers of the
    class, the compiled module realizes its source behind `haxcLeakSim` at
    `Z.input.rounds * ε`. -/
theorem haxc_rrcH {m : HaxModule} {σ : AbiLayout} {bytes : List (BitVec 8)}
    (hrcH : ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ)
        (haxcTgtRes σ (pc ++ shiftProg pc.length Q)) (haxcLeakRun (pc ++ shiftProg pc.length Q)) ∧
      HandlerRC m σ pc sym) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      ∀ (h₂ : ∀ e : (TargetCallTree.kSig AState).Event,
          SPComp ((TargetCallTree.kSig AState).Resp e)), HandlerCoupledCG m eqPre h₂ →
        ∀ ε : ℝ≥0∞, (∀ sa, σ.Regions sa → ∀ h, HandlerCoupledCG m eqPre h → ∀ s,
          interpTargetω m pc sym sa h s none ≤ ε) → ∀ t₀ u₀ : AState,
        RealizesSim (haxcTgtSysH m σ pc sym h₂ (pc ++ shiftProg pc.length Q) t₀)
          (haxcSrcSys m σ u₀) (haxcLeakSim m σ (pc ++ shiftProg pc.length Q))
          (fun _ Z => Z.input.rounds * ε) := by
  obtain ⟨pc, Q, sym, hd, g, hRC⟩ := hrcH
  exact ⟨pc, Q, sym, hd, fun h₂ hh ε hε t₀ u₀ => haxc_rrcH_of_handlerRC hRC g hh hε t₀ u₀⟩

end Instance

end CatCrypt.Crypto.SecureCompilation.Haxc
