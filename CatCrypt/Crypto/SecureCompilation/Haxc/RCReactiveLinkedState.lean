/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed
public import CatCrypt.Crypto.SecureCompilation.Haxc.RCReactiveLinked

/-!
# Reactive robust compilation of the hax compiler with keyed linked functions

`Haxc.RCReactiveLinked` states reactive robust compilation for modules whose linked functions
are answered by a stateless handler. This module states it for linked functions that answer
from a key drawn once per reactive run: a keyed oracle `O` (`RCHandlerKeyed.KeyedOracle`) on
the source side, and a target handler family `h₂` indexed by the key, coupled at each key with
the answers `O.ans k` (`HandlerCoupledKeyed`).

Both reactive systems hold the key in their state. The first activation draws it by
`O.keyDist`, and every activation steps at the key held (`keyedSys`). At the key `k`, a call of
the source answers a value of the source run of the module with the linked calls answered by
`O.ans k` (`haxcKeyedSrcRun`), and a call of the compiled module interprets the calling body
under `h₂ k`, reads the result back with `σ` and keeps the return state. The domain of a call
is that of `Haxc.RCReactive` intersected with the domain of the keyed source run at the key
(`gatedRun`), so that the leakage trace of the linked program is simulated by the per-call
leakage simulator `haxcLeakSim` of the stateless statement.

The coupling of the two runs draws the same key on both sides at equal heaps (`rHoare_refl`)
and then couples each activation at that key, at the per-call bound `ε` of the failure weight of
the target interpretation; the bound of a run is `Z.input.rounds * ε`.

## Main definitions

* `keyedSys` — a reactive system that draws a key at its first activation and steps at it.
* `gatedRun` — a source relation restricted to the entry states of a run of another one.
* `RCHandlerKeyed.KeyedOracle.atKey` — the keyed oracle at a fixed key.
* `haxcKeyedSrcRun` — the source run of the module with the linked calls answered at a key.
* `haxcKeyedTgtSys`, `haxcKeyedSrcSys` — the compiled module and the source module with keyed
  linked functions, as reactive systems.

* `stSys` — a reactive system holding a state drawn at its first activation and passed on by
  every activation.
* `gateTgtStepSt`, `gateSrcStepSt` — one activation of the target and the source at a carried
  state.
* `chooseSt` — the source computation of a relation at a carried state.

## Main results

* `realizesSim_of_gate_run_st` — the generic reactive statement at a carried state.
* `realizesSim_of_gate_run_keyed` — the keyed target system realizes the keyed source system
  behind the leakage simulator at `Z.input.rounds * ε`, from per-key statistical distances `ε`
  of the read-back values.
* `haxc_rrcHKeyed_of_handlerRCKeyed` — the instance for the hax compiler, from
  `HandlerRCKeyed` at every fixed key and the gate conclusion of the linked program.
* `haxc_rrcHKeyed` — from `HandlerRCKeyed` at every keyed oracle (the conclusion of
  `haxc_rcHKeyed`) and the gate conclusion.
* `haxc_rrcHKeyed_point_of_handlerRC` — at the point oracle `pointOracle m`, from the
  hypotheses of `haxc_rrcH_of_handlerRC`.

## Search words

reactive robust compilation, RrHP, linked functions, keyed oracle, key drawn once, stateful
handler, per-call bound, summed over rounds, leakage simulator, ABI view
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

/-! ## Reactive systems with a key drawn at the first activation -/

section KeyedGate

variable {St E V Tr P K : Type}

/-- The key of an activation: the key held, or a draw by `kd` when none is held. -/
noncomputable def keyAt (kd : SPComp K) : Option K → SPComp K
  | some k => SPComp.pure k
  | none => kd

/-- **A reactive system with a key drawn at its first activation.** The state holds the key
    once drawn and the state of the steps `S`; each activation steps as `S k` at the key `k` it
    holds or draws by `kd`. -/
noncomputable def keyedSys {τ O : Type} (kd : SPComp K) (S : K → τ → E → SPComp (τ × O))
    (init : τ) : Sys (Option K × τ) E O where
  init := (none, init)
  step t e := SPComp.bind (keyAt kd t.1) fun k =>
    SPComp.bind (S k t.2 e) fun q => SPComp.pure ((some k, q.1), q.2)

/-- The source relation `srcK` restricted to the entry states from which `srcRun` has a run. -/
def gatedRun (srcRun srcK : St → V → Prop) (s : St) (v : V) : Prop :=
  (∃ w, srcRun s w) ∧ srcK s v

section CarriedState

variable {X : Type}

/-- **A reactive system carrying a state across activations.** The system state holds the
    carried state once drawn and the state of the steps; each activation draws the carried
    state by `kd` when none is held, steps as `S` at the carried state, and holds the carried
    state that `S` returns. -/
noncomputable def stSys {τ O : Type} (kd : SPComp X) (S : X → τ → E → SPComp ((X × τ) × O))
    (init : τ) : Sys (Option X × τ) E O where
  init := (none, init)
  step t e := SPComp.bind (keyAt kd t.1) fun x =>
    SPComp.bind (S x t.2 e) fun q => SPComp.pure ((some q.1.1, q.1.2), q.2)

/-- **A system with a key drawn at its first activation carries the key**: `keyedSys` is
    `stSys` at the steps that return the key they receive. -/
theorem keyedSys_eq_stSys {τ O : Type} (kd : SPComp X) (S : X → τ → E → SPComp (τ × O))
    (S' : X → τ → E → SPComp ((X × τ) × O)) (init : τ)
    (hS : ∀ k t e, SPComp.map (fun q => ((k, q.1), q.2)) (S k t e) = S' k t e) :
    keyedSys kd S init = stSys kd S' init := by
  simp only [keyedSys, stSys, ← hS, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

open Classical in
/-- **One target activation at a carried state `x`.** In the domain of the one-call statement
    at the source relation `srcX x`, the call from the entry state `enter e t` runs `run x` to a
    return state and a carried state, answers the value `read` reads back with the leakage
    trace, and holds both states; outside the domain it answers `none` and keeps both. -/
noncomputable def gateTgtStepSt (enter : E → St → St) (Pre : St → Prop)
    (srcX : X → St → V → Prop) (leakRun : St → Tr → Prop) (run : X → St → SPComp (St × X))
    (read : St → St → V) (x : X) (t : St) (e : E) : SPComp ((X × St) × Option (V × Tr)) :=
  if h : (Pre (enter e t) ∧ ∃ v, srcX x (enter e t) v) ∧ ∃ tr, leakRun (enter e t) tr then
    SPComp.map (fun p => ((p.2, p.1), some (read (enter e t) p.1,
      leakOf (Pre := Pre) (srcRun := srcX x) (leakRun := leakRun) ⟨enter e t, h⟩)))
      (run x (enter e t))
  else SPComp.pure ((x, t), none)

open Classical in
/-- **One source activation at a carried state `x`.** When the entry state `enter e u`
    satisfies the precondition and the source relation `srcX x` has a run, the call runs
    `src x (enter e u)` to a value and a carried state, answers the value and keeps the entry
    state; otherwise it answers `none` and keeps both states. -/
noncomputable def gateSrcStepSt (enter : E → St → St) (Pre : St → Prop)
    (srcX : X → St → V → Prop) (src : X → St → SPComp (V × X)) (x : X) (u : St) (e : E) :
    SPComp ((X × St) × Option V) :=
  if Pre (enter e u) ∧ ∃ v, srcX x (enter e u) v then
    SPComp.map (fun p => ((p.2, enter e u), some p.1)) (src x (enter e u))
  else SPComp.pure ((x, u), none)

/-- **Reactive robust compilation at a carried state.** Let the gate conclusion of `srcRun`
    give constant-time leakage, with public projections whose equality implies the public
    relation and a target that has a leakage trace whenever it has a result, and let the entry
    map `enter` give entry states whose precondition, source relations and source computations
    do not depend on the kept state and whose public projection is `pe e`. Let each source
    relation `srcX x` run only where `srcRun` runs. When at every carried state `x` and every
    entry state `s` of the domain of `srcX x` the target run `run x s` and the source
    computation `src x s` are related at grade `ε` with the read-back value and the carried
    state equal, the system that steps as the target realizes the system that steps as the
    source, both carrying the state drawn by `kd`, behind the leakage simulator of `srcRun`, at
    `Z.input.rounds * ε`. -/
theorem realizesSim_of_gate_run_st [Nonempty Tr] {Pre : St → Prop} {Pub : St → St → Prop}
    {srcRun : St → V → Prop} {tgtRes : St → V → Prop} {leakRun : St → Tr → Prop}
    (g : GateConclusion Pre Pub srcRun tgtRes leakRun) (pub : St → P)
    (hpub : ∀ s₁ s₂, pub s₁ = pub s₂ → Pub s₁ s₂)
    (hterm : ∀ s v, Pre s → tgtRes s v → ∃ tr, leakRun s tr)
    (enter : E → St → St) (pe : E → P)
    (hPre : ∀ e t u, Pre (enter e t) ↔ Pre (enter e u))
    (hpe : ∀ e t, pub (enter e t) = pe e) (kd : SPComp X) (srcX : X → St → V → Prop)
    (hsub : ∀ x s v, srcX x s v → ∃ w, srcRun s w)
    (hsrcX : ∀ x e t u, srcX x (enter e t) = srcX x (enter e u))
    (run : X → St → SPComp (St × X)) (read : St → St → V) (src : X → St → SPComp (V × X))
    (hsrcS : ∀ x e t u, src x (enter e t) = src x (enter e u)) (ε : ℝ≥0∞)
    (hrun : ∀ x s, Pre s → (∃ v, srcX x s v) → rHoareApprox ε eqPre (run x s) (src x s)
      (fun a h₁ b h₂ => (read s a.1, a.2) = b ∧ h₁ = h₂))
    (t₀ u₀ : St) :
    RealizesSim (stSys kd (gateTgtStepSt enter Pre srcX leakRun run read) t₀)
      (stSys kd (gateSrcStepSt enter Pre srcX src) u₀)
      (leakSim pe (simLeak Pre srcRun leakRun pub)) (fun _ Z => Z.input.rounds * ε) := by
  refine realizes_of_couplingApprox _ _ (fun t x => t.1 = x.2.1) ε rfl ?_
  rintro ⟨kt, t⟩ ⟨l, ku, u⟩ e (rfl : kt = ku)
  rw [leakSim_withSub_step]
  simp only [stSys, SPComp.bind_assoc, SPComp.pure_bind]
  rw [← zero_add ε]
  refine rHoareApprox_bind (rHoareApprox_of_rHoare (rHoare_refl (keyAt kd kt))) fun x x' => ?_
  rintro h₁ h₂ ⟨rfl, hh⟩
  revert h₁ h₂ hh
  change rHoareApprox ε eqPre _ _ _
  by_cases hD : Pre (enter e u) ∧ ∃ v, srcX x (enter e u) v
  · obtain ⟨v, hv⟩ := hD.2
    have hp : Pre (enter e t) := (hPre e t u).2 hD.1
    have hv' : srcX x (enter e t) v := by rw [hsrcX x e t u]; exact hv
    obtain ⟨w, hw'⟩ := hsub x _ v hv'
    have hT : (Pre (enter e t) ∧ ∃ v, srcX x (enter e t) v) ∧ ∃ tr, leakRun (enter e t) tr :=
      ⟨⟨hp, v, hv'⟩, hterm _ w hp (g.value _ _ hp hw')⟩
    have hL : leakOf (Pre := Pre) (srcRun := srcX x) (leakRun := leakRun)
        ⟨enter e t, hT⟩ = simLeak Pre srcRun leakRun pub (pe e) := by
      rw [← hpe e t]
      exact leakOf_eq_simLeak g pub hpub ⟨enter e t, ⟨hp, w, hw'⟩, hT.2⟩
    simp only [gateTgtStepSt, gateSrcStepSt, dite_eq_left hT,
      ite_eq_left_of_eq_true _ _ (eq_true hD), hL, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind, ← hsrcS x e t u]
    rw [← add_zero ε]
    refine rHoareApprox_bind (hrun x _ hp ⟨v, hv'⟩) fun a b => ?_
    refine rHoareApprox_of_rHoare (rHoare_ret fun _ _ hh => ?_)
    obtain ⟨hab, hs⟩ := hh
    subst hab
    exact ⟨hs, rfl, rfl⟩
  · have hT : ¬ ((Pre (enter e t) ∧ ∃ v, srcX x (enter e t) v) ∧
        ∃ tr, leakRun (enter e t) tr) := by
      rintro ⟨⟨hp, v, hv⟩, -⟩
      refine hD ⟨(hPre e t u).1 hp, v, ?_⟩
      rw [← hsrcX x e t u]; exact hv
    simp only [gateTgtStepSt, gateSrcStepSt, dite_eq_right hT,
      ite_eq_right_of_eq_false _ _ (eq_false hD), SPComp.pure_bind,
      pairLeak, Option.bind_none]
    exact rHoareApprox_mono_eps zero_le
      (rHoareApprox_of_rHoare (rHoare_ret fun _ _ hh => ⟨hh, rfl, rfl⟩))

open Classical in
/-- **The source computation of a relation at a key**: the point mass at a value of the
    relation `srcX k s`, with the key `k`, and failure where the relation has no value. -/
noncomputable def chooseSt (srcX : X → St → V → Prop) (k : X) (s : St) : SPComp (V × X) :=
  if h : ∃ v, srcX k s v then SPComp.pure (Classical.choose h, k) else SPComp.fail

end CarriedState

/-- **Reactive robust compilation with a key drawn once per run, from per-key statistical
    distances.** Let the gate conclusion of `srcRun` give constant-time leakage, with public
    projections whose equality implies the public relation and a target that has a leakage
    trace whenever it has a result, and let the entry map `enter` give entry states whose
    precondition and source runs (`srcRun` and each `srcK k`) do not depend on the kept state
    and whose public projection is `pe e`. When at every key `k` and every entry state `s` of
    the domain of `srcRun` from which `srcK k` runs to `v`, the read-back value
    `map (read s) (run k s)` is at statistical distance at most `ε` from `v`, the system that
    draws the key by `kd` and steps as the target at the key realizes the system that draws the
    key by `kd` and steps as the source `gatedRun srcRun (srcK k)` at the key, behind the
    leakage simulator of `srcRun`, at `Z.input.rounds * ε`. -/
theorem realizesSim_of_gate_run_keyed [Nonempty Tr] {Pre : St → Prop} {Pub : St → St → Prop}
    {srcRun : St → V → Prop} {tgtRes : St → V → Prop} {leakRun : St → Tr → Prop}
    (g : GateConclusion Pre Pub srcRun tgtRes leakRun) (pub : St → P)
    (hpub : ∀ s₁ s₂, pub s₁ = pub s₂ → Pub s₁ s₂)
    (hterm : ∀ s v, Pre s → tgtRes s v → ∃ tr, leakRun s tr)
    (enter : E → St → St) (pe : E → P)
    (hPre : ∀ e t u, Pre (enter e t) ↔ Pre (enter e u))
    (hsrc : ∀ e t u, srcRun (enter e t) = srcRun (enter e u))
    (hpe : ∀ e t, pub (enter e t) = pe e) (kd : SPComp K) (srcK : K → St → V → Prop)
    (hsrcK : ∀ k e t u, srcK k (enter e t) = srcK k (enter e u))
    (run : K → St → SPComp St) (read : St → St → V) (ε : ℝ≥0∞)
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

end KeyedGate

/-! ## The instance of the hax compiler with keyed linked functions -/

section Instance

open CatCrypt.Crypto.SecureCompilation.SepLogic (Footprinted)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerInstance
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed
open _root_.Hax (Value Env)
open CatCrypt.Crypto.Hax (HaxModule hax64WExit)

/-- **A keyed oracle at a fixed key**: a single key, and the answers of `O` at the key `k`. -/
noncomputable def RCHandlerKeyed.KeyedOracle.atKey {m : HaxModule} (O : KeyedOracle m)
    (k : O.Key) : KeyedOracle m where
  Key := Unit
  keyDist := SPComp.pure ()
  ans _ := O.ans k
  typed _ := O.typed k

/-- **The source run of `m` with the linked calls answered at the key `k`** of the keyed oracle
    `O`, from the entry state `sa` to the value `v`: an environment `σ` reads off the entry state
    `narrowEntry m σ sa` and fuels at which the source read-back of the call tree of the entry,
    interpreted under the point mass at the answers `O.ans k`, is the point mass at `v`. -/
def haxcKeyedSrcRun (m : HaxModule) (σ : AbiLayout) (O : KeyedOracle m) (k : O.Key)
    (sa : AState) (v : Value) : Prop :=
  ∃ env fuelC fuel, σ.EnvOf (narrowEntry m σ sa) env ∧
    readBack srcRead (interpSP (fun e => SPComp.pure (O.ans k e))
      (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)) = SPComp.pure v

/-- **The compiled module with keyed linked functions**, as a reactive system: the key is drawn
    by `O.keyDist` at the first activation, and at the key `k` a call is a call of
    `haxcTgtSysH` at the handler `h₂ k`, on the domain of the source run at `k`. -/
noncomputable def haxcKeyedTgtSys (m : HaxModule) (σ : AbiLayout) (pc : List RInstr)
    (sym : Nat → String) (O : KeyedOracle m)
    (h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e))
    (prog : List RInstr) (t₀ : AState) :
    Sys (Option O.Key × AState) AState (Option (Value × List CTLeak)) :=
  keyedSys O.keyDist (fun k => (gateTgtSysRun (abiEnter σ) σ.Regions
    (gatedRun (haxcSrcRun m σ) (haxcKeyedSrcRun m σ O k)) (haxcLeakRun prog)
    (fun sa => interpTargetω m pc sym sa (h₂ k)) (fun sa s' => σ.result.read sa s') t₀).step) t₀

/-- **The source module with keyed linked functions**, as a reactive system: the key is drawn
    by `O.keyDist` at the first activation, and at the key `k` a call answers a value of the
    source run at `k` on the entry states from which the source relation `haxcSrcRun` runs. -/
noncomputable def haxcKeyedSrcSys (m : HaxModule) (σ : AbiLayout) (O : KeyedOracle m)
    (u₀ : AState) : Sys (Option O.Key × AState) AState (Option Value) :=
  keyedSys O.keyDist (fun k => (gateSrcSys (abiEnter σ) σ.Regions
    (gatedRun (haxcSrcRun m σ) (haxcKeyedSrcRun m σ O k)) u₀).step) u₀

/-- The environments read off the entry state of a call are those read off its event. -/
theorem envOf_narrowEntry_abiEnter (m : HaxModule) (σ : AbiLayout) (e t : AState) (env : Env) :
    σ.EnvOf (narrowEntry m σ (abiEnter σ e t)) env ↔ σ.EnvOf (narrowEntry m σ e) env := by
  have hm : Footprinted.AgreeOn (regionLocs σ (abiEnter σ e t).regs) (abiEnter σ e t) e :=
    Footprinted.agreeOn_anti Set.subset_union_left (abiEnter_agreeOn σ e t)
  have hr : ∀ a ∈ σ.args,
      a.read (narrowEntry m σ (abiEnter σ e t)) = a.read (narrowEntry m σ e) :=
    fun a ha => abiArg_read_narrowEntry_congr ha rfl hm
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨fun a ha => (h1 a ha).trans (by rw [hr a ha]), h2, h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨fun a ha => (h1 a ha).trans (by rw [hr a ha]), h2, h3⟩⟩

/-- The keyed source run from the entry state of a call is the keyed source run from its
    event. -/
theorem haxcKeyedSrcRun_abiEnter (m : HaxModule) (σ : AbiLayout) (O : KeyedOracle m)
    (k : O.Key) (e t : AState) :
    haxcKeyedSrcRun m σ O k (abiEnter σ e t) = haxcKeyedSrcRun m σ O k e := by
  funext v
  simp only [haxcKeyedSrcRun, envOf_narrowEntry_abiEnter]

/-- **One call at a key from `HandlerRCKeyed` at that key.** Let `ε` bound the failure weight of
    the target interpretation under `h₂ k` at the entry state `sa` of the domain. When the
    source runs at the key `k` from `sa` to `v`, the value read back from the interpretation of
    `pc` under `h₂ k` is at statistical distance at most `ε` from the point mass at `v`. -/
theorem sdist_interpTargetω_le_of_handlerRCKeyed {m : HaxModule} {σ : AbiLayout}
    {pc : List RInstr} {sym : Nat → String} {O : KeyedOracle m} {k : O.Key}
    (hRC : HandlerRCKeyed m σ pc sym (O.atKey k))
    {h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hh : HandlerCoupledKeyed O h₂) {ε : ℝ≥0∞} {sa : AState} (hs : σ.Regions sa)
    (hε : ∀ s, interpTargetω m pc sym sa (h₂ k) s none ≤ ε) {v : Value}
    (hv : haxcKeyedSrcRun m σ O k sa v) :
    sdist (fun _ : Unit => SPComp.map (fun s' => σ.result.read sa s')
        (interpTargetω m pc sym sa (h₂ k)))
      (fun _ : Unit => SPComp.pure v) ≤ ε := by
  obtain ⟨env, fuelC, fuel, hE, hrb⟩ := hv
  have h0 := hRC sa hs env hE fuelC fuel ε 0 fun _ s => by
    simp only [KeyedOracle.atKey]
    rw [hrb]
    simp [SPComp.pure, SDistr.pure_apply_none]
  have h1 := (robustCompilationH_iff_sdist _ _ _ _).mp h0 (fun _ => h₂ k)
    ⟨fun _ => hh k, fun _ => hε⟩
  simp only [keyedTgt, keyedSrc, KeyedOracle.atKey, SPComp.pure_bind] at h1
  rw [hrb, add_zero] at h1
  exact h1

/-- **Reactive robust compilation with keyed linked functions.** Let `HandlerRCKeyed` hold at
    the calling body `pc` for the keyed oracle `O` at every fixed key, let the linked program
    `prog` satisfy the gate conclusion, let the target handler family `h₂` be coupled with `O`,
    and let `ε` bound the failure weight of the target interpretation under `h₂ k` at every key
    and every entry state of the domain. Then the compiled module with the linked functions
    answered by `h₂` at a key drawn once per run realizes the source module with the linked
    calls answered by `O` at the same key, behind the per-call leakage simulator `haxcLeakSim`,
    at `Z.input.rounds * ε`, for all initial kept states. -/
theorem haxc_rrcHKeyed_of_handlerRCKeyed {m : HaxModule} {σ : AbiLayout} {pc prog : List RInstr}
    {sym : Nat → String} (O : KeyedOracle m) (hRC : ∀ k, HandlerRCKeyed m σ pc sym (O.atKey k))
    (g : GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ) (haxcTgtRes σ prog)
      (haxcLeakRun prog))
    {h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hh : HandlerCoupledKeyed O h₂) {ε : ℝ≥0∞}
    (hε : ∀ sa, σ.Regions sa → ∀ k s, interpTargetω m pc sym sa (h₂ k) s none ≤ ε)
    (t₀ u₀ : AState) :
    RealizesSim (haxcKeyedTgtSys m σ pc sym O h₂ prog t₀) (haxcKeyedSrcSys m σ O u₀)
      (haxcLeakSim m σ prog) (fun _ Z => Z.input.rounds * ε) :=
  realizesSim_of_gate_run_keyed g (pubOf σ) (pubAgree_of_pubOf_eq σ)
    (fun s v _ h => haxcLeakRun_of_tgtRes σ prog s v h) (abiEnter σ) (pubOf σ)
    (fun e t u => (regions_abiEnter σ e t).trans (regions_abiEnter σ e u).symm)
    (fun e t u => (haxcSrcRun_abiEnter m σ e t).trans (haxcSrcRun_abiEnter m σ e u).symm)
    (pubOf_abiEnter σ) O.keyDist (haxcKeyedSrcRun m σ O)
    (fun k e t u => (haxcKeyedSrcRun_abiEnter m σ O k e t).trans
      (haxcKeyedSrcRun_abiEnter m σ O k e u).symm)
    (fun k sa => interpTargetω m pc sym sa (h₂ k)) (fun sa s' => σ.result.read sa s') ε
    (fun k _ _ hs _ hv => sdist_interpTargetω_le_of_handlerRCKeyed (hRC k) hh hs
      (hε _ hs k) hv) t₀ u₀

/-- **Reactive robust compilation of a result of `compileA` with keyed linked functions.** From
    a decoding of the bytes into a calling body `pc` followed by the shifted linked code `Q`, the
    gate conclusion of the linked program and `HandlerRCKeyed` at `pc` for every keyed oracle
    (the conclusion of `haxc_rcHKeyed`): for every keyed oracle `O`, every target handler family
    `h₂` coupled with `O` and every bound `ε` of its failure weight, the compiled module realizes
    its source behind `haxcLeakSim` at `Z.input.rounds * ε`. -/
theorem haxc_rrcHKeyed {m : HaxModule} {σ : AbiLayout} {bytes : List (BitVec 8)}
    (hrcK : ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ)
        (haxcTgtRes σ (pc ++ shiftProg pc.length Q)) (haxcLeakRun (pc ++ shiftProg pc.length Q)) ∧
      ∀ O : KeyedOracle m, HandlerRCKeyed m σ pc sym O) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      ∀ (O : KeyedOracle m)
        (h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)),
        HandlerCoupledKeyed O h₂ → ∀ ε : ℝ≥0∞,
        (∀ sa, σ.Regions sa → ∀ k s, interpTargetω m pc sym sa (h₂ k) s none ≤ ε) →
        ∀ t₀ u₀ : AState,
        RealizesSim (haxcKeyedTgtSys m σ pc sym O h₂ (pc ++ shiftProg pc.length Q) t₀)
          (haxcKeyedSrcSys m σ O u₀) (haxcLeakSim m σ (pc ++ shiftProg pc.length Q))
          (fun _ Z => Z.input.rounds * ε) := by
  obtain ⟨pc, Q, sym, hd, g, hRC⟩ := hrcK
  exact ⟨pc, Q, sym, hd, fun O h₂ hh ε hε t₀ u₀ =>
    haxc_rrcHKeyed_of_handlerRCKeyed O (fun k => hRC (O.atKey k)) g hh hε t₀ u₀⟩

/-- **The stateless linked functions as the point oracle.** Under the hypotheses of
    `haxc_rrcH_of_handlerRC` (`HandlerRC` at `pc`, the gate conclusion of `prog`, a handler `h₂`
    coupled with the meanings of the linked functions, and a bound `ε` of the failure weight of
    the target under the handlers of the class), the keyed systems at the point oracle
    `pointOracle m` and the constant family at `h₂` satisfy the conclusion of
    `haxc_rrcHKeyed_of_handlerRCKeyed`. -/
theorem haxc_rrcHKeyed_point_of_handlerRC {m : HaxModule} {σ : AbiLayout}
    {pc prog : List RInstr} {sym : Nat → String} (hRC : HandlerRC m σ pc sym)
    (g : GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ) (haxcTgtRes σ prog)
      (haxcLeakRun prog))
    {h₂ : ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hh : HandlerCoupledCG m eqPre h₂) {ε : ℝ≥0∞}
    (hε : ∀ sa, σ.Regions sa → ∀ h, HandlerCoupledCG m eqPre h → ∀ s,
      interpTargetω m pc sym sa h s none ≤ ε)
    (t₀ u₀ : AState) :
    RealizesSim (haxcKeyedTgtSys m σ pc sym (pointOracle m) (fun _ => h₂) prog t₀)
      (haxcKeyedSrcSys m σ (pointOracle m) u₀) (haxcLeakSim m σ prog)
      (fun _ Z => Z.input.rounds * ε) := by
  refine realizesSim_of_gate_run_keyed g (pubOf σ) (pubAgree_of_pubOf_eq σ)
    (fun s v _ h => haxcLeakRun_of_tgtRes σ prog s v h) (abiEnter σ) (pubOf σ)
    (fun e t u => (regions_abiEnter σ e t).trans (regions_abiEnter σ e u).symm)
    (fun e t u => (haxcSrcRun_abiEnter m σ e t).trans (haxcSrcRun_abiEnter m σ e u).symm)
    (pubOf_abiEnter σ) _ (haxcKeyedSrcRun m σ (pointOracle m))
    (fun k e t u => (haxcKeyedSrcRun_abiEnter m σ _ k e t).trans
      (haxcKeyedSrcRun_abiEnter m σ _ k e u).symm)
    (fun _ sa => interpTargetω m pc sym sa h₂) (fun sa s' => σ.result.read sa s') ε
    (fun _ sa v hs _ hv => ?_) t₀ u₀
  obtain ⟨env, fuelC, fuel, hE, hrb⟩ := hv
  have hrb' : readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
      (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)) = SPComp.pure v :=
    hrb
  have h0 := hRC sa hs env hE fuelC fuel ε 0 (hε sa hs) fun s => by
    rw [hrb']
    simp [SPComp.pure, SDistr.pure_apply_none]
  have h1 := (robustCompilationH_iff_sdist _ _ _ _).mp h0 h₂ hh
  rw [hrb', add_zero] at h1
  exact h1

end Instance

end CatCrypt.Crypto.SecureCompilation.Haxc
