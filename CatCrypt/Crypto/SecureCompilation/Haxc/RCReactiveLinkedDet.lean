/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RCReactiveLinkedState
public import CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuelSource
public import CatCryptCore.Crypto.UCParallel

/-!
# Determinism of the hax source semantics and the stateless statement from the keyed one

The source semantics `haxRuns` of the hax front has at most one value at a fixed entry state: the
source environment is determined by the entry state (`AbiLayout.envOf_unique`), and two runs of
the reference reading at two pairs of fuels are both the run at the larger fuels
(`denoteSpine_val_mono`, `table_le_of_fuel_le`).

At the point oracle `pointOracle m`, the keyed source run at a key is the source relation
`haxcSrcRun` itself, so the gated source relation of the keyed systems is `haxcSrcRun`. The keyed
systems of `Haxc.RCReactiveLinkedState` at the point oracle then have the views of the systems of
`Haxc.RCReactiveLinked` (the projection that forgets the key commutes with the steps), and the
reactive statement with stateless linked functions follows from the keyed one.

## Main results

* `AbiLayout.envOf_unique` — the source environment read off an entry state is unique.
* `haxRunsW_unique`, `haxRuns_unique`, `haxcSrcRun_unique` — the source semantics has at most
  one value at a fixed entry state.
* `haxcKeyedSrcRun_point_iff` — the keyed source run at the point oracle is `haxcSrcRun`.
* `gatedRun_point` — the gated source relation at the point oracle is `haxcSrcRun`.
* `view_haxcKeyedTgtSys_point`, `view_haxcKeyedSrcSys_point` — the keyed systems at the point
  oracle have the views of the stateless systems.
The closing `example` derives the conclusion of `haxc_rrcH_of_handlerRC` from
`haxc_rrcHKeyed_point_of_handlerRC` and these views, so the stateless statement is an instance of
the keyed one.

## Search words

determinism, functional relation, unique value, source semantics, keyed oracle, point oracle,
state map, view equality, reactive robust compilation
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.RCGate
open CatCrypt.Crypto.UCTransparent
open CatCrypt.Relational (eqPre)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuelSource
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerInstance
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerSourceRun (readBack_srcRead_of_runs)
open _root_.Hax (Value Env)
open CatCrypt.Crypto.Hax (HaxModule hax64WExit)
open scoped ENNReal

/-! ## Determinism of the source semantics -/

/-- **The source environment read off an entry state is unique.** -/
theorem AbiLayout.envOf_unique {σ : AbiLayout} {sa : AState} {env₁ env₂ : Env}
    (h₁ : σ.EnvOf sa env₁) (h₂ : σ.EnvOf sa env₂) : env₁ = env₂ := by
  have key : ∀ {e₁ e₂ : Env}, σ.EnvOf sa e₁ → σ.EnvOf sa e₂ → ∀ y, (e₁ y).isSome →
      e₁ y = e₂ y := by
    intro e₁ e₂ h₁ h₂ y hy
    rcases List.mem_append.mp (h₁.2.2 y hy) with h | h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      rw [h₁.1 a ha, h₂.1 a ha]
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
      rw [h₁.2.1 c hc, h₂.2.1 c hc]
  funext y
  cases hy₁ : env₁ y with
  | some w => rw [← hy₁]; exact key h₁ h₂ y (by simp [hy₁])
  | none =>
    cases hy₂ : env₂ y with
    | none => rfl
    | some w => rw [← hy₂, ← hy₁]; exact (key h₂ h₁ y (by simp [hy₂])).symm

/-- **The register-wide source semantics has at most one value** at a fixed entry state. -/
theorem haxRunsW_unique {σ : AbiLayout} {m : HaxModule} {sa : AState} {v w : Value}
    (hv : haxRunsW σ m sa v) (hw : haxRunsW σ m sa w) : v = w := by
  obtain ⟨env, fuel, fuelC, env', hE, hr, -⟩ := hv
  obtain ⟨env₂, fuel₂, fuelC₂, env₂', hE₂, hr₂, -⟩ := hw
  cases AbiLayout.envOf_unique hE₂ hE
  have h₁ := denoteSpine_val_mono fuel _ _ (table_le_of_fuel_le m hax64WExit
    (Nat.le_max_left fuelC fuelC₂)) (Nat.le_max_left fuel fuel₂) env env' v hr
  have h₂ := denoteSpine_val_mono fuel₂ _ _ (table_le_of_fuel_le m hax64WExit
    (Nat.le_max_right fuelC fuelC₂)) (Nat.le_max_right fuel fuel₂) env env₂' w hr₂
  rw [h₁] at h₂
  grind

/-- **The source semantics of the hax front has at most one value** at a fixed entry state. -/
theorem haxRuns_unique {σ : AbiLayout} {m : HaxModule} {sa : AState} {v w : Value}
    (hv : haxRuns σ m sa v) (hw : haxRuns σ m sa w) : v = w :=
  haxRunsW_unique hv hw

/-- The source relation of the reactive statements has at most one value at an entry state. -/
theorem haxcSrcRun_unique {σ : AbiLayout} {m : HaxModule} {sa : AState} {v w : Value}
    (hv : haxcSrcRun m σ sa v) (hw : haxcSrcRun m σ sa w) : v = w :=
  haxRuns_unique hv hw

/-! ## The keyed source run at the point oracle -/

/-- A read of an optional value that is the point mass at `v` reads `some v`. -/
theorem optSP_eq_pure {α : Type} {o : Option α} {v : α} (h : optSP o = SPComp.pure v) :
    o = some v := by
  classical
  cases o with
  | none =>
    have := congrArg (fun c : SPComp α => c Heap.empty none) h
    simp [optSP, SPComp.fail, SPComp.pure, SDistr.fail_apply_none, SDistr.pure_apply_none] at this
  | some w =>
    have := congrArg (fun c : SPComp α => c Heap.empty (some (w, Heap.empty))) h
    simp only [optSP, SPComp.pure, SDistr.pure_apply_some] at this
    by_contra hne
    simp_all

/-- **The keyed source run at the point oracle is the source relation** `haxcSrcRun`. -/
theorem haxcKeyedSrcRun_point_iff (m : HaxModule) (σ : AbiLayout) (k : (pointOracle m).Key)
    (sa : AState) (v : Value) :
    haxcKeyedSrcRun m σ (pointOracle m) k sa v ↔ haxcSrcRun m σ sa v := by
  constructor
  · rintro ⟨env, fuelC, fuel, hE, hrb⟩
    have hrb' : readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
        (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)) =
          SPComp.pure v := hrb
    rw [readBack, interpSP_pure, SPComp.pure_bind, interp_nfTree_table] at hrb'
    have hs := optSP_eq_pure hrb'
    revert hs
    rcases hr : (_root_.Hax.InlineLocalClosures.denoteSpine (m.table hax64WExit fuelC) fuel
      m.entry.erase).run env with ⟨o, env'⟩
    intro hs
    simp only [srcRead] at hs
    split at hs
    · rename_i w hw
      split at hs
      · cases hs
        exact ⟨env, fuel, fuelC, env', hE, hr, by assumption⟩
      · cases hs
    · cases hs
  · intro h
    exact readBack_srcRead_of_runs h

/-- **The gated source relation at the point oracle is the source relation** `haxcSrcRun`. -/
theorem gatedRun_point (m : HaxModule) (σ : AbiLayout) (k : (pointOracle m).Key) :
    gatedRun (haxcSrcRun m σ) (haxcKeyedSrcRun m σ (pointOracle m) k) = haxcSrcRun m σ := by
  funext sa v
  simp only [gatedRun, haxcKeyedSrcRun_point_iff, eq_iff_iff]
  grind

/-! ## The keyed systems at the point oracle -/

/-- The key of an activation of a system at the point oracle is a point mass. -/
theorem keyAt_point (m : HaxModule) (k : Option (pointOracle m).Key) :
    ∃ k₀ : (pointOracle m).Key, keyAt (pointOracle m).keyDist k = SPComp.pure k₀ := by
  cases k with
  | none => exact ⟨(), rfl⟩
  | some k => exact ⟨k, rfl⟩

/-- **The compiled module at the point oracle has the views of `haxcTgtSysH`**: forgetting the
    key commutes with the steps. -/
theorem view_haxcKeyedTgtSys_point {ζ : Type} (m : HaxModule) (σ : AbiLayout)
    (pc : List RInstr) (sym : Nat → String)
    (h₂ : ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)) (prog : List RInstr)
    (t₀ : AState) (Z : Strat ζ AState (Option (Value × List CTLeak))) :
    view (haxcKeyedTgtSys m σ pc sym (pointOracle m) (fun _ => h₂) prog t₀) Z =
      view (haxcTgtSysH m σ pc sym h₂ prog t₀) Z := by
  refine view_eq_of_stepMap _ _ Prod.snd rfl (fun t e => ?_) Z
  obtain ⟨k₀, hk⟩ := keyAt_point m t.1
  simp only [haxcKeyedTgtSys, keyedSys, hk, SPComp.pure_bind, gatedRun_point, SPComp.map,
    SPComp.bind_assoc, haxcTgtSysH]
  exact SPComp.bind_pure _

/-- **The source module at the point oracle behind the leakage simulator has the views of
    `haxcSrcSys` behind it**: forgetting the key commutes with the steps. -/
theorem view_haxcKeyedSrcSys_point {ζ : Type} (m : HaxModule) (σ : AbiLayout)
    (prog : List RInstr) (u₀ : AState) (Z : Strat ζ AState (Option (Value × List CTLeak))) :
    view ((haxcLeakSim m σ prog).withSub (haxcKeyedSrcSys m σ (pointOracle m) u₀)) Z =
      view ((haxcLeakSim m σ prog).withSub (haxcSrcSys m σ u₀)) Z := by
  refine view_eq_of_stepMap _ ((haxcLeakSim m σ prog).withSub (haxcSrcSys m σ u₀))
    (fun p : Option (List CTLeak) × (Option (pointOracle m).Key × AState) => (p.1, p.2.2)) rfl
    (fun t e => ?_) Z
  rcases t with ⟨l, k, u⟩
  obtain ⟨k₀, hk⟩ := keyAt_point m k
  simp only [haxcLeakSim, leakSim_withSub_step]
  simp only [haxcKeyedSrcSys, haxcSrcSys, keyedSys, hk, SPComp.pure_bind, SPComp.bind_assoc,
    gatedRun_point, SPComp.map]
  rfl

/- Reactive robust compilation with stateless linked functions from the keyed statement: under
the hypotheses of `haxc_rrcH_of_handlerRC`, its conclusion follows from the keyed statement at the
point oracle (`haxc_rrcHKeyed_point_of_handlerRC`), since the keyed systems at the point oracle
have the views of the stateless systems. -/
example {m : HaxModule} {σ : AbiLayout}
    {pc prog : List RInstr} {sym : Nat → String} (hRC : HandlerRC m σ pc sym)
    (g : GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ) (haxcTgtRes σ prog)
      (haxcLeakRun prog))
    {h₂ : ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hh : HandlerCoupledCG m eqPre h₂) {ε : ℝ≥0∞}
    (hε : ∀ sa, σ.Regions sa → ∀ h, HandlerCoupledCG m eqPre h → ∀ s,
      interpTargetω m pc sym sa h s none ≤ ε)
    (t₀ u₀ : AState) :
    RealizesSim (haxcTgtSysH m σ pc sym h₂ prog t₀) (haxcSrcSys m σ u₀) (haxcLeakSim m σ prog)
      (fun _ Z => Z.input.rounds * ε) := fun ζ => by
  have h := haxc_rrcHKeyed_point_of_handlerRC hRC g hh hε t₀ u₀ ζ
  rwa [funext (view_haxcKeyedTgtSys_point (ζ := ζ) m σ pc sym h₂ prog t₀),
    funext (view_haxcKeyedSrcSys_point (ζ := ζ) m σ prog u₀)] at h

end CatCrypt.Crypto.SecureCompilation.Haxc
