/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Hax.HaxToLowCTSimulates
import CatCrypt.Crypto.Hax.HaxToLowCTSim_Call
import CatCrypt.Crypto.Hax.HaxToLowCTSim_Main
import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta

/-!
# H3.quarta-Discharge: discharge Hyp_letBindApp / Hyp_assignApp

Uses the tower-agreement framework from `HaxToLowCTSim_Quarta.lean`
to prove the two app-simulation hypotheses from `HaxToLowCTSim_Main.lean`.

## Approach

The existing `HaxToLowCTSimulates` uses scalar-only `envAgreesRust`.
The app cases produce tower bindings, so we need the combined
`envAgreesRustFull` agreement.  We define a **stronger parallel
simulation predicate** `HaxToLowCTSimulatesFull` that includes
tower agreement, prove the app cases under it, and a forgetful
lemma `HaxToLowCTSimulatesFull → HaxToLowCTSimulates` that
recovers the original predicate.

This avoids invasively refactoring the main predicate.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located RustVal
   rsSetTower rsSetScalar locatedUpdate locatedLookup)

/-! ## §1  Full simulation predicate

Mirrors `HaxToLowCTSimulates` but requires combined scalar + tower
agreement (`envAgreesRustFull`) on both ends.  The app cases need
the tower side; pure-scalar cases (var, unitVal, seq, letBind lit)
also lift because the tower side is preserved trivially. -/

/-- Stronger sim predicate: uses `envAgreesRustFull` instead of
    scalar-only `envAgreesRust`. -/
def HaxToLowCTSimulatesFull
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value) : Prop :=
  haxToLowCT e = some c →
  evalImp bi fuel e env = some (v, env') →
  envAgreesRustFull bridge env rs →
  ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesRustFull bridge env' rs'

/-! ## §2  Forgetful lemma (sketch)

The forgetful direction `HaxToLowCTSimulatesFull → HaxToLowCTSimulates`
is *not* trivially true: the original predicate consumes only the scalar
agreement `envAgreesRust env rs`, but the Full predicate requires the
input to also satisfy `envAgreesRustTower bridge env rs`.

The cleanest forgetful lemma therefore needs an *extra* premise: a
witness that the tower agreement also holds on the input.  We package
that as a wrapper.  In the eventual Main-theorem assembly, the wrapper
is satisfied trivially by callers that maintain `envAgreesRustFull`
throughout.
-/

/-- Forgetful direction: if we additionally know the input tower
    agreement, the Full simulation implies the scalar-only simulation.
    The extra premise is the obstacle for a clean unconditional
    forgetful lemma. -/
theorem HaxToLowCTSimulatesFull_to_simulates
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (e : ImpExpr) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value)
    (hTowerIn : envAgreesRustTower bridge env rs)
    (hFull : HaxToLowCTSimulatesFull bridge bi fuel N leafSpec e c env env' rs v) :
    HaxToLowCTSimulates bi fuel N leafSpec e c env env' rs v := by
  intro hHax hEval hAgree
  obtain ⟨rs', hExec, hAgreeFull'⟩ := hFull hHax hEval ⟨hAgree, hTowerIn⟩
  exact ⟨rs', hExec, hAgreeFull'.1⟩

/-! ## §3  Syntactic unpacker for `letBind name (.app f args) body`

Companion to `haxToLowCT_letBind_lit_some` (Agreement.lean) for the
let-of-call arm. -/

/-- Unpack the syntactic translation for the `letBind name (.app f args) body`
    arm.  Yields the translated body, the translated argument list, the
    destination's tower type, and the assembled shape.

    After the 2026-05 extension of `haxToLowCT`, two special call names
    (`"array_update"` and `"index"`) trigger array store / load lowering
    instead of the generic `RCall` shape.  This lemma covers only the
    generic shape; the guards `hf_not_arr` / `hf_not_idx` rule out those
    special call names. -/
theorem haxToLowCT_letBind_app_some
    (name f : String) (args : List ImpExpr) (body : ImpExpr) (c : LowCT)
    (hf_not_arr : f ≠ "array_update")
    (hf_not_idx : f ≠ "index")
    (h : haxToLowCT (.letBind name (.app f args) body) = some c) :
    ∃ (args' : List Located) (bodyC : LowCT),
      haxArgsToLocated (towerOfCallName f) args = some args' ∧
      haxToLowCT body = some bodyC ∧
      c = .RLetZero name (towerOfCallName f)
            (.RSeq (.RCall f { locVar := name, locSrc := towerOfCallName f } args')
                   bodyC) := by
  simp only [haxToLowCT] at h
  cases hArgs : haxArgsToLocated (towerOfCallName f) args with
  | none => simp [hArgs] at h
  | some args' =>
    cases hBody : haxToLowCT body with
    | none => simp [hArgs, hBody] at h
    | some bodyC =>
      simp only [hArgs, hBody, if_neg hf_not_arr, if_neg hf_not_idx,
                 Option.some.injEq] at h
      exact ⟨args', bodyC, rfl, rfl, h.symm⟩

/-! ## §4  Source-side inverse for `letBind name (.app f args) body`

When all `args` are plain `.var` lookups (the only shape `haxToLowCT`
accepts), the source-side evaluation of `letBind name (.app f args) body`
decomposes into a `bi f vals = some vRes` step that updates the env
with `name ↦ vRes`, followed by evaluation of `body`. -/

theorem evalImp_letBind_app_vars_inv
    (bi : Builtins) (fuel : Nat) (name f : String)
    (args : List ImpExpr) (body : ImpExpr) (env : Env)
    (v : Value) (env' : Env)
    (hVars : ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w)
    (h : evalImp bi fuel (.letBind name (.app f args) body) env = some (v, env')) :
    ∃ vals vRes,
      AllVars env args vals ∧
      bi f vals = some vRes ∧
      evalImp bi fuel body (env.extend name vRes) = some (v, env') := by
  -- Build the AllVars witness and the reduction of denoteArgs.
  obtain ⟨vals, hAV⟩ := allVars_of_forall env args hVars
  have hda := denoteArgs_vars bi fuel env hAV
  -- Unfold evalImp at h and reduce the letBind/app cascade.
  unfold evalImp at h
  simp only [denote, bind, Bind.bind, StateT.bind, StateT.run,
             pure, Pure.pure, modify, modifyGet,
             MonadStateOf.modifyGet] at h
  -- Normalise denoteArgs on hAV to match the shape in h.
  simp only [StateT.run] at hda
  rw [hda] at h
  dsimp only at h
  -- Case on bi f vals.
  cases hbi : bi f vals with
  | none =>
    rw [hbi] at h
    simp [StateT.pure] at h
  | some vRes =>
    rw [hbi] at h
    simp [StateT.pure] at h
    -- After the modify-with-Env.extend, the remaining state is the body
    -- evaluation against the extended env.
    refine ⟨vals, vRes, hAV, hbi, ?_⟩
    unfold evalImp
    exact h

/-! ## §5  RustState collapse helpers for `letZero + call` chain -/

/-- Setting the same tower variable twice collapses to the second value. -/
theorem rsSetTower_collapse (rs : RustState) (name : String)
    (v1 v2 : Σ t : TowerType, RustVal t) :
    rsSetTower (rsSetTower rs name v1) name v2 = rsSetTower rs name v2 := by
  rcases rs with ⟨t, s⟩
  simp only [rsSetTower]
  congr 1
  funext y
  by_cases hy : y = name <;> simp [hy]

/-- `locatedLookup` on a freshly-`letZero`'d slot returns the default. -/
theorem locatedLookup_letZero
    (rs : RustState) (name : String) (dt : TowerType) :
    locatedLookup (rsSetTower rs name ⟨dt, default⟩)
      { locVar := name, locSrc := dt } = some default := by
  unfold locatedLookup rsSetTower
  simp

/-! ## §6  Args-precondition hypothesis

The leaf-call simulation needs the args of the translated call to be
already-bound in the RustState with their declared tower type.  This
hypothesis is shaped to match exactly what `haxArgsToLocated` produces
(parent tower type on every arg) and what `RustExec.call` requires.

In practice, this is maintained by the caller (the hax extraction
pipeline emits well-typed code) and verified syntactically at the
top of the pipeline; here we take it as a relational assumption. -/

/-- Args in the RustState satisfy the tower-typing precondition for
    `RustExec.call`.  All args' `locDst` must equal `dt` (the parent
    tower from `haxArgsToLocated dt args` — this is automatic from how
    the translator builds the list). -/
def ArgsTowerBound (rs : RustState) (args' : List Located) : Prop :=
  ∀ a ∈ args', ∃ val, rs.rsTower a.locVar = some ⟨a.locDst, val⟩

/-- The args-bound predicate is preserved by adding a *different* tower
    binding (one whose name isn't in the args list).  The eventual
    `letZero` adds the binding for `name` (the destination), so this
    lemma covers the freshness side-condition. -/
theorem ArgsTowerBound_preserved_extend
    (rs : RustState) (args' : List Located) (name : String)
    (v : Σ t : TowerType, RustVal t)
    (hFresh : ∀ a ∈ args', a.locVar ≠ name)
    (h : ArgsTowerBound rs args') :
    ArgsTowerBound (rsSetTower rs name v) args' := by
  intro a haIn
  obtain ⟨val, hVal⟩ := h a haIn
  refine ⟨val, ?_⟩
  have hne : a.locVar ≠ name := hFresh a haIn
  unfold rsSetTower
  have hbeq : (a.locVar == name) = false := beq_eq_false_iff_ne.mpr hne
  simp [hbeq, hVal]

/-! ## §7  Goal 3: letBind-app simulation under Full predicate

Given:

* `LeafCallAgreesTower bi leafSpec f dt bridge` — leaf agrees with bridge,
* an args-bound hypothesis on `rs` for the translated `args'`,
* freshness: `name` isn't already an arg's variable,
* the body simulation IH,
* and the leaf's returned value decodes to `none` as a scalar (the
  typical case for tower leaves: `vRes` is a Fp/Fp2/etc value, not a Nat),

the letBind-app case simulates under `HaxToLowCTSimulatesFull`.

The proof chains:
1. Syntactic unpack via `haxToLowCT_letBind_app_some`.
2. Source-side unpack via `evalImp_letBind_app_vars_inv` (needs the
   `args-are-vars` precondition; satisfied by `haxArgsToLocated`-success
   syntactically — proved below as `haxArgsToLocated_imp_allVars`).
3. `RustExec.letZero` to enter the scope.
4. `RustExec.call` to consume the leaf.
5. `envAgreesRustFull_extend_tower` (via the collapse lemma) to lift
   agreement across the binding.
6. The body IH closes the rest.
-/

/-- If `haxArgsToLocated dt args = some args'`, then every `args[i]` is
    `.var aᵢ.locVar`.  This is the witness for the `args-are-vars`
    precondition of `evalImp_letBind_app_vars_inv`. -/
theorem haxArgsToLocated_imp_all_vars
    (dt : TowerType) (args : List ImpExpr) (args' : List Located)
    (h : haxArgsToLocated dt args = some args') :
    ∀ a ∈ args, ∃ n, a = .var n := by
  induction args generalizing args' with
  | nil => intro a ha; simp at ha
  | cons a as ih =>
    intro b hb
    rw [List.mem_cons] at hb
    rcases hb with hb | hb
    · -- b = a; need to show a = .var _.  Inspect haxArgToLocated dt a.
      subst hb
      cases hb_eq : b with
      | var n => exact ⟨n, rfl⟩
      | _ =>
        rw [hb_eq] at h
        simp only [haxArgsToLocated, haxArgToLocated] at h
        exact absurd h (by simp)
    · -- b ∈ as; recurse via IH on the tail.
      simp only [haxArgsToLocated] at h
      cases hHead : haxArgToLocated dt a with
      | none => rw [hHead] at h; simp at h
      | some _ =>
        cases hRest : haxArgsToLocated dt as with
        | none => rw [hHead, hRest] at h; simp at h
        | some rest => exact ih rest hRest b hb

/-! ## §8  Goal 3: letBind-app simulation (Full predicate, with ArgsBound)

The proof needs an `ArgsTowerBound`-style precondition on the input
state because the leaf call's `RustExec.call` constructor requires
each arg to be already-bound in the tower heap with its declared type.
Agreement is a *consistency* condition (relates env values to existing
tower values), not an *existence* condition.

We therefore state the simulation with the args-bound hypothesis as an
explicit precondition.  In a full pipeline run, the caller's invariant
(e.g. a strengthened bridge that asserts "if env has a value at name n
of tower-typeable shape, then rs has a tower binding at n") discharges
this.  This stratification is the same pattern used in CryptoSSA's
`bindingOK` (tower binding existence is tracked alongside agreement).

Note on `hLeafScalar`: the leaf's return value `vRes` must decode to
`none` as a scalar — this is the tower-only case, matching the
`fp_*`, `fp2_*`, `fp25519_*`, etc. leaves that produce TFp/TFp2/...
values (not Nats).  Pure-Nat leaves like `u64_add` aren't covered by
this lemma; they need a parallel scalar variant.
-/

theorem haxToLowCT_simulates_letBind_app_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name f : String) (args : List ImpExpr) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (hLeaf : LeafCallAgreesTower bi leafSpec f (towerOfCallName f) bridge)
    (hArgsEnv : ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w)
    (hArgsBound :
       ∀ args', haxArgsToLocated (towerOfCallName f) args = some args' →
       ArgsTowerBound rs args')
    (hArgsFresh :
       ∀ args', haxArgsToLocated (towerOfCallName f) args = some args' →
       ∀ a ∈ args', a.locVar ≠ name)
    (hLeafScalar : ∀ vals vRes, bi f vals = some vRes →
                   valueToScalar vRes = none)
    (hf_not_arr : f ≠ "array_update")
    (hf_not_idx : f ≠ "index")
    (ihBody : ∀ c' env_a env_b rs_a v_a,
                HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
                  body c' env_a env_b rs_a v_a) :
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.letBind name (.app f args) body) c env env' rs v := by
  intro hHax hEval hAgreeFull
  -- §1: Unpack syntactic translation.
  obtain ⟨args', bodyC, hArgsT, hBodyT, hC⟩ :=
    haxToLowCT_letBind_app_some name f args body c hf_not_arr hf_not_idx hHax
  subst hC
  -- §2: Source-side decomposition.
  obtain ⟨vals, vRes, _hAV, hBi, hBodyEval⟩ :=
    evalImp_letBind_app_vars_inv bi fuel name f args body env v env'
      hArgsEnv hEval
  -- §3: Specialize the args hypotheses.
  have hAB : ArgsTowerBound rs args' := hArgsBound args' hArgsT
  have hAF : ∀ a ∈ args', a.locVar ≠ name := hArgsFresh args' hArgsT
  have hDecode : valueToScalar vRes = none := hLeafScalar vals vRes hBi
  -- §4: Set up the destination and rs_init.
  set dt := towerOfCallName f with hdt_def
  set dest : Located := { locVar := name, locSrc := dt } with hdest_def
  set rs_init := rsSetTower rs name ⟨dt, default⟩ with hrs_init_def
  -- §5: Args are tower-bound on rs_init via freshness preservation.
  have hABinit : ArgsTowerBound rs_init args' := by
    apply ArgsTowerBound_preserved_extend rs args' name ⟨dt, default⟩ hAF hAB
  -- §6: rs_init satisfies locatedLookup at dest.
  have hLookup : locatedLookup rs_init dest = some default :=
    locatedLookup_letZero rs name dt
  -- §7: Build the RustExec.call step.
  -- The call produces rs_mid = locatedUpdate rs_init dest newVal where:
  --   newVal = leafSpec.call f dt (args'.map (·.locDst)) default argList
  --   argList = args'.filterMap (fun a => rs_init.rsTower a.locVar)
  set argList := args'.filterMap (fun a => rs_init.rsTower a.locVar) with hargList_def
  set newVal := leafSpec.call f dt (args'.map (·.locDst)) default argList
    with hnewVal_def
  set rs_mid := locatedUpdate rs_init dest newVal with hrs_mid_def
  -- The args-typing precondition for RustExec.call:
  have hCallArgs : ∀ a ∈ args', ∃ vv, rs_init.rsTower a.locVar = some ⟨a.locDst, vv⟩ :=
    hABinit
  have hCall : RustExec N leafSpec (.RCall f dest args') rs_init rs_mid := by
    have hcall := RustExec.call (N := N) (leafSpec := leafSpec)
                    f dest args' rs_init default argList hLookup rfl hCallArgs
    -- hcall : RustExec N leafSpec (.RCall f dest args') rs_init
    --           (locatedUpdate rs_init dest
    --              (leafSpec.call f dest.locDst (args'.map (·.locDst)) default argList))
    -- We want: RustExec ... rs_init rs_mid.
    -- dest.locDst = dt, and rs_mid = locatedUpdate rs_init dest newVal.
    exact hcall
  -- §8: Get the bridge agreement from LeafCallAgreesTower.
  have hBridgeAgr : bridge dt vRes newVal := by
    have hL := hLeaf rs_init name args' vals vRes hBi hCallArgs
    -- hL : bridge dt vRes (leafSpec.call f dt (args'.map (·.locDst))
    --                       ((locatedLookup rs_init {locVar:=name,locSrc:=dt}).getD default)
    --                       argList)
    -- We need: bridge dt vRes newVal, where newVal uses oldDestV = default.
    -- By hLookup: (locatedLookup rs_init {locVar:=name,locSrc:=dt}).getD default = default.
    have hOld : (locatedLookup rs_init { locVar := name, locSrc := dt }).getD default
                = (default : RustVal dt) := by
      rw [hLookup]; rfl
    -- Rewrite hL using hOld.
    rw [hOld] at hL
    exact hL
  -- §9: rs_mid equals rsSetTower rs name ⟨dt, newVal⟩ via collapse.
  have hRsMidEq : rs_mid = rsSetTower rs name ⟨dt, newVal⟩ := by
    show locatedUpdate rs_init dest newVal = rsSetTower rs name ⟨dt, newVal⟩
    show rsSetTower rs_init dest.locVar ⟨dest.locDst, newVal⟩ = rsSetTower rs name ⟨dt, newVal⟩
    show rsSetTower (rsSetTower rs name ⟨dt, default⟩) name ⟨dt, newVal⟩
         = rsSetTower rs name ⟨dt, newVal⟩
    exact rsSetTower_collapse rs name ⟨dt, default⟩ ⟨dt, newVal⟩
  -- §10: Extend agreement to rs_mid.
  have hAgreeMid : envAgreesRustFull bridge (env.extend name vRes) rs_mid := by
    rw [hRsMidEq]
    exact envAgreesRustFull_extend_tower bridge env rs name vRes dt newVal
            hAgreeFull hBridgeAgr hDecode
  -- §11: Apply body IH.
  obtain ⟨rs', hBodyExec, hAgreeFinal⟩ :=
    ihBody bodyC (env.extend name vRes) env' rs_mid v
           hBodyT hBodyEval hAgreeMid
  -- §12: Chain the executions: letZero + (call ; bodyC).
  refine ⟨rs', ?_, hAgreeFinal⟩
  refine RustExec.letZero name dt _ rs rs' ?_
  -- Now need: RustExec N leafSpec (.RSeq (.RCall ...) bodyC) rs_init rs'
  exact RustExec.seq _ _ _ _ _ hCall hBodyExec

/-! ## §9  Goal 4: assign-app simulation (Full predicate, with ArgsBound)

Simpler than letBind-app: no body recursion, single RCall command.
The destination slot must already be bound in `rs` (since `assign`
doesn't enter a fresh scope) — this is a stronger preexistence
condition than the letBind case (which uses `RLetZero` to fresh-init
the slot).
-/

/-- Source-side inverse for `.assign name (.app f args)` with all-var args. -/
theorem evalImp_assign_app_vars_inv
    (bi : Builtins) (fuel : Nat) (name f : String)
    (args : List ImpExpr) (env : Env) (v : Value) (env' : Env)
    (hVars : ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w)
    (h : evalImp bi fuel (.assign name (.app f args)) env = some (v, env')) :
    ∃ vals vRes,
      AllVars env args vals ∧
      bi f vals = some vRes ∧
      env' = env.extend name vRes ∧
      v = .unit := by
  -- Build the AllVars witness and the reduction of denoteArgs.
  obtain ⟨vals, hAV⟩ := allVars_of_forall env args hVars
  have hda := denoteArgs_vars bi fuel env hAV
  unfold evalImp at h
  simp only [denote, bind, Bind.bind, StateT.bind, StateT.run,
             pure, Pure.pure, modify, modifyGet,
             MonadStateOf.modifyGet] at h
  simp only [StateT.run] at hda
  rw [hda] at h
  dsimp only at h
  cases hbi : bi f vals with
  | none =>
    rw [hbi] at h
    simp [StateT.pure] at h
  | some vRes =>
    rw [hbi] at h
    simp [StateT.pure, StateT.bind, StateT.modifyGet, bind, Bind.bind] at h
    -- After full simp, h = ⟨v = .unit, env' = env.extend name vRes⟩.
    refine ⟨vals, vRes, hAV, hbi, h.2.symm, h.1.symm⟩

/-- Unpack the syntactic translation for `.assign name (.app f args)`. -/
theorem haxToLowCT_assign_app_some
    (name f : String) (args : List ImpExpr) (c : LowCT)
    (h : haxToLowCT (.assign name (.app f args)) = some c) :
    ∃ (args' : List Located),
      haxArgsToLocated (towerOfCallName f) args = some args' ∧
      c = .RCall f { locVar := name, locSrc := towerOfCallName f } args' := by
  simp only [haxToLowCT] at h
  cases hArgs : haxArgsToLocated (towerOfCallName f) args with
  | none => simp [hArgs] at h
  | some args' =>
    simp [hArgs] at h
    exact ⟨args', rfl, h.symm⟩

/-- Goal 4: assign-app simulation. -/
theorem haxToLowCT_simulates_assign_app_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name f : String) (args : List ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (hLeaf : LeafCallAgreesTower bi leafSpec f (towerOfCallName f) bridge)
    (hArgsEnv : ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w)
    (hArgsBound :
       ∀ args', haxArgsToLocated (towerOfCallName f) args = some args' →
       ArgsTowerBound rs args')
    (hDestBound :
       ∃ oldDestV : RustVal (towerOfCallName f),
         locatedLookup rs { locVar := name, locSrc := towerOfCallName f }
           = some oldDestV)
    (hLeafScalar : ∀ vals vRes, bi f vals = some vRes →
                   valueToScalar vRes = none) :
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.assign name (.app f args)) c env env' rs v := by
  intro hHax hEval hAgreeFull
  -- §1: Unpack syntactic translation.
  obtain ⟨args', hArgsT, hC⟩ := haxToLowCT_assign_app_some name f args c hHax
  subst hC
  -- §2: Source-side decomposition.
  obtain ⟨vals, vRes, _hAV, hBi, henvEq, hvEq⟩ :=
    evalImp_assign_app_vars_inv bi fuel name f args env v env' hArgsEnv hEval
  subst henvEq
  subst hvEq
  -- §3: Set up dest.
  set dt := towerOfCallName f with hdt_def
  set dest : Located := { locVar := name, locSrc := dt } with hdest_def
  -- §4: Specialize args hypothesis.
  have hAB : ArgsTowerBound rs args' := hArgsBound args' hArgsT
  obtain ⟨oldDestV, hLookup⟩ := hDestBound
  have hDecode : valueToScalar vRes = none := hLeafScalar vals vRes hBi
  -- §5: Build the call's argList and newVal.
  set argList := args'.filterMap (fun a => rs.rsTower a.locVar) with hargList_def
  set newVal := leafSpec.call f dt (args'.map (·.locDst)) oldDestV argList
    with hnewVal_def
  set rs_mid := locatedUpdate rs dest newVal with hrs_mid_def
  -- §6: Apply RustExec.call.
  have hCallArgs : ∀ a ∈ args', ∃ vv, rs.rsTower a.locVar = some ⟨a.locDst, vv⟩ :=
    hAB
  have hCall : RustExec N leafSpec (.RCall f dest args') rs rs_mid := by
    exact RustExec.call (N := N) (leafSpec := leafSpec)
            f dest args' rs oldDestV argList hLookup rfl hCallArgs
  -- §7: Get the bridge agreement.
  have hBridgeAgr : bridge dt vRes newVal := by
    have hL := hLeaf rs name args' vals vRes hBi hCallArgs
    have hOld : (locatedLookup rs { locVar := name, locSrc := dt }).getD default
                = oldDestV := by
      rw [hLookup]; rfl
    rw [hOld] at hL
    exact hL
  -- §8: rs_mid equals rsSetTower rs name ⟨dt, newVal⟩.
  have hRsMidEq : rs_mid = rsSetTower rs name ⟨dt, newVal⟩ := by
    show locatedUpdate rs dest newVal = rsSetTower rs name ⟨dt, newVal⟩
    show rsSetTower rs dest.locVar ⟨dest.locDst, newVal⟩ = rsSetTower rs name ⟨dt, newVal⟩
    rfl
  -- §9: Conclude.
  refine ⟨rs_mid, hCall, ?_⟩
  rw [hRsMidEq]
  exact envAgreesRustFull_extend_tower bridge env rs name vRes dt newVal
          hAgreeFull hBridgeAgr hDecode

/-! ## §10  Goal 5 (stretch): discharge `Hyp_letBindApp` from `Main.lean`

`Hyp_letBindApp` is stated over the scalar-only `HaxToLowCTSimulates`,
not the Full predicate.  Discharging it from
`haxToLowCT_simulates_letBind_app_full` therefore requires the
following non-trivial bridge:

* The Full-side IH expects a body-side IH over the **Full** predicate,
  but `Hyp_letBindApp` provides only the scalar-only body IH.  Lifting
  scalar-IH ⟹ Full-IH requires knowing the input tower agreement —
  which is exactly the gap covered by
  `HaxToLowCTSimulatesFull_to_simulates` (in the *reverse* direction).
* The `hArgsEnv`, `hArgsBound`, `hArgsFresh`, `hLeafScalar` hypotheses
  must be supplied universally for every `(name, f, args, body)` —
  i.e. as part of the global discharge witness.
* The args-bound / dest-bound hypotheses are *not* derivable from
  scalar agreement alone; they need a stronger global invariant
  (a bridge that asserts existence of tower bindings for env-bound
  names of the appropriate parent type).

The cleanest path to a true discharge is therefore:

1. Strengthen the simulation predicate of `Main.lean` from
   `HaxToLowCTSimulates` to `HaxToLowCTSimulatesFull` throughout,
   and adapt `Hyp_letBindApp` / `Hyp_assignApp` to match.
2. Pass the args-bound / dest-bound / leaf-scalar witnesses as part
   of a strengthened global hypothesis (a single
   `HaxToLowCTGlobalInvariant` structure).
3. Discharge the resulting hypotheses using
   `haxToLowCT_simulates_letBind_app_full` and
   `haxToLowCT_simulates_assign_app_full`.

That refactor is invasive to `Main.lean` and outside this file's
scope (per the constraint not to modify existing files).  We therefore
land Goals 1–4 here and document the residual integration step as a
follow-up for the next agent who can invasively refactor `Main.lean`.
-/

end CatCrypt.Crypto.Hax
