/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCTSimulates
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Agreement
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_AssignMatch
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Call
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_If
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_While
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Main
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta_Discharge
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta_LeafAgrees

/-!
# Per-arm simulation lemmas under the Full predicate

Per-constructor simulation lemmas for `haxToLowCT` under the
`HaxToLowCTSimulatesFull` predicate (combined scalar and tower
agreement), and the bridge-level preconditions `FullSimPreconds` of the
leaf-call arms.  The leaf-call arms are
`haxToLowCT_simulates_letBind_app_full` and
`haxToLowCT_simulates_assign_app_full` in
`HaxToLowCTSim_Quarta_Discharge.lean`.

The program-level theorem over these arms is
`haxToLowCT_simulates_program` (`HaxToLowCTSim_Program.lean`), with the
call-side conditions decided on the source program by `simScope`; its
corollary with exit invariants is `haxToLowCT_simulates_full`
(`HaxToLowCTSim_Full.lean`).  The `Hyp_*_full` abbreviations below state
the remaining arms (`match_`, `whileLoop`, alias, array calls,
tuple-component reads) as inductive-step hypotheses.

## Productive scalar cases

For productive scalar-only cases (`var`, `unitVal`, `seq`, `letBind
(lit ..)`, `assign (lit ..)`) we provide Full-predicate variants that
re-prove the agreement preservation directly.  `rsSetScalar` doesn't
touch `rsTower`, so tower agreement is preserved under scalar updates
*provided the extended name is fresh in the tower* (otherwise the new
env binding at `name` could conflict with a pre-existing tower
binding).

The freshness condition is the predicate `TowerFresh rs name` on the
entry state of the arm.  At the program level it is
`NamesFresh rs (scalarNames e)` (`HaxToLowCTSim_Program.lean`).

## Arm index

| Constructor | Lemma | Source file |
|---|---|---|
| `var _` | `simulates_var_full` | this file |
| `unitVal` | `simulates_unitVal_full` | this file |
| `seq a b` | `simulates_seq_full` | this file |
| `letBind _ (lit _) _` | `simulates_letBind_lit_full` (with freshness) | this file |
| `letBind _ (app _ _) _` | `haxToLowCT_simulates_letBind_app_full` | Quarta_Discharge |
| `letBind _ (proj (var _) _) _` | `Hyp_letBindProj_full` (discharged by `haxToLowCT_simulates_letBind_proj_full`) | this file |
| `assign _ (lit _)` | `simulates_assign_lit_full` / `_bool_full` (with freshness) | this file |
| `assign _ (app _ _)` | `haxToLowCT_simulates_assign_app_full` | Quarta_Discharge |
| `ifThenElse (var _) _ _` | `simulates_ifThenElse_var_full` | this file |
| `match_ _ _` | `Hyp_match_full` | this file |
| `whileLoop (var _) _` | `Hyp_whileLoop_full`; `progSim_whileLoop` at program level | this file; Program |
-/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located RustVal
   rsSetTower rsSetScalar locatedUpdate locatedLookup)

/-! ## §1  Full-predicate hypothesis abbreviations

These mirror `Hyp_match` and `Hyp_whileLoop` from `Main.lean` but use
the stronger `HaxToLowCTSimulatesFull` predicate. -/

/-- Hypothesis: `match_ scrut arms` simulates under the Full predicate.
    Discharging requires H2.1 tuple-destructure mechanics. -/
abbrev Hyp_match_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (scrut : ImpExpr) (arms : List (Hax.ImpPat × ImpExpr))
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihScrut : ∀ c' env_a env_b rs_a v_a,
                  HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
                    scrut c' env_a env_b rs_a v_a)
    (_ihArms : ∀ pa ∈ arms,
                  ∀ c' env_a env_b rs_a v_a,
                    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
                      pa.2 c' env_a env_b rs_a v_a),
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.match_ scrut arms) c env env' rs v

/-- Hypothesis: `whileLoop (var cond) body` simulates under the Full
    predicate.  Discharge needs a fuel-polymorphic IH + AnfShaped lemma. -/
abbrev Hyp_whileLoop_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (cond : String) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
                   body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.whileLoop (.var cond) body) c env env' rs v

/-- Hypothesis: `letBind name (.var src) body` simulates under the Full
    predicate.

The source extends `env` with `name ↦ env src`; the lowering is the body's
lowering when `name = src` and a scalar copy of `src` into `name` otherwise.
The scalar copy leaves the tower slot `name` unchanged, so for `name ≠ src`
the statement fails at a state holding a tower binding at `name`; the
fragment checkers (`simScope` and its variants) accept only `name = src`. -/
abbrev Hyp_letBindVarAlias_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (name src : String) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
                   body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.letBind name (.var src) body) c env env' rs v

/-- Hypothesis: `letBind name (.app "array_update" args) body` simulates
    under the Full predicate.

The translator emits a `RArrStore` (or fallback `RCall`) for this shape.
Closure requires a semantic spec relating `bi "array_update"`'s
functional update to `leafSpec.arrStore`'s in-place update — which is
protocol-specific.  Deployers discharge via vacuity (`bi "array_update"
vals = none`) when the extraction doesn't actually exercise array
updates, or via a concrete bridge for protocols that do. -/
abbrev Hyp_arrayUpdate_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (name : String) (args : List ImpExpr) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
                   body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.letBind name (.app "array_update" args) body) c env env' rs v

/-- Hypothesis: `letBind name (.app "index" args) body` simulates under
    the Full predicate.

The translator emits a `RArrLoad` (or fallback `RCall`) for this shape.
Like `Hyp_arrayUpdate_full`, deployers discharge via vacuity when the
extraction doesn't index arrays, or via a concrete bridge otherwise. -/
abbrev Hyp_index_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (name : String) (args : List ImpExpr) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
                   body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.letBind name (.app "index" args) body) c env env' rs v

/-! ## §1.bis  Vacuity-based discharge of array_update / index hypotheses

For protocols whose `Builtins` table does not implement `"array_update"`
or `"index"`, the source-side `evalImp` of these calls returns `none`
(error outcome), making the simulation hypothesis vacuous.  These
helpers package that discharge so deployers only need to provide the
vacuity premise (already maintained by their `<Protocol>Vacuity`
infrastructure). -/

/-- Internal: when `bi f vals = none`, the source-side evaluation of
    `letBind name (.app f args) body` is `none`, contradicting any
    `evalImp ... = some _` hypothesis.  This makes the simulation
    arm vacuously true. -/
theorem evalImp_letBind_app_vacuous
    (bi : Builtins) (fuel : Nat) (name f : String)
    (args : List ImpExpr) (body : ImpExpr) (env : Env) (v : Value) (env' : Env)
    (hVac : ∀ vals, bi f vals = none)
    (h : evalImp bi fuel (.letBind name (.app f args) body) env = some (v, env')) :
    False := by
  -- Unfold the letBind + app cascade and use vacuity to derive `none`.
  unfold evalImp at h
  simp only [denote, bind, Bind.bind, StateT.bind, StateT.run,
             pure, Pure.pure] at h
  -- Inspect `denoteArgs bi fuel args env` (as applied, not `.run`).
  cases hDA : Hax.denoteArgs bi fuel args env with
  | mk oDA emDA =>
    rw [hDA] at h
    cases oDA with
    | none =>
      simp only [StateT.pure] at h
      cases h
    | some vals =>
      simp only [hVac vals, StateT.pure] at h
      cases h

/-- Vacuity-based discharge of `Hyp_arrayUpdate_full`: if
    `bi "array_update" vals = none` for all `vals`, the array_update
    simulation arm is vacuously satisfied. -/
theorem Hyp_arrayUpdate_full_of_vacuity
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (hVac : ∀ vals, bi "array_update" vals = none) :
    Hyp_arrayUpdate_full bridge bi fuel N leafSpec := by
  intro name args body c env env' rs v _ihBody _hHax hEval _hAgree
  exact absurd hEval (fun h =>
    evalImp_letBind_app_vacuous bi fuel name "array_update" args body env v env' hVac h)

/-- Vacuity-based discharge of `Hyp_index_full`. -/
theorem Hyp_index_full_of_vacuity
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (hVac : ∀ vals, bi "index" vals = none) :
    Hyp_index_full bridge bi fuel N leafSpec := by
  intro name args body c env env' rs v _ihBody _hHax hEval _hAgree
  exact absurd hEval (fun h =>
    evalImp_letBind_app_vacuous bi fuel name "index" args body env v env' hVac h)

/-! ## §1.ter  letBind-proj: tuple-component read

`let name = tup.i; body` (the K-PKE keygen `(ek, dk)` destructuring)
lowers to `RLetZero name .TFp (RSeq (RTupleLoad dst src i) bodyC)`.
The simulation relates `Value.projIdx` on the source side to
the `leafSpec.tupleLoad` oracle on the target side, in the same way
the letBind-app case relates `Builtins` calls to `leafSpec.call` via
`LeafCallAgreesTower`. -/

/-- Hypothesis: `letBind name ((.var t).i) body` simulates under the
    Full predicate.  Dischargeable per instance via
    `haxToLowCT_simulates_letBind_proj_full` below (tuple slot bound in
    `rs`, `leafSpec.tupleLoad` bridge-aligned with `Value.projIdx`). -/
abbrev Hyp_letBindProj_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec) : Prop :=
  ∀ (name t : String) (i : Nat) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (_ihBody : ∀ c' env_a env_b rs_a v_a,
                 HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
                   body c' env_a env_b rs_a v_a),
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.letBind name (.proj (.var t) i) body) c env env' rs v

/-- Unpack the syntactic translation for the letBind-proj arm. -/
theorem haxToLowCT_letBind_proj_some
    (name t : String) (i : Nat) (body : ImpExpr) (c : LowCT)
    (h : haxToLowCT (.letBind name (.proj (.var t) i) body) = some c) :
    ∃ bodyC, haxToLowCT body = some bodyC ∧
      c = .RLetZero name .TFp
            (.RSeq (.RTupleLoad { locVar := name, locSrc := .TFp }
                                { locVar := t, locSrc := .TFp } i) bodyC) := by
  simp only [haxToLowCT] at h
  cases hBody : haxToLowCT body with
  | none => simp [hBody] at h
  | some bodyC =>
    simp only [hBody, Option.some.injEq] at h
    exact ⟨bodyC, rfl, h.symm⟩

/-- Inversion for `locatedLookup`: a successful lookup pins the raw
    tower binding (stored Sigma type = `loc.locDst`). -/
theorem locatedLookup_some_rsTower
    (rs : RustState) (loc : Located) (v : RustVal loc.locDst)
    (h : locatedLookup rs loc = some v) :
    rs.rsTower loc.locVar = some ⟨loc.locDst, v⟩ := by
  unfold CatCrypt.Crypto.Jasmin.LowCT.locatedLookup at h
  cases hT : rs.rsTower loc.locVar with
  | none => rw [hT] at h; cases h
  | some p =>
    rcases p with ⟨ty, w⟩
    rw [hT] at h
    by_cases hty : ty = loc.locDst
    · subst hty
      simp only [dite_eq_left, Option.some.injEq] at h
      subst h
      rfl
    · simp [hty] at h

/-- **letBind-proj simulation (Full predicate).**

Source side (`evalImp_letBind_proj_inv`): `env t` holds a tuple value
`vTup` with component `i` = `vi`; the env extends `name ↦ vi` and
`body` runs.  Target side: `letZero` zero-inits the fresh `name` slot,
`RTupleLoad` reads component `i` of the tuple-valued slot `t` through
the `leafSpec.tupleLoad` oracle.  Preconditions:

* `hFresh` — the tuple slot is distinct from the freshly bound name
  (so `letZero` does not clobber it);
* `hSrcBound` — the tuple slot is tower-bound in `rs` at the
  translator's placeholder type;
* `hTupleAgrees` — the tuple-load oracle is bridge-aligned with
  `Value.projIdx` (the tuple-load analogue of `LeafCallAgreesTower`);
* `hCompScalar` — the component value is tower-typed (does not decode
  as a scalar), preserving scalar agreement across the binding. -/
theorem haxToLowCT_simulates_letBind_proj_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name t : String) (i : Nat) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (hFresh : t ≠ name)
    (hSrcBound : ∃ srcV : RustVal .TFp,
        locatedLookup rs { locVar := t, locSrc := .TFp } = some srcV)
    (hTupleAgrees : ∀ (vTup vi : Value) (srcV : RustVal .TFp),
        bridge .TFp vTup srcV →
        vTup.projIdx i = some vi →
        bridge .TFp vi
          (leafSpec.tupleLoad { locVar := name, locSrc := .TFp }
            (default : RustVal .TFp) ⟨.TFp, srcV⟩ i))
    (hCompScalar : ∀ (vTup vi : Value),
        env t = some vTup → vTup.projIdx i = some vi →
        valueToScalar vi = none)
    (ihBody : ∀ c' env_a env_b rs_a v_a,
        HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
          body c' env_a env_b rs_a v_a) :
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.letBind name (.proj (.var t) i) body) c env env' rs v := by
  intro hHax hEval hAgreeFull
  -- §1: Syntactic unpack.
  obtain ⟨bodyC, hBodyT, hC⟩ := haxToLowCT_letBind_proj_some name t i body c hHax
  subst hC
  -- §2: Source-side decomposition.
  obtain ⟨vTup, vi, hEnvT, hProj, hBodyEval⟩ :=
    evalImp_letBind_proj_inv bi fuel name t i body env v env' hEval
  obtain ⟨srcV, hSrcLook⟩ := hSrcBound
  -- §3: Target-side states.
  set dst : Located := { locVar := name, locSrc := .TFp } with hdst
  set src : Located := { locVar := t, locSrc := .TFp } with hsrc
  set rs_init := rsSetTower rs name ⟨.TFp, default⟩ with hrs_init
  have hDstLook : locatedLookup rs_init dst = some default :=
    locatedLookup_letZero rs name .TFp
  have hSrcLook' : locatedLookup rs_init src = some srcV := by
    rw [hrs_init,
        CatCrypt.Crypto.Jasmin.LowCT.locatedLookup_rsSetTower_other
          rs name ⟨.TFp, default⟩ src (Ne.symm hFresh)]
    exact hSrcLook
  -- §4: The tuple-load step.
  set newVal := leafSpec.tupleLoad dst default ⟨src.locDst, srcV⟩ i with hnewVal
  set rs_mid := locatedUpdate rs_init dst newVal with hrs_mid
  have hLoad : RustExec N leafSpec (.RTupleLoad dst src i) rs_init rs_mid :=
    RustExec.tupleLoad dst src i rs_init default srcV hDstLook hSrcLook'
  -- §5: Bridge the component value through the oracle.
  have hRawT : rs.rsTower t = some ⟨.TFp, srcV⟩ :=
    locatedLookup_some_rsTower rs src srcV hSrcLook
  have hTupBridge : bridge .TFp vTup srcV :=
    hAgreeFull.2 t vTup hEnvT .TFp srcV hRawT
  have hCompBridge : bridge .TFp vi newVal :=
    hTupleAgrees vTup vi srcV hTupBridge hProj
  have hDecode : valueToScalar vi = none := hCompScalar vTup vi hEnvT hProj
  -- §6: Collapse the double tower-set and extend agreement.
  have hRsMidEq : rs_mid = rsSetTower rs name ⟨.TFp, newVal⟩ := by
    show rsSetTower (rsSetTower rs name ⟨.TFp, default⟩) name ⟨.TFp, newVal⟩
        = rsSetTower rs name ⟨.TFp, newVal⟩
    exact rsSetTower_collapse rs name ⟨.TFp, default⟩ ⟨.TFp, newVal⟩
  have hAgreeMid : envAgreesRustFull bridge (env.extend name vi) rs_mid := by
    rw [hRsMidEq]
    exact envAgreesRustFull_extend_tower bridge env rs name vi .TFp newVal
            hAgreeFull hCompBridge hDecode
  -- §7: Body IH + assembly.
  obtain ⟨rs', hBodyExec, hAgreeFinal⟩ :=
    ihBody bodyC (env.extend name vi) env' rs_mid v hBodyT hBodyEval hAgreeMid
  refine ⟨rs', ?_, hAgreeFinal⟩
  refine RustExec.letZero name .TFp _ rs rs' ?_
  exact RustExec.seq _ _ _ _ _ hLoad hBodyExec

/-! ## §2  Tower freshness predicate

Holds when there is no tower binding at `name` in `rs` — i.e. scalar
operations binding `name` are safe to lift across tower agreement. -/

/-- A name is "tower-fresh" in `rs` if no tower binding exists for it. -/
def TowerFresh (rs : RustState) (name : String) : Prop :=
  rs.rsTower name = none

/-- Tower agreement preserved under scalar extension at a tower-fresh
    name.  The freshness ensures the new env binding can't conflict
    with a pre-existing tower binding. -/
theorem envAgreesRustTower_extend_scalar_fresh
    (bridge : ValueTowerBridge)
    (env : Env) (rs : RustState) (name : String) (v : Value) (n : Nat)
    (hFresh : TowerFresh rs name)
    (hAgree : envAgreesRustTower bridge env rs) :
    envAgreesRustTower bridge (Env.extend env name v) (rsSetScalar rs name n) := by
  intro m
  unfold nameAgreesTower
  intro v' hExt dt' val' hLookup
  -- rsSetScalar doesn't change rsTower
  have hRs : (rsSetScalar rs name n).rsTower m = rs.rsTower m := rfl
  rw [hRs] at hLookup
  by_cases hm : m = name
  · -- m = name: rs.rsTower name = some ⟨dt', val'⟩, but hFresh says none.
    subst hm
    rw [hFresh] at hLookup
    cases hLookup
  · have hEnvFall : Env.extend env name v m = env m := by
      simp [Env.extend, hm]
    rw [hEnvFall] at hExt
    exact hAgree m v' hExt dt' val' hLookup

/-- Combined Full agreement preserved under scalar-lit extension at a
    tower-fresh name.  Bundles the scalar and tower preservation
    lemmas. -/
theorem envAgreesRustFull_extend_scalar_fresh
    (bridge : ValueTowerBridge)
    (env : Env) (rs : RustState) (name : String) (v : Value) (n : Nat)
    (hFresh : TowerFresh rs name)
    (hDecode : valueToScalar v = some n)
    (hAgree : envAgreesRustFull bridge env rs) :
    envAgreesRustFull bridge (Env.extend env name v) (rsSetScalar rs name n) :=
  ⟨envAgreesRust_extend_scalar env rs name v n hAgree.1 hDecode,
   envAgreesRustTower_extend_scalar_fresh bridge env rs name v n hFresh hAgree.2⟩

/-! ## §3  Full-predicate productive cases (scalar-only) -/

/-- Full-predicate var case: env and rs unchanged, agreement trivial. -/
theorem simulates_var_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name : String) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value) :
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.var name) c env env' rs v := by
  intro hHax hEval hAgree
  rw [haxToLowCT_var_some] at hHax
  cases hHax
  obtain ⟨_hLookup, henv⟩ := evalImp_var_inv bi fuel name env v env' hEval
  refine ⟨rs, RustExec.skip rs, ?_⟩
  rw [henv]
  exact hAgree

/-- Full-predicate unitVal case: env and rs unchanged. -/
theorem simulates_unitVal_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value) :
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      .unitVal c env env' rs v := by
  intro hHax hEval hAgree
  rw [haxToLowCT_unitVal_some] at hHax
  cases hHax
  obtain ⟨_hv, henv⟩ := evalImp_unitVal_inv bi fuel env v env' hEval
  refine ⟨rs, RustExec.skip rs, ?_⟩
  rw [henv]
  exact hAgree

/-- Full-predicate seq case: thread Full agreement through both IHs. -/
theorem simulates_seq_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (a b : ImpExpr) (c : LowCT) (env env' : Env)
    (rs : RustState) (v : Value)
    (iha : ∀ c' env_a env_b rs_a v_a,
             HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
               a c' env_a env_b rs_a v_a)
    (ihb : ∀ c' env_a env_b rs_a v_a,
             HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
               b c' env_a env_b rs_a v_a) :
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.seq a b) c env env' rs v := by
  intro hHax hEval hAgree
  obtain ⟨aC, bC, hAtrans, hBtrans, hC⟩ := haxToLowCT_seq_some a b c hHax
  subst hC
  obtain ⟨vA, env_mid, hAeval, hBeval⟩ :=
    evalImp_seq_inv bi fuel a b env v env' hEval
  obtain ⟨rs_mid, hAexec, hAgreeMid⟩ :=
    iha aC env env_mid rs vA hAtrans hAeval hAgree
  obtain ⟨rs', hBexec, hAgree'⟩ :=
    ihb bC env_mid env' rs_mid v hBtrans hBeval hAgreeMid
  exact ⟨rs', rustExec_RSeq_chain N leafSpec aC bC rs rs_mid rs' hAexec hBexec,
         hAgree'⟩

/-! ## §4  Full-predicate letBind-lit case (with freshness) -/

/-- Full-predicate letBind-lit case.  Requires tower-freshness of the
    bound name to lift agreement across the scalar update. -/
theorem simulates_letBind_lit_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name : String) (l : ImpLit) (body : ImpExpr) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value)
    (hFresh : TowerFresh rs name)
    (ihBody : ∀ c' env_a env_b rs_a v_a,
                HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
                  body c' env_a env_b rs_a v_a) :
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.letBind name (.lit l) body) c env env' rs v := by
  intro hHax hEval hAgree
  obtain ⟨bodyC, n, hBodyTrans, hDecode, hC⟩ :=
    haxToLowCT_letBind_lit_some name l body c hHax
  subst hC
  have hBodyEval := evalImp_letBind_lit_inv bi fuel name l body env v env' hEval
  have hAgreeExt : envAgreesRustFull bridge (env.extend name (Value.ofLit l))
                    (rsSetScalar rs name n) :=
    envAgreesRustFull_extend_scalar_fresh bridge env rs name
      (Value.ofLit l) n hFresh hDecode hAgree
  obtain ⟨rs', hBodyExec, hAgree'⟩ :=
    ihBody bodyC (env.extend name (Value.ofLit l)) env' (rsSetScalar rs name n) v
           hBodyTrans hBodyEval hAgreeExt
  exact ⟨rs', rustExec_RLetU64Zero_ScalarSet N leafSpec name n bodyC rs rs' hBodyExec,
         hAgree'⟩

/-! ## §5  Full-predicate assign-lit cases (with freshness) -/

/-- Full-predicate assign-uintLit case. -/
theorem simulates_assign_lit_uintLit_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name : String) (w : IntWidth) (n : Nat) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value)
    (hFresh : TowerFresh rs name) :
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.assign name (.lit (.uintLit w n))) c env env' rs v := by
  intro hHax hEval hAgree
  -- Reuse the scalar-side simulation to get rs' and scalar agreement.
  have hScalar :=
    haxToLowCT_simulates_assign_lit_uintLit bi fuel N leafSpec
      name w n c env env' rs v hHax hEval hAgree.1
  obtain ⟨rs', hExec, hScalarAgree⟩ := hScalar
  refine ⟨rs', hExec, hScalarAgree, ?_⟩
  -- Identify rs' = rsSetScalar rs name (n % w.modulus) and
  -- env' = env.extend name (Value.uint w (n % w.modulus)).
  rw [haxToLowCT_assign_lit_uintLit_some] at hHax
  -- hHax : some (.RScalarSet name (n % w.modulus)) = some c
  injection hHax with hC
  subst hC
  -- hExec : RustExec N leafSpec (.RScalarSet name (n % w.modulus)) rs rs'
  -- This determines rs' = rsSetScalar rs name (n % w.modulus).
  have hRs : rs' = rsSetScalar rs name (n % w.modulus) := by
    cases hExec
    rfl
  subst hRs
  -- env' comes from hEval; env' = env.extend name (Value.ofLit (.uintLit w n)) and v = .unit
  obtain ⟨hv, henv⟩ := evalImp_assign_lit_inv bi fuel name (.uintLit w n) env v env' hEval
  subst henv
  -- Value.ofLit (.uintLit w n) = Value.uint w (n % w.modulus)
  -- valueToScalar (Value.ofLit (.uintLit w n)) = some (n % w.modulus)
  apply envAgreesRustTower_extend_scalar_fresh bridge env rs name
    (Value.ofLit (.uintLit w n)) (n % w.modulus) hFresh hAgree.2

/-- Full-predicate assign-int case (n ≥ 0). -/
theorem simulates_assign_lit_int_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name : String) (n : Int) (hn : n ≥ 0) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value)
    (hFresh : TowerFresh rs name) :
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.assign name (.lit (.int n))) c env env' rs v := by
  intro hHax hEval hAgree
  have hScalar :=
    haxToLowCT_simulates_assign_lit_int bi fuel N leafSpec
      name n hn c env env' rs v hHax hEval hAgree.1
  obtain ⟨rs', hExec, hScalarAgree⟩ := hScalar
  refine ⟨rs', hExec, hScalarAgree, ?_⟩
  rw [haxToLowCT_assign_lit_int_some_of_nonneg name n hn] at hHax
  injection hHax with hC
  subst hC
  have hRs : rs' = rsSetScalar rs name n.toNat := by
    cases hExec
    rfl
  subst hRs
  obtain ⟨hv, henv⟩ := evalImp_assign_lit_inv bi fuel name (.int n) env v env' hEval
  subst henv
  apply envAgreesRustTower_extend_scalar_fresh bridge env rs name
    (Value.ofLit (.int n)) n.toNat hFresh hAgree.2

/-- Full-predicate assign-bool case.  Bools are 0/1 scalars; mirrors
    the uintLit case with `n = if b then 1 else 0`. -/
theorem simulates_assign_lit_bool_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (name : String) (b : Bool) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value)
    (hFresh : TowerFresh rs name) :
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.assign name (.lit (.bool b))) c env env' rs v := by
  intro hHax hEval hAgree
  have hScalar :=
    haxToLowCT_simulates_assign_lit_bool bi fuel N leafSpec
      name b c env env' rs v hHax hEval hAgree.1
  obtain ⟨rs', hExec, hScalarAgree⟩ := hScalar
  refine ⟨rs', hExec, hScalarAgree, ?_⟩
  rw [haxToLowCT_assign_lit_bool_some] at hHax
  injection hHax with hC
  subst hC
  have hRs : rs' = rsSetScalar rs name (if b then 1 else 0) := by
    cases hExec
    rfl
  subst hRs
  obtain ⟨hv, henv⟩ := evalImp_assign_lit_inv bi fuel name (.bool b) env v env' hEval
  subst henv
  apply envAgreesRustTower_extend_scalar_fresh bridge env rs name
    (Value.ofLit (.bool b)) (if b then 1 else 0) hFresh hAgree.2

/-! ## §6  Full-predicate ifThenElse case -/

/-- Full-predicate ifThenElse-var case: thread Full agreement through
    both branch IHs.  No env extension, no rs update other than what
    the branches do internally. -/
theorem simulates_ifThenElse_var_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (cond : String) (t e : ImpExpr) (c : LowCT)
    (env env' : Env) (rs : RustState) (v : Value)
    (ihT : ∀ c' env_a env_b rs_a v_a,
             HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
               t c' env_a env_b rs_a v_a)
    (ihE : ∀ c' env_a env_b rs_a v_a,
             HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
               e c' env_a env_b rs_a v_a) :
    HaxToLowCTSimulatesFull bridge bi fuel N leafSpec
      (.ifThenElse (.var cond) t e) c env env' rs v := by
  intro hHax hEval hAgree
  obtain ⟨tC, eC, hTtrans, hEtrans, hC⟩ :=
    haxToLowCT_ifThenElse_var_some cond t e c hHax
  subst hC
  rcases evalImp_ifThenElse_var_inv bi fuel cond t e env v env' hEval with
    ⟨hCond, hTeval⟩ | ⟨hCond, hEeval⟩
  · -- True branch
    obtain ⟨rs', hTexec, hAgree'⟩ :=
      ihT tC env env' rs v hTtrans hTeval hAgree
    have hScalar : rs.rsScalar cond = 1 :=
      envAgreesRust_bool_to_scalar env rs cond true hAgree.1 hCond
    refine ⟨rs', ?_, hAgree'⟩
    exact rustExec_RIfNz_dispatch_true N leafSpec cond tC eC rs rs' 1 hScalar
            (by decide) hTexec
  · -- False branch
    obtain ⟨rs', hEexec, hAgree'⟩ :=
      ihE eC env env' rs v hEtrans hEeval hAgree
    have hScalar : rs.rsScalar cond = 0 :=
      envAgreesRust_bool_to_scalar env rs cond false hAgree.1 hCond
    refine ⟨rs', ?_, hAgree'⟩
    exact rustExec_RIfNz_dispatch_false N leafSpec cond tC eC rs rs' hScalar hEexec

/-! ## §7  Bridge-level preconditions of the leaf-call arms

For every constructor whose `haxToLowCT` arm returns `none`, the
hypothesis `haxToLowCT e = some c` is `False`.  The program-level
theorem over the arms of this file is `haxToLowCT_simulates_program`
(`HaxToLowCTSim_Program.lean`), whose call-side conditions are decided
on the source program by `simScope`. -/

/-- The bridge-level preconditions of the `letBind (.app)` and
    `assign (.app)` arms: every leaf call is bridge-aligned with its
    `LeafSpec` output, and no leaf result decodes to a scalar. -/
structure FullSimPreconds (bi : Builtins) (leafSpec : LeafSpec)
    (bridge : ValueTowerBridge) where
  /-- Every leaf call has a tower-typed bridge agreement. -/
  allLeavesAgree :
    ∀ f, LeafCallAgreesTower bi leafSpec f (towerOfCallName f) bridge
  /-- Leaf return values are tower-typed (do not decode to scalar). -/
  leafScalar :
    ∀ f vals vRes, bi f vals = some vRes → valueToScalar vRes = none

end CatCrypt.Crypto.Hax
