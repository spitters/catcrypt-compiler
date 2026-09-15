/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Program
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta_LeafAgrees

/-!
# Whole-program simulation for `haxToLowCT` with exit invariants

`haxToLowCT_simulates_full` is the extraction step `ImpExpr → LowCT` of the
compiler-correctness chain: for a source program `e` accepted by the scope
checker `simScope (scalarNames e) Γ` (`SimWellFormed Γ e = true`), an entry
state tower-bound on `Γ` (`ScopeBound`) with no tower binding at the scalar
names of `e` (`NamesFresh`), and an entry environment agreeing with the state,
a successful source run `evalImp bi fuel e env = some (v, env')` is matched by a
run `RustExec N leafSpec c rs rs'` of the lowered program `c`, whose exit state
agrees with `env'`, is tower-bound on the checker's exit scope, and is fresh on
the scalar names.  The bridge-level side conditions are `FullSimPreconds`
(leaf-call agreement and tower-typed leaf results), `ProjPreconds`
(tuple-component reads) and `ProgramSimArms` (the `array_update` and `index`
arms; `ProgramSimArms_of_vacuity` discharges them when the builtin table
implements neither).  It is a corollary of `haxToLowCT_simulates_program`.

The field `FullSimPreconds.leafScalar` requires that no builtin result decodes
as a scalar, so a builtin table with arithmetic builtins does not satisfy the
hypotheses.  Programs calling such builtins are the scope of
`haxToLowCT_simulates_programT` (`HaxToLowCTSim_ProgramTower.lean`), which
replaces `FullSimPreconds` by the argument-relating agreement
`LeafCallAgreesArgs`.

§2 instantiates every hypothesis for the program `let y = leaf(a); y`, with a
builtin table whose one builtin `leaf` returns the constant `.array []` (a value
that decodes to no scalar), and obtains the lowered run.

## Main results

* `haxToLowCT_simulates_full`: a successful source run of a `simScope`-accepted
  program is matched by a `RustExec` run of its lowering, with the exit invariants.
* `simFull_runs`: the hypotheses hold for `let y = leaf(a); y` with the constant
  builtin table `simFullBuiltins`, and the lowered program runs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr Value Env Builtins)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustExec LeafSpec)

/-! ## §1  The theorem -/

/-- **Whole-program simulation for `haxToLowCT`.**  For a program accepted by
    `simScope (scalarNames e) Γ`, an entry state bound on `Γ` and fresh on
    `scalarNames e`, and the bridge-level preconditions, every successful source
    run from an agreeing environment is matched by a run of the lowered program
    to a state that agrees with the exit environment, is bound on the exit
    scope `Γ'` returned by the checker, and is fresh on `scalarNames e`. -/
theorem haxToLowCT_simulates_full
    (bridge : ValueTowerBridge) (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (hPre : FullSimPreconds bi leafSpec bridge)
    (hProj : ProjPreconds bridge leafSpec)
    (e : ImpExpr)
    (hArms : ProgramSimArms bridge bi N leafSpec (scalarNames e))
    (Γ : TowerScope) (hWF : SimWellFormed Γ e = true)
    (rs : RustState) (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs (scalarNames e))
    (c : LowCT) (env env' : Env) (v : Value)
    (hHax : haxToLowCT e = some c)
    (hEval : evalImp bi fuel e env = some (v, env'))
    (hAgree : envAgreesRustFull bridge env rs) :
    ∃ Γ' rs', simScope (scalarNames e) Γ e = some Γ' ∧ RustExec N leafSpec c rs rs'
      ∧ envAgreesRustFull bridge env' rs' ∧ ScopeBound rs' Γ'
      ∧ NamesFresh rs' (scalarNames e) := by
  obtain ⟨Γ', hS⟩ := Option.isSome_iff_exists.mp hWF
  obtain ⟨rs', hExec, hAgree', hSB', hSF'⟩ :=
    haxToLowCT_simulates_program bridge bi N leafSpec (scalarNames e) hPre hProj hArms e
      fuel Γ Γ' c env env' rs v hS hSB hSF hHax hEval hAgree
  exact ⟨Γ', rs', hS, hExec, hAgree', hSB', hSF'⟩

/-! ## §2  The hypotheses hold for a program with a leaf call -/

/-- The bridge relating the empty array to every tower value and relating no
    other source value. -/
def simFullBridge : ValueTowerBridge := fun _ v _ => v = .array []

/-- The builtin table implementing one leaf, `leaf`, which returns the empty
    array on every argument list; every other name is unimplemented.  The
    result is constant and decodes to no scalar, as `FullSimPreconds.leafScalar`
    requires. -/
def simFullBuiltins : Builtins := fun f _ => if f = "leaf" then some (.array []) else none

/-- The program `let y = leaf(a); y`. -/
def simFullProgram : ImpExpr := .letBind "y" (.app "leaf" [.var "a"]) (.var "y")

/-- The entry scope: `a` is tower-bound at the type `towerOfCallName` assigns to
    `leaf`. -/
def simFullScope : TowerScope := [("a", towerOfCallName "leaf")]

/-- The entry environment: `a` is bound to the empty array. -/
def simFullEnv : Env := fun n => if n = "a" then some (.array []) else none

/-- The entry state: `a` holds the default tower value at the type of `leaf`,
    and every scalar slot holds `0`. -/
def simFullState : RustState :=
  { rsTower := fun n => if n = "a" then some ⟨towerOfCallName "leaf", default⟩ else none
    rsScalar := fun _ => 0 }

theorem simFull_preconds (leafSpec : LeafSpec) :
    FullSimPreconds simFullBuiltins leafSpec simFullBridge where
  allLeavesAgree := by
    intro f
    by_cases h : f = "leaf"
    · subst h
      intro rs dest args vals vRes hBi _
      simp only [simFullBuiltins, if_true, Option.some.injEq] at hBi
      subst hBi
      rfl
    · exact leafCallAgreesTower_of_unmatched _ _ _ _ _ (fun _ => by simp [simFullBuiltins, h])
  leafScalar := by
    intro f vals vRes h
    simp only [simFullBuiltins] at h
    split at h
    · cases h; rfl
    · cases h

theorem simFull_proj (leafSpec : LeafSpec) : ProjPreconds simFullBridge leafSpec where
  tupleAgrees := by
    intro _ _ vTup _ _ hB hP
    simp only [simFullBridge] at hB
    subst hB
    simp [Value.projIdx] at hP
  compScalar := by
    intro vTup _ _ _ hB hP
    simp only [simFullBridge] at hB
    subst hB
    simp [Value.projIdx] at hP

theorem simFull_arms (N : Nat) (leafSpec : LeafSpec) :
    ProgramSimArms simFullBridge simFullBuiltins N leafSpec (scalarNames simFullProgram) :=
  ProgramSimArms_of_vacuity _ _ _ _ _ (fun _ => by simp [simFullBuiltins])
    (fun _ => by simp [simFullBuiltins])

theorem simFull_wellFormed : SimWellFormed simFullScope simFullProgram = true := by
  simp +decide [SimWellFormed, simScope, simFullScope, simFullProgram, scalarNames, argsInScope,
    argsAvoid, scopeCompat, List.lookup]

theorem simFull_hax : (haxToLowCT simFullProgram).isSome = true := by
  decide

theorem simFull_eval (fuel : Nat) :
    ∃ v env', evalImp simFullBuiltins (fuel + 1) simFullProgram simFullEnv = some (v, env') := by
  simp [evalImp, simFullProgram, _root_.Hax.denote, _root_.Hax.denoteArgs, bind, StateT.bind,
    pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, StateT.run, simFullEnv,
    simFullBuiltins, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

theorem simFull_scopeBound : ScopeBound simFullState simFullScope := by
  intro n dt h
  simp only [simFullScope, List.lookup] at h
  split at h
  · rename_i hn
    cases h
    simp only [beq_iff_eq] at hn
    exact ⟨default, by simp [simFullState, hn]⟩
  · cases h

theorem simFull_agree : envAgreesRustFull simFullBridge simFullEnv simFullState := by
  refine ⟨fun n w hw m hm => ?_, fun n w hw dt val hv => ?_⟩
  · simp only [simFullEnv] at hw
    split at hw
    · cases hw; simp [valueToScalar] at hm
    · cases hw
  · simp only [simFullEnv] at hw
    split at hw
    · cases hw; rfl
    · cases hw

/-- Every hypothesis of `haxToLowCT_simulates_full` other than the source run
    and the lowering holds for `simFullProgram`, `simFullBuiltins`,
    `simFullBridge`, `simFullScope`, `simFullState` and `simFullEnv`, at every
    `N` and `leafSpec`. -/
theorem simFull_hyps (N : Nat) (leafSpec : LeafSpec) :
    FullSimPreconds simFullBuiltins leafSpec simFullBridge
      ∧ ProjPreconds simFullBridge leafSpec
      ∧ ProgramSimArms simFullBridge simFullBuiltins N leafSpec (scalarNames simFullProgram)
      ∧ SimWellFormed simFullScope simFullProgram = true
      ∧ ScopeBound simFullState simFullScope
      ∧ NamesFresh simFullState (scalarNames simFullProgram)
      ∧ envAgreesRustFull simFullBridge simFullEnv simFullState :=
  ⟨simFull_preconds leafSpec, simFull_proj leafSpec, simFull_arms N leafSpec, simFull_wellFormed,
   simFull_scopeBound, fun _ h => by simp [simFullProgram, scalarNames] at h, simFull_agree⟩

/-- **`haxToLowCT_simulates_full` at `let y = leaf(a); y`.**  At every positive
    fuel, `N` and `leafSpec`, the program lowers to some `c`, its source run from
    `simFullEnv` with the `leaf` builtin returns some `(v, env')`, and `c` runs
    from `simFullState` to a state agreeing with `env'`, bound on the exit scope
    and fresh on the scalar names. -/
theorem simFull_runs (fuel N : Nat) (leafSpec : LeafSpec) :
    ∃ c v env' Γ' rs', haxToLowCT simFullProgram = some c
      ∧ evalImp simFullBuiltins (fuel + 1) simFullProgram simFullEnv = some (v, env')
      ∧ simScope (scalarNames simFullProgram) simFullScope simFullProgram = some Γ'
      ∧ RustExec N leafSpec c simFullState rs'
      ∧ envAgreesRustFull simFullBridge env' rs' ∧ ScopeBound rs' Γ'
      ∧ NamesFresh rs' (scalarNames simFullProgram) := by
  obtain ⟨hPre, hProj, hArms, hWF, hSB, hSF, hAgree⟩ := simFull_hyps N leafSpec
  obtain ⟨c, hHax⟩ := Option.isSome_iff_exists.mp simFull_hax
  obtain ⟨v, env', hEval⟩ := simFull_eval fuel
  obtain ⟨Γ', rs', hS, hExec, hAgree', hSB', hSF'⟩ :=
    haxToLowCT_simulates_full simFullBridge simFullBuiltins (fuel + 1) N leafSpec hPre hProj
      simFullProgram hArms simFullScope hWF simFullState hSB hSF c simFullEnv env' v
      hHax hEval hAgree
  exact ⟨c, v, env', Γ', rs', hHax, hEval, hS, hExec, hAgree', hSB', hSF'⟩

end CatCrypt.Crypto.Hax
