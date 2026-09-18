/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.LowCTToHax
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramLoops

/-!
# Semantic agreement of `lowCTToImp` with `RustExec`

The source run of a translation `e = lowCTToImp c` under hax-lean's `denote`
(through `evalImp`, of `forToLoop e`, which reads each `forFold` as the
`forLoop` over the same range) is simulated by `RustExec` of `frontNF c`.  The
result is the program-level front simulation `haxToLowCT_simulates_programW`
instantiated at `e`, with the round trip `lowCTToImp_roundTrip` discharging its
lowering hypothesis; its hypotheses are carried unchanged:

* the leaf, projection, literal-store, index, array-update and scalar-call
  agreements of the builtin table `bi` with `leafSpec` through `bridge`
  (`hLeaf`, `hProj`, `hLit`, `hIdx`, `hUpd`, `hSc`);
* the scope checker `simScopeW towerOfCallName D S T A Γ e` accepts `e`;
* the entry state is bound on `Γ` and fresh on the scalar names `S`, the entry
  environment agrees with it (`envAgreesRustT`) and satisfies `ScalarInv D S`.

The checker accepts the call, literal, scalar-call, tuple-load, array-load and
array-store bindings, `if`/`while` on a variable, `forFold` from a non-negative
literal to a literal or a variable bound, and sequencing.  It rejects the
`match_` of a two-destination call, so the `RCallSwap` arm of `lowCTToImp` has
the round trip and no simulation, as has a runtime loop bound other than a
variable.

The scalar call `scalar#Sub` is read by `ScalarCallsAgree` as the natural-number
subtraction `scalarCallNat`, which truncates at `0` as `SExpr.eval` of `SSub`
does.

## Main results

* `lowCTToImp_simulates` — the simulation, with the tower-literal and array
  tables `T`, `A`.
* `lowCTToImp_simulates_frontNF` — the simulation with empty tables, stated on
  `frontNF c`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr Value Env Builtins)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustExec LeafSpec)

/-- **Semantic agreement.**  The source run of the translation of `c` is
    simulated by `RustExec` of `frontNF c`, with the literal and array typing
    passes `litTower T`, `arrTower A`, from the hypotheses of
    `haxToLowCT_simulates_programW`. -/
theorem lowCTToImp_simulates
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (D S T : List String) (A : TowerScope)
    (hLeaf : ∀ f, f ≠ "array_update" → f ≠ "index" → scalarCallName f = false →
      LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (hLit : LitStoreAgrees bridge leafSpec)
    (hIdx : IndexAgrees bridge bi leafSpec)
    (hUpd : ArrUpdateAgrees bridge bi leafSpec)
    (hSc : ScalarCallsAgree bi)
    (c : LowCT) (e : ImpExpr) (he : lowCTToImp c = some e)
    (fuel : Nat) (Γ Γ' : TowerScope) (env env' : Env) (rs : RustState) (v : Value)
    (hScope : simScopeW towerOfCallName D S T A Γ e = some Γ')
    (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs S)
    (hEval : evalImp bi fuel (forToLoop e) env = some (v, env'))
    (hAgree : envAgreesRustT bridge env rs) (hInv : ScalarInv D S env) :
    ∃ rs', RustExec N leafSpec (arrTower A (litTower T (frontNF c))) rs rs' ∧
      envAgreesRustT bridge env' rs' ∧ ScopeBound rs' Γ' ∧ NamesFresh rs' S ∧
      ScalarInv D S env' :=
  haxToLowCT_simulates_programW bridge bi N leafSpec D S T A hLeaf hProj hLit hIdx hUpd hSc e
    fuel Γ Γ' (frontNF c) env env' rs v hScope hSB hSF (lowCTToImp_roundTrip c e he) hEval
    hAgree hInv

/-- `lowCTToImp_simulates` with no literal stored at the tower and no array
    table: the source run of the translation is simulated by `RustExec` of
    `frontNF c` itself. -/
theorem lowCTToImp_simulates_frontNF
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (D S : List String)
    (hLeaf : ∀ f, f ≠ "array_update" → f ≠ "index" → scalarCallName f = false →
      LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (hLit : LitStoreAgrees bridge leafSpec)
    (hIdx : IndexAgrees bridge bi leafSpec)
    (hUpd : ArrUpdateAgrees bridge bi leafSpec)
    (hSc : ScalarCallsAgree bi)
    (c : LowCT) (e : ImpExpr) (he : lowCTToImp c = some e)
    (fuel : Nat) (Γ Γ' : TowerScope) (env env' : Env) (rs : RustState) (v : Value)
    (hScope : simScopeW towerOfCallName D S [] [] Γ e = some Γ')
    (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs S)
    (hEval : evalImp bi fuel (forToLoop e) env = some (v, env'))
    (hAgree : envAgreesRustT bridge env rs) (hInv : ScalarInv D S env) :
    ∃ rs', RustExec N leafSpec (frontNF c) rs rs' ∧
      envAgreesRustT bridge env' rs' ∧ ScopeBound rs' Γ' ∧ NamesFresh rs' S ∧
      ScalarInv D S env' := by
  have h := lowCTToImp_simulates bridge bi N leafSpec D S [] [] hLeaf hProj hLit hIdx hUpd hSc
    c e he fuel Γ Γ' env env' rs v hScope hSB hSF hEval hAgree hInv
  rwa [litTower_nil, arrTower_nil] at h

end CatCrypt.Crypto.Hax
