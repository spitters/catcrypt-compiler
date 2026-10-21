/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxNFRel
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Program -- deprecated_module: ignore
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramTower -- deprecated_module: ignore
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramLit -- deprecated_module: ignore
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramArr -- deprecated_module: ignore
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramFor -- deprecated_module: ignore
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramLoops -- deprecated_module: ignore
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Exit -- deprecated_module: ignore

/-!
# The simulation theorems of the `ImpExpr` front on the normal form `NF`

The domain of the front is the monadic A-normal form `Hax.NF`. Each simulation
theorem of the front is restated here with `NF e` as its first hypothesis,
followed by the acceptance hypothesis of its scope checker. Each corollary follows
from the unrestricted theorem; the `NF` hypothesis is implied by the checker
hypothesis (`nf_of_simScope`, `nf_of_simScopeL`, `nf_of_simScopeA`,
`nf_of_simScopeF`, `nf_of_simScopeW`, `isNFK_of_exitSimOk`), so each corollary
applies on the same inputs as the theorem it restates.

## Main results

* `haxToLowCT_simulates_program_of_NF`, `haxToLowCT_simulates_programT_of_NF`,
  `haxToLowCT_simulates_programL_of_NF`, `haxToLowCT_simulates_programA_of_NF`,
  `haxToLowCT_simulates_programF_of_NF`, `haxToLowCT_simulates_programW_of_NF` —
  the program-level simulations on `NF`
* `haxToLowCTK_simulates_of_isNFK`, `haxToLowCTK_simulates_of_NF` — the exit-flag
  simulation on the normal form of the loop context, and on `NF`
* `haxToLowCT_front_domain` — an input `haxToLowCT` lowers is in `NF`, has the
  shape `AnfShaped`, and is in normal form in every loop context
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr Value Env Outcome Builtins denote' isNFK NF isNFK_of_isNF)
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## The program-level simulations -/

/-- `haxToLowCT_simulates_program` on the domain `NF`: for an expression in `NF`
    that `simScope` accepts, the lowering runs to a state agreeing with the exit
    environment of every terminating `evalImp` run. -/
theorem haxToLowCT_simulates_program_of_NF
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S : List String)
    (hPre : FullSimPreconds bi leafSpec bridge)
    (hProj : ProjPreconds bridge leafSpec)
    (hArms : ProgramSimArms bridge bi N leafSpec S)
    (e : ImpExpr) (_hNF : NF e)
    {fuel : Nat} {Γ Γ' : TowerScope} {c : LowCT} {env env' : Env} {rs : RustState} {v : Value}
    (hScope : simScope S Γ e = some Γ')
    (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs S)
    (hHax : haxToLowCT e = some c)
    (hEval : evalImp bi fuel e env = some (v, env'))
    (hAgree : envAgreesRustFull bridge env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesRustFull bridge env' rs' ∧
      ScopeBound rs' Γ' ∧ NamesFresh rs' S :=
  haxToLowCT_simulates_program bridge bi N leafSpec S hPre hProj hArms e
    fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree

/-- `haxToLowCT_simulates_programT` on the domain `NF`. -/
theorem haxToLowCT_simulates_programT_of_NF
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S : List String)
    (hLeaf : ∀ f, LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (hArr : ∀ vals, bi "array_update" vals = none)
    (hIdx : ∀ vals, bi "index" vals = none)
    (e : ImpExpr) (_hNF : NF e)
    {fuel : Nat} {Γ Γ' : TowerScope} {c : LowCT} {env env' : Env} {rs : RustState} {v : Value}
    (hScope : simScope S Γ e = some Γ') (hConds : condsScalar S e = true)
    (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs S)
    (hHax : haxToLowCT e = some c)
    (hEval : evalImp bi fuel e env = some (v, env'))
    (hAgree : envAgreesRustT bridge env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesRustT bridge env' rs' ∧
      ScopeBound rs' Γ' ∧ NamesFresh rs' S :=
  haxToLowCT_simulates_programT bridge bi N leafSpec S hLeaf hProj hArr hIdx e
    fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree

/-- `haxToLowCT_simulates_programL` on the domain `NF`. -/
theorem haxToLowCT_simulates_programL_of_NF
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S T : List String)
    (hLeaf : ∀ f, LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (hLit : LitStoreAgrees bridge leafSpec)
    (hArr : ∀ vals, bi "array_update" vals = none)
    (hIdx : ∀ vals, bi "index" vals = none)
    (e : ImpExpr) (_hNF : NF e)
    {fuel : Nat} {Γ Γ' : TowerScope} {c : LowCT} {env env' : Env} {rs : RustState} {v : Value}
    (hScope : simScopeL S T Γ e = some Γ') (hConds : condsScalar S e = true)
    (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs S)
    (hHax : haxToLowCT e = some c)
    (hEval : evalImp bi fuel e env = some (v, env'))
    (hAgree : envAgreesRustT bridge env rs) :
    ∃ rs', RustExec N leafSpec (litTower T c) rs rs' ∧ envAgreesRustT bridge env' rs' ∧
      ScopeBound rs' Γ' ∧ NamesFresh rs' S :=
  haxToLowCT_simulates_programL bridge bi N leafSpec S T hLeaf hProj hLit hArr hIdx e
    fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree

/-- `haxToLowCT_simulates_programA` on the domain `NF`. -/
theorem haxToLowCT_simulates_programA_of_NF
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S T : List String) (A : TowerScope)
    (hLeaf : ∀ f, f ≠ "array_update" → f ≠ "index" →
      LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (hLit : LitStoreAgrees bridge leafSpec)
    (hIdx : IndexAgrees bridge bi leafSpec)
    (hUpd : ArrUpdateAgrees bridge bi leafSpec)
    (e : ImpExpr) (_hNF : NF e)
    {fuel : Nat} {Γ Γ' : TowerScope} {c : LowCT} {env env' : Env} {rs : RustState} {v : Value}
    (hScope : simScopeA towerOfCallName S T A Γ e = some Γ') (hConds : condsScalar S e = true)
    (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs S)
    (hHax : haxToLowCT e = some c)
    (hEval : evalImp bi fuel e env = some (v, env'))
    (hAgree : envAgreesRustT bridge env rs) :
    ∃ rs', RustExec N leafSpec (arrTower A (litTower T c)) rs rs' ∧
      envAgreesRustT bridge env' rs' ∧ ScopeBound rs' Γ' ∧ NamesFresh rs' S :=
  haxToLowCT_simulates_programA bridge bi N leafSpec S T A hLeaf hProj hLit hIdx hUpd e
    fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree

/-- `haxToLowCT_simulates_programF` on the domain `NF`. -/
theorem haxToLowCT_simulates_programF_of_NF
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S T : List String) (A : TowerScope)
    (hLeaf : ∀ f, f ≠ "array_update" → f ≠ "index" →
      LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (hLit : LitStoreAgrees bridge leafSpec)
    (hIdx : IndexAgrees bridge bi leafSpec)
    (hUpd : ArrUpdateAgrees bridge bi leafSpec)
    (e : ImpExpr) (_hNF : NF e)
    {fuel : Nat} {Γ Γ' : TowerScope} {c : LowCT} {env env' : Env} {rs : RustState} {v : Value}
    (hScope : simScopeF towerOfCallName S T A Γ e = some Γ')
    (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs S)
    (hHax : haxToLowCT e = some c)
    (hEval : evalImp bi fuel (forToLoop e) env = some (v, env'))
    (hAgree : envAgreesRustT bridge env rs) :
    ∃ rs', RustExec N leafSpec (arrTower A (litTower T c)) rs rs' ∧
      envAgreesRustT bridge env' rs' ∧ ScopeBound rs' Γ' ∧ NamesFresh rs' S :=
  haxToLowCT_simulates_programF bridge bi N leafSpec S T A hLeaf hProj hLit hIdx hUpd e
    fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree

/-- `haxToLowCT_simulates_programW` on the domain `NF`. -/
theorem haxToLowCT_simulates_programW_of_NF
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (D S T : List String) (A : TowerScope)
    (hLeaf : ∀ f, f ≠ "array_update" → f ≠ "index" → scalarCallName f = false →
      LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (hLit : LitStoreAgrees bridge leafSpec)
    (hIdx : IndexAgrees bridge bi leafSpec)
    (hUpd : ArrUpdateAgrees bridge bi leafSpec)
    (hSc : ScalarCallsAgree bi)
    (hLimb : LimbReadAgrees bridge bi)
    (e : ImpExpr) (_hNF : NF e)
    {fuel : Nat} {Γ Γ' : TowerScope} {c : LowCT} {env env' : Env} {rs : RustState} {v : Value}
    (hScope : simScopeW towerOfCallName D S T A Γ e = some Γ')
    (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs S)
    (hHax : haxToLowCT e = some c)
    (hEval : evalImp bi fuel (forToLoop e) env = some (v, env'))
    (hAgree : envAgreesRustT bridge env rs) (hInv : ScalarInv D S env) :
    ∃ rs', RustExec N leafSpec (arrTower A (litTower T c)) rs rs' ∧
      envAgreesRustT bridge env' rs' ∧ ScopeBound rs' Γ' ∧ NamesFresh rs' S ∧
      ScalarInv D S env' :=
  haxToLowCT_simulates_programW bridge bi N leafSpec D S T A hLeaf hProj hLit hIdx hUpd hSc
    hLimb e fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree hInv

/-! ## The exit-flag simulation -/

/-- `haxToLowCTK_simulates` on the normal form of the loop context `fl.isSome`:
    for an expression in that normal form that `exitSimOk` accepts, the lowered
    command matches every `denote'` run that ends in a value. -/
theorem haxToLowCTK_simulates_of_isNFK (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (hs : ScalarOpsSound bi) (e : ImpExpr) {tl : Bool} {fl : Option String}
    (_hNF : isNFK fl.isSome e = true)
    {fuel : Nat} {env env' : Env} {o : Outcome} {rs : RustState} {c : LowCT} {x : Bool}
    (hOk : exitSimOk tl fl.isSome e = true) (hCtx : RunCtx fl)
    (hLow : haxToLowCTK true tl fl e = some (c, x))
    (hRun : (denote' bi fuel e).run env = (o, env'))
    (hVal : ∃ v, o = .val v)
    (hAgree : envAgreesOff env rs) (hRet : rs.rsScalar exitRetName = 0) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesExit tl o env' rs' ∧
      (x = false → rs'.rsScalar exitRetName = 0) :=
  haxToLowCTK_simulates bi N leafSpec hs e tl fl fuel env env' o rs c x
    hOk hCtx hLow hRun hVal hAgree hRet

/-- `haxToLowCTK_simulates` on the domain `NF`, in every loop context. -/
theorem haxToLowCTK_simulates_of_NF (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (hs : ScalarOpsSound bi) (e : ImpExpr) {tl : Bool} {fl : Option String}
    (hNF : NF e)
    {fuel : Nat} {env env' : Env} {o : Outcome} {rs : RustState} {c : LowCT} {x : Bool}
    (hOk : exitSimOk tl fl.isSome e = true) (hCtx : RunCtx fl)
    (hLow : haxToLowCTK true tl fl e = some (c, x))
    (hRun : (denote' bi fuel e).run env = (o, env'))
    (hVal : ∃ v, o = .val v)
    (hAgree : envAgreesOff env rs) (hRet : rs.rsScalar exitRetName = 0) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesExit tl o env' rs' ∧
      (x = false → rs'.rsScalar exitRetName = 0) :=
  haxToLowCTK_simulates_of_isNFK bi N leafSpec hs e (isNFK_of_isNF e _ hNF)
    hOk hCtx hLow hRun hVal hAgree hRet

/-! ## The domain of the front -/

/-- **The input domain of `haxToLowCT`.** An expression `haxToLowCT` lowers is in
    the normal form `NF`, has the shape `AnfShaped`, and is in normal form in every
    loop context. -/
theorem haxToLowCT_front_domain {e : ImpExpr} {c : LowCT} (h : haxToLowCT e = some c) :
    NF e ∧ AnfShaped e = true ∧ ∀ il, isNFK il e = true := by
  have hs : (haxToLowCT e).isSome = true := by rw [h]; rfl
  exact ⟨nf_of_haxToLowCT_isSome e hs, (haxToLowCT_isSome_iff_anf e).mp hs,
    isNFK_of_anfShaped e ((haxToLowCT_isSome_iff_anf e).mp hs)⟩

end CatCrypt.Crypto.Hax
