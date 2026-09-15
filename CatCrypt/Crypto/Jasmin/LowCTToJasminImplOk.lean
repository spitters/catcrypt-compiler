/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTToJasmin
public import Std.Data.String.ToNat

/-!
# Satisfiability of the leaf oracle hypotheses of `LowCTToJasmin`

The simulation lemmas of `LowCTToJasmin` take oracle hypotheses stating the heap
effect of one translated instruction: `LeafImplOk`, `LeafImplOkNewSid` and
`CallNImplOk` for a `Ccall`, `LimbStoreImplOk`, `SelectImplOk` and `CloneImplOk`
for the `STORE64`, `CMOV` and `CLONE_TOWER` operators.

Each hypothesis is stated at one fuel. At fuel `0`, `translateCmd` returns the
code `.fail`, whose evaluation `SDistr.fail = PMF.pure none` is not a point
distribution, so none of them holds at every fuel; the refutations instantiate
their premises with a satisfying state. At every fuel `≥ 2` a one-instruction
command runs, and the operator hypotheses hold for every environment:
`STORE64` with the limb-store oracle that writes the word at byte offset `8 * idx`,
`CMOV` and `CLONE_TOWER` with no condition on the leaf specification.

The `Ccall` translation keeps the caller scope and writes the values the callee body
returns to the result l-values. For an environment `pureLeafEnv g` whose function `f`
returns `gf` of its argument values, `LeafImplOk` and `LeafImplOkNewSid` hold with the
call specification `pureCallSpec g`, and `CallNImplOk` holds for every specification
whose output `i` is the result at position `i`. The function `add` of `addLeafTable`
returns the bytewise sum of two arrays, so its calls write a destination value that
depends on the arguments only; `addProg_simulates` instantiates
`rustExecSimulates_withCalls` on a program with one such call.

## Contents

* `not_forall_leafImplOk`, `not_forall_leafImplOkNewSid`, `not_forall_callNImplOk`,
  `not_forall_limbStoreImplOk`, `not_forall_selectImplOk`,
  `not_forall_cloneImplOk` — the all-fuel forms are false.
* `storeLeafSpec`, `emptyTransEnv` — a leaf specification whose call returns the old
  destination, and the environment with no function bodies.
* `limbStoreImplOk_storeLeafSpec`, `selectImplOk_of_two_le`, `cloneImplOk_of_two_le`,
  `leafImplOk_storeLeafSpec`, `callNImplOk_storeLeafSpec` — the hypotheses at every
  fuel `≥ 2`.
* `translateCmd_ccall_newSid`, `translateWriteLVals_locToLVal_results`,
  `translateWriteLVals_dests_callNUpdate` — the scope and heap effect of a call.
* `pureLeafEnv`, `pureCallSpec`, `leafImplOk_pureLeafEnv`,
  `leafImplOkNewSid_of_leafImplOk`, `callNImplOk_pureLeafEnv` — the call hypotheses
  for environments of pure functions.
* `addLeafSpec`, `addCallNLeafSpec`, `leafImplOkNewSid_addLeafSpec`,
  `callNImplOk_addCallNLeafSpec`, `addProg_simulates` — bytewise addition.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.LowCT

open CatCrypt.Crypto.Jasmin
open CatCrypt.Core CatCrypt.Deep CatCrypt.Prob

/-! ## Refutations of the all-fuel forms -/

/-- Evaluation of a translated command at fuel `0` is never a point distribution. -/
theorem translateCmd_zero_eval_ne_pure (env : TransEnv) (cmd : Cmd) (sid : ScopeId)
    (heap0 heap1 : Heap) :
    (translateCmd env cmd sid 0).code.eval heap0 ≠ SDistr.pure (⟨()⟩, heap1) := by
  intro hEval
  have hfail := congrArg (fun p : SDistr _ => p none) hEval
  simp [translateCmd, SPComp.fail, SDistr.fail, SDistr.pure] at hfail

/-- A state binding the tower variable `"x"` at `TFp` and every scalar to the value
    its cell holds in `heap0`, with the invariants it satisfies at scope `1`. -/
theorem exists_state_encoded (heap0 : Heap) :
    ∃ rs0 : RustState,
      HeapInv rs0 heap0 1 ∧ ScalarInv rs0 heap0 1 ∧ ScalarsBounded rs0 ∧
      rs0.rsTower "x" = some ⟨.TFp, heap0.get (towerLoc 1 "x" .TFp)⟩ := by
  refine ⟨{ rsTower := fun y => if y = "x" then
              some ⟨.TFp, heap0.get (towerLoc 1 "x" .TFp)⟩ else none,
            rsScalar := fun y =>
              (heap0.get (translateVar 1 { vname := y, vtype := .sword .U64 }) :
                BitVec 64).toNat }, ?_, ?_, ?_, by simp⟩
  · intro y t v hy
    by_cases hyx : y = "x"
    · subst hyx
      simp only [if_true, Option.some.injEq] at hy
      cases hy
      rfl
    · simp [hyx] at hy
  · intro y
    have key : ∀ w : BitVec 64, w = BitVec.ofNat 64 w.toNat := fun w =>
      ((BitVec.ofNat_toNat 64 w).trans (BitVec.setWidth_eq w)).symm
    exact key _
  · intro y
    exact BitVec.isLt _

/-- `LeafImplOk` holds at no family of fuels containing `0`: the translated call
    at fuel `0` evaluates to the failure distribution. -/
theorem not_forall_leafImplOk (leafSpec : LeafSpec) (env : TransEnv) :
    ¬ ∀ fuel', LeafImplOk leafSpec env fuel' := by
  intro h
  obtain ⟨rs0, hInv, -, -, hx⟩ := exists_state_encoded default
  obtain ⟨heap1, hEval, -⟩ :=
    h 0 "f" (mkFpLoc "x") [] rs0 1 default _ [] hInv hx rfl (by simp)
  exact translateCmd_zero_eval_ne_pure _ _ _ _ _ hEval

/-- `LeafImplOkNewSid` holds at no family of fuels containing `0`. -/
theorem not_forall_leafImplOkNewSid (leafSpec : LeafSpec) (env : TransEnv) :
    ¬ ∀ fuel', LeafImplOkNewSid leafSpec env fuel' := by
  intro h
  obtain ⟨rs0, hInv, hSInv, hB, hx⟩ := exists_state_encoded default
  obtain ⟨heap1, hEval, -⟩ :=
    h 0 "f" (mkFpLoc "x") [] rs0 1 default _ [] hInv hSInv hx rfl (by simp) hB
  exact translateCmd_zero_eval_ne_pure _ _ _ _ _ hEval

/-- `CallNImplOk` holds at no family of fuels containing `0`. -/
theorem not_forall_callNImplOk (leafSpec : LeafSpec) (env : TransEnv) :
    ¬ ∀ fuel', CallNImplOk leafSpec env fuel' := by
  intro h
  obtain ⟨rs0, hInv, -, -, -⟩ := exists_state_encoded default
  obtain ⟨heap1, hEval, -⟩ :=
    h 0 "f" [] [] rs0 1 default hInv (by simp) (by simp)
  exact translateCmd_zero_eval_ne_pure _ _ _ _ _ hEval

/-- `LimbStoreImplOk` holds at no family of fuels containing `0`. -/
theorem not_forall_limbStoreImplOk (leafSpec : LeafSpec) (env : TransEnv) :
    ¬ ∀ fuel', LimbStoreImplOk leafSpec env fuel' := by
  intro h
  obtain ⟨rs0, hInv, -, -, hx⟩ := exists_state_encoded default
  obtain ⟨heap1, hEval, -⟩ :=
    h 0 (mkFpLoc "x") 0 0 rs0 1 default _ hInv hx
  exact translateCmd_zero_eval_ne_pure _ _ _ _ _ hEval

/-- `SelectImplOk` holds at no family of fuels containing `0`. -/
theorem not_forall_selectImplOk (leafSpec : LeafSpec) (env : TransEnv) :
    ¬ ∀ fuel', SelectImplOk leafSpec env fuel' := by
  intro h
  obtain ⟨rs0, hInv, hSInv, hB, hx⟩ := exists_state_encoded default
  have hLk : locatedLookup rs0 (mkFpLoc "x") =
      some ((default : Heap).get (towerLoc 1 "x" .TFp)) := by
    simp [locatedLookup, hx, mkFpLoc]
    rfl
  obtain ⟨heap1, hEval, -⟩ :=
    h 0 (mkFpLoc "x") "s" (mkFpLoc "x") (mkFpLoc "x") rs0 1 default rfl rfl _ _ _
      hInv hSInv hB hx hLk hLk
  exact translateCmd_zero_eval_ne_pure _ _ _ _ _ hEval

/-- `CloneImplOk` holds at no family of fuels containing `0`. -/
theorem not_forall_cloneImplOk (env : TransEnv) :
    ¬ ∀ fuel', CloneImplOk env fuel' := by
  intro h
  obtain ⟨rs0, hInv, -, -, hx⟩ := exists_state_encoded default
  obtain ⟨heap1, hEval, -⟩ :=
    h 0 "y" .TFp (mkFpLoc "x") rs0 1 default _ rfl hInv hx
  exact translateCmd_zero_eval_ne_pure _ _ _ _ _ hEval

/-! ## Evaluation of the one-instruction commands -/

/-- Tower locations of different names have different ids, at any tower types. -/
theorem towerLoc_id_ne (sid : ScopeId) (x y : String) (t t' : TowerType) (hne : x ≠ y) :
    (towerLoc sid x t).id ≠ (towerLoc sid y t').id := by
  simp only [towerLoc, translateVar, varLocId]
  intro h
  exact hne (encodeVarName_injective (Nat.pair_eq_pair.mp h).2)

/-- A successful `locatedLookup` is a tower binding at the location's type. -/
theorem rsTower_of_locatedLookup (rs : RustState) (loc : Located) (v : RustVal loc.locDst)
    (h : locatedLookup rs loc = some v) :
    rs.rsTower loc.locVar = some ⟨loc.locDst, v⟩ := by
  unfold locatedLookup at h
  split at h
  · rename_i ty w heq
    split at h
    · rename_i hty
      cases hty
      simp at h
      rw [heq, h]
    · simp at h
  · simp at h

/-- Reading a tower variable returns the array at its tower location. -/
theorem translatePExpr_locToPExpr_eval (sid : ScopeId) (loc : Located) (heap : Heap) :
    (translatePExpr sid (locToPExpr loc)).eval heap =
      SDistr.pure (⟨.sarr loc.locSrc.storageBytes,
        heap.get (towerLoc sid loc.locVar loc.locSrc)⟩, heap) := by
  simp only [locToPExpr, locToGVar, locToVar, towerToSType, translatePExpr, readGVar, readVar,
    CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_get, CatCrypt.Deep.eval_ret,
    SPComp.bind_def, SPComp.get_def, SPComp.pure_def, SDistr.pure_bind]
  rfl

/-- Reading a list of tower variables leaves the heap unchanged. -/
theorem translatePExprAll_locToPExpr_eval (sid : ScopeId) (args : List Located) (heap : Heap) :
    ∃ vs, (translatePExprAll sid (args.map locToPExpr)).eval heap = SDistr.pure (vs, heap) := by
  induction args with
  | nil => exact ⟨[], by simp [translatePExprAll, CatCrypt.Deep.eval_ret, SPComp.pure_def]⟩
  | cons a rest ih =>
    obtain ⟨vs, hvs⟩ := ih
    refine ⟨⟨.sarr a.locSrc.storageBytes, heap.get (towerLoc sid a.locVar a.locSrc)⟩ :: vs, ?_⟩
    simp only [List.map_cons, translatePExprAll, CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret,
      SPComp.bind_def, SPComp.pure_def, translatePExpr_locToPExpr_eval, SDistr.pure_bind, hvs]

/-- Writing an array to the tower variable `loc` is one heap write at its tower
    location. -/
theorem translateWriteLVals_locToLVal_eval (sid : ScopeId) (loc : Located)
    (a : JArray loc.locSrc.storageBytes) (heap : Heap) :
    (translateWriteLVals sid [locToLVal loc] [⟨.sarr loc.locSrc.storageBytes, a⟩]).eval heap =
      SDistr.pure (⟨()⟩, heap.set (towerLoc sid loc.locVar loc.locSrc) a) := by
  simp only [translateWriteLVals, translateWriteLVal, locToLVal, locToVar, towerToSType,
    writeVar_sarr_eq, CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret, SPComp.bind_def,
    SPComp.pure_def]
  exact eval_put_bind_heap heap _ _ (fun h => SDistr.pure ((⟨()⟩ : ULift Unit), h))

/-- The integer constant `v.toNat` converts back to the 64-bit word `v`. -/
theorem intToWord_U64_toNat (v : BitVec 64) : intToWord .U64 (v.toNat : Int) = v := by
  simp [intToWord, WSize.bits]

/-- `STORE64` at fuel `n + 2` writes `v` at byte offset `8 * idx` of `loc`. -/
theorem translateCmd_store64_eval (env : TransEnv) (loc : Located) (idx : Nat)
    (v : BitVec 64) (sid : ScopeId) (n : Nat) (heap0 : Heap) :
    (translateCmd env [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
                               [locToPExpr loc, .Pconst idx, .Pconst v.toNat]]
        sid (n + 2)).code.eval heap0 =
      SDistr.pure (⟨()⟩, heap0.set (towerLoc sid loc.locVar loc.locSrc)
        (JArray.setWord (heap0.get (towerLoc sid loc.locVar loc.locSrc)) .U64 (idx * 8) v)) := by
  simp only [translateCmd, translateInstrR, translatePExprAll,
    CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret, SPComp.bind_def, SPComp.pure_def,
    translatePExpr_locToPExpr_eval, SDistr.pure_bind, translatePExpr]
  simp only [execSopn, execStore64, if_true, Int.toNat_natCast, intToWord_U64_toNat]
  erw [translateWriteLVals_locToLVal_eval]
  simp only [SDistr.pure_bind]

/-- `CLONE_TOWER` at fuel `n + 2` copies the array of `oldVar` to `cloneVar`. -/
theorem translateCmd_cloneTower_eval (env : TransEnv) (cloneVar oldVar : String)
    (cloneTy : TowerType) (sid : ScopeId) (n : Nat) (heap0 : Heap) :
    (translateCmd env
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                        info := { towerTag := cloneTy.byteSize } }] .AT_none
              (.Oasm { name := "CLONE_TOWER" })
              [locToPExpr { locVar := oldVar, locSrc := cloneTy }]]
        sid (n + 2)).code.eval heap0 =
      SDistr.pure (⟨()⟩, heap0.set (towerLoc sid cloneVar cloneTy)
        (heap0.get (towerLoc sid oldVar cloneTy))) := by
  simp only [translateCmd, translateInstrR, translatePExprAll,
    CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret, SPComp.bind_def, SPComp.pure_def,
    translatePExpr_locToPExpr_eval, SDistr.pure_bind]
  simp [execSopn, execCloneTower]
  erw [translateWriteLVals_locToLVal_eval sid { locVar := cloneVar, locSrc := cloneTy }]
  simp only [SDistr.pure_bind]

/-- `CMOV` at fuel `n + 2` writes to `dstVar` the array of `x0` when the selector
    cell holds `0` and the array of `x1` otherwise. -/
theorem translateCmd_cmov_eval (env : TransEnv) (sel dstVar x0 x1 : String)
    (t : TowerType) (sid : ScopeId) (n : Nat) (heap0 : Heap) (s : BitVec 64)
    (hsel : heap0.get (translateVar sid { vname := sel, vtype := .sword .U64 }) = s) :
    (translateCmd env
        [.Copn [locToLVal { locVar := dstVar, locSrc := t }] .AT_none (.Oasm { name := "CMOV" })
               [.Pvar { gv := { var := { vname := sel, vtype := .sword .U64 }, info := {} },
                        gs := false },
                locToPExpr { locVar := x0, locSrc := t },
                locToPExpr { locVar := x1, locSrc := t }]]
        sid (n + 2)).code.eval heap0 =
      SDistr.pure (⟨()⟩, heap0.set (towerLoc sid dstVar t)
        (if s = 0 then heap0.get (towerLoc sid x0 t) else heap0.get (towerLoc sid x1 t))) := by
  simp only [translateCmd, translateInstrR, translatePExprAll,
    CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret, SPComp.bind_def, SPComp.pure_def,
    translatePExpr_locToPExpr_eval, translatePExpr_pvar_u64_eval, SDistr.pure_bind, hsel]
  by_cases hs : s = 0
  · simp [execSopn, execCmovTower, hs]
    erw [translateWriteLVals_locToLVal_eval sid { locVar := dstVar, locSrc := t }]
    simp only [SDistr.pure_bind]
  · have hs' : ¬ s = 0#WSize.U64.bits := hs
    simp [execSopn, execCmovTower]
    rw [if_neg hs']
    erw [translateWriteLVals_locToLVal_eval sid { locVar := dstVar, locSrc := t }]
    simp only [SDistr.pure_bind]
    exact congrArg (fun a => SDistr.pure ((⟨()⟩ : ULift Unit), heap0.set (towerLoc sid dstVar t) a))
      (if_neg hs).symm

/-- The translation environment with no function bodies. -/
def emptyTransEnv : TransEnv := ⟨fun _ => none⟩

/-- A `Ccall` to a function absent from the environment leaves the heap unchanged. -/
theorem translateCmd_ccall_emptyTransEnv_eval (lvs : List LVal) (f : String)
    (args : List Located) (sid : ScopeId) (n : Nat) (heap0 : Heap) :
    (translateCmd emptyTransEnv [.Ccall .DoNotInline lvs { name := f } (args.map locToPExpr)]
        sid (n + 2)).code.eval heap0 = SDistr.pure (⟨()⟩, heap0) := by
  obtain ⟨vs, hvs⟩ := translatePExprAll_locToPExpr_eval sid args heap0
  simp only [translateCmd, translateInstrR, emptyTransEnv, CatCrypt.Deep.eval_bind,
    CatCrypt.Deep.eval_ret, SPComp.bind_def, SPComp.pure_def, hvs, SDistr.pure_bind]

/-! ## The oracle hypotheses at every fuel `≥ 2` -/

/-- A leaf specification whose call returns the old destination value, and whose limb
    store writes the 64-bit word little-endian at byte offset `8 * idx`. -/
def storeLeafSpec : LeafSpec where
  call := fun _ _ _ oldV _ => oldV
  limbStore := fun _ oldV idx v => JArray.setWord oldV .U64 (idx * 8) v

/-- `LimbStoreImplOk` holds for `storeLeafSpec`, every environment and every fuel `≥ 2`. -/
theorem limbStoreImplOk_storeLeafSpec (env : TransEnv) (fuel : Nat) (hfuel : 2 ≤ fuel) :
    LimbStoreImplOk storeLeafSpec env fuel := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  intro loc idx v rs0 sid heap0 oldDestV hInv hTower
  refine ⟨_, translateCmd_store64_eval env loc idx v sid n heap0, ?_, ?_, ?_⟩
  · erw [Heap.get_set_same]
    exact congrArg (fun a => JArray.setWord a .U64 (idx * 8) v) (hInv _ _ _ hTower)
  · intro x t hx
    exact Heap.get_set_other _ _ _ _ (towerLoc_id_ne sid loc.locVar x _ t (Ne.symm hx))
  · intro x
    exact Heap.get_set_other _ _ _ _ (wordLoc_id_ne_towerLoc_id sid x loc.locVar _).symm

/-- `CloneImplOk` holds for every environment and every fuel `≥ 2`. -/
theorem cloneImplOk_of_two_le (env : TransEnv) (fuel : Nat) (hfuel : 2 ≤ fuel) :
    CloneImplOk env fuel := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  intro cloneVar cloneTy oldDest rs0 sid heap0 oldDestV hTy hInv hTower
  obtain ⟨oldVar, oldTy⟩ := oldDest
  simp only [Located.locDst] at hTy
  subst hTy
  refine ⟨_, translateCmd_cloneTower_eval env cloneVar oldVar oldTy sid n heap0, ?_, ?_, ?_⟩
  · erw [Heap.get_set_same]
    exact hInv _ _ _ hTower
  · intro x t hx
    exact Heap.get_set_other _ _ _ _ (towerLoc_id_ne sid cloneVar x _ t (Ne.symm hx))
  · intro x
    exact Heap.get_set_other _ _ _ _ (wordLoc_id_ne_towerLoc_id sid x cloneVar _).symm

/-- `SelectImplOk` holds for every leaf specification, every environment and every
    fuel `≥ 2`. -/
theorem selectImplOk_of_two_le (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hfuel : 2 ≤ fuel) : SelectImplOk leafSpec env fuel := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  intro dst sel src0 src1 rs0 sid heap0 h0 h1 oldDestV src0V src1V hInv hSInv hB _ hLk0 hLk1
  have e0 := hInv _ _ _ (rsTower_of_locatedLookup rs0 src0 src0V hLk0)
  have e1 := hInv _ _ _ (rsTower_of_locatedLookup rs0 src1 src1V hLk1)
  obtain ⟨d, t⟩ := dst
  obtain ⟨x0, t0⟩ := src0
  obtain ⟨x1, t1⟩ := src1
  simp only [Located.locDst] at h0 h1 src0V src1V oldDestV e0 e1
  subst h0 h1
  refine ⟨_, translateCmd_cmov_eval env sel d x0 x1 t1 sid n heap0 _ (hSInv sel), ?_, ?_, ?_⟩
  · erw [Heap.get_set_same]
    by_cases hz : rs0.rsScalar sel = 0
    · simp only [hz, BitVec.ofNat_eq_ofNat]
      exact e0
    · have hne : BitVec.ofNat 64 (rs0.rsScalar sel) ≠ 0 :=
        bitVec_ofNat_ne_zero _ hz (hB sel)
      simp only [hz, hne]
      exact e1
  · intro x t hx
    exact Heap.get_set_other _ _ _ _ (towerLoc_id_ne sid d x _ t (Ne.symm hx))
  · intro x
    exact Heap.get_set_other _ _ _ _ (wordLoc_id_ne_towerLoc_id sid x d _).symm

/-- `LeafImplOk` holds for `storeLeafSpec`, the empty environment and every fuel `≥ 2`. -/
theorem leafImplOk_storeLeafSpec (fuel : Nat) (hfuel : 2 ≤ fuel) :
    LeafImplOk storeLeafSpec emptyTransEnv fuel := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  intro f dest args rs0 sid heap0 oldDestV argList hInv hTower _ _
  exact ⟨heap0, translateCmd_ccall_emptyTransEnv_eval _ f args sid n heap0,
    hInv _ _ _ hTower, fun _ _ _ => rfl, fun _ => rfl⟩

/-- With the call oracle of `storeLeafSpec`, `callNUpdate` leaves the tower unchanged
    when every destination is bound at its type. -/
theorem callNUpdate_storeLeafSpec_rsTower (f : String) (argTs : List TowerType)
    (argList : List (Σ t, RustVal t)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState),
      (∀ d ∈ dests, ∃ v, rs.rsTower d.locVar = some ⟨d.locDst, v⟩) →
      (callNUpdate storeLeafSpec f argTs argList i dests rs).rsTower = rs.rsTower := by
  intro dests
  induction dests with
  | nil => intro _ _ _; rfl
  | cons d rest ih =>
    intro i rs hB
    obtain ⟨v, hv⟩ := hB d (List.mem_cons_self ..)
    have hLk : locatedLookup rs d = some v := by simp [locatedLookup, hv]
    have hUpd : (locatedUpdate rs d
        (storeLeafSpec.call (callNLeafName f i) d.locDst argTs
          ((locatedLookup rs d).getD default) argList)).rsTower = rs.rsTower := by
      funext y
      simp only [storeLeafSpec, hLk, Option.getD_some, locatedUpdate, rsSetTower]
      by_cases hy : y = d.locVar
      · subst hy; simp [hv]
      · simp [hy]
    simp only [callNUpdate]
    rw [ih (i + 1) _ (fun d' hd' => by rw [hUpd]; exact hB d' (List.mem_cons_of_mem d hd')), hUpd]

/-- `CallNImplOk` holds for `storeLeafSpec`, the empty environment and every fuel `≥ 2`. -/
theorem callNImplOk_storeLeafSpec (fuel : Nat) (hfuel : 2 ≤ fuel) :
    CallNImplOk storeLeafSpec emptyTransEnv fuel := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  intro f dests args rs0 sid heap0 hInv _ hDests
  refine ⟨heap0, translateCmd_ccall_emptyTransEnv_eval _ f args sid n heap0, ?_, fun _ => rfl⟩
  intro x t v hx
  rw [callNUpdate_storeLeafSpec_rsTower f _ _ dests 0 rs0 hDests] at hx
  exact hInv x t v hx

/-! ## Scope and heap effect of a call -/

/-- `SDistr.pure` is injective. -/
theorem sdistr_pure_inj {α : Type} (a b : α) (h : SDistr.pure a = SDistr.pure b) : a = b := by
  have := congrArg PMF.support h
  simp [SDistr.pure, PMF.support_pure] at this
  exact this

/-- A one-instruction `Ccall` command keeps the scope. -/
theorem translateCmd_ccall_newSid (env : TransEnv) (lvs : List LVal) (fn : FunName)
    (args : List PExpr) (sid : ScopeId) (fuel : Nat) :
    (translateCmd env [.Ccall .DoNotInline lvs fn args] sid fuel).newSid = sid := by
  cases fuel with
  | zero => simp only [translateCmd]
  | succ n => cases n <;> simp only [translateCmd, translateInstrR]

/-- The array a destination of storage size `n` holds after a call returning `results`:
    the first result when it is an array of size `n`, and `old` otherwise. -/
def callResultArr (n : Nat) (old : JArray n) : List TypedValue → JArray n
  | [] => old
  | ⟨.sarr m, v⟩ :: _ => if h : m = n then h ▸ v else old
  | _ :: _ => old

theorem callResultArr_cons (n : Nat) (old : JArray n) (r : TypedValue) (rest : List TypedValue) :
    callResultArr n old (r :: rest) = callResultArr n old [r] := by
  obtain ⟨ty, v⟩ := r
  cases ty <;> rfl

/-- The argument value a tower binding passes to a call. -/
def towerArgVal : (Σ t : TowerType, RustVal t) → TypedValue
  | ⟨t, v⟩ => ⟨.sarr t.storageBytes, v⟩

/-- Reading a list of tower variables returns their arrays and leaves the heap unchanged. -/
theorem translatePExprAll_locToPExpr_eval_eq (sid : ScopeId) (args : List Located)
    (heap : Heap) :
    (translatePExprAll sid (args.map locToPExpr)).eval heap =
      SDistr.pure (args.map (fun a : Located => (⟨.sarr a.locSrc.storageBytes,
        heap.get (towerLoc sid a.locVar a.locSrc)⟩ : TypedValue)), heap) := by
  induction args with
  | nil => simp [translatePExprAll, CatCrypt.Deep.eval_ret, SPComp.pure_def]
  | cons a rest ih =>
    simp only [List.map_cons, translatePExprAll, CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret,
      SPComp.bind_def, SPComp.pure_def, translatePExpr_locToPExpr_eval, SDistr.pure_bind, ih]

/-- With every argument bound at its type and `HeapInv`, the argument values a call
    reads from the heap are the tower bindings. -/
theorem argVals_eq (rs : RustState) (heap : Heap) (sid : ScopeId) (args : List Located)
    (hInv : HeapInv rs heap sid)
    (hArgs : ∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) :
    (args.filterMap (fun a => rs.rsTower a.locVar)).map towerArgVal =
      args.map (fun a : Located => (⟨.sarr a.locSrc.storageBytes,
        heap.get (towerLoc sid a.locVar a.locSrc)⟩ : TypedValue)) := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨v, hv⟩ := hArgs a (List.mem_cons_self ..)
    have hrest := ih (fun b hb => hArgs b (List.mem_cons_of_mem a hb))
    simp only [List.filterMap_cons, hv, List.map_cons, hrest, towerArgVal]
    rw [hInv _ _ _ hv]

/-- Writing a result list to one l-value writes its first element. -/
theorem translateWriteLVals_single_cons (sid : ScopeId) (lv : LVal) (r : TypedValue)
    (rest : List TypedValue) :
    translateWriteLVals sid [lv] (r :: rest) = translateWriteLVals sid [lv] [r] := by
  simp only [translateWriteLVals]

/-- Writing a one-element result list to one l-value is the single write. -/
theorem translateWriteLVals_single_eval (sid : ScopeId) (lv : LVal) (r : TypedValue) :
    (translateWriteLVals sid [lv] [r]).eval = (translateWriteLVal sid lv r).eval := by
  simp only [translateWriteLVals, CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret]
  exact SPComp.bind_pure _

/-- Writing the results of a call to the tower variable `loc` sets its location to
    `callResultArr` of the results and leaves every other location unchanged. -/
theorem translateWriteLVals_locToLVal_results (sid : ScopeId) (loc : Located)
    (results : List TypedValue) (heap : Heap) :
    ∃ heap1 : Heap,
      (translateWriteLVals sid [locToLVal loc] results).eval heap =
        SDistr.pure (⟨()⟩, heap1) ∧
      heap1.get (towerLoc sid loc.locVar loc.locSrc) =
        callResultArr _ (heap.get (towerLoc sid loc.locVar loc.locSrc)) results ∧
      ∀ ℓ : CatCrypt.Core.Location, ℓ.id ≠ (towerLoc sid loc.locVar loc.locSrc).id →
        heap1.get ℓ = heap.get ℓ := by
  have hret : ∀ c : RawCode (ULift Unit), c.eval = SPComp.pure ⟨()⟩ →
      c.eval heap = SDistr.pure (⟨()⟩, heap) := by
    intro c hc; rw [hc]; rfl
  cases results with
  | nil =>
    exact ⟨heap, hret _ (by simp [translateWriteLVals, CatCrypt.Deep.eval_ret]), rfl,
      fun _ _ => rfl⟩
  | cons r rest =>
    rw [translateWriteLVals_single_cons]
    obtain ⟨ty, v⟩ := r
    cases ty with
    | sarr m =>
      by_cases hm : m = loc.locSrc.storageBytes
      · subst hm
        refine ⟨_, translateWriteLVals_locToLVal_eval sid loc v heap, ?_, ?_⟩
        · erw [Heap.get_set_same]
          simp [callResultArr]
          rfl
        · intro ℓ hℓ
          exact Heap.get_set_other _ _ _ _ hℓ.symm
      · refine ⟨heap, hret _ ?_, ?_, fun _ _ => rfl⟩
        · simp [translateWriteLVals, translateWriteLVal, locToLVal, locToVar, towerToSType,
            writeVar, Ne.symm hm, CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret,
            SPComp.pure_bind]
        · simp [callResultArr, hm]
    | sbool =>
      exact ⟨heap, hret _ (by simp [translateWriteLVals, translateWriteLVal, locToLVal,
        locToVar, towerToSType, writeVar, CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret,
        SPComp.pure_bind]), rfl, fun _ _ => rfl⟩
    | sint =>
      exact ⟨heap, hret _ (by simp [translateWriteLVals, translateWriteLVal, locToLVal,
        locToVar, towerToSType, writeVar, CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret,
        SPComp.pure_bind]), rfl, fun _ _ => rfl⟩
    | sword ws =>
      exact ⟨heap, hret _ (by simp [translateWriteLVals, translateWriteLVal, locToLVal,
        locToVar, towerToSType, writeVar, CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret,
        SPComp.pure_bind]), rfl, fun _ _ => rfl⟩

/-- Writing a result list to the destinations of an N-output call encodes the state
    `callNUpdate` produces, when output `i` of the specification is `callResultArr` of the
    results from position `i` on, and leaves the scalar cells unchanged. -/
theorem translateWriteLVals_dests_callNUpdate (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t, RustVal t)) (R : List TypedValue)
    (sid : ScopeId)
    (hspec : ∀ i dt old, leafSpec.call (callNLeafName f i) dt argTs old argList =
      callResultArr _ old (R.drop i)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState) (heap : Heap),
      HeapInv rs heap sid →
      (∀ d ∈ dests, ∃ v, rs.rsTower d.locVar = some ⟨d.locDst, v⟩) →
      ∃ heap1 : Heap,
        (translateWriteLVals sid (dests.map locToLVal) (R.drop i)).eval heap =
          SDistr.pure (⟨()⟩, heap1) ∧
        HeapInv (callNUpdate leafSpec f argTs argList i dests rs) heap1 sid ∧
        ∀ x : String,
          heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
          heap.get (translateVar sid { vname := x, vtype := .sword .U64 }) := by
  intro dests
  induction dests with
  | nil =>
    intro i rs heap hInv _
    refine ⟨heap, ?_, hInv, fun _ => rfl⟩
    simp only [List.map_nil, translateWriteLVals, CatCrypt.Deep.eval_ret]
    rfl
  | cons d rest ih =>
    intro i rs heap hInv hB
    obtain ⟨v, hv⟩ := hB d (List.mem_cons_self ..)
    have hLk : locatedLookup rs d = some v := by simp [locatedLookup, hv]
    have hOld : heap.get (towerLoc sid d.locVar d.locSrc) = v := hInv _ _ _ hv
    have hBrest : ∀ (rs' : RustState) (w : RustVal d.locDst),
        rs' = locatedUpdate rs d w →
        ∀ d' ∈ rest, ∃ v', rs'.rsTower d'.locVar = some ⟨d'.locDst, v'⟩ := by
      intro rs' w hrs' d' hd'
      obtain ⟨v', hv'⟩ := hB d' (List.mem_cons_of_mem d hd')
      subst hrs'
      by_cases hx : d'.locVar = d.locVar
      · rw [hx] at hv'
        rw [hv] at hv'
        obtain ⟨ht, -⟩ := Sigma.mk.inj (Option.some.inj hv')
        refine ⟨cast (congrArg RustVal ht) w, ?_⟩
        simp only [locatedUpdate, rsSetTower, hx, BEq.rfl, if_true]
        exact congrArg some (Sigma.ext ht (cast_heq _ _).symm)
      · refine ⟨v', ?_⟩
        simp only [locatedUpdate, rsSetTower, beq_iff_eq, hx, if_false]
        exact hv'
    simp only [List.map_cons, callNUpdate, hLk, Option.getD_some, hspec]
    cases hR : R.drop i with
    | nil =>
      have hR1 : R.drop (i + 1) = [] := by rw [← List.tail_drop, hR]; rfl
      have hrs : locatedUpdate rs d (callResultArr _ v []) = rs := by
        cases rs with
        | mk tw sc =>
          simp only [locatedUpdate, rsSetTower, callResultArr, RustState.mk.injEq, and_true]
          funext y
          by_cases hy : y = d.locVar
          · subst hy; simpa using hv.symm
          · simp [hy]
      obtain ⟨heap1, hE, hI, hS⟩ := ih (i + 1) rs heap hInv
        (fun d' hd' => hB d' (List.mem_cons_of_mem d hd'))
      rw [hR1] at hE
      have hh : heap1 = heap := by
        have h0 : (translateWriteLVals sid (rest.map locToLVal) []).eval heap =
            SDistr.pure (⟨()⟩, heap) := by
          cases rest <;> simp [translateWriteLVals, CatCrypt.Deep.eval_ret, SPComp.pure_def]
        exact (Prod.mk.inj (sdistr_pure_inj _ _ (hE.symm.trans h0))).2
      subst hh
      refine ⟨heap1, ?_, ?_, fun _ => rfl⟩
      · simp [translateWriteLVals, CatCrypt.Deep.eval_ret, SPComp.pure_def]
      · rw [hrs]; exact hI
    | cons r R' =>
      have hR1 : R.drop (i + 1) = R' := by rw [← List.tail_drop, hR]; rfl
      obtain ⟨heapA, hEA, hDA, hFA⟩ := translateWriteLVals_locToLVal_results sid d [r] heap
      rw [translateWriteLVals_single_eval] at hEA
      have hInvA : HeapInv (locatedUpdate rs d (callResultArr _ v (r :: R'))) heapA sid := by
        intro x t w hx
        by_cases hxd : x = d.locVar
        · subst hxd
          simp only [locatedUpdate, rsSetTower, BEq.rfl, if_true] at hx
          obtain ⟨ht, hw⟩ := Sigma.mk.inj (Option.some.inj hx)
          subst ht
          simp at hw
          subst hw
          rw [callResultArr_cons, ← hOld]
          exact hDA
        · simp only [locatedUpdate, rsSetTower, beq_iff_eq, hxd, if_false] at hx
          rw [hFA _ (towerLoc_id_ne sid x d.locVar t _ hxd)]
          exact hInv x t w hx
      obtain ⟨heap1, hE, hI, hS⟩ := ih (i + 1) _ heapA hInvA (hBrest _ _ rfl)
      rw [hR1] at hE
      refine ⟨heap1, ?_, hI, ?_⟩
      · simp only [translateWriteLVals, CatCrypt.Deep.eval_bind, SPComp.bind_def, hEA,
          SDistr.pure_bind]
        exact hE
      · intro x
        rw [hS x]
        exact hFA _ (wordLoc_id_ne_towerLoc_id sid x d.locVar _)

/-! ## Environments of pure functions -/

/-- The environment whose function `f` returns `gf` of its argument values when
    `g f = some gf`, and which has no body for `f` when `g f = none`. -/
def pureLeafEnv (g : String → Option (List TypedValue → List TypedValue)) : TransEnv :=
  ⟨fun fn => (g fn.name).map fun gf => fun _ vs => .ret (gf vs)⟩

/-- The call specification of `pureLeafEnv g`: the destination receives
    `callResultArr` of `gf` applied to the argument values. -/
def pureCallSpec (g : String → Option (List TypedValue → List TypedValue)) : CallSpec :=
  fun f _ _ old argList =>
    match g f with
    | some gf => callResultArr _ old (gf (argList.map towerArgVal))
    | none => old

/-- A call to `f` in `pureLeafEnv g` at fuel `n + 2` evaluates to the heap its result
    write produces, and leaves the heap unchanged when `g f = none`. -/
theorem translateCmd_ccall_pureLeafEnv_eval
    (g : String → Option (List TypedValue → List TypedValue))
    (lvs : List LVal) (f : String) (args : List Located) (sid : ScopeId) (n : Nat)
    (heap heap1 : Heap)
    (hW : ∀ gf, g f = some gf →
      (translateWriteLVals sid lvs (gf (args.map (fun a : Located =>
        (⟨.sarr a.locSrc.storageBytes, heap.get (towerLoc sid a.locVar a.locSrc)⟩ :
          TypedValue))))).eval heap = SDistr.pure (⟨()⟩, heap1))
    (hN : g f = none → heap1 = heap) :
    (translateCmd (pureLeafEnv g)
        [.Ccall .DoNotInline lvs { name := f } (args.map locToPExpr)]
        sid (n + 2)).code.eval heap = SDistr.pure (⟨()⟩, heap1) := by
  simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def,
    translatePExprAll_locToPExpr_eval_eq, SDistr.pure_bind, pureLeafEnv]
  cases hg : g f with
  | none =>
    rw [hN hg]
    simp [CatCrypt.Deep.eval_ret, SPComp.pure_def, SDistr.pure_bind]
  | some gf =>
    simp only [Option.map_some, CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret, SPComp.bind_def,
      SPComp.pure_def, SDistr.pure_bind, hW gf hg]

/-- `LeafImplOk` holds for `pureLeafEnv g` with call specification `pureCallSpec g`,
    every limb-store specification and every fuel `≥ 2`. -/
theorem leafImplOk_pureLeafEnv (g : String → Option (List TypedValue → List TypedValue))
    (limbStore : LimbStoreSpec) (fuel : Nat) (hfuel : 2 ≤ fuel) :
    LeafImplOk { call := pureCallSpec g, limbStore := limbStore } (pureLeafEnv g) fuel := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  intro f dest args rs0 sid heap0 oldDestV argList hInv hTower hArgList hArgsT
  have hOld : heap0.get (towerLoc sid dest.locVar dest.locSrc) = oldDestV := hInv _ _ _ hTower
  have hVals := argVals_eq rs0 heap0 sid args hInv hArgsT
  cases hg : g f with
  | none =>
    refine ⟨heap0, translateCmd_ccall_pureLeafEnv_eval g _ f args sid n heap0 heap0
      (fun gf h => by simp [hg] at h) (fun _ => rfl), ?_, fun _ _ _ => rfl, fun _ => rfl⟩
    simp only [pureCallSpec, hg]
    exact hOld
  | some gf =>
    obtain ⟨heap1, hE, hD, hF⟩ := translateWriteLVals_locToLVal_results sid dest
      (gf (args.map (fun a : Located => (⟨.sarr a.locSrc.storageBytes,
        heap0.get (towerLoc sid a.locVar a.locSrc)⟩ : TypedValue)))) heap0
    refine ⟨heap1, translateCmd_ccall_pureLeafEnv_eval g _ f args sid n heap0 heap1
      (fun gf' h => by rw [hg] at h; cases h; exact hE) (fun h => by simp [hg] at h),
      ?_, ?_, ?_⟩
    · simp only [pureCallSpec, hg]
      rw [hD, hOld, hArgList, hVals]
    · intro x t hx
      exact hF _ (towerLoc_id_ne sid x dest.locVar t _ hx)
    · intro x
      exact hF _ (wordLoc_id_ne_towerLoc_id sid x dest.locVar _)

/-- `LeafImplOk` at a fuel implies `LeafImplOkNewSid` at that fuel: a call keeps the
    scope, and the leaf hypothesis frames the other tower and scalar cells. -/
theorem leafImplOkNewSid_of_leafImplOk (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (h : LeafImplOk leafSpec env fuel) : LeafImplOkNewSid leafSpec env fuel := by
  intro f dest args rs0 sid heap0 oldDestV argList hInv hSInv hTower hArgList hArgsT hB
  simp only [translateCmd_ccall_newSid]
  obtain ⟨heap1, hEval, hDest, hOther, hScalar⟩ :=
    h f dest args rs0 sid heap0 oldDestV argList hInv hTower hArgList hArgsT
  refine ⟨heap1, hEval, ?_, ?_, fun x => hB x⟩
  · intro x t v hx
    by_cases hxd : x = dest.locVar
    · subst hxd
      simp only [locatedUpdate, rsSetTower, BEq.rfl, if_true] at hx
      obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hx)
      subst ht
      simp at hv
      subst hv
      exact hDest
    · simp only [locatedUpdate, rsSetTower, beq_iff_eq, hxd, if_false] at hx
      rw [hOther x t hxd]
      exact hInv x t v hx
  · intro x
    rw [hScalar x, hSInv x]
    rfl

/-- `CallNImplOk` holds for `pureLeafEnv g` at every fuel `≥ 2` for every leaf
    specification whose output `i` of `f` is the result of `g f` at position `i`. -/
theorem callNImplOk_pureLeafEnv (leafSpec : LeafSpec)
    (g : String → Option (List TypedValue → List TypedValue)) (fuel : Nat) (hfuel : 2 ≤ fuel)
    (hspec : ∀ f i dt argTs old argList,
      leafSpec.call (callNLeafName f i) dt argTs old argList =
        match g f with
        | some gf => callResultArr _ old ((gf (argList.map towerArgVal)).drop i)
        | none => old) :
    CallNImplOk leafSpec (pureLeafEnv g) fuel := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  intro f dests args rs0 sid heap0 hInv hArgs hDests
  have hVals := argVals_eq rs0 heap0 sid args hInv hArgs
  cases hg : g f with
  | none =>
    obtain ⟨heap1, hE, hI, hS⟩ := translateWriteLVals_dests_callNUpdate leafSpec f
      (args.map (·.locDst)) (args.filterMap (fun a => rs0.rsTower a.locVar)) [] sid
      (fun i dt old => by rw [hspec, hg]; simp [callResultArr]) dests 0 rs0 heap0 hInv hDests
    have hh : heap1 = heap0 := by
      have h0 : (translateWriteLVals sid (dests.map locToLVal) ([] : List TypedValue)).eval
          heap0 = SDistr.pure (⟨()⟩, heap0) := by
        cases dests <;> simp [translateWriteLVals, CatCrypt.Deep.eval_ret, SPComp.pure_def]
      exact (Prod.mk.inj (sdistr_pure_inj _ _ (hE.symm.trans h0))).2
    subst hh
    exact ⟨heap1, translateCmd_ccall_pureLeafEnv_eval g _ f args sid n heap1 heap1
      (fun gf h => by simp [hg] at h) (fun _ => rfl), hI, hS⟩
  | some gf =>
    obtain ⟨heap1, hE, hI, hS⟩ := translateWriteLVals_dests_callNUpdate leafSpec f
      (args.map (·.locDst)) (args.filterMap (fun a => rs0.rsTower a.locVar))
      (gf ((args.filterMap (fun a => rs0.rsTower a.locVar)).map towerArgVal)) sid
      (fun i dt old => by rw [hspec, hg]) dests 0 rs0 heap0 hInv hDests
    refine ⟨heap1, translateCmd_ccall_pureLeafEnv_eval g _ f args sid n heap0 heap1
      (fun gf' h => by rw [hg] at h; cases h; rw [← hVals]; simpa using hE)
      (fun h => by simp [hg] at h), hI, hS⟩

/-! ## Bytewise addition -/

/-- Bytewise addition of two arrays of equal size, as a one-element result list. -/
def addArrays : List TypedValue → List TypedValue
  | [⟨.sarr n, a⟩, ⟨.sarr m, b⟩] =>
    if h : m = n then [⟨.sarr n, fun i => (a : JArray n) i + (h ▸ (b : JArray m)) i⟩] else []
  | _ => []

theorem addArrays_length_le (l : List TypedValue) : (addArrays l).length ≤ 1 := by
  unfold addArrays
  split
  · split <;> simp
  · simp

/-- The function table with the single function `add`, returning `addArrays`. -/
def addLeafTable : String → Option (List TypedValue → List TypedValue) :=
  fun f => if f = "add" then some addArrays else none

/-- The leaf specification of `addLeafTable`: `add` is bytewise addition, and a limb
    store writes the 64-bit word little-endian at byte offset `8 * idx`. -/
def addLeafSpec : LeafSpec :=
  { call := pureCallSpec addLeafTable,
    limbStore := fun _ oldV idx v => JArray.setWord oldV .U64 (idx * 8) v }

/-- A call of `add` on two arrays of the destination's type writes their bytewise sum. -/
theorem addLeafSpec_call_add (t : TowerType) (old a b : RustVal t) :
    addLeafSpec.call "add" t [t, t] old [⟨t, a⟩, ⟨t, b⟩] = fun i => a i + b i := by
  simp [addLeafSpec, pureCallSpec, addLeafTable, addArrays, towerArgVal, callResultArr]
  rfl

/-- `LeafImplOkNewSid` holds for `addLeafSpec` and `pureLeafEnv addLeafTable` at every
    fuel `≥ 2`. -/
theorem leafImplOkNewSid_addLeafSpec (fuel : Nat) (hfuel : 2 ≤ fuel) :
    LeafImplOkNewSid addLeafSpec (pureLeafEnv addLeafTable) fuel :=
  leafImplOkNewSid_of_leafImplOk _ _ _ (leafImplOk_pureLeafEnv _ _ fuel hfuel)

/-- `callNLeafName f i` names output `0` of `add` only for `f = "add"` and `i = 0`. -/
theorem callNLeafName_eq_add_zero (f : String) (i : Nat)
    (h : callNLeafName f i = callNLeafName "add" 0) : f = "add" ∧ i = 0 := by
  have hl := congrArg String.toList h
  simp only [callNLeafName, String.toList_append] at hl
  simp only [List.append_assoc, List.append_cancel_left_eq] at hl
  have h0 : "add".toList ++ ("#".toList ++ (toString (0 : Nat)).toList) =
      ['a', 'd', 'd', '#', '0'] := by
    simp
  rw [h0] at hl
  have hh : "#".toList = ['#'] := by decide
  rw [hh] at hl
  generalize hfl : f.toList = fl at hl
  generalize hsl : (toString i).toList = sl at hl
  match fl, hl with
  | [], hl => simp at hl
  | [_], hl => simp at hl
  | [_, _], hl => simp at hl
  | [a, b, c], hl =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hl
    obtain ⟨rfl, rfl, rfl, -, rfl⟩ := hl
    refine ⟨?_, ?_⟩
    · rw [← String.ofList_toList (s := f), hfl]
    · apply Nat.repr_injective
      exact String.toList_injective (hsl.trans (by simp))
  | [_, _, _, _], hl => simp at hl
  | _ :: _ :: _ :: _ :: _ :: _, hl =>
    simp only [List.cons_append, List.cons.injEq] at hl
    obtain ⟨-, -, -, -, -, hl⟩ := hl
    simp at hl

/-- The N-output leaf specification of `addLeafTable`: output `0` of `add` is bytewise
    addition, and every other output keeps its destination. -/
def addCallNLeafSpec : LeafSpec :=
  { call := fun name _ _ old argList =>
      if name = callNLeafName "add" 0 then
        callResultArr _ old (addArrays (argList.map towerArgVal))
      else old,
    limbStore := fun _ oldV idx v => JArray.setWord oldV .U64 (idx * 8) v }

/-- Output `0` of a call of `add` on two arrays of the destination's type is their
    bytewise sum. -/
theorem addCallNLeafSpec_call_add (t : TowerType) (old a b : RustVal t) :
    addCallNLeafSpec.call (callNLeafName "add" 0) t [t, t] old [⟨t, a⟩, ⟨t, b⟩] =
      fun i => a i + b i := by
  simp [addCallNLeafSpec, addArrays, towerArgVal, callResultArr]
  rfl

/-- `CallNImplOk` holds for `addCallNLeafSpec` and `pureLeafEnv addLeafTable` at every
    fuel `≥ 2`. -/
theorem callNImplOk_addCallNLeafSpec (fuel : Nat) (hfuel : 2 ≤ fuel) :
    CallNImplOk addCallNLeafSpec (pureLeafEnv addLeafTable) fuel := by
  refine callNImplOk_pureLeafEnv _ _ fuel hfuel ?_
  intro f i dt argTs old argList
  by_cases hname : callNLeafName f i = callNLeafName "add" 0
  · obtain ⟨rfl, rfl⟩ := callNLeafName_eq_add_zero f i hname
    simp [addCallNLeafSpec, addLeafTable]
  · simp only [addCallNLeafSpec, hname, if_false, addLeafTable]
    by_cases hf : f = "add"
    · subst hf
      have hi : i ≠ 0 := fun h => hname (by rw [h])
      have hlen := addArrays_length_le (argList.map towerArgVal)
      simp only [if_true]
      rw [List.drop_eq_nil_of_le (by omega)]
      rfl
    · rw [if_neg hf]

/-! ## A program with one call of `add` -/

/-- The state binding `x`, `y` and `z` at `TFp`, with every scalar `0`. -/
def addProgState (x y z : RustVal .TFp) : RustState where
  rsTower := fun n =>
    if n = "x" then some ⟨.TFp, x⟩ else if n = "y" then some ⟨.TFp, y⟩
    else if n = "z" then some ⟨.TFp, z⟩ else none
  rsScalar := fun _ => 0

/-- `k := 1; z := add(x, y)`. -/
def addCallProg : LowCT :=
  .RSeq (.RScalarSet "k" 1) (.RCall "add" (mkFpLoc "z") [mkFpLoc "x", mkFpLoc "y"])

/-- `addCallProg` runs from `addProgState x y z` to the state with `k = 1` and
    `z` bound to the bytewise sum of `x` and `y`. -/
theorem addCallProg_exec (N : Nat) (x y z : RustVal .TFp) :
    RustExec N addLeafSpec addCallProg (addProgState x y z)
      (locatedUpdate (rsSetScalar (addProgState x y z) "k" 1) (mkFpLoc "z")
        (fun i => x i + y i)) := by
  refine RustExec.seq _ _ _ _ _ (RustExec.scalarSet _ _ _) ?_
  have h := RustExec.call (N := N) (leafSpec := addLeafSpec) "add" (mkFpLoc "z")
    [mkFpLoc "x", mkFpLoc "y"] (rsSetScalar (addProgState x y z) "k" 1) z
    [⟨.TFp, x⟩, ⟨.TFp, y⟩]
    (by simp [locatedLookup, rsSetScalar, addProgState, mkFpLoc])
    (by simp [rsSetScalar, addProgState, mkFpLoc])
    (by intro a ha; simp [mkFpLoc] at ha; rcases ha with rfl | rfl <;>
          simp [rsSetScalar, addProgState])
  simpa [mkFpLoc, addLeafSpec_call_add] using h

/-- The translation of `addCallProg` in `pureLeafEnv addLeafTable`, run at scope `1` and
    fuel `4` from a heap encoding `addProgState x y z`, ends in a heap encoding the state
    where `z` holds the bytewise sum of `x` and `y`, at scope `1`. -/
theorem addProg_simulates (N : Nat) (x y z : RustVal .TFp) (heap : Heap)
    (hInv : HeapInv (addProgState x y z) heap 1)
    (hSInv : ScalarInv (addProgState x y z) heap 1) :
    ∃ heap' : Heap,
      (translateCmd (pureLeafEnv addLeafTable) (toJasminCmd addCallProg) 1 4).code.eval heap =
        SDistr.pure (⟨()⟩, heap') ∧
      HeapInv (locatedUpdate (rsSetScalar (addProgState x y z) "k" 1) (mkFpLoc "z")
        (fun i => x i + y i)) heap' 1 ∧
      ScalarInv (locatedUpdate (rsSetScalar (addProgState x y z) "k" 1) (mkFpLoc "z")
        (fun i => x i + y i)) heap' 1 := by
  have hNS : (translateCmd (pureLeafEnv addLeafTable) (toJasminCmd addCallProg) 1 4).newSid =
      1 := by
    simp only [addCallProg, toJasminCmd_RSeq, translateCmd_append_newSid]
    rw [callFree_toJasmin_newSid (.RScalarSet "k" 1) (by simp [callFree])]
    simp only [toJasminCmd_RCall]
    exact translateCmd_ccall_newSid _ _ _ _ _ _
  obtain ⟨heap', hE, hI, hS, -⟩ :=
    rustExecSimulates_withCalls N addLeafSpec (pureLeafEnv addLeafTable) 4
      leafImplOkNewSid_addLeafSpec
      (fun f h => limbStoreImplOk_storeLeafSpec _ f h) (fun f h => cloneImplOk_of_two_le _ f h)
      addCallProg _ _ (by rfl) (by rfl) (by decide) (by simp [jasminFuel, addCallProg])
      (addCallProg_exec N x y z) ⟨trivial, fun _ _ => trivial⟩ 1 heap hInv hSInv
      (fun _ => by simp [addProgState]) ⟨trivial, fun _ _ => trivial⟩
  rw [hNS] at hI hS
  exact ⟨heap', hE, hI, hS⟩

end CatCrypt.Crypto.Jasmin.LowCT
