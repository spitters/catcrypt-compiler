/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTToJasmin

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
`CMOV` and `CLONE_TOWER` with no condition on the leaf specification. `LeafImplOk`
and `CallNImplOk` hold for the empty environment with a call oracle that returns
the old destination value; the `Ccall` translation discards its result
l-values, so a call changes no destination.

## Contents

* `not_forall_leafImplOk`, `not_forall_leafImplOkNewSid`, `not_forall_callNImplOk`,
  `not_forall_limbStoreImplOk`, `not_forall_selectImplOk`,
  `not_forall_cloneImplOk` — the all-fuel forms are false.
* `storeLeafSpec`, `emptyTransEnv` — the leaf specification and environment of the
  witnesses.
* `limbStoreImplOk_storeLeafSpec`, `selectImplOk_of_two_le`, `cloneImplOk_of_two_le`,
  `leafImplOk_storeLeafSpec`, `callNImplOk_storeLeafSpec` — the hypotheses at every
  fuel `≥ 2`.
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
    h 0 "f" (mkFpLoc "x") [] rs0 1 default _ [] hInv hx rfl
  exact translateCmd_zero_eval_ne_pure _ _ _ _ _ hEval

/-- `LeafImplOkNewSid` holds at no family of fuels containing `0`. -/
theorem not_forall_leafImplOkNewSid (leafSpec : LeafSpec) (env : TransEnv) :
    ¬ ∀ fuel', LeafImplOkNewSid leafSpec env fuel' := by
  intro h
  obtain ⟨rs0, hInv, hSInv, hB, hx⟩ := exists_state_encoded default
  obtain ⟨heap1, hEval, -⟩ :=
    h 0 "f" (mkFpLoc "x") [] rs0 1 default _ [] hInv hSInv hx rfl hB
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

/-- The leaf specification of the witnesses: a call returns the old destination value,
    and a limb store writes the 64-bit word little-endian at byte offset `8 * idx`. -/
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
  intro f dest args rs0 sid heap0 oldDestV argList hInv hTower _
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

end CatCrypt.Crypto.Jasmin.LowCT
