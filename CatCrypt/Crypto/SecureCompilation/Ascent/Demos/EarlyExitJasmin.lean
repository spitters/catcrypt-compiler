/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.EarlyExitLowCT
public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree

/-!
# Demo: the search loop with an early return, compiled to a jasmin `Com`

`searchLowCT x` (`Ascent/Demos/EarlyExitLowCT.lean`) is the lowered search function
of hax-lean's `searchU x`. `searchUnrolled x` is the function with its loop
unrolled three times (`GuardedUnroll.unrollAll`). The guarded translator compiles
it to `catCryptDialect`, and `cryptoDialectToJasminCom` lowers the result to a
jasmin `Com`. The statements below are about the denotation of that `Com`; they
say nothing about emitted assembly or bytes.

For `x = 1` and `x = 5`: the search function runs within three loop trips, the
unrolled function lies in the guarded fragment, and the jasmin program returning
the result slot denotes `1`, respectively `100`. The value is the one
`searchLowCT_one` and `searchLowCT_five` give for the `RustExec` run of
`searchLowCT`, carried to the unrolled function by determinism of `RustExec` and
`runK_unrollAll`, then to the jasmin program by
`GuardedAgree.translateDialectGuarded_jasmin`. The function reads no input, so the
jasmin program is closed.

The side conditions of that theorem at the two inputs are closed by sound Boolean
checks: `coveredGuardedB`, `readsB` and the result-slot membership by `simp`, and
the existence of the three-trip run (`runKL`) and the in-range check
(`inRangeRunBL`) by kernel evaluation over an association-list store. Each of the
four kernel evaluations is a fixed closed term whose kernel check takes under two
seconds; they are proof obligations of `searchJasmin_one` and `searchJasmin_five`
and change only when `searchLowCT`, `unrollAll` or the interpreters change.

## Main results

* `searchUnrolled`: the search function with its loop unrolled three times
* `searchJasmin_of_run`: the denotation of the compiled jasmin program at an input,
  from the run and the Boolean checks
* `searchJasmin_one`, `searchJasmin_five`: the compiled jasmin program denotes `1`
  at `x = 1` and `100` at `x = 5`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (Ctx CVar)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedUnroll
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree

/-- The search function with every loop unrolled three times. -/
def searchUnrolled (x : Nat) : LowCT := unrollAll 3 (searchLowCT x)

theorem searchLowCT_isScalarCmd (x : Nat) : IsScalarCmd (searchLowCT x) :=
  isScalarCmd_of_isScalarCmdB _ rfl

theorem searchUnrolled_isScalarCmd (x : Nat) : IsScalarCmd (searchUnrolled x) :=
  isScalarCmd_of_isScalarCmdB _ rfl

/-- The denotation of the compiled jasmin program at an input `x`: from a
    three-trip run of the search function over the empty store, a value `v` of the
    result slot in every `RustExec` run from the default state, and the Boolean
    checks of the fragment, scoping and range conditions on the unrolled function,
    the compiled jasmin program returning the result slot denotes `v`. -/
theorem searchJasmin_of_run (N : Nat) (leafSpec : LeafSpec) (x v : Nat)
    (l : List (String × Nat))
    (hrunL : runKL 3 (searchLowCT x) [] = some l)
    (hres : ∀ rs', RustExec N leafSpec (searchLowCT x) default rs' →
      rs'.rsScalar exitResName = v)
    (hcov : coveredGuardedB (searchUnrolled x) = true)
    (hreads : readsB [] (searchUnrolled x) = true)
    (hIRL : inRangeRunBL 3 (searchUnrolled x) [] = true)
    (hname : exitResName ∈ afterL [] (searchUnrolled x)) :
    ∃ (o : DTransOut ([] : Ctx)) (w : CVar o.Γ' (.sword 64))
      (com : Com catCryptDialect ([] : Ctx) (.sword 64))
      (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64))),
      translateDialectGuarded VarMap.empty (searchUnrolled x) = some o ∧
      o.vm.lookup exitResName = some ⟨.sword 64, w⟩ ∧
      o.cont (Com.ret (toVIRVar w)) = some com ∧
      cryptoDialectToJasminCom com = some jcom ∧
      jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 v) := by
  have hrun : runK 3 (searchLowCT x) default = some (storeState (fun _ => none) l) := by
    rw [default_eq_storeState, runK_storeState, hrunL]; rfl
  have hIR : inRangeRunB 3 (searchUnrolled x) default = true := by
    rw [default_eq_storeState, inRangeRunB_storeState]; exact hIRL
  set s := storeState (fun _ => none) l
  have hv := hres s (runK_rustExec 3 _ _ _ hrun)
  have hexecU : RustExec N leafSpec (searchUnrolled x) default s :=
    runK_unrollAll 3 _ _ _ hrun
  have h := translateDialectGuarded_jasmin (isCoveredSCtlGuarded_of_coveredGuardedB _ hcov)
    hexecU (fun _ => by show (0 : Nat) < 2 ^ 64; norm_num)
    (readsB_sound _ [] _ (fun _ h => by cases h) hreads)
    (inRangeRunB_sound 3 _ _ (searchUnrolled_isScalarCmd x) hIR) exitResName
    (afterL_sound _ [] _ (fun _ h => by cases h) _ hname)
  rw [hv] at h
  exact h

/-! ## The input `x = 1` -/

/-- At `x = 1` the unrolled search function lies in the guarded fragment. -/
theorem searchUnrolled_one_covered : coveredGuardedB (searchUnrolled 1) = true := by
  simp [coveredGuardedB, searchUnrolled, unrollAll, unrollNz, searchLowCT, searchLoopBody,
    exitFunction, exitLoop, exitGuard, exitRunName, exitRetName, exitValName, exitResName,
    srcNameB, ltCleanSrcB, _root_.Hax.IntWidth.modulus, _root_.Hax.IntWidth.bits]

theorem searchUnrolled_one_reads : readsB [] (searchUnrolled 1) = true := by
  simp [readsB, afterL, varsInL, searchUnrolled, unrollAll, unrollNz, searchLowCT,
    searchLoopBody, exitFunction, exitLoop, exitGuard, exitRunName, exitRetName, exitValName,
    exitResName]

theorem searchUnrolled_one_res : exitResName ∈ afterL [] (searchUnrolled 1) := by
  simp [afterL, searchUnrolled, unrollAll, unrollNz, searchLowCT, searchLoopBody, exitFunction,
    exitLoop, exitGuard, exitRunName, exitRetName, exitValName, exitResName]

/-- The search function at `x = 1` runs within three loop trips. -/
theorem searchLowCT_one_run : (runKL 3 (searchLowCT 1) []).isSome = true := by
  decide +kernel

/-- Every expression of the unrolled search function at `x = 1` stays in range. -/
theorem searchUnrolled_one_inRange : inRangeRunBL 3 (searchUnrolled 1) [] = true := by
  decide +kernel

/-- At `x = 1` the jasmin program compiled from the unrolled search function by the
    guarded translator and returning the result slot denotes `1`. -/
theorem searchJasmin_one (N : Nat) (leafSpec : LeafSpec) :
    ∃ (o : DTransOut ([] : Ctx)) (w : CVar o.Γ' (.sword 64))
      (com : Com catCryptDialect ([] : Ctx) (.sword 64))
      (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64))),
      translateDialectGuarded VarMap.empty (searchUnrolled 1) = some o ∧
      o.vm.lookup exitResName = some ⟨.sword 64, w⟩ ∧
      o.cont (Com.ret (toVIRVar w)) = some com ∧
      cryptoDialectToJasminCom com = some jcom ∧
      jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 1) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp searchLowCT_one_run
  refine searchJasmin_of_run N leafSpec 1 1 s hs (fun rs' h => ?_) searchUnrolled_one_covered
    searchUnrolled_one_reads searchUnrolled_one_inRange searchUnrolled_one_res
  obtain ⟨r, hr, hv⟩ := searchLowCT_one N leafSpec default
  rw [← rustExec_deterministic hr (searchLowCT_isScalarCmd 1) h]
  exact hv

/-! ## The input `x = 5` -/

/-- At `x = 5` the unrolled search function lies in the guarded fragment. -/
theorem searchUnrolled_five_covered : coveredGuardedB (searchUnrolled 5) = true := by
  simp [coveredGuardedB, searchUnrolled, unrollAll, unrollNz, searchLowCT, searchLoopBody,
    exitFunction, exitLoop, exitGuard, exitRunName, exitRetName, exitValName, exitResName,
    srcNameB, ltCleanSrcB, _root_.Hax.IntWidth.modulus, _root_.Hax.IntWidth.bits]

theorem searchUnrolled_five_reads : readsB [] (searchUnrolled 5) = true := by
  simp [readsB, afterL, varsInL, searchUnrolled, unrollAll, unrollNz, searchLowCT,
    searchLoopBody, exitFunction, exitLoop, exitGuard, exitRunName, exitRetName, exitValName,
    exitResName]

theorem searchUnrolled_five_res : exitResName ∈ afterL [] (searchUnrolled 5) := by
  simp [afterL, searchUnrolled, unrollAll, unrollNz, searchLowCT, searchLoopBody, exitFunction,
    exitLoop, exitGuard, exitRunName, exitRetName, exitValName, exitResName]

/-- The search function at `x = 5` runs within three loop trips. -/
theorem searchLowCT_five_run : (runKL 3 (searchLowCT 5) []).isSome = true := by
  decide +kernel

/-- Every expression of the unrolled search function at `x = 5` stays in range. -/
theorem searchUnrolled_five_inRange : inRangeRunBL 3 (searchUnrolled 5) [] = true := by
  decide +kernel

/-- At `x = 5` the jasmin program compiled from the unrolled search function by the
    guarded translator and returning the result slot denotes `100`. -/
theorem searchJasmin_five (N : Nat) (leafSpec : LeafSpec) :
    ∃ (o : DTransOut ([] : Ctx)) (w : CVar o.Γ' (.sword 64))
      (com : Com catCryptDialect ([] : Ctx) (.sword 64))
      (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64))),
      translateDialectGuarded VarMap.empty (searchUnrolled 5) = some o ∧
      o.vm.lookup exitResName = some ⟨.sword 64, w⟩ ∧
      o.cont (Com.ret (toVIRVar w)) = some com ∧
      cryptoDialectToJasminCom com = some jcom ∧
      jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 100) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp searchLowCT_five_run
  refine searchJasmin_of_run N leafSpec 5 100 s hs (fun rs' h => ?_) searchUnrolled_five_covered
    searchUnrolled_five_reads searchUnrolled_five_inRange searchUnrolled_five_res
  obtain ⟨r, hr, hv⟩ := searchLowCT_five N leafSpec default
  rw [← rustExec_deterministic hr (searchLowCT_isScalarCmd 5) h]
  exact hv

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
