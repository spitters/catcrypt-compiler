/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.EarlyExit
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Exit

/-!
# Demo: the search loop with an early return, lowered to `LowCT` and run

The source is hax-lean's `searchU x` (`Ascent/Demos/EarlyExit.lean`): the loop
index runs over `0, 1, 2`, the first index at or above `x` is returned from inside
the loop, and without one the program falls through to `100`.  `Hax.pipeline`
rewrites it into a `whileFoldReturn` with a `cfBreak` (`searchU_pipeline`); at
`x = 1` the pipeline output is `searchLoopShape`.

This module lowers the pipeline output with the exit-flag lowering
`haxToLowCTFn` (`Hax/HaxToLowCTExit.lean`) and runs the lowered command:

* `searchLowCT x` is the lowered command: the function frame `exitFunction`
  around the literal bindings, the comparison `c := i < three`, the loop
  `exitLoop` over `searchLoopBody`, and the fall-through store of `100` under the
  exit guard.  The comparison `le xv i` lowers to `1 - (i < xv)`.
* The reference runs are stated over `Hax.denote'` with the builtin table
  `noOverflow64 widthScalarOps`, the table `haxToLowCTFn_simulates` takes: hax-lean's
  width-aware comparison and arithmetic tables with the overflowing `u64`
  operations refused.  The additions the loop performs (`i + 1` for `i ≤ 2`) stay
  in range, so the refusal never fires.
* The `RustExec` runs follow from `haxToLowCTFn_simulates`: from any entry state
  the lowered command terminates with the returned word in the result slot
  `exitResName`, `x` when `x < 3` and `100` when `3 ≤ x < 2^64`.

## Main results

* `searchLowCT`, `searchU_lowers`: `haxToLowCTFn` lowers the pipeline output of
  `searchU x` to `searchLowCT x`
* `searchU_exitSimOk`: the pipeline output lies in the simulated fragment
* `searchU_denote'_found`, `searchU_denote'_notFound`: the reference runs over
  `noOverflow64 widthScalarOps`
* `searchLowCT_found`, `searchLowCT_notFound`: the `RustExec` run of the lowered
  command leaves `x`, respectively `100`, in `exitResName`
* `searchLowCT_one`, `searchLowCT_five`: the demo inputs `x = 1` and `x = 5`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## The pipeline output and its lowering -/

/-- The pipeline output of `searchU 1` is `searchLoopShape`. -/
theorem pipeline_searchU_one : _root_.Hax.pipeline (searchU 1) = searchLoopShape :=
  searchU_pipeline 1

/-- The lowered body of the search loop: `e := 1 - (i < xv)`; when `e` is nonzero
    store `i` into `exitValName` and set the exit flag; under the exit guard,
    `i := i + one` and `c := i < three`. -/
def searchLoopBody : LowCT :=
  .RSeq (.RScalarSetExpr "e" (.SSub (.SLit 1) (.SLt (.SVar "i") (.SVar "xv"))))
    (.RSeq
      (.RIfNz "e"
        (.RSeq (.RScalarSetExpr exitValName (.SVar "i")) (.RScalarSet exitRetName 1))
        .RSkip)
      (exitGuard
        (.RSeq
          (.RSeq (.RSeq (.RScalarSetExpr "i" (.SAdd (.SVar "i") (.SVar "one"))) .RSkip) .RSkip)
          (.RSeq (.RSeq (.RScalarSetExpr "c" (.SLt (.SVar "i") (.SVar "three"))) .RSkip)
            .RSkip))))

/-- The lowered search function at input `x`. -/
def searchLowCT (x : Nat) : LowCT :=
  exitFunction
    (.RLetU64Zero "three" (.RSeq (.RScalarSet "three" 3)
     (.RLetU64Zero "one" (.RSeq (.RScalarSet "one" 1)
      (.RLetU64Zero "xv" (.RSeq (.RScalarSet "xv" (x % _root_.Hax.IntWidth.w64.modulus))
       (.RLetU64Zero "i" (.RSeq (.RScalarSet "i" 0)
        (.RSeq (.RScalarSetExpr "c" (.SLt (.SVar "i") (.SVar "three")))
         (.RSeq (exitLoop (exitRunName none) "c" searchLoopBody)
           (exitGuard (.RScalarSet exitResName 100))))))))))))

/-- `haxToLowCTFn` lowers the pipeline output of `searchU x` to `searchLowCT x`. -/
theorem searchU_lowers (x : Nat) :
    haxToLowCTFn (_root_.Hax.pipeline (searchU x)) = some (searchLowCT x) := by
  rw [searchU_pipeline]
  simp [haxToLowCTFn, haxToLowCTK, letHeadK, letHead, scalarOpExpr, exitStore, resultStore,
    storeScalar, haxToLowCT, searchLowCT, searchLoopBody, _root_.Hax.IntWidth.modulus,
    _root_.Hax.IntWidth.bits]

/-- The pipeline output of `searchU x` lies in the fragment `exitSimOk` at tail
    position, outside every loop. -/
theorem searchU_exitSimOk (x : Nat) :
    exitSimOk true false (_root_.Hax.pipeline (searchU x)) = true := by
  rw [searchU_pipeline]; rfl

/-! ## The reference runs over the no-overflow table -/

/-- For `x < 3` the reference run of the pipeline output returns early with the
    index `x`. -/
theorem searchU_denote'_found (x : Nat) (hx : x < 3) :
    ((_root_.Hax.denote' (noOverflow64 widthScalarOps) 8 (_root_.Hax.pipeline (searchU x))).run
      _root_.Hax.Env.empty).1 = .val (.controlFlow true (.uint .w64 x)) := by
  rw [searchU_pipeline]
  interval_cases x <;>
  simp [_root_.Hax.denote', _root_.Hax.denoteWhile'Return, _root_.Hax.denoteArgs',
    _root_.Hax.denoteApp', StateT.run, bind, StateT.bind, pure, StateT.pure, get, getThe,
    MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    _root_.Hax.Value.ofLit, _root_.Hax.Env.extend, noOverflow64, widthScalarOps,
    _root_.Hax.widthCmpOps, _root_.Hax.widthArithOps, _root_.Hax.wrapUint,
    _root_.Hax.IntWidth.modulus, _root_.Hax.IntWidth.bits]

/-- For `3 ≤ x < 2^64` no index qualifies and the reference run of the pipeline
    output falls through with `100`. -/
theorem searchU_denote'_notFound (x : Nat) (h3 : 3 ≤ x) (hx : x < 2 ^ 64) :
    ((_root_.Hax.denote' (noOverflow64 widthScalarOps) 8 (_root_.Hax.pipeline (searchU x))).run
      _root_.Hax.Env.empty).1 = .val (.uint .w64 100) := by
  rw [searchU_pipeline]
  have hm : x % 18446744073709551616 = x := Nat.mod_eq_of_lt hx
  have h0 : x ≠ 0 := by omega
  have h1 : ¬ x ≤ 1 := by omega
  have h2 : ¬ x ≤ 2 := by omega
  simp [_root_.Hax.denote', _root_.Hax.denoteWhile'Return, _root_.Hax.denoteArgs',
    _root_.Hax.denoteApp', StateT.run, bind, StateT.bind, pure, StateT.pure, get, getThe,
    MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    _root_.Hax.Value.ofLit, _root_.Hax.Env.extend, noOverflow64, widthScalarOps,
    _root_.Hax.widthCmpOps, _root_.Hax.widthArithOps, _root_.Hax.wrapUint,
    _root_.Hax.IntWidth.modulus, _root_.Hax.IntWidth.bits, hm, h0, h1, h2]

/-! ## The `RustExec` runs of the lowered command -/

/-- Every state agrees with the empty environment. -/
theorem envAgreesOff_empty (rs : RustState) : envAgreesOff _root_.Hax.Env.empty rs := by
  intro name v _ hv; cases hv

/-- **Found.** For `x < 3`, from any entry state the lowered search function
    terminates with the index `x` in the result slot. -/
theorem searchLowCT_found (N : Nat) (leafSpec : LeafSpec) (x : Nat) (hx : x < 3)
    (rs : RustState) :
    ∃ rs', RustExec N leafSpec (searchLowCT x) rs rs' ∧ rs'.rsScalar exitResName = x := by
  obtain ⟨rs', hexec, hout⟩ := haxToLowCTFn_simulates (noOverflow64 widthScalarOps) N leafSpec
    scalarOpsSound_noOverflow64_width _ (searchLowCT x) (searchU_exitSimOk x) (searchU_lowers x) 8
    _root_.Hax.Env.empty _ _ rs rfl ⟨_, searchU_denote'_found x hx⟩ (envAgreesOff_empty rs)
  refine ⟨rs', hexec, ?_⟩
  have hd := searchU_denote'_found x hx
  simp only [StateT.run] at hd
  rw [hd] at hout
  exact ((Option.some.injEq _ _).mp hout).symm

/-- **Not found.** For `3 ≤ x < 2^64`, from any entry state the lowered search
    function terminates with the fall-through value `100` in the result slot. -/
theorem searchLowCT_notFound (N : Nat) (leafSpec : LeafSpec) (x : Nat) (h3 : 3 ≤ x)
    (hx : x < 2 ^ 64) (rs : RustState) :
    ∃ rs', RustExec N leafSpec (searchLowCT x) rs rs' ∧ rs'.rsScalar exitResName = 100 := by
  obtain ⟨rs', hexec, hout⟩ := haxToLowCTFn_simulates (noOverflow64 widthScalarOps) N leafSpec
    scalarOpsSound_noOverflow64_width _ (searchLowCT x) (searchU_exitSimOk x) (searchU_lowers x) 8
    _root_.Hax.Env.empty _ _ rs rfl ⟨_, searchU_denote'_notFound x h3 hx⟩ (envAgreesOff_empty rs)
  refine ⟨rs', hexec, ?_⟩
  have hd := searchU_denote'_notFound x h3 hx
  simp only [StateT.run] at hd
  rw [hd] at hout
  exact ((Option.some.injEq _ _).mp hout).symm

/-- At the demo input `x = 1` the lowered function leaves `1` in the result slot. -/
theorem searchLowCT_one (N : Nat) (leafSpec : LeafSpec) (rs : RustState) :
    ∃ rs', RustExec N leafSpec (searchLowCT 1) rs rs' ∧ rs'.rsScalar exitResName = 1 :=
  searchLowCT_found N leafSpec 1 (by decide) rs

/-- At the demo input `x = 5` the lowered function leaves `100` in the result slot. -/
theorem searchLowCT_five (N : Nat) (leafSpec : LeafSpec) (rs : RustState) :
    ∃ rs', RustExec N leafSpec (searchLowCT 5) rs rs' ∧ rs'.rsScalar exitResName = 100 :=
  searchLowCT_notFound N leafSpec 5 (by decide) (by decide) rs

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
