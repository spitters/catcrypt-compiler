/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend

/-!
# The allocated program of a region export as post-pass after allocation

The allocated program `regionLprog` of a region export is the fusion post-pass
`regionPostFuse` of the program of the allocation stage `regionAllocC` (the export, its webs
and the physical-ABI allocation). The printed program that `compileRegion` returns is the
printed program `printedLprog` of that post-pass, so the theorems on `printedLprog` and on
`regionPostFuse` apply to it at the program of the allocation stage.

## Main results

* `regionLprog_split`: `regionLprog` is `regionPostFuse` of the program of `regionAllocC`.
* `regionEncode_fst`: the program of a result of `regionEncode P` is `printedLprog P`.
* `regionImage_split`: the program of a result of `compileRegion` is
  `printedLprog (regionPostFuse P0)` for the program `P0` of the allocation stage.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionLprogSplit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- **The allocated program of a region export is the post-pass of the allocation stage**:
    `regionLprog` is `regionPostFuse` of the program of `regionAllocC`. -/
theorem regionLprog_split (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (callee : Option CalleeTab) (ex : List String) :
    regionLprog a p callee ex = (regionAllocC a p callee ex).map fun x => regionPostFuse x.1 := by
  simp only [regionLprog, regionLprogC, Option.map_map]
  rfl

/-- The program of a result of `regionEncode P` is the printed program of `P`. -/
theorem regionEncode_fst {P : Lprog} {gate : Lcmd → Bool} {callee : Option CalleeTab}
    {out : Lprog × List (BitVec 8)} (h : regionEncode P gate callee = some out) :
    out.1 = printedLprog P := by
  unfold regionEncode at h
  grind

/-- **The printed program of the region back half is the printed post-pass of the allocation
    stage**: every result `(P, bytes)` of `compileRegion` has a callee `callee` and a result
    `(P0, cert)` of the allocation stage `regionAllocC` on the legalised program at the webs
    of the result buffer, with `P = printedLprog (regionPostFuse P0)`. -/
theorem regionImage_split {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData} {P : Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p linked = some (P, bytes)) :
    ∃ callee P0 cert,
      regionAllocC a (legalizeRegion p) callee (regionWebsEx σ exportReg) = some (P0, cert)
      ∧ P = printedLprog (regionPostFuse P0) := by
  unfold compileRegion at h
  split at h
  · split at h
    · split at h
      · rename_i callee _
        split at h
        · rename_i P1 cert hP
          have hE := regionEncode_fst h
          unfold regionLprogC at hP
          obtain ⟨⟨P0, c0⟩, h0, h1⟩ := Option.map_eq_some_iff.mp hP
          simp only [Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          exact ⟨callee, P0, c0, h0, hE⟩
        · cases h
      · cases h
    · cases h
  · cases h

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionLprogSplit
