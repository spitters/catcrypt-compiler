/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomAssemble
import CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvStraightComplete
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCoalesceShape

/-!
# The index invariant check on the field domain from the shape of the reference

The stage `idxInvCheckB` (`G14`) of the region gate checks the reference `d.ref` of the parts
`regionCoParts` with the bounds-invariant check `idxInvCheckB` from the entry facts
`boundFacts σ exportReg` and the annotation `idxAnnot`. On a non-empty straight-line reference
whose symbolic run is inside the fragment and whose index obligations are immediates of width
`64` below the lengths of their arrays, the check accepts (`idxInvCheckB_straight`).

## Main results

* `regionCoStage_ne_idxInvCheckB`: the gate does not refuse at `idxInvCheckB` when the check
  accepts the reference.
* `fieldDom_idxInvCheckB_of_ref`: stage `G14` on the field domain from the shape of the
  reference.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (idxInvCheckB idxAnnot boundFacts
  idxInvCheckB_straight)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (symRun SSt straightR)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (symObl)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- The gate does not refuse at `idxInvCheckB` when the bounds-invariant check accepts the
    reference of the parts. -/
theorem regionCoStage_ne_idxInvCheckB {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h : idxInvCheckB (boundFacts σ nm)
      (idxAnnot (boundFacts σ nm)
        (regionCoParts σ nm b t (calleeCodeT none code) res cert none).ref)
      (regionCoParts σ nm b t (calleeCodeT none code) res cert none).ref = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "idxInvCheckB" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **Stage `G14` on the field domain from the shape of the reference**: the gate does not
    refuse at `idxInvCheckB` when the reference of the parts is a non-empty straight-line body
    whose symbolic run is inside the fragment and whose index obligations are immediates of
    width `64` below the lengths of their arrays. -/
theorem fieldDom_idxInvCheckB_of_ref
    (hne : (regionCoParts σ exportReg b t r.code r.res cert).ref ≠ [])
    (hs : ∀ p ∈ (regionCoParts σ exportReg b t r.code r.res cert).ref, straightR p.1 = true)
    (hunk : symRun (regionCoParts σ exportReg b t r.code r.res cert).ref SSt.start ≠ .unk)
    (hidx : ∀ o ∈ symObl (regionCoParts σ exportReg b t r.code r.res cert).ref SSt.start,
      ∃ c, o.1 = .immW 64 c ∧ c < o.2) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "idxInvCheckB" :=
  regionCoStage_ne_idxInvCheckB (idxInvCheckB_straight σ exportReg hne hs hunk hidx)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
