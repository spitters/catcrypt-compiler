/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomFrontRefusal
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoStorage

/-!
# The class stage and the event check on the exported field domain

The webs `r` of `FieldBody` are the webs `regionWebsAt` of an export on x86, so every
instruction of `r.code` has the forms `RegionExportForms.FormB`
(`RegionExportForms.formB_regionWebsAt`). From the forms, the gate `regionCoStage` does not
refuse at its class stage `coClass` (stage `G1` of `FieldDomStages`), and the first four
conjuncts of the event check `regionLeakB` (stage `C1`) hold.

## Main results

* `fieldDom_formB` — every instruction of the webs of a member of the field domain has the
  forms `FormB`.
* `fieldDom_coClass` — stage `G1`: the gate does not refuse at `coClass`.
* `fieldDom_regionLeakB_head` — the first four conjuncts of stage `C1`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfgLeak (leakFixCfgB)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- Every instruction of the webs `r` of `FieldBody` has the forms `FormB`: `r` is the webs
    `regionWebsAt` of an export on x86. -/
theorem fieldDom_formB (hB : FieldBody e σ fname b t r cert) :
    ∀ i ∈ r.code, RegionExportForms.FormB i := by
  obtain ⟨t0, q, q', r0, P, -, -, hr0, rfl, -, -, -⟩ := hB
  exact RegionExportForms.formB_regionWebsAt hr0 _ none

/-- **Stage `G1`**: on the field domain the gate `regionCoStage` does not refuse at the class
    stage `coClass`. -/
theorem fieldDom_coClass (_h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coClass" :=
  RegionExportForms.regionCoStage_ne_coClass (fieldDom_formB hB) σ exportReg b t cert fname

/-- **The first four conjuncts of stage `C1`**: on the field domain the alias map fixes the
    array bases of the events of the code with the result copies, the coalesced code has no
    compile-time array operand, and the renamed and the merged code pass the liveness checks
    of their events. -/
theorem fieldDom_regionLeakB_head (_h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    (leakFixCfgB (regionAliasN σ exportReg t r.res (regionCoCodeN σ exportReg t r.code r.res))
        (regionCoCodeN σ exportReg t r.code r.res)
      && (regionCoBody σ exportReg t r.code r.res).all constArrFreeB
      && ((regionCoParts σ exportReg b t r.code r.res cert).tau == []
        || regLeakB (renOf (regionCoParts σ exportReg b t r.code r.res cert).tau)
          (regionCoParts σ exportReg b t r.code r.res cert).pre
          (regionCoParts σ exportReg b t r.code r.res cert).ren
          (tabAt (regionCoParts σ exportReg b t r.code r.res cert).live))
      && regLeakB id (regionCoParts σ exportReg b t r.code r.res cert).pre
        (regionCoParts σ exportReg b t r.code r.res cert).merged
        (tabAt (regionCoParts σ exportReg b t r.code r.res cert).liveM)) = true :=
  RegionExportForms.regionLeakB_four (fieldDom_formB hB) σ exportReg b t cert

example (S : FieldDomStages) : type_of% @S.coClass :=
  fun h hB => fieldDom_coClass (fieldDomB_of_fieldDomB' h) hB

example (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    regionLeakB σ exportReg b t r.code r.res cert
      = X86Backend.OwnedTVLeak.ownedCheckML (regionCoParts σ exportReg b t r.code r.res cert).outs
        (regionCoParts σ exportReg b t r.code r.res cert).ref
        (JasminLsemAddrImage.virtImg
          (regionSl σ exportReg (regionCoParts σ exportReg b t r.code r.res cert))
          (X86Backend.ImageAddrCells.cellBody
            (regionSl σ exportReg (regionCoParts σ exportReg b t r.code r.res cert)) b)) := by
  dsimp only [regionLeakB]
  rw [fieldDom_regionLeakB_head h hB, Bool.true_and]

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
