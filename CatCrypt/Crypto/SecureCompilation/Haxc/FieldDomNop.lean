/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomResult
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapClose

/-!
# The liveness check of the merged code on the field domain

The check `regionNopB` of the region gate reads the merged code of the parts at the identity
merge: `regCoB id` at the liveness table `liveM` of the prefix followed by the merged code, and
the targets of the result copy live at the end. At the identity a name live after a write and
the written name have distinct images whenever they are distinct, so the conditions
`InstrCover` reduce to the shape `CoShape` of the merged code, the closure of the computed
table, and written names that are not empty. The merged code is the renamed code under the
merge of the allocation certificate, which sends no name other than the empty name to the
empty name.

## Main results

* `regionNopB_of_parts`: the check from the shape of the code, written names that are not
  empty and a merge that sends no other name to the empty name.
* `fieldDom_regionNopB`: the stage `G9` on the field domain.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (regDefs)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapComplete (CoShape InstrCover
  regCoB_of_cover liveRegTab_closed liveRegTab_stable condOKB_of_coShape
  regDefs_length_le_of_coShape coShape_renRM regCallB_none)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapClose (coShape_regionCoParts_ren
  mem_ren_of_getElem? mem_arrNames_use mem_arrNames_def)
open CatCrypt.Crypto.Hax (HaxModule)

/-- **The liveness check of the merged code** of the parts without a callee, from the shape
    `CoShape` of the code, written names of the renamed code that are not empty, a merge that
    sends no other name to the empty name, and no target of the result copy. -/
theorem regionNopB_of_parts (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) {code : List LinstrRM} (res : List LOperand) (cert : List (String × String))
    (hc : ∀ i ∈ code, CoShape i)
    (hdef : ∀ (k : Nat) (i : LinstrRM),
      (regionCoParts σ nm body t code res cert none).pre.length ≤ k →
      ((regionCoParts σ nm body t code res cert none).pre
        ++ (regionCoParts σ nm body t code res cert none).ren)[k]? = some i →
      ∀ x ∈ regDefs i, x ≠ "")
    (hτ : ∀ x, x ≠ "" → renOf (regionCoParts σ nm body t code res cert none).tau x ≠ "")
    (hout : (regionCoParts σ nm body t code res cert none).outs = []) :
    regionNopB (regionCoParts σ nm body t code res cert none) = true := by
  unfold regionNopB
  rw [hout]
  simp only [List.all_nil, Bool.and_true]
  refine regCoB_of_cover rfl (fun _ _ => rfl) (fun _ _ => rfl) fun k i hk hi => ?_
  have hmem := mem_ren_of_getElem? hk hi
  rw [List.getElem?_append_right hk] at hi
  have hmerged : (regionCoParts σ nm body t code res cert none).merged =
      (regionCoParts σ nm body t code res cert none).ren.map
        (JasminLsemExportTransfer.renRM (renOf (regionCoParts σ nm body t code res cert none).tau))
      := rfl
  have hi' := hi
  rw [hmerged, List.getElem?_map] at hi'
  obtain ⟨i', hi'1, rfl⟩ := Option.map_eq_some_iff.mp hi'
  have hs' := coShape_regionCoParts_ren σ nm body t res cert none hc i'
    (List.mem_of_getElem? hi'1)
  have hs := coShape_renRM (renOf (regionCoParts σ nm body t code res cert none).tau) hs'
  exact
    { need := liveRegTab_closed (liveRegTab_stable _ _)
        (by rw [List.getElem?_append_right hk]; exact hi)
      cond := condOKB_of_coShape hs
      noGoto := hs.1
      arrUse := fun a ha => List.mem_append_left _ (List.mem_append_left _
        (mem_arrNames_use hmem ha))
      arrDef := fun a ha => List.mem_append_left _ (List.mem_append_left _
        (mem_arrNames_def hmem ha))
      defs := regDefs_length_le_of_coShape hs
      defNe := fun d hd => by
        rw [RegionAllocMapLive.regDefs_renRM] at hd
        obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
        exact hτ d' (hdef k i' hk (by rw [List.getElem?_append_right hk]; exact hi'1) d' hd')
      inj := fun _ _ _ _ hne => hne
      call := regCallB_none _ _ _ k _ }

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- The gate does not refuse at `regionNopB` when the liveness check of the merged code
    accepts. -/
theorem regionCoStage_ne_regionNopB {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h : regionNopB (regionCoParts σ nm b t (calleeCodeT none code) res cert none) = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "regionNopB" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **Stage `G9` on the field domain**: the gate does not refuse at the liveness check of the
    merged code `regionNopB`. -/
theorem fieldDom_regionNopB (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regionNopB" := by
  refine regionCoStage_ne_regionNopB ?_
  have hret : regionRet σ exportReg t r.res = none := by
    obtain ⟨-, R, n, hR⟩ := fieldDomB_abi h
    exact regionRet_words hR
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, hr, hP, -, rfl⟩ := hB
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal h) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hcf : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree h hq))
  have hEx : regionExportableB (legalizeRegion q') = true := fieldDom_legalize hE1
  have hX : RegionExp fname (legalizeRegion q') (regionWebsEx σ exportReg) r := by
    rw [hr]
    exact regionExp_webs _ hr0
  obtain ⟨r1, r2, hr1, hr2, hcert⟩ :=
    RegionAllocMapAlign.regionLprogC_cert (nfAbiNames fname σ) _ _ hP
  obtain rfl : r1 = r0 := Option.some.inj (hr1.symm.trans hr0)
  rw [← hr] at hr2
  subst r2
  subst hcert
  have hc : ∀ i ∈ r.code, CoShape i := by
    rw [hr, regionWebsAt_none]
    exact forall_mem_regionWebs (P := CoShape)
      (fun σ i hi => RegionAllocMapComplete.coShape_renArr σ hi) _ r1 _ _
      (RegionAllocMapClose.exportR_coShape _ _ _ _ _ r1 hr0)
  refine regionNopB_of_parts σ exportReg b _ r.res _ hc
    (RegionAllocMapLive.defs_ne_empty_regionCoParts σ exportReg b _ r.res _
      (hX.defsR hEx hcf) (hX.noShadow hEx hcf) fun RA hRA => ?_)
    (fun x hx he => hx (RegionAllocMapLive.renOf_certMerge_allocCertOf_eq_empty he)) ?_
  · obtain ⟨-, R, n, hR⟩ := fieldDomB_abi h
    rw [hR] at hRA
    cases hRA
  · show (regionRet σ exportReg _ r.res).toList.map Prod.snd = []
    rw [hret]
    rfl

example (S : FieldDomStages) : type_of% @S.regionNopB := @fieldDom_regionNopB

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
