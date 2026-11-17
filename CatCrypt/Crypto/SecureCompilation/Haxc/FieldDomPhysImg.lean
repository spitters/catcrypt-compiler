/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSplit
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomAssemble
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomInputAcc

/-!
# The image conjunct of the region gate on the field domain (stage `G16`)

The statement of the field `physImgB` of `FieldDomOpen`: for every member of `fieldDomB''` and
every printed body `FieldBody e σ fname b t r cert`, the region gate does not name `physImgB` as
the refusing stage. The proof applies `RegionPhysImgSplit.regionCoStage_ne_physImgB_split` to
the legalised narrowed output of the chain and discharges its hypotheses on the field domain:
the export facts of the front (`fieldDom_legalize`, `legalizeRegion_callFree`), the save slots
of the field layout (`wordsSlotB_fieldAbi`), distinct export registers, the virtual function of
the export, the access form `AccArg` of the allocator input (from `accP_regionAllocBody` at the
webs, `webs_aliasRoots` and `websCopy_accCode`, `websCopy_immCode`, `websCopy_untagP`), the
absence of compile-time array operands (`noCArr_regionAllocBody_of`) and of `ZEROARR` and
`STOREIMM` (`noArrImm_regionAllocBody`). The side conditions `physImgSideB` of the printer
passes on the allocated function `regionAllocFnSplit` are the hypothesis `FieldPhysImgSide`.

## Main results

* `noArrImm_of_plain`: an instruction of the form `ImmCode` with a plain tag is no `ZEROARR`
  and no `STOREIMM`.
* `FieldPhysImgSide`: the side conditions `physImgSideB` on the allocated function of a member
  of the field domain, at the slot map of the gate.
* `fieldDom_physImgB_of_side`: the region gate does not refuse at `physImgB` on `fieldDomB''`
  under `FieldPhysImgSide`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomPhysImg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (NoCArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapAlign
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg (ImmCode NoArrImm ArgSlotName
  noArrImm_regionLprogCopy exportR_noCArr noCArr_renArr accP_regionAllocBody accArg_of_accP
  arrNamed_nfCtx noArrImm_regionAllocBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSplit (regionAllocFnSplit
  regionCoStage_ne_physImgB_split)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate (physImgSideB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotArrOf slotRen)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (slotArrC)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (fieldAbi)
open CatCrypt.Crypto.Hax (HaxModule)

/-- An instruction of the form `ImmCode` with a plain tag is no `ZEROARR` and no `STOREIMM`. -/
theorem noArrImm_of_plain {i : LinstrRM} (hm : ImmCode i) (hp : PlainTag i) : NoArrImm i.1 := by
  intro ds o ss he
  constructor
  · rintro rfl
    obtain ⟨_, _, _, _, _, rfl⟩ := hm.1 ds ss he
    exact absurd hp id
  · rintro rfl
    obtain ⟨_, _, _, _, _, _, rfl⟩ := hm.2 ds ss he
    exact absurd hp id

/-- **The side conditions of the printer passes on a member of the field domain**: on the
    narrowed output of the chain, its export `r0`, the allocation `regionLprogC` at its default
    arguments, the first printed body `b` and the virtual function `fd0` of the export, the
    side conditions `physImgSideB` hold on the allocated function `regionAllocFnSplit` of the
    webs at the slot map of the parts `regionCoParts` of the gate. -/
def FieldPhysImgSide (e : _root_.Hax.TExpr) (σ : AbiLayout) (fname : String) : Prop :=
  ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
    (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0])
    (r0 : Exported) (P : Lprog) (cert : List (String × String)) (b : Lcmd) (fd0 : Lfundef),
    haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩ →
    NarrowWords.narrowPrep q = some q' →
    exportR ((nfCtx σ).map NarrowWords.wideTy).length fname (legalizeRegion q')
      ((nfCtx σ).map NarrowWords.wideTy).length 0 = some r0 →
    regionLprogC (nfAbiNames fname σ) (legalizeRegion q') none (regionWebsEx σ exportReg)
      = some (P, cert) →
    firstBody (regionPrinted P) = some b →
    exportRLfundef fname (legalizeRegion q') = some fd0 →
    physImgSideB
      (slotArrC (regionCoParts σ exportReg b (NarrowWords.wideTy t0)
          (regionWebsAt (regionWebsEx σ exportReg) none r0).code
          (regionWebsAt (regionWebsEx σ exportReg) none r0).res cert).cells
        (slotRen (slotArrOf σ exportReg)
          (renOf (regionCoParts σ exportReg b (NarrowWords.wideTy t0)
            (regionWebsAt (regionWebsEx σ exportReg) none r0).code
            (regionWebsAt (regionWebsEx σ exportReg) none r0).res cert).ps)))
      (regionAllocFnSplit (nfAbiNames fname σ) [NarrowWords.wideTy t0]
        (regionWebsAt (regionWebsEx σ exportReg) none r0) fd0).lfd_res
      (regionAllocFnSplit (nfAbiNames fname σ) [NarrowWords.wideTy t0]
        (regionWebsAt (regionWebsEx σ exportReg) none r0) fd0).lfd_body = true

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String}

/-- **Stage `G16` on `fieldDomB''`**: the region gate does not name `physImgB` as the refusing
    stage on a printed body of a member of `fieldDomB''`, under the side conditions
    `FieldPhysImgSide` of the printer passes. -/
theorem fieldDom_physImgB_of_side (hS : FieldPhysImgSide e σ fname) {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "physImgB" := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, hP, hb, rfl⟩ := hB
  have h' := fieldDomB'_of_fieldDomB'' h
  have hd := fieldDomB_of_fieldDomB' h'
  obtain ⟨k, n, hk, rfl, -⟩ := fieldDomB'_layout h'
  have hk' := fieldDomE_k hk
  have ht0 : t0 = .stackArr 64 n := fieldDom_chainTy hd hq hk' rfl
  subst ht0
  have hts' : ∀ w, [NarrowWords.wideTy (.stackArr 64 n)] ≠ [.reg w] := fun w h' => by
    simp [NarrowWords.wideTy] at h'
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal hd) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hcf : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans
      (fieldDom_callFree hd hq))
  have hEx : regionExportableB (legalizeRegion q') = true := fieldDom_legalize hE1
  have hL := fieldDom_legalize_loadsChainS hd hq hq'
  have hw := arrW64B_loadsChainS hL hEx (ctxW64_nfCtx _)
  have hσ := wordsSlotB_fieldAbi (n := n) hk'
  have hA : RegionPhysImgArg.ArrNamed (ArgSlotName (fieldAbi k n))
      ((nfCtx (fieldAbi k n)).map NarrowWords.wideTy).length
      ((nfCtx (fieldAbi k n)).map NarrowWords.wideTy).length
      ((nfCtx (fieldAbi k n)).map NarrowWords.wideTy) := by
    rw [List.length_map]
    exact arrNamed_map_wideTy (arrNamed_nfCtx hσ)
  have hnd : ((fieldAbi k n).args.map fun a => exportReg a.reg).Nodup := by
    have x0 : exportReg "%rdi" = "RDI" := by decide
    have x1 : exportReg "%rsi" = "RSI" := by decide
    have x2 : exportReg "%rdx" = "RDX" := by decide
    rcases hk' with rfl | rfl <;>
      simp [fieldAbi, List.range_succ, FieldRoute.fieldArgReg, x0, x1, x2]
  obtain ⟨fd0, hfd⟩ : ∃ fd0, exportRLfundef fname (legalizeRegion q') = some fd0 :=
    by simp only [exportRLfundef, hr0, Option.map_some]; exact ⟨_, rfl⟩
  set ex := regionWebsEx (fieldAbi k n) exportReg
  set a := nfAbiNames fname (fieldAbi k n)
  have hC := websCopy_accCode a (ts := [NarrowWords.wideTy (.stackArr 64 n)]) hcf hw hr0 ex
  have hI := websCopy_immCode a (ts := [NarrowWords.wideTy (.stackArr 64 n)]) hcf hL hr0 ex
  have hU := websCopy_untagP a (ts := [NarrowWords.wideTy (.stackArr 64 n)]) hcf hr0 ex
  have hroot := webs_aliasRoots fname (fieldAbi k n) _ hEx hcf hw hL hσ hA hr0 ex
  have hN : ∀ i ∈ (regionWebs ex r0).code, NoCArr i.1 :=
    forall_mem_regionWebs (P := fun i => NoCArr i.1) (fun ρ i hi => noCArr_renArr ρ hi)
      ex r0 _ _ (exportR_noCArr _ _ _ hcf _ _ r0 hr0)
  have hplain : ∀ i ∈ (regionWebs ex r0).code, PlainTag i := by
    obtain ⟨⟨_, hE⟩, -⟩ := loadsChainS_export_class (fn := fname) hL le_rfl hr0
    refine forall_mem_regionWebs (P := PlainTag)
      (fun ρ i hi => by rw [PlainTag, renArr_snd]; exact hi) ex r0 _ _ (fun i hi => ?_)
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    exact (hE k i hk).1
  have hshape : ∀ i ∈ (regionWebs ex r0).code, ShapeB i.1 :=
    forall_mem_regionWebs (P := fun i => ShapeB i.1) (fun ρ i hi => shapeB_renArr ρ hi)
      ex r0 _ _ (fun i hi => (exportR_mnemDom _ _ _ hEx hcf _ _ r0 hr0 i hi).2.2)
  have hacc : ∀ i ∈ regionAllocBody a ((nfCtx (fieldAbi k n)).map NarrowWords.wideTy).length
      [NarrowWords.wideTy (.stackArr 64 n)] (regionWebs ex r0),
      RegionPhysImg.AccArg (fieldAbi k n) i.li_i := fun i hi =>
    accArg_of_accP (accP_regionAllocBody _ _ _ _ hts' hC hI hroot hU i hi)
  have harr : ∀ i ∈ regionAllocBody a ((nfCtx (fieldAbi k n)).map NarrowWords.wideTy).length
      [NarrowWords.wideTy (.stackArr 64 n)] (regionWebs ex r0), ∀ q n,
        LOperand.arr q n ∈ lopnOperands i.li_i → hasPrefix q "qsave." = false := by
    intro i hi q m hq
    have h := noCArr_regionAllocBody_of _ _ hN hts' i hi
    revert h hq
    cases i.li_i with
    | Lopn ds o ss => exact fun hq h => absurd rfl (h _ hq q m)
    | _ => exact fun hq _ => absurd hq (by simp [lopnOperands])
  have hne : ∀ i ∈ regionAllocBody a ((nfCtx (fieldAbi k n)).map NarrowWords.wideTy).length
      [NarrowWords.wideTy (.stackArr 64 n)] (regionWebs ex r0), NoArrImm i.li_i := by
    refine noArrImm_regionAllocBody _ _ _ hts' fun i hi => ?_
    rcases List.mem_append.mp hi with hi' | hi'
    · exact ⟨noArrImm_of_plain (hI i hi) (hplain i hi'), hshape i hi'⟩
    · exact ⟨noArrImm_regionLprogCopy _ _ _ _ i hi', shapeB_regionLprogCopy _ _ _ _ i hi'⟩
  exact regionCoStage_ne_physImgB_split fname (fieldAbi k n) (legalizeRegion q') hEx hcf hσ hr0
    hfd hts' hnd ex hacc harr hne hP hb fname (hS _ q q' r0 P cert b fd0 hq hq' hr0 hP hb hfd)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomPhysImg
