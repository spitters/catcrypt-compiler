/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgCmp
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgLoadGp
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgLoadOrder

/-!
# The optimizer and load-CSE conditions on the allocated function of the region route

`RegionPhysImgCmp.regionCoStage_ne_physImgB_of_loadCSE` takes two hypotheses on the post-pass
body of the allocated function `RegionPhysImgGate.regionAllocFn`: the optimizer condition
`optSideB` on every straight run (`hopt`) and the absence of 64-bit moves between two memory
names (`hhold`). This module proves both on the domain of
`RegionPhysImgArg.physImgB_regionExport_words`, under the bound
`numGPRegs + |bodyNames B| + 1 ≤ vectorBase` on the names of the allocator input `B`.

Under the bound every name of the allocator input renders as a general-purpose register or a
spill slot `k.N`, so every instruction of the fused export body satisfies
`PhysImgLoadGp.WideOk`. The order conditions, the spill pairs and `saveFreshB` of the fused
body come from the compiler lemmas on `lfundefPhysAbiOfVirtCert`; each passes from the fused
body to a run and from the run through `elimReloads`, `reloadElimBody`, `scheduleBody` and
`copyPropagateBody` to the body the load CSE reads.

## Main results

* `regionSl_slotOfReg`: the slot map of the gate has no slot at the slot `qsave.R` of a name
  `R` without a frame slot.
* `hasPrefix_exportReg`: an export register name has no prefix `qsave.`.
* `physRegName_nameOk`: a physical index below `vectorBase` renders as a general-purpose
  register or a spill slot.
* `instrModeled_rwClosed`, `saveSrcI_rwClosed`: two conditions closed under the source
  rewrites of the copy propagation.
* `optSide_regionAllocFn`: `hopt` and `hhold` on the allocated function.
* `regionCoStage_ne_physImgB_words`: the region gate never refuses at its image conjunct.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgLoad

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg gpNameB)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad (asReload elimReloads
  elimReloads_sublist)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit (isAccB slotArr_none_of_prefix AccForm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotArrOf slotArrOf_some slotRen)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (slotArrC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgOpt (optSideB loadSideB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (splitStraightRuns
  bodyAllModeled instrModeled)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim (reloadElimBody
  reloadElimBody_sublist)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate (isFactSrc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass (RwClosed OpRw preLoad
  forall_preLoad slotArr_physGP memMovFreeB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideOpt (saveSrcI saveSrcB_iff
  slotAfterSlotReloadFreeB_sublist sublist_of_mem_splitStraightRuns optSideB_runs
  order_lfundefPhysAbiOfVirtCert pairs_lfundefPhysAbiOfVirtCert)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgLoadGp (WideOk NameOk wideOk_rwClosed
  wideMovB_of_wideOk memMovFreeB_of_wideOk wideOk_lfundefPhysAbiOfVirtCert)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgLoadOrder (saveFreshB_sublist
  saveFreshB_scheduleBody saveFreshB_copyPropagateBody saveFreshB_lfundefPhysAbiOfVirtCert
  slotAfterSlotReloadFreeB_scheduleBody slotAfterSlotReloadFreeB_copyPropagateBody
  slotAfterSlotLoadFreeB_of_reload loadChkB_of_fresh)
open RegionPhysImgGate (regionAllocFn postBody)
open RegionPhysImgSide (sideAlloc_regionAllocFn regionAllocFn_exportHyps deadWriteRet_sublist)
open RegionAllocMapAlign (regionAllocBody regionAllocTbl)
open RegionAllocMapDom (ShapeB bodyHasCall_of_shapeB bodyStraightCall_of_shapeB
  physMapTabled_regionAllocTbl_lt)

/-! ## 1. The slot map and the names of the export -/

/-- **The slot map of the gate has no slot at the slot `qsave.R` of a name `R` without a
    frame slot** (`abiSlotOfExt`), at a layout whose word-array parameters have frame slots. -/
theorem regionSl_slotOfReg {σ : AbiLayout} (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    (R : Slots) (ps : List (String × String)) {Rg : String} (hRg : abiSlotOfExt Rg = none) :
    slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)) (slotOfReg Rg) = none := by
  have hi := RegionPhysImg.regionSl_isSome R (slotArrOf σ exportReg) (renOf ps) (slotOfReg Rg)
  cases hsl : slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)) (slotOfReg Rg) with
  | none => rfl
  | some x =>
    rw [hsl, Option.isSome_some] at hi
    cases hs : slotArrOf σ exportReg (slotOfReg Rg) with
    | none => rw [hs] at hi; cases hi
    | some An =>
      exfalso
      obtain ⟨A, n⟩ := An
      obtain ⟨j, a, ha, hk, -, he⟩ := slotArrOf_some hs
      have hw := List.all_eq_true.mp hσ a (List.mem_of_getElem? ha)
      rw [hk] at hw
      have hr : exportReg a.reg = Rg := by
        have := congrArg String.toList he
        simp only [slotOfReg, String.toList_append, List.append_cancel_left_eq] at this
        exact String.ext this
      rw [hr, hRg] at hw
      cases hw

/-- **An export register name has no prefix `qsave.`**: its characters are upper case. -/
theorem hasPrefix_exportReg (r : String) : hasPrefix (exportReg r) "qsave." = false := by
  unfold exportReg hasPrefix
  rw [String.toList_ofList]
  cases r.toList.drop 1 with
  | nil => rfl
  | cons c t =>
    have hc : c.toUpper ≠ 'q' := by
      intro h
      unfold Char.toUpper at h
      split at h
      · rename_i hl
        rw [Char.ext_iff] at h
        simp only at h
        obtain ⟨h3, h4⟩ := hl
        rw [show 'a'.val = 97 from rfl, show 'A'.val = 65 from rfl,
          show 'q'.val = 113 from rfl] at h
        rw [show 'a'.val = 97 from rfl] at h3
        rw [show 'z'.val = 122 from rfl] at h4
        revert h h3 h4
        generalize c.val = v
        intro h h3 h4
        rw [UInt32.le_iff_toNat_le] at h3 h4
        have h5 := congrArg UInt32.toNat h
        rw [UInt32.toNat_add] at h5
        simp only [UInt32.reduceSub, UInt32.reduceToNat] at h5 h3 h4
        omega
      · rename_i hl
        subst h
        exact hl (by decide)
    simp [List.isPrefixOf, Ne.symm hc]

/-- **A physical index below `vectorBase` renders as a general-purpose register or a spill
    slot `k.N`.** -/
theorem physRegName_nameOk {p : Nat} (hp : p < vectorBase) : NameOk (physRegName p) := by
  unfold physRegName
  rw [ite_eq_right (by omega)]
  split
  · rename_i r hr
    have hm : r ∈ gpRegNames := List.mem_of_getElem? hr
    have hg : ∀ x ∈ gpRegNames, gpNameB x = true := by decide
    exact Or.inl (hg r hm)
  · exact Or.inr (by simp [hasPrefix, String.toList_append])

/-! ## 2. Closure under the copy propagation -/

/-- **`instrModeled` is closed under the source rewrites of the copy propagation**: it reads
    the destinations, the mnemonic and the number of sources. -/
theorem instrModeled_rwClosed : RwClosed fun j => instrModeled j = true := by
  intro i dsts opn srcs g hi he _
  simp only [instrModeled, he] at hi ⊢
  rcases dsts with _ | ⟨_ | _ | _ | _ | _, _ | _⟩ <;> simp_all

/-- **The reload condition of `saveSrcB` is closed under the source rewrites of the copy
    propagation**, when every array slot is a `qsave.` slot: a rewritten source is a
    general-purpose register or an immediate. -/
theorem saveSrcI_rwClosed {slotArr : String → Option (String × Nat)}
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    RwClosed fun j => saveSrcI slotArr j = true := by
  intro i dsts opn srcs g hi he hg
  simp only [saveSrcI] at hi ⊢
  rw [he] at hi
  cases hr : asReload (.Lopn dsts opn (srcs.map g)) with
  | none => rfl
  | some p =>
    obtain ⟨d, s⟩ := p
    obtain ⟨o, ho⟩ := X86Backend.PhysImgSideOpt.asReload_eq hr
    simp only [LinstrR.Lopn.injEq] at ho
    obtain ⟨rfl, rfl, hs⟩ := ho
    rcases srcs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq, and_false,
        and_true] at hs
    rcases hg a with ha | ⟨u, rfl, hf, -⟩
    · rw [ha] at hs
      subst hs
      simp only [List.map_cons, List.map_nil, ha] at hr
      rw [hr] at hi
      exact hi
    · rw [hs] at hf
      simp only [Bool.or_eq_true, Option.isNone_iff_eq_none]
      exact Or.inr (slotArr_physGP hq (by simpa [isFactSrc] using hf))

/-! ## 3. The allocated function -/

/-- **The optimizer and load-CSE conditions on the allocated function of the region route**,
    on the domain of `RegionPhysImgArg.physImgB_regionExport_words` under the bound `hsize`
    on the names of the allocator input: at the slot map of the gate, every straight run of
    the post-pass body of `regionAllocFn` satisfies `optSideB`, and no 64-bit move of the
    post-pass body is between two memory names. -/
theorem optSide_regionAllocFn (fname : String) (σ : AbiLayout) {ts : List JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hw : RegionPhysImgArg.arrW64B p = true)
    (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    {r : Exported} (hr : exportR (nfCtx σ).length fname p (nfCtx σ).length 0 = some r)
    (hzr : RegionPhysImgArg.ZeroAtRoot (nfAbiNames fname σ) ts r)
    (hts : ∀ w, ts ≠ [.reg w]) (fd0 : Lfundef)
    (hnd : (σ.args.map fun a => exportReg a.reg).Nodup) (R : Slots)
    (ps : List (String × String))
    (hsize : numGPRegs + (bodyNames
      (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r)).length + 1 ≤ vectorBase) :
    (splitStraightRuns
      (postBody (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body)).all
      (optSideB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))) = true ∧
    memMovFreeB (postBody (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body) = true := by
  obtain ⟨-, -, -, hmul, -⟩ :=
    sideAlloc_regionAllocFn fname σ p hp hc hw hσ hr hzr hts fd0 hnd R ps
  obtain ⟨virt0, hbody, hb1, hcf, hshape, harr, hidx, hB⟩ :=
    regionAllocFn_exportHyps fname σ p hp hc hw hσ hr hzr hts fd0 hnd R ps
  have hq := RegionPhysImg.regionSl_qsave R σ exportReg (renOf ps)
  have hcs : ∀ Rg ∈ ["RBX", "RBP", "R12", "R13", "R14", "R15"],
      slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)) (slotOfReg Rg) = none := by
    intro Rg hRg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRg
    rcases hRg with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact regionSl_slotOfReg hσ R ps (by decide +kernel)
  have habi : ∀ a ∈ (nfAbiNames fname σ).abiArgs, hasPrefix a "qsave." = false := by
    intro a ha
    simp only [nfAbiNames, List.mem_map] at ha
    obtain ⟨x, -, rfl⟩ := ha
    exact hasPrefix_exportReg _
  have hT : regionAllocTbl (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r) =
      physTableOut (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r) [] := by
    unfold regionAllocTbl straightCallComposeTable
    rw [bodyStraightCall_of_shapeB hB]
    rfl
  have hname : ∀ n, NameOk (physRegName (physMapTabled
      (straightCallComposeTable (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r)
        (physTableOut (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r) [] []))
      (nameSlot (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r) n))) := fun n =>
    physRegName_nameOk (physMapTabled_regionAllocTbl_lt hB hsize List.idxOf_le_length)
  have hmat : ∀ j, NameOk (physNameForBody
      (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r)
      (physTableOut (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r) [])
      (argName j)) := by
    intro j
    unfold physNameForBody
    rw [RegionPhysImg.isFrameSlotName_argName, hcf, ← hT]
    simp only [Bool.false_eq_true, ite_false]
    exact physRegName_nameOk (physMapTabled_regionAllocTbl_lt hB hsize List.idxOf_le_length)
  rw [hbody] at hmul ⊢
  have hZ := order_lfundefPhysAbiOfVirtCert virt0 _ _ [] (fun _ => none) _
    ((nfAbiNames fname σ).abiArgs.map fun _ => 64) true _ hb1 _ rfl hcf hshape harr hidx hq
  have hP := pairs_lfundefPhysAbiOfVirtCert virt0 _ _ [] (fun _ => none) _
    ((nfAbiNames fname σ).abiArgs.map fun _ => 64) true _ hb1 _ rfl hcf hshape harr hidx hq
    hmul hcs habi
  have hW := wideOk_lfundefPhysAbiOfVirtCert virt0 (nfAbiNames fname σ).outArg
    (nfAbiNames fname σ).inArgs [] (fun _ => none) _
    ((nfAbiNames fname σ).abiArgs.map fun _ => 64) true _ hb1 _ rfl hcf hname hmat
  have hF := saveFreshB_lfundefPhysAbiOfVirtCert virt0 _ _ [] (fun _ => none) _
    ((nfAbiNames fname σ).abiArgs.map fun _ => 64) true _ hb1 _ rfl hcf hshape harr hidx hq
  dsimp only at hZ hP hW hF
  unfold postBody
  generalize fuseMulHiBody (lfundefPhysAbiOfVirtCert virt0 (nfAbiNames fname σ).outArg
    (nfAbiNames fname σ).inArgs [] (fun _ => none) (nfAbiNames fname σ).abiArgs
    ((nfAbiNames fname σ).abiArgs.map fun _ => 64) x86Abi true).1.lfd_body true = Z
    at hZ hP hW hF ⊢
  have hs := deadWriteRet_sublist Z
  refine ⟨optSideB_runs hZ hP hs fun seg hseg hm => ?_,
    memMovFreeB_of_wideOk fun j hj => hW j (hs.subset hj)⟩
  have hsub := (sublist_of_mem_splitStraightRuns hseg).trans hs
  have hWp : ∀ j ∈ preLoad seg, WideOk j :=
    forall_preLoad wideOk_rwClosed fun j hj => hW j (hsub.subset hj)
  have hFp := saveFreshB_copyPropagateBody hq (saveFreshB_scheduleBody hq
    (saveFreshB_sublist (reloadElimBody_sublist _) (fun _ h => h)
      (saveFreshB_sublist (elimReloads_sublist _) (fun _ h => h)
        (saveFreshB_sublist hsub (fun _ h => h) hF))))
  show loadSideB _ (preLoad seg) = true
  simp only [loadSideB, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, wideMovB_of_wideOk hWp⟩, ?_⟩, ?_⟩, ?_⟩
  · exact List.all_eq_true.mpr (forall_preLoad instrModeled_rwClosed (List.all_eq_true.mp hm))
  · exact loadChkB_of_fresh hq hFp (memMovFreeB_of_wideOk hWp)
      fun j hj d s mn h => (hWp j hj d s mn h).1
  · exact saveSrcB_iff.mpr (forall_preLoad (saveSrcI_rwClosed hq)
      fun j hj => saveSrcB_iff.mp hZ.2 j (hsub.subset hj))
  · exact slotAfterSlotLoadFreeB_of_reload _ id
      (slotAfterSlotReloadFreeB_copyPropagateBody hq (slotAfterSlotReloadFreeB_scheduleBody hq
        (slotAfterSlotReloadFreeB_sublist (reloadElimBody_sublist _) id
          (slotAfterSlotReloadFreeB_sublist (elimReloads_sublist _) id
            (slotAfterSlotReloadFreeB_sublist hsub id hZ.1)))))

/-! ## 4. The gate -/

/-- **The region gate never refuses at its image conjunct** on the domain of
    `RegionPhysImgArg.physImgB_regionExport_words`, under the bound `hsize` on the names of
    the allocator input: `RegionPhysImgCmp.regionCoStage_ne_physImgB_of_loadCSE` with `hopt`
    and `hhold` from `optSide_regionAllocFn`. -/
theorem regionCoStage_ne_physImgB_words (fname : String) (σ : AbiLayout) {t : JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) [t]) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hw : RegionPhysImgArg.arrW64B p = true)
    (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    {r : Exported} (hr : exportR (nfCtx σ).length fname p (nfCtx σ).length 0 = some r)
    (hzr : RegionPhysImgArg.ZeroAtRoot (nfAbiNames fname σ) [t] r)
    {fd0 : Lfundef} (hfd : exportRLfundef fname p = some fd0)
    (hts : ∀ w, [t] ≠ [.reg w]) (hnd : (σ.args.map fun a => exportReg a.reg).Nodup)
    (hsize : numGPRegs + (bodyNames
      (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length [t] r)).length + 1 ≤ vectorBase)
    (ex : List String) {P : Lprog} {cert : List (String × String)}
    (hP : regionLprogC (nfAbiNames fname σ) p none ex = some (P, cert))
    {b : Lcmd} (hb : firstBody (printedLprog P) = some b) (fn : String) :
    regionCoStage σ exportReg b t r.code r.res cert none fn ≠ some "physImgB" :=
  have h := optSide_regionAllocFn fname σ p hp hc hw hσ hr hzr hts fd0 hnd
    (regionCoParts σ exportReg b t r.code r.res cert).cells
    (regionCoParts σ exportReg b t r.code r.res cert).ps hsize
  RegionPhysImgCmp.regionCoStage_ne_physImgB_of_loadCSE fname σ p hp hc hw hσ hr hzr hfd hts hnd
    ex hP hb fn h.1 h.2

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgLoad
