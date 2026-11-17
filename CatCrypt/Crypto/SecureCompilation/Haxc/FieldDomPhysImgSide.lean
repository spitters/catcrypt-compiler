/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSplitSide
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomPhysImg
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgCmp

/-!
# The side conditions of the region gate on the field domain from the optimizer conditions

This module proves the side conditions `physImgSideB` of the region gate on the allocated
function with split intervals `regionAllocFnSplit` of an exported code (`RegionExp`) from the
optimizer condition on the straight runs of the post-pass body (`hopt`) and the absence of
64-bit moves between two memory names in it (`hhold`), and so reduces the hypothesis
`FieldDomPhysImg.FieldPhysImgSide` of stage `G16` on `fieldDomB''` to these two conditions.

The tied flag compares (conjunct 7) and the free compare scratch (conjunct 8) are carried over
the body with split intervals `physBodySplit`: each chunk of an operation is made of moves
`MOV`/`MOV:64` with one source, the expansion `physExpandR` (which is `physExpand`) under a
renaming that sends registers to registers, and moves back. A move with one source is a tied
compare vacuously and is a quiet operation for `cmpAccFreeB`, so the chunk refines the
operation (`PhysImgSideCmp.CmpRefines`) and its compares are tied when those of the expansion
are (`RegionPhysImgFlag.physExpand_tiedI`). Conjunct 8 follows from `cmpAccFreeB false` on the
allocated body (`PhysImgSideCmp.cmpScratchFreeB_twoAddrBody`). The flag form and the closed
compares of the export pass to the webs, whose renaming of array positions keeps both.

The register-indexed operands of the allocator input are in its accesses
(`RegionPhysImgSide.idxAcc_regionAllocBody`) at the access form `AccCode` of the webs
(`FieldDomComplete.websCopy_accCode`), which gives the hypothesis `hidx` of
`RegionPhysImgSplitSide.sideAlloc_regionAllocFnSplit`.

## Main results

* `physBodySplit_tiedI`, `physBodySplit_cmpRefines`: the tied compares and the compare
  refinement of the body with split intervals.
* `flagTiedB_regionAllocFnSplit`, `cmpAccFreeB_regionAllocFnSplit`: `flagTiedB` and
  `cmpAccFreeB false` on the body of `regionAllocFnSplit`.
* `physImgSideB_of_exportSplit_opt`: `physImgSideB` on `regionAllocFnSplit` from `hopt` and
  `hhold`.
* `fieldPhysImgSide_of_opt`, `fieldDom_physImgB_of_opt`: `FieldPhysImgSide` and stage `G16` on
  `fieldDomB''` from the optimizer conditions `FieldOptSide` and `FieldMemMovFree`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomPhysImgSide

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint (flagTiedB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass (TiedI flagTiedB_iff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideCmp (isCmpB isOpnB isMemB
  cmpAccFreeB CmpRefines QuietI cmpAccFreeB_quiet_left cmpAccFreeB_quiet_right
  cmpRefines_reloadArrImmBody cmpRefines_filter cmpRefines_physExpand
  cmpAccFreeB_dropLast quietI_of_slotMov quiet_of_mn cmpScratchFreeB_twoAddrBody)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapAlign
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgFlag (FlagForm flagForm_renArr
  exportR_flagForm flagForm_regionLprogCopy flagForm_backEdgePins flagForm_lopn flagForm_livepin
  flagForm_canonicalizeMemrefThread flagForm_nonLopn physExpand_tiedI tiedI_of_one
  tiedI_of_slotMov)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgCmp (CmpClosed toL cmpClosed_append
  cmpClosed_of_noCmp exportR_cmpClosed noCmp_regionLprogCopy cmpRefines_one_of_mn
  cmpRefines_regionAllocCode cmpRefines_canonicalizeMemrefThread quietI_livepin
  cmpRefines_deadWriteRet cmpRefines_quietOps_left)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg (renArr_lopn)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSplitSide (physExpandR_eq)

/-! ## 1. The body with split intervals -/

/-- An operation with one source is a tied flag compare. -/
theorem tiedI_of_oneSrc {j : Linstr} {ds : List LOperand} {o : String} {s : LOperand}
    (h : j.li_i = .Lopn ds o [s]) : TiedI j := by
  intro d opn x c he _
  rw [h] at he
  simp at he

/-- **The compares of the body with split intervals are tied** when every instruction of the
    body has the flag form. -/
theorem physBodySplit_tiedI (shiftImm : ShiftImmOracle) (body : Lcmd) (cfg : SplitCfg)
    (mbr : String → Option String) (hflag : ∀ i ∈ body, FlagForm i.li_i) :
    ∀ j ∈ physBodySplit shiftImm body cfg mbr x86Abi, TiedI j := by
  unfold physBodySplit
  dsimp only
  generalize (bodySplitPieces body cfg x86Abi).foldl _ _ = byPos
  refine FieldDomComplete.foldl_inv _ (fun st : Array Linstr × Nat =>
    ∀ j ∈ st.1.toList, TiedI j) body (#[], 0) (by simp) ?_
  intro st i hi hst j hj
  split at hj
  · simp only [Array.toList_append, List.mem_append] at hj
    rcases hj with hj | (hj | hj) | hj
    · exact hst j hj
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hj
      exact tiedI_of_oneSrc rfl
    · rw [physExpandR_eq] at hj
      refine physExpand_tiedI _ _ _ mbr (fun n => ?_) i (hflag i hi) j hj
      dsimp only
      split <;> exact ⟨_, rfl⟩
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hj
      exact tiedI_of_oneSrc rfl
  · simp only [Array.toList_append, List.mem_append] at hj
    rcases hj with hj | hj
    · exact hst j hj
    · rw [physExpandR_eq] at hj
      exact physExpand_tiedI _ _ _ mbr (fun n => ⟨_, rfl⟩) i (hflag i hi) j hj

/-- Quiet operations refine the empty block. -/
theorem cmpRefines_quiet_nil {q : Lcmd}
    (h : ∀ j ∈ q, isOpnB j.li_i = true ∧ isCmpB j.li_i = false ∧ isMemB j.li_i = false) :
    CmpRefines q [] := by
  simpa using cmpRefines_quietOps_left h (CmpRefines.refl [])

/-- **A fold that appends a refining chunk per instruction refines the instructions.** -/
theorem cmpRefines_foldl {β : Type} (f : Array Linstr × β → Linstr → Array Linstr × β)
    (body : Lcmd)
    (hf : ∀ st i, i ∈ body → ∃ c, (f st i).1 = st.1 ++ c.toArray ∧ CmpRefines c [i]) :
    ∀ (l : Lcmd), (∀ i ∈ l, i ∈ body) → ∀ (st : Array Linstr × β) (A : Lcmd),
      CmpRefines st.1.toList A → CmpRefines (l.foldl f st).1.toList (A ++ l)
  | [], _, st, A, h => by simpa using h
  | i :: l, hl, st, A, h => by
    obtain ⟨c, hc, hr⟩ := hf st i (hl i List.mem_cons_self)
    have := cmpRefines_foldl f body hf l (fun j hj => hl j (List.mem_cons_of_mem _ hj)) (f st i)
      (A ++ [i]) (by rw [hc, Array.toList_append, List.toList_toArray]; exact h.append hr)
    simpa using this

/-- The fold from the empty array refines the instructions. -/
theorem cmpRefines_foldl_nil {β : Type} (f : Array Linstr × β → Linstr → Array Linstr × β)
    (body : Lcmd)
    (hf : ∀ st i, i ∈ body → ∃ c, (f st i).1 = st.1 ++ c.toArray ∧ CmpRefines c [i])
    (b0 : β) : CmpRefines (body.foldl f (#[], b0)).1.toList body := by
  simpa using cmpRefines_foldl f body hf body (fun _ h => h) (#[], b0) []
    (by simpa using CmpRefines.refl ([] : Lcmd))

/-- **The body with split intervals refines the body** for `cmpAccFreeB`: each chunk is made
    of quiet moves around the expansion of the instruction. -/
theorem physBodySplit_cmpRefines (shiftImm : ShiftImmOracle) (body : Lcmd) (cfg : SplitCfg)
    (mbr : String → Option String) :
    CmpRefines (physBodySplit shiftImm body cfg mbr x86Abi) body := by
  unfold physBodySplit
  dsimp only
  generalize (bodySplitPieces body cfg x86Abi).foldl _ _ = byPos
  refine cmpRefines_foldl_nil _ body (fun st i _ => ?_) 0
  have hmov : ∀ (u : Bool) (d s : LOperand),
      isOpnB (Linstr.li_i ⟨0, .Lopn [d] (if u then "MOV:64" else "MOV") [s]⟩) = true ∧
        isCmpB (Linstr.li_i ⟨0, .Lopn [d] (if u then "MOV:64" else "MOV") [s]⟩) = false ∧
        isMemB (Linstr.li_i ⟨0, .Lopn [d] (if u then "MOV:64" else "MOV") [s]⟩) = false := by
    intro u d s
    refine ⟨rfl, ?_⟩
    cases u
    · exact quiet_of_mn (by decide +kernel) (by decide +kernel)
    · exact quiet_of_mn (by decide +kernel) (by decide +kernel)
  split
  · refine ⟨_, rfl, show CmpRefines _ ([] ++ [i] ++ []) from ?_⟩
    refine ((cmpRefines_quiet_nil fun j hj => ?_).append ?_).append
      (cmpRefines_quiet_nil fun j hj => ?_)
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hj
      exact hmov _ _ _
    · rw [physExpandR_eq]
      exact cmpRefines_physExpand _ _ _ mbr i
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hj
      exact hmov _ _ _
  · exact ⟨_, rfl, by rw [physExpandR_eq]; exact cmpRefines_physExpand _ _ _ mbr i⟩

/-! ## 2. The physical ABI export with split intervals -/

/-- The body of the call-free physical ABI export with split intervals: the prologue, the
    saves, the argument materialization and the epilogue around the reload of the body with
    split intervals without its `LIVEPIN` instructions. -/
theorem lfundefPhysAbiOfVirtCert_split_body
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (splitCfg : Lcmd → Option SplitCfg) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (cfg : SplitCfg) (hcfg : splitCfg body1 = some cfg) :
    ∃ sh mbr, (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind [] splitCfg).1.lfd_body =
      (buildPrologue { virt0 with lfd_body := body1 }
          (physTableOut body1 [] [] x86Abi (some cfg)) (fun _ => none) ++ extraSaves abiArgs) ++
        buildArgPtrMaterialize { virt0 with lfd_body := body1 }
            (physTableOut body1 [] [] x86Abi (some cfg)) abiArgs (fun _ => none) ++
          insertEpilogue (reloadArrImmBody mbr ((physBodySplit sh body1 cfg mbr x86Abi).filter
              notLivePin))
            calleeSaveRestoreEpilogue := by
  subst hb1
  simp only [lfundefPhysAbiOfVirtCert, hcfg]
  exact ⟨_, _, rfl⟩

/-- **The tied flag compares of the call-free physical ABI export with split intervals** when
    every instruction of the allocator input `body1` has the flag form. -/
theorem flagTiedB_lfundefPhysAbiOfVirtCert_split
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (splitCfg : Lcmd → Option SplitCfg) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (cfg : SplitCfg) (hcfg : splitCfg body1 = some cfg)
    (hflag : ∀ i ∈ body1, FlagForm i.li_i) :
    flagTiedB (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind [] splitCfg).1.lfd_body = true := by
  obtain ⟨sh, mbr, hb⟩ := lfundefPhysAbiOfVirtCert_split_body virt0 outArg' inArgs' accRegs
    shiftImm abiArgs abiTyin posBind splitCfg body1 hb1 cfg hcfg
  rw [hb]
  refine flagTiedB_iff.mpr fun j hj => ?_
  simp only [insertEpilogue, List.mem_append, or_assoc] at hj
  rcases hj with hj | hj | hj | hj | hj | hj
  · exact tiedI_of_slotMov ((prologue_moves _ _ abiArgs).1 j (List.mem_append_left _ hj))
  · exact tiedI_of_slotMov ((prologue_moves virt0 #[] abiArgs).1 j
      (List.mem_append_right (buildPrologue virt0 #[] (fun _ => none)) hj))
  · unfold buildArgPtrMaterialize at hj
    obtain ⟨⟨abiReg, k⟩, -, hj⟩ := List.mem_flatMap.mp hj
    simp only at hj
    split at hj
    · simp at hj
    · split_ifs at hj <;>
        rcases hs : abiSlotOfExt abiReg with _ | s <;>
        simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hj <;>
        (try rcases hj with rfl | rfl) <;> exact tiedI_of_one rfl
  · rcases mem_reloadArrImmBody (List.dropLast_subset _ hj) with hj | ⟨i', -, l', hl, -, hx⟩
    · exact physBodySplit_tiedI sh body1 cfg mbr hflag j (List.mem_of_mem_filter hj)
    · obtain ⟨b, q, -, ⟨n, w, -, rfl⟩ | ⟨d, v, k, -, rfl⟩⟩ := reloadArrImm_eq_some hl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with hx | hx
        all_goals try (rcases ptrLoad_cases q with hp | hp <;> rw [hp] at hx)
        all_goals first
          | exact tiedI_of_one hx
          | (intro d' opn x c he _; rw [hx] at he; simp at he)
      rcases List.mem_cons.mp hx with hx | hx
      · rcases ptrLoad_cases q with hp | hp <;> rw [hp] at hx <;> exact tiedI_of_one hx
      rcases mem_storeImmVia hx with hx | hx | hx
      · exact tiedI_of_one hx
      all_goals (intro d' opn x c he _; rw [hx] at he; simp at he)
  · simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> exact tiedI_of_one rfl
  · rw [List.mem_singleton.mp hj]
    intro d opn x c he
    cases he

/-- **`cmpAccFreeB` on the call-free physical ABI export with split intervals** when the
    allocator input `body1` passes `cmpAccFreeB`. -/
theorem cmpAccFreeB_lfundefPhysAbiOfVirtCert_split
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (splitCfg : Lcmd → Option SplitCfg) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (cfg : SplitCfg) (hcfg : splitCfg body1 = some cfg)
    (hacc : cmpAccFreeB false body1 = true) :
    cmpAccFreeB false (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind [] splitCfg).1.lfd_body = true := by
  obtain ⟨sh, mbr, hb⟩ := lfundefPhysAbiOfVirtCert_split_body virt0 outArg' inArgs' accRegs
    shiftImm abiArgs abiTyin posBind splitCfg body1 hb1 cfg hcfg
  rw [hb]
  have hlp : ∀ j ∈ physBodySplit sh body1 cfg mbr x86Abi,
      notLivePin j = false → isOpnB j.li_i = true := by
    intro j _ hj
    unfold notLivePin at hj
    split at hj
    · rename_i ds o ss he
      rw [he]
      rfl
    · cases hj
  have hF := (((cmpRefines_reloadArrImmBody mbr _).trans
    (cmpRefines_filter notLivePin hlp)).trans (physBodySplit_cmpRefines sh body1 cfg mbr)).final
    hacc
  have hP : ∀ j ∈ buildPrologue { virt0 with lfd_body := body1 }
      (physTableOut body1 [] [] x86Abi (some cfg)) (fun _ => none) ++ extraSaves abiArgs,
      QuietI j :=
    fun j hj => quietI_of_slotMov ((prologue_moves _ _ abiArgs).1 j hj)
  have hM : ∀ j ∈ buildArgPtrMaterialize { virt0 with lfd_body := body1 }
      (physTableOut body1 [] [] x86Abi (some cfg)) abiArgs (fun _ => none), QuietI j := by
    intro r hr
    unfold buildArgPtrMaterialize at hr
    obtain ⟨⟨abiReg, j⟩, -, hr⟩ := List.mem_flatMap.mp hr
    simp only at hr
    split at hr
    · simp at hr
    · split_ifs at hr <;>
        rcases hs : abiSlotOfExt abiReg with _ | s <;>
        simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
        (try rcases hr with rfl | rfl) <;>
        exact quiet_of_mn (by decide +kernel) (by decide +kernel)
  have hE : ∀ j ∈ calleeSaveRestoreEpilogue ++ [(⟨0, .Lret⟩ : Linstr)], QuietI j := by
    intro j hj
    simp only [calleeSaveRestoreEpilogue, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide +kernel, by decide +kernel⟩
  have hT := cmpAccFreeB_quiet_right (cmpAccFreeB_dropLast _ hF) hE
  rw [← List.append_assoc] at hT
  unfold insertEpilogue
  rw [List.append_assoc]
  exact cmpAccFreeB_quiet_left hP (cmpAccFreeB_quiet_left hM hT)

/-! ## 3. The flag form and the closed compares of an exported code -/

/-- The renaming of the array positions at each position refines the code for `cmpAccFreeB`. -/
theorem cmpRefines_mapIdx_renArr :
    ∀ (C : List LinstrRM) (f : Nat → LinstrRM → String → String),
    CmpRefines ((C.mapIdx fun k i => renArr (f k i) i).map toL) (C.map toL)
  | [], _ => CmpRefines.refl _
  | i :: C, f => by
    rw [List.mapIdx_cons, List.map_cons, List.map_cons]
    refine (cmpRefines_one_of_mn (i := toL i) (j := toL (renArr (f 0 i) i))
      fun ds o ss he => ?_).append (cmpRefines_mapIdx_renArr C fun k => f (k + 1))
    obtain ⟨ds', ss', hi, -⟩ := renArr_lopn (f 0 i) he
    exact ⟨ds', ss', hi⟩

/-- The webs of a closed code are closed. -/
theorem cmpClosed_regionWebs (ex : List String) (r0 : Exported)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) (h : CmpClosed r0.code) :
    CmpClosed (regionWebs ex r0 aa ao).code := by
  rcases regionWebs_cases ex r0 aa ao with he | ⟨w, he⟩ <;> rw [he]
  · exact h
  · unfold X86Backend.ArrWebs.webRen
    obtain ⟨h1, h2⟩ := cmpRefines_mapIdx_renArr r0.code (X86Backend.ArrWebs.stepRen w ao)
      false h.1
    exact ⟨h1, Bool.eq_false_iff.mpr fun ho => by simpa [h.2] using h2 ho⟩

/-- **An exported code is closed for `cmpAccFreeB`.** -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.cmpClosed {fn : String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {ex : List String} {r : Exported}
    (hr : RegionExp fn p ex r) (hp : regionExportableB p = true) (hc : p.callFree = true) :
    CmpClosed r.code := by
  obtain ⟨r0, h0, hr | hr⟩ := hr <;> subst r
  · exact exportR_cmpClosed _ _ p hp hc _ _ r0 h0
  · exact cmpClosed_regionWebs ex r0 _ _ (exportR_cmpClosed _ _ p hp hc _ _ r0 h0)

/-- **Every instruction of an exported code has the flag form.** -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.flagForm {fn : String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {ex : List String} {r : Exported}
    (hr : RegionExp fn p ex r) : ∀ i ∈ r.code, FlagForm i.1 := by
  obtain ⟨r0, h0, hr | hr⟩ := hr <;> subst r
  · exact exportR_flagForm _ _ p _ _ r0 h0
  · exact forall_mem_regionWebs (fun σ i hi => flagForm_renArr σ hi) ex r0 _ _
      (exportR_flagForm _ _ p _ _ r0 h0)

/-! ## 4. The allocator input -/

/-- **The flag form of the allocator input body** of a code whose instructions have the flag
    form, for a result other than one register. -/
theorem flagForm_regionAllocBody_of (a : AbiNames) (nArgs : Nat) {ts : List JasminTy}
    (r : Exported) (hts : ∀ w, ts ≠ [.reg w]) (hr : ∀ i ∈ r.code, FlagForm i.1) :
    ∀ i ∈ regionAllocBody a nArgs ts r, FlagForm i.li_i := by
  have hC : ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res, FlagForm i.1 := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hr i hi
    · exact flagForm_regionLprogCopy a ts _ _ i hi
  have hac : ∀ i ∈ regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res),
      FlagForm i.1 := by
    refine flagForm_backEdgePins fun i hi => ?_
    rcases mem_pinSelfMoves hi with hi | ⟨t, c, z, _, _, _, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact flagForm_renArr _ (hC j hj)
    · exact flagForm_lopn (by decide)
    · exact flagForm_livepin _
  intro i hi
  unfold regionAllocBody at hi
  split at hi
  · exact absurd rfl (hts _)
  · rcases List.mem_append.mp hi with hi | hi
    · split at hi
      · rw [List.mem_singleton.mp hi]; exact flagForm_livepin _
      · cases hi
    · refine flagForm_canonicalizeMemrefThread (fun j hj => ?_) i hi
      rcases List.mem_append.mp hj with hj | hj
      · unfold arrBasePins at hj
        dsimp only at hj
        split at hj
        · cases hj
        · rw [List.mem_singleton.mp hj]; exact flagForm_livepin _
      · rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hj
          exact hac l hl
        · rw [List.mem_singleton.mp hj]
          exact flagForm_nonLopn fun _ _ _ e => by cases e

/-- **`cmpAccFreeB` on the allocator input body** of a closed code, for a result other than
    one register. -/
theorem cmpAccFreeB_regionAllocBody_of (a : AbiNames) (nArgs : Nat) {ts : List JasminTy}
    (r : Exported) (hts : ∀ w, ts ≠ [.reg w]) (hr : CmpClosed r.code) :
    cmpAccFreeB false (regionAllocBody a nArgs ts r) = true := by
  have hC : CmpClosed (r.code ++ regionLprogCopy a none ts r.code r.res) :=
    cmpClosed_append hr (cmpClosed_of_noCmp (noCmp_regionLprogCopy a ts _ _))
  have hac := (cmpRefines_regionAllocCode
    (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res)).final hC.1
  have hbody : cmpAccFreeB false
      (arrBasePins a (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res))
        ++ ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res)).map
          (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩])) = true := by
    refine cmpAccFreeB_quiet_left (fun j hj => ?_)
      (cmpAccFreeB_quiet_right hac fun j hj => ?_)
    · unfold arrBasePins at hj
      dsimp only at hj
      split at hj
      · cases hj
      · rw [List.mem_singleton.mp hj]; exact quietI_livepin _ _
    · rw [List.mem_singleton.mp hj]; exact ⟨rfl, rfl⟩
  unfold regionAllocBody
  split
  · exact absurd rfl (hts _)
  · refine cmpAccFreeB_quiet_left (fun j hj => ?_)
      ((cmpRefines_canonicalizeMemrefThread _).final hbody)
    split at hj
    · rw [List.mem_singleton.mp hj]; exact quietI_livepin _ _
    · cases hj

/-- **The hypothesis `hidx`** of `RegionPhysImgSplitSide.sideAlloc_regionAllocFnSplit`: when
    every instruction of the code given to the renaming has the access form `AccCode`, the
    instructions of the allocator input body other than its accesses have no register-indexed
    operand. -/
theorem noIdxB_regionAllocBody (a : AbiNames) (nArgs : Nat) {ts : List JasminTy}
    (r : Exported) (hts : ∀ w, ts ≠ [.reg w])
    (hC : ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res,
      RegionPhysImgArg.AccCode i) :
    ∀ i ∈ regionAllocBody a nArgs ts r, isAccB i.li_i = false →
      ∀ x ∈ lopnOperands i.li_i, noIdxB x = true := fun i hi hA =>
  RegionPhysImgSide.noIdxB_of_idxAcc (RegionPhysImgSide.idxAcc_regionAllocBody _ _ r hts hC i hi)
    hA

/-! ## 5. The allocated function with split intervals -/

open RegionPhysImgSplit (regionAllocFnSplit)

/-- The allocator input body of an exported code at a result other than one register, in the
    form taken by the physical ABI export. -/
theorem regionAllocBody_eq (a : AbiNames) (nArgs : Nat) {ts : List JasminTy} (r : Exported)
    (hts : ∀ w, ts ≠ [.reg w]) :
    regionAllocBody a nArgs ts r =
      (if a.abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range a.abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (([] : List String).foldl (fun b r => aliasRegBody r a.outArg b)
            (arrBasePins a (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res))
              ++ ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res)).map
                (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]))) := by
  unfold regionAllocBody
  split
  · exact absurd rfl (hts _)
  · rfl

/-- **Conjunct 7 on the allocated function with split intervals**: for an exported code of a
    program without `call` that passes `regionExportableB`, with a result other than one
    register, every flag-only compare of the body of `regionAllocFnSplit` with a register first
    source is tied. -/
theorem flagTiedB_regionAllocFnSplit (fn : String) (a : AbiNames) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {ex : List String} {r : Exported} (hr : RegionExp fn p ex r)
    (hts : ∀ w, ts ≠ [.reg w]) (fd0 : Lfundef) :
    flagTiedB (regionAllocFnSplit a ts r fd0).lfd_body = true := by
  have hB : ∀ i ∈ regionAllocBody a Γ.length ts r, ShapeB i.li_i :=
    shapeB_regionAllocBody _ _ ts r fun i hi => (hr.mnemDom hp hc i hi).2.2
  have hcf := bodyHasCall_of_shapeB hB
  have hcfg : bodySplitOpt (regionAllocBody a Γ.length ts r) =
      some (bodySplitCfg (regionAllocBody a Γ.length ts r)) := by
    simp [bodySplitOpt, hcf]
  simp only [regionAllocFnSplit, calleeAllocCert]
  exact flagTiedB_lfundefPhysAbiOfVirtCert_split _ _ _ [] (fun _ => none) _ _ true bodySplitOpt
    _ (regionAllocBody_eq a Γ.length r hts) _ hcfg
    (flagForm_regionAllocBody_of a _ r hts hr.flagForm)

/-- **`cmpAccFreeB` on the allocated function with split intervals**: for an exported code of
    a program without `call` that passes `regionExportableB`, with a result other than one
    register, no indexed access of the body of `regionAllocFnSplit` follows a compare with only
    operations between them. -/
theorem cmpAccFreeB_regionAllocFnSplit (fn : String) (a : AbiNames) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {ex : List String} {r : Exported} (hr : RegionExp fn p ex r)
    (hts : ∀ w, ts ≠ [.reg w]) (fd0 : Lfundef) :
    cmpAccFreeB false (regionAllocFnSplit a ts r fd0).lfd_body = true := by
  have hB : ∀ i ∈ regionAllocBody a Γ.length ts r, ShapeB i.li_i :=
    shapeB_regionAllocBody _ _ ts r fun i hi => (hr.mnemDom hp hc i hi).2.2
  have hcf := bodyHasCall_of_shapeB hB
  have hcfg : bodySplitOpt (regionAllocBody a Γ.length ts r) =
      some (bodySplitCfg (regionAllocBody a Γ.length ts r)) := by
    simp [bodySplitOpt, hcf]
  simp only [regionAllocFnSplit, calleeAllocCert]
  exact cmpAccFreeB_lfundefPhysAbiOfVirtCert_split _ _ _ [] (fun _ => none) _ _ true
    bodySplitOpt _ (regionAllocBody_eq a Γ.length r hts) _ hcfg
    (cmpAccFreeB_regionAllocBody_of a _ r hts (hr.cmpClosed hp hc))

open RegionPhysImgGate (postBody reallocStage physImgSideB)
open X86Backend.PhysImgOpt (optSideB)
open X86Backend.LprogOptPipeline (splitStraightRuns)
open X86Backend.FuseMulHi (fuseMulHiBody)
open X86Backend.PhysImgSidePass (memMovFreeB)
open X86Backend.ImageAddrRoute (slotArrOf slotRen)
open X86Backend.ImageStraightCells (slotArrC)
open VIR.JasminLsemRenameLoop (renOf)
open RegionPhysImg (AccArg)

/-- **The side conditions of the region gate on the allocated function with split intervals
    from the optimizer conditions.** Under the hypotheses of
    `RegionPhysImgSplitSide.sideAlloc_regionAllocFnSplit`, `physImgSideB sl res b0` holds for
    the body `b0` and the result names `res` of `regionAllocFnSplit` when the optimizer
    condition holds on every straight run of the post-pass body (`hopt`) and no 64-bit move of
    the post-pass body is between two memory names (`hhold`). -/
theorem physImgSideB_of_exportSplit_opt (fname : String) (σ : AbiLayout)
    {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {ex : List String} {r : Exported}
    (hr : RegionExp fname p ex r)
    (hts : ∀ w, ts ≠ [.reg w]) (fd0 : Lfundef)
    (hnd : (σ.args.map fun a => exportReg a.reg).Nodup)
    (hacc : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r, AccArg σ i.li_i)
    (harr : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r, ∀ q n,
      LOperand.arr q n ∈ lopnOperands i.li_i → hasPrefix q "qsave." = false)
    (hidx : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r,
      isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true)
    (hne : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r, ∀ ds o ss,
      i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM")
    (R : X86Backend.ImageCellFold.Slots) (ps : List (String × String))
    (hopt : (splitStraightRuns
      (postBody (regionAllocFnSplit (nfAbiNames fname σ) ts r fd0).lfd_body)).all
      (optSideB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))) = true)
    (hhold : memMovFreeB (postBody (regionAllocFnSplit (nfAbiNames fname σ) ts r fd0).lfd_body)
      = true) :
    physImgSideB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
      (regionAllocFnSplit (nfAbiNames fname σ) ts r fd0).lfd_res
      (regionAllocFnSplit (nfAbiNames fname σ) ts r fd0).lfd_body = true := by
  obtain ⟨h1, h2, hcell, hmul, hcopy⟩ :=
    RegionPhysImgSplitSide.sideAlloc_regionAllocFnSplit fname σ p hp hc hr hts fd0 hnd hacc
      harr hidx hne R ps
  have hq := RegionPhysImg.regionSl_qsave R σ exportReg (renOf ps)
  have hs := RegionPhysImgSide.deadWriteRet_sublist
    (fuseMulHiBody (regionAllocFnSplit (nfAbiNames fname σ) ts r fd0).lfd_body true)
  simp only [physImgSideB, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hopt⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact X86Backend.PhysImgSidePass.copyNoSlotB_postOpt hq hcopy hmul hs hhold
  · exact X86Backend.PhysImgSidePass.cellBaseFreeB_postOpt hcell hs
  · rw [RegionPhysImgSplitSide.regionAllocFnSplit_lfd_res]; rfl
  · exact X86Backend.PhysImgSidePass.flagTiedB_reallocStage _
      (flagTiedB_regionAllocFnSplit fname _ p hp hc hr hts fd0) hs
  · exact cmpScratchFreeB_twoAddrBody _
      (cmpAccFreeB_regionAllocFnSplit fname _ p hp hc hr hts fd0) (cmpRefines_deadWriteRet _)
  · exact X86Backend.PhysImgSidePass.cellBaseFreeB_printedChain _ hcell hs

/-! ## 6. The field domain -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (NoCArr)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg (ArgSlotName
  noArrImm_regionLprogCopy exportR_noCArr noCArr_renArr accP_regionAllocBody accArg_of_accP
  arrNamed_nfCtx noArrImm_regionAllocBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomPhysImg (FieldPhysImgSide noArrImm_of_plain
  fieldDom_physImgB_of_side)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (fieldAbi)
open CatCrypt.Crypto.Hax (HaxModule)

/-- **The optimizer condition on a member of the field domain**: at the data of
    `FieldPhysImgSide`, the optimizer condition `optSideB` holds on every straight run of the
    post-pass body of the allocated function `regionAllocFnSplit` of the webs at the slot map of
    the parts `regionCoParts` of the gate. -/
def FieldOptSide (e : _root_.Hax.TExpr) (σ : AbiLayout) (fname : String) : Prop :=
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
    (splitStraightRuns (postBody (regionAllocFnSplit (nfAbiNames fname σ)
        [NarrowWords.wideTy t0] (regionWebsAt (regionWebsEx σ exportReg) none r0)
          fd0).lfd_body)).all
      (optSideB (slotArrC (regionCoParts σ exportReg b (NarrowWords.wideTy t0)
          (regionWebsAt (regionWebsEx σ exportReg) none r0).code
          (regionWebsAt (regionWebsEx σ exportReg) none r0).res cert).cells
        (slotRen (slotArrOf σ exportReg)
          (renOf (regionCoParts σ exportReg b (NarrowWords.wideTy t0)
            (regionWebsAt (regionWebsEx σ exportReg) none r0).code
            (regionWebsAt (regionWebsEx σ exportReg) none r0).res cert).ps)))) = true

/-- **The holder condition on a member of the field domain**: no 64-bit move of the post-pass
    body of the allocated function `regionAllocFnSplit` of the webs of the export is between two
    memory names. -/
def FieldMemMovFree (e : _root_.Hax.TExpr) (σ : AbiLayout) (fname : String) : Prop :=
  ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
    (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0])
    (r0 : Exported) (fd0 : Lfundef),
    haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩ →
    NarrowWords.narrowPrep q = some q' →
    exportR ((nfCtx σ).map NarrowWords.wideTy).length fname (legalizeRegion q')
      ((nfCtx σ).map NarrowWords.wideTy).length 0 = some r0 →
    exportRLfundef fname (legalizeRegion q') = some fd0 →
    memMovFreeB (postBody (regionAllocFnSplit (nfAbiNames fname σ) [NarrowWords.wideTy t0]
      (regionWebsAt (regionWebsEx σ exportReg) none r0) fd0).lfd_body) = true

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String}

/-- **The side conditions of the printer passes on `fieldDomB''` from the optimizer
    conditions**: `FieldPhysImgSide` holds under the optimizer condition `FieldOptSide` and the
    holder condition `FieldMemMovFree`. -/
theorem fieldPhysImgSide_of_opt (h : fieldDomB'' e σ = true) (hopt : FieldOptSide e σ fname)
    (hhold : FieldMemMovFree e σ fname) : FieldPhysImgSide e σ fname := by
  intro t0 q q' r0 P cert b fd0 hq hq' hr0 hP hb hfd
  have ho := hopt t0 q q' r0 P cert b fd0 hq hq' hr0 hP hb hfd
  have hh := hhold t0 q q' r0 fd0 hq hq' hr0 hfd
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
  rw [regionWebsAt_none] at ho hh ⊢
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
      AccArg (fieldAbi k n) i.li_i := fun i hi =>
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
      [NarrowWords.wideTy (.stackArr 64 n)] (regionWebs ex r0), ∀ ds o ss,
        i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM" := by
    refine noArrImm_regionAllocBody _ _ _ hts' fun i hi => ?_
    rcases List.mem_append.mp hi with hi' | hi'
    · exact ⟨noArrImm_of_plain (hI i hi) (hplain i hi'), hshape i hi'⟩
    · exact ⟨noArrImm_regionLprogCopy _ _ _ _ i hi', shapeB_regionLprogCopy _ _ _ _ i hi'⟩
  exact physImgSideB_of_exportSplit_opt fname (fieldAbi k n) (legalizeRegion q') hEx hcf
    (regionExp_webs ex hr0) hts' fd0 hnd hacc harr (noIdxB_regionAllocBody _ _ _ hts' hC) hne
    _ _ ho hh

/-- **Stage `G16` on `fieldDomB''` from the optimizer conditions**: the region gate does not
    name `physImgB` as the refusing stage on a printed body of a member of `fieldDomB''` under
    the optimizer condition `FieldOptSide` and the holder condition `FieldMemMovFree`. -/
theorem fieldDom_physImgB_of_opt (hopt : FieldOptSide e σ fname)
    (hhold : FieldMemMovFree e σ fname) {b : Lcmd} {t : JasminTy} {r : Exported}
    {cert : List (String × String)} (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "physImgB" :=
  fieldDom_physImgB_of_side (fieldPhysImgSide_of_opt h hopt hhold) h hB

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomPhysImgSide
