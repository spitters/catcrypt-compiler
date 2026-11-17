/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSplit
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSide

/-!
# The side conditions of the region gate on the allocated function with split intervals

This module proves the side conditions `physImgSideB` of the region gate, as in
`RegionPhysImgSide`, on the allocated function `regionAllocFnSplit` of the region route at the
split configuration `bodySplitOpt`.

The body with split intervals `physBodySplit` writes for each operation the moves of the cells
of the pieces into their registers, the expansion `physExpandR` of the operation under a
renaming `RkReg` that sends an operand through the allocation table or a register name to an
allocated register, and the moves back. The moves are plain; the expansion is `physExpand`
(`physExpandR_eq`), whose side conditions `PhysImgSideAlloc` and `RegionPhysImgSide` prove
under such a renaming. So the body is `SideOk` by induction over the fold of `physBodySplit`.

## Main results

* `physExpandR_eq`: the expansion with split intervals is `physExpand`.
* `physBodySplit_sideOk`: the body with split intervals without its `LIVEPIN` instructions keeps
  its scans, satisfies the home condition and has no cell base, no high product and no 64-bit
  copy reading an array slot.
* `sideAlloc_lfundefPhysAbiOfVirtCert_split`, `sideAlloc_regionAllocFnSplit`: the conditions
  of the fusion and the fold on the physical ABI export with split intervals and on
  `regionAllocFnSplit`.
* `physImgSideB_of_exportSplit`: `physImgSideB` on `regionAllocFnSplit` from the optimizer
  condition, the holder condition, the condition `noScratchBaseB` and the tied flag compares.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSplitSide

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideOpt (GoodOp)

/-! ## 1. The expansion with split intervals -/

/-- `physExpandR` is the expansion `physExpand` case by case (`physExpand_eq`). -/
theorem physExpandR_eq (shiftImm : ShiftImmOracle) (u64 : Bool) (rm : LOperand → LOperand)
    (mbr : String → Option String) (i : Linstr) :
    physExpandR shiftImm u64 rm mbr i = physExpand shiftImm u64 rm mbr i := by
  rw [physExpand_eq]
  rfl

/-- A renaming that sends an operand through the allocation table `rmap` or a register name to
    an allocated register. -/
def RkReg (body : Lcmd) (tbl : Array Nat) (rk : LOperand → LOperand) : Prop :=
  ∀ x, rk x = remapOperand body tbl x ∨ ∃ nm ph, x = .reg nm ∧ rk x = .reg (physRegName ph x86Abi)

section Rk

variable {slotArr : String → Option (String × Nat)} {body : Lcmd} {tbl : Array Nat}
  {rk : LOperand → LOperand}

/-- An `RkReg` renaming keeps operands without index. -/
theorem RkReg.noIdx (h : RkReg body tbl rk) :
    ∀ x, noIdxB x = true → noIdxB (rk x) = true := by
  intro x hx
  rcases h x with e | ⟨nm, ph, -, e⟩ <;> rw [e]
  · exact noIdxB_remapOperand _ _ hx
  · rfl

/-- An `RkReg` renaming sends registers to registers. -/
theorem RkReg.reg (h : RkReg body tbl rk) : ∀ n, ∃ n', rk (.reg n) = .reg n' := by
  intro n
  rcases h (.reg n) with e | ⟨nm, ph, -, e⟩ <;> rw [e]
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The register images of an `RkReg` renaming are no reload scratches and no array slots. -/
theorem RkReg.regOk (hP : ∀ p, slotArr (physRegName p x86Abi) = none) (h : RkReg body tbl rk) :
    ∀ x n, rk x = .reg n → n ∉ X86Backend.FuseMulHi.fuseReloadScratches ∧
      slotArr n = none := by
  intro x n hx
  rcases h x with e | ⟨nm, ph, -, e⟩ <;> rw [e] at hx
  · cases x with
    | reg m =>
      simp only [remapOperand, LOperand.reg.injEq] at hx
      subst hx
      exact ⟨physRegName_not_scratch _, hP _⟩
    | _ => simp [remapOperand] at hx
  · cases hx
    exact ⟨physRegName_not_scratch _, hP _⟩

/-- The image of an operand naming no array slot under an `RkReg` renaming is `OperandOk`. -/
theorem RkReg.operandOk (hP : ∀ p, slotArr (physRegName p x86Abi) = none)
    (h : RkReg body tbl rk) (x : LOperand) (harr : ∀ q n, x = .arr q n → slotArr q = none) :
    OperandOk slotArr (rk x) := by
  rcases h x with e | ⟨nm, ph, -, e⟩ <;> rw [e]
  · exact RegionPhysImgSplit.operandOk_remapOperand hP _ _ x harr
  · exact ⟨fun q hq => by cases hq; exact hP _, nofun, nofun⟩

/-- Every image of an `RkReg` renaming names no array slot. -/
theorem RkReg.goodOp (hP : ∀ p, slotArr (physRegName p x86Abi) = none)
    (h : RkReg body tbl rk) (x : LOperand) : GoodOp slotArr (rk x) := by
  rcases h x with e | ⟨nm, ph, -, e⟩ <;> rw [e]
  · cases x <;> simp [remapOperand, GoodOp, hP]
  · exact hP _

/-- The access form under the table passes to an `RkReg` renaming. -/
theorem RkReg.accForm {mbr : String → Option String} {i : LinstrR} (h : RkReg body tbl rk)
    (hne : ∀ ds o ss, i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM")
    (hacc : AccForm slotArr (fun o => remapOperand body tbl o) mbr i) :
    AccForm slotArr rk mbr i := by
  refine RegionPhysImgSplit.accForm_of_agree (fun b y => ?_) hne hacc
  rcases h (.arrIdx b y 8) with e | ⟨nm, ph, he, -⟩
  · exact e
  · cases he

end Rk

/-! ## 2. The side conditions on the body with split intervals -/

open X86Backend.PhysImgFuse (mulHiSiteB homeOkB)
open X86Backend.PhysImgSidePass (CellOk)
open RegionPhysImgSide (MulHiOk CopyOkR)
open X86Backend.PhysImgFuse (fuseSiteOkB dstOkB)
open X86Backend.PhysImgFold (cellBaseFreeB copyNoSlotB)
open X86Backend.PhysImgSidePass (mulHiNoSlotB)

/-- **The side conditions of a part of the body**: its scans stay inside it, so do the scans
    of every suffix behind a site, `homeOkB` holds from every environment of reload scratches,
    and every instruction has no cell base, no high product and no 64-bit copy reading an
    array slot. -/
def SideOk (slotArr : String → Option (String × Nat)) (L : Lcmd) : Prop :=
  ScanStays slotArr L ∧ SiteStays slotArr L ∧
    (∀ env, EnvScratch env → homeOkB slotArr env L = true) ∧
    ∀ j ∈ L, CellOk j ∧ MulHiOk slotArr j.li_i ∧ CopyOkR slotArr j.li_i

section Side

variable {slotArr : String → Option (String × Nat)}

/-- `SideOk` is kept by concatenation. -/
theorem SideOk.append {a b : Lcmd} (ha : SideOk slotArr a) (hb : SideOk slotArr b) :
    SideOk slotArr (a ++ b) := by
  refine ⟨ha.1.append hb.1, ha.2.1.append hb.2.1 hb.1, fun env he => ?_, fun j hj => ?_⟩
  · rw [homeOkB_append, ha.2.2.1 env he, Bool.true_and]
    exact hb.2.2.1 _ (envScratch_foldl he _)
  · rcases List.mem_append.mp hj with hj | hj
    · exact ha.2.2.2 j hj
    · exact hb.2.2.2 j hj

/-- The empty body is `SideOk`. -/
theorem SideOk.nil : SideOk slotArr [] :=
  ⟨ScanStays.nil, SiteStays.nil, fun _ _ => rfl, fun _ hj => by cases hj⟩

/-- A list of moves between allocated registers under `MOV` or `MOV:64` is `SideOk`. -/
theorem sideOk_moves (hP : ∀ p, slotArr (physRegName p x86Abi) = none) (u : Bool) (L : Lcmd)
    (h : ∀ j ∈ L, ∃ a b, j.li_i = .Lopn [.reg (physRegName a x86Abi)]
      (if u then "MOV:64" else "MOV") [.reg (physRegName b x86Abi)]) :
    SideOk slotArr L := by
  have hpl : ∀ j ∈ L, PlainB j := fun j hj => by
    obtain ⟨a, b, e⟩ := h j hj
    exact plainB_of_mov e (by rw [e]; cases u <;> rfl)
  refine ⟨scanStays_of_idxFree fun r hr => (hpl r hr).2.1,
    SiteStays.of_noSite fun r hr => (hpl r hr).1,
    fun env _ => homeOkB_of_noLowMul (fun r hr => (hpl r hr).2.2) env, fun j hj => ⟨?_, ?_, ?_⟩⟩
  · exact RegionPhysImgSide.cellOk_of_baseR14
      (RegionPhysImgSide.baseR14_of_idxFree (hpl j hj).2.1.1)
      (RegionPhysImgSide.immBaseR14_of_ne (hpl j hj).2.1.2)
  · exact RegionPhysImgSide.mulHiOk_of_site (hpl j hj).1
  · intro d x he
    obtain ⟨a, b, e⟩ := h j hj
    rw [e] at he
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at he
    rw [← he.2.2]
    exact hP _

/-- **One expansion with split intervals is `SideOk`** without its `LIVEPIN` instructions,
    under a renaming `RkReg` through the table or to allocated registers. -/
theorem sideOk_expand {body : Lcmd} {tbl : Array Nat}
    (hs15 : slotArr reloadScratch = none) (hs14 : slotArr reloadScratch2 = none)
    (hmem : ∀ c, slotArr ("mem." ++ c) = none)
    (hP : ∀ p, slotArr (physRegName p x86Abi) = none)
    (shiftImm : ShiftImmOracle) (u64 : Bool) (rk : LOperand → LOperand)
    (mbr : String → Option String) (i : Linstr) (hrk : RkReg body tbl rk)
    (hacc : AccForm slotArr (fun o => remapOperand body tbl o) mbr i.li_i)
    (harr : ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → slotArr q = none)
    (hidx : isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true)
    (hne : ∀ ds o ss, i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM") :
    SideOk slotArr ((physExpandR shiftImm u64 rk mbr i).filter notLivePin) := by
  have hacc' := hrk.accForm hne hacc
  have hblk := RegionPhysImgSplit.physExpandR_blockOk shiftImm u64 rk mbr i hs15 hs14 hmem
    (fun x hx => hrk.operandOk hP x fun q n he => harr q n (he ▸ hx)) hrk.reg hacc' hne
  rw [physExpandR_eq] at hblk ⊢
  have hmn : MnemOk i.li_i (physExpand shiftImm u64 rk mbr i) :=
    fun r hr ds o ss he => (hblk.1 r hr ds o ss he).2
  obtain ⟨h1, h2, h3⟩ := physExpand_block hs15 shiftImm u64 rk mbr i hmn hrk.noIdx
    (hrk.regOk hP) hrk.reg hacc' hidx hne
  refine ⟨h1, h2, h3, fun j hj => ?_⟩
  replace hj := List.mem_of_mem_filter hj
  refine ⟨?_, ?_, ?_⟩
  · exact RegionPhysImgSide.cellOk_of_baseR14
      (RegionPhysImgSide.physExpand_baseR14 _ _ rk mbr i hrk.noIdx hrk.reg hacc' hidx j hj)
      (RegionPhysImgSide.immBaseR14_of_ne (physExpand_arrImmFree _ _ _ mbr i hne
        (fun ds o ss h => (hacc' ds o ss h).2.2.2.2) j hj))
  · obtain ⟨ii, w⟩ := i
    by_cases hw : ∃ ds o ss, w = .Lopn ds o ss ∧ X86Backend.FuseMulHi.isMulHiMnem o = true
    · obtain ⟨ds, o, ss, rfl, hm⟩ := hw
      exact RegionPhysImgSide.physExpand_mulHiOk _ _ rk mbr ii ds o ss hm
        (fun x n h => (hrk.regOk hP x n h).2) j hj
    · refine RegionPhysImgSide.mulHiOk_of_site (noSite_of_mnemOk hmn (fun o ho => ?_) j hj)
      cases w with
      | Lopn ds o' ss =>
        simp only [opnOf, Option.some.injEq] at ho
        subst ho
        cases hm : X86Backend.FuseMulHi.isMulHiMnem o'
        · rfl
        · exact absurd ⟨ds, o', ss, rfl, hm⟩ hw
      | _ => simp [opnOf] at ho
  · exact RegionPhysImgSide.physExpand_copyOk _ _ rk mbr i (hrk.goodOp hP) hs15 hs14 j hj

/-- **The body with split intervals is `SideOk`** without its `LIVEPIN` instructions: each
    chunk of an operation is made of moves between allocated registers and the expansion
    under a renaming `RkReg`. -/
theorem physBodySplit_sideOk (shiftImm : ShiftImmOracle) (body : Lcmd) (cfg : SplitCfg)
    (mbr : String → Option String)
    (hs15 : slotArr reloadScratch = none) (hs14 : slotArr reloadScratch2 = none)
    (hmem : ∀ c, slotArr ("mem." ++ c) = none)
    (hP : ∀ p, slotArr (physRegName p x86Abi) = none)
    (hacc : ∀ i ∈ body, AccForm slotArr
      (fun o => remapOperand body (physAllocTbl body [] [] x86Abi (some cfg)) o) mbr i.li_i)
    (harr : ∀ i ∈ body, ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → slotArr q = none)
    (hidx : ∀ i ∈ body, isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true)
    (hne : ∀ i ∈ body, ∀ ds o ss, i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM") :
    SideOk slotArr ((physBodySplit shiftImm body cfg mbr x86Abi).filter notLivePin) := by
  unfold physBodySplit
  dsimp only
  have hpos := FieldDomComplete.mem_byPos (bodySplitPieces body cfg x86Abi)
    (bodyTraceOut body []).length
  generalize (bodySplitPieces body cfg x86Abi).foldl _ _ = byPos at hpos ⊢
  refine FieldDomComplete.foldl_inv _ (fun st : Array Linstr × Nat =>
    SideOk slotArr (st.1.toList.filter notLivePin)) body (#[], 0) SideOk.nil ?_
  intro st i hi hst
  split
  · simp only [Array.toList_append, List.filter_append]
    let u := body.any fun j => match j.li_i with
      | .Lopn _ opn _ => hasSuffix opn ":64"
      | _ => false
    refine hst.append (((sideOk_moves hP u _ fun j hj => ?_).append
      (sideOk_expand hs15 hs14 hmem hP _ _ _ mbr i (fun x => ?_) (hacc i hi) (harr i hi)
        (hidx i hi) (hne i hi))).append (sideOk_moves hP u _ fun j hj => ?_))
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_of_mem_filter hj)
      obtain ⟨ph, he⟩ := FieldDomComplete.reg_of_mem_bodySplitPieces
        (hpos _ p (List.mem_filter.mp hp).1)
      exact ⟨ph, _, by rw [he]; rfl⟩
    · cases x with
      | reg nm =>
        dsimp only
        split
        · rename_i p hf
          obtain ⟨ph, he⟩ := FieldDomComplete.reg_of_mem_bodySplitPieces
            (hpos _ p (List.mem_of_find?_eq_some hf))
          exact Or.inr ⟨nm, ph, rfl, by rw [he]⟩
        · exact Or.inl rfl
      | _ => exact Or.inl rfl
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_of_mem_filter hj)
      obtain ⟨ph, he⟩ := FieldDomComplete.reg_of_mem_bodySplitPieces
        (hpos _ p (List.mem_filter.mp hp).1)
      exact ⟨_, ph, by rw [he]; rfl⟩
  · simp only [Array.toList_append, List.filter_append]
    exact hst.append (sideOk_expand hs15 hs14 hmem hP _ _ _ mbr i (fun x => Or.inl rfl)
      (hacc i hi) (harr i hi) (hidx i hi) (hne i hi))

/-- **The side conditions on a body made of a plain prefix `A`, a body `F` without its last
    instruction, and a plain tail `T`**, when `F` is `SideOk` and writes no array slot, `T`
    writes no array slot, and no instruction of `A` or `T` is a 64-bit copy reading an array
    slot. -/
theorem side_shape {A F T : Lcmd}
    (hA : ∀ r ∈ A, PlainB r ∧ CopyOkR slotArr r.li_i)
    (hT : ∀ r ∈ T, PlainB r ∧ CopyOkR slotArr r.li_i) (hF : SideOk slotArr F)
    (hD : ∀ r ∈ F, dstOkB slotArr r.li_i = true) (hDT : ∀ r ∈ T, dstOkB slotArr r.li_i = true) :
    fuseSiteOkB slotArr (A ++ (F.dropLast ++ T)) = true ∧
      homeOkB slotArr [] (A ++ (F.dropLast ++ T)) = true ∧
      cellBaseFreeB (A ++ (F.dropLast ++ T)) = true ∧
      mulHiNoSlotB slotArr (A ++ (F.dropLast ++ T)) = true ∧
      copyNoSlotB slotArr (A ++ (F.dropLast ++ T)) = true := by
  have hpt : ∀ j ∈ A ++ (F.dropLast ++ T),
      CellOk j ∧ MulHiOk slotArr j.li_i ∧ CopyOkR slotArr j.li_i := by
    have hpl : ∀ j, PlainB j → CopyOkR slotArr j.li_i →
        CellOk j ∧ MulHiOk slotArr j.li_i ∧ CopyOkR slotArr j.li_i := fun j h hc =>
      ⟨RegionPhysImgSide.cellOk_of_baseR14 (RegionPhysImgSide.baseR14_of_idxFree h.2.1.1)
        (RegionPhysImgSide.immBaseR14_of_ne h.2.1.2), RegionPhysImgSide.mulHiOk_of_site h.1, hc⟩
    intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact hpl j (hA j hj).1 (hA j hj).2
    rcases List.mem_append.mp hj with hj | hj
    · exact hF.2.2.2 j (List.dropLast_subset _ hj)
    · exact hpl j (hT j hj).1 (hT j hj).2
  refine ⟨fuseSiteOkB_shape (fun r hr => (hA r hr).1) (fun r hr => (hT r hr).1) hF.1 hF.2.1 hD
      hDT,
    homeOkB_shape (fun r hr => (hA r hr).1) (fun r hr => (hT r hr).1) hF.2.2.1,
    X86Backend.PhysImgSidePass.cellBaseFreeB_iff.mpr fun j hj => (hpt j hj).1,
    RegionPhysImgSide.mulHiNoSlotB_of fun j hj => (hpt j hj).2.1,
    X86Backend.PhysImgSidePass.copyNoSlotB_iff.mpr fun j hj => (hpt j hj).2.2⟩

end Side

/-! ## 3. The physical ABI export with split intervals -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)

/-- **The conditions of the fusion and the fold on the call-free physical ABI export with split
    intervals**: under the hypotheses of
    `RegionPhysImgSplit.physImgB_lfundefPhysAbiOfVirtCert_split` and `hidx` (the instructions of
    the allocator input other than its accesses have no register-indexed operand), the body
    satisfies `fuseSiteOkB`, `homeOkB` from the empty environment, `cellBaseFreeB`,
    `mulHiNoSlotB` and `copyNoSlotB`. -/
theorem sideAlloc_lfundefPhysAbiOfVirtCert_split {slotArr : String → Option (String × Nat)}
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (splitCfg : Lcmd → Option SplitCfg) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (cfg : SplitCfg) (hcfg : splitCfg body1 = some cfg)
    (mbr : String → Option String)
    (hmbr : mbr = fun base =>
      (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1
            (physTableOut body1 [] [] x86Abi (some cfg)) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hshape : ∀ i ∈ body1, AccForm slotArr
      (fun o => remapOperand body1 (physAllocTbl body1 [] [] x86Abi (some cfg)) o) mbr i.li_i)
    (harr : ∀ i ∈ body1, ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → slotArr q = none)
    (hidx : ∀ i ∈ body1, isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true)
    (hne : ∀ i ∈ body1, ∀ ds o ss, i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM")
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    let b := (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind [] splitCfg).1.lfd_body
    fuseSiteOkB slotArr b = true ∧ homeOkB slotArr [] b = true ∧ cellBaseFreeB b = true ∧
      mulHiNoSlotB slotArr b = true ∧ copyNoSlotB slotArr b = true := by
  intro b
  have hb : ∃ sh, b =
      (buildPrologue { virt0 with lfd_body := body1 }
          (physTableOut body1 [] [] x86Abi (some cfg)) (fun _ => none) ++ extraSaves abiArgs) ++
        buildArgPtrMaterialize { virt0 with lfd_body := body1 }
            (physTableOut body1 [] [] x86Abi (some cfg)) abiArgs (fun _ => none) ++
          insertEpilogue (reloadArrImmBody mbr ((physBodySplit sh body1 cfg mbr x86Abi).filter
              notLivePin))
            calleeSaveRestoreEpilogue := by
    subst hb1 hmbr
    simp only [b, lfundefPhysAbiOfVirtCert, hcfg]
    exact ⟨_, rfl⟩
  obtain ⟨sh, hb⟩ := hb
  have hs15 : slotArr reloadScratch = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hs14 : slotArr reloadScratch2 = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hmem : ∀ c, slotArr ("mem." ++ c) = none := fun c =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_mem c)
  have hP : ∀ p, slotArr (physRegName p x86Abi) = none := fun p =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_physRegName p)
  obtain ⟨hFd, -⟩ := RegionPhysImgSplit.physBodySplit_splitOk sh body1 cfg mbr hs15 hs14 hmem hP
    hshape harr hne
  have hF := physBodySplit_sideOk sh body1 cfg mbr hs15 hs14 hmem hP hshape harr hidx hne
  have hre : reloadArrImmBody mbr ((physBodySplit sh body1 cfg mbr x86Abi).filter notLivePin) =
      (physBodySplit sh body1 cfg mbr x86Abi).filter notLivePin :=
    reloadArrImmBody_eq_of_noArrImm mbr fun r hr => (hFd r (List.mem_of_mem_filter hr)).2
  rw [hb, hre]
  unfold insertEpilogue
  rw [List.append_assoc (List.dropLast _) calleeSaveRestoreEpilogue]
  refine side_shape (fun r hr => ?_) (fun r hr => ?_) hF
    (fun r hr => dstOkB_of_dstOk (hFd r (List.mem_of_mem_filter hr)).1)
    (fun r hr => ?_)
  · refine ⟨?_, ?_⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact prologue_plainB _ _ _ r hr
      · exact buildArgPtrMaterialize_plainB _ _ _ _ r hr
    · simp only [List.mem_append] at hr
      rcases hr with (hr | hr) | hr
      · simp only [buildPrologue, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact RegionPhysImgSide.copyOkR_movq _ _
      · obtain ⟨r', s, -, rfl⟩ := mem_extraSaves hr
        exact RegionPhysImgSide.copyOkR_movq _ _
      · unfold buildArgPtrMaterialize at hr
        obtain ⟨⟨abiReg, k⟩, -, hr⟩ := List.mem_flatMap.mp hr
        simp only at hr
        split at hr
        · simp at hr
        · split_ifs at hr <;>
            rcases hs : abiSlotOfExt abiReg with _ | s <;>
            simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
            (try rcases hr with rfl | rfl) <;> exact RegionPhysImgSide.copyOkR_movq _ _
  · refine ⟨epilogue_plainB r hr, ?_⟩
    simp only [List.mem_append] at hr
    rcases hr with hr | hr
    · simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact RegionPhysImgSide.copyOkR_movq _ _
    · simp only [List.mem_singleton] at hr
      subst hr
      intro d x he
      cases he
  · rcases List.mem_append.mp hr with hr | hr
    · exact dstOkB_of_dstOk (calleeSaveRestoreEpilogue_dstOk hslot r hr)
    · simp only [List.mem_singleton] at hr; subst hr; rfl

/-! ## 4. The allocated function of the region route with split intervals -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapAlign
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotArrOf slotRen)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (slotArrC)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImg (AccArg argPair_nfAbiNames)
open RegionPhysImgSplit (regionAllocFnSplit)

/-- **The conditions of the fusion and the fold on the allocated function of the region route
    with split intervals**: for the body `b0` of `regionAllocFnSplit` at an exported code `r`
    (`RegionExp`) and the slot map `sl` of the gate, `fuseSiteOkB sl b0`, `homeOkB sl [] b0`,
    `cellBaseFreeB b0`, `mulHiNoSlotB sl b0` and `copyNoSlotB sl b0` hold under the hypotheses
    of `RegionPhysImgSplit.physImgB_regionExport_split` and `hidx`: the instructions of the
    allocator input body other than its accesses have no register-indexed operand. -/
theorem sideAlloc_regionAllocFnSplit (fname : String) (σ : AbiLayout)
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
    (R : X86Backend.ImageCellFold.Slots) (ps : List (String × String)) :
    let sl := slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps))
    let b0 := (regionAllocFnSplit (nfAbiNames fname σ) ts r fd0).lfd_body
    fuseSiteOkB sl b0 = true ∧ homeOkB sl [] b0 = true ∧ cellBaseFreeB b0 = true ∧
      mulHiNoSlotB sl b0 = true ∧ copyNoSlotB sl b0 = true := by
  intro sl b0
  have hB : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r, ShapeB i.li_i :=
    shapeB_regionAllocBody _ _ ts r fun i hi => (hr.mnemDom hp hc i hi).2.2
  have hcf := bodyHasCall_of_shapeB hB
  have hslot := RegionPhysImg.regionSl_qsave R σ exportReg (renOf ps)
  have hsave := RegionPhysImg.nfAbiNames_pairSave fname σ hnd R (renOf ps)
  have hb1 : regionAllocBody (nfAbiNames fname σ) Γ.length ts r =
      (if (nfAbiNames fname σ).abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range (nfAbiNames fname σ).abiArgs.length).map
            (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (([] : List String).foldl (fun b r => aliasRegBody r (nfAbiNames fname σ).outArg b)
            (arrBasePins (nfAbiNames fname σ)
                (regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code
                  r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res))
              ++ ((regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts
                  r.code r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res)).map
                    (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]))) := by
    unfold regionAllocBody
    split
    · exact absurd rfl (hts _)
    · rfl
  have hcfg : bodySplitOpt (regionAllocBody (nfAbiNames fname σ) Γ.length ts r) =
      some (bodySplitCfg (regionAllocBody (nfAbiNames fname σ) Γ.length ts r)) := by
    simp [bodySplitOpt, hcf]
  have harr' : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r, ∀ q n,
      LOperand.arr q n ∈ lopnOperands i.li_i → sl q = none :=
    fun i hi q n hx => slotArr_none_of_prefix hslot (harr i hi q n hx)
  simp only [b0, regionAllocFnSplit, calleeAllocCert]
  exact sideAlloc_lfundefPhysAbiOfVirtCert_split _ _ _ [] (fun _ => none) _ _ true bodySplitOpt
    _ hb1 _ hcfg _ rfl
    (fun i hi => RegionPhysImgSplit.accForm_of_accArg_tbl _ hcf hsave
      (argPair_nfAbiNames fname σ) (hacc i hi) (hne i hi))
    harr' hidx hne hslot

/-- The result names of the allocated function of the region route with split intervals are
    empty (an unfolding lemma of `regionAllocFnSplit`). -/
theorem regionAllocFnSplit_lfd_res (a : AbiNames) (ts : List JasminTy) (r : Exported)
    (fd0 : Lfundef) : (regionAllocFnSplit a ts r fd0).lfd_res = [] := rfl

open RegionPhysImgGate (postBody reallocStage physImgSideB)
open X86Backend.PhysImgOpt (optSideB)
open X86Backend.PhysImgPrint (flagTiedB)
open X86Backend.LprogOptPipeline (splitStraightRuns)
open X86Backend.TwoAddrLegalize (twoAddrBody)
open X86Backend.FuseMulHi (fuseMulHiBody)
open X86Backend.PhysImgSidePass (memMovFreeB)
open X86Backend.PhysImgSideCmp (noScratchBaseB)

/-- **The side conditions of the region gate on the allocated function with split intervals
    from the conditions that remain open.** Under the hypotheses of
    `sideAlloc_regionAllocFnSplit`, `physImgSideB sl res b0` holds for the body `b0` and the
    result names `res` of `regionAllocFnSplit` when the optimizer condition holds on every
    straight run of the post-pass body (`hopt`), no 64-bit move of the post-pass body is
    between two memory names (`hhold`), the re-allocated and legalised body satisfies
    `noScratchBaseB` (`hcmp`), and every flag-only compare of `b0` with a register first source
    is tied (`hflag`). -/
theorem physImgSideB_of_exportSplit (fname : String) (σ : AbiLayout)
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
      = true)
    (hcmp : noScratchBaseB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
      (twoAddrBody (reallocStage (regionAllocFnSplit (nfAbiNames fname σ) ts r fd0).lfd_res
        (regionAllocFnSplit (nfAbiNames fname σ) ts r fd0).lfd_body)) = true)
    (hflag : flagTiedB (regionAllocFnSplit (nfAbiNames fname σ) ts r fd0).lfd_body = true) :
    physImgSideB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
      (regionAllocFnSplit (nfAbiNames fname σ) ts r fd0).lfd_res
      (regionAllocFnSplit (nfAbiNames fname σ) ts r fd0).lfd_body = true := by
  obtain ⟨h1, h2, hcell, hmul, hcopy⟩ :=
    sideAlloc_regionAllocFnSplit fname σ p hp hc hr hts fd0 hnd hacc harr hidx hne R ps
  have hq := RegionPhysImg.regionSl_qsave R σ exportReg (renOf ps)
  have hs := RegionPhysImgSide.deadWriteRet_sublist
    (fuseMulHiBody (regionAllocFnSplit (nfAbiNames fname σ) ts r fd0).lfd_body true)
  simp only [physImgSideB, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hopt⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact X86Backend.PhysImgSidePass.copyNoSlotB_postOpt hq hcopy hmul hs hhold
  · exact X86Backend.PhysImgSidePass.cellBaseFreeB_postOpt hcell hs
  · rw [regionAllocFnSplit_lfd_res]; rfl
  · exact X86Backend.PhysImgSidePass.flagTiedB_reallocStage _ hflag hs
  · exact X86Backend.PhysImgSideCmp.cmpScratchFreeB_of_baseNoScratch hcmp
  · exact X86Backend.PhysImgSidePass.cellBaseFreeB_printedChain _ hcell hs

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSplitSide
