/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomNameAlloc

/-!
# The image conjunct of the region gate on the trimmed body with split intervals

The back half of the region route, at its default arguments, allocates the webs
`regionWebsAt ex none r0` of the export `r0` at the split configuration `bodySplitOpt`, and the
gate runs on the first body of `regionPrinted P`, the printed body after the frame trim
`frameTrim`. `RegionPhysImgGate.physImgB_printed` covers the allocation at `noSplit`, the
untrimmed printed body and an export with `regionWebs ex r = r`. This module proves the image
conjunct `physImgB sl (cellBody sl b)` of the gate on the body of the default route.

The allocation `lfundefPhysAbiOfVirtCert` of a call-free body at a split configuration
`splitCfg` with `splitCfg body1 = some cfg` emits its body through `physBodySplit`: for each
operation of the allocator input body, the moves of the cells of the pieces that start there
into their registers, the expansion `physExpandR` of the operation under the renaming `rk`
that sends the name of a piece to the register of the piece and every other operand through
the allocation table, and the moves of the registers of the pieces that end there into their
cells. Every such chunk is a block of the operation (`BlockOk`): its moves are under a move
mnemonic and write allocated registers or cells, and the expansion is a block by the argument
of `PhysImgEmit.physPositionEmit_blockOk`, which reads the renaming only through the
operands it produces. So the body with split intervals is in the image class `physImgB`
under the hypotheses of `PhysImgEmit.physImgB_lfundefPhysAbiOfVirtCert`, for an allocator
input without `ZEROARR` and `STOREIMM`.

The frame trim removes saves `MOVQ qsave.X, X` and restores `MOVQ X, qsave.X`. A removed
instruction is a move into a slot that no kept instruction names, or a move out of a slot that
is no array slot and no general-purpose name (the restore of a callee-saved register, whose
slot is no array slot of the gate). So the backward scan `reloadOf` of an access of the trimmed
body finds the slot that it finds in the body (`reloadOf_filter`), and the trim keeps the
image class (`physImgB_frameTrim`).

## Main results

* `physExpandR_blockOk`: the expansion of an operation under any renaming whose operands are
  no array slots and whose register images are registers is a block of the operation.
* `physBodySplit_splitOk`: every instruction of the body with split intervals writes no
  array slot and is no constant-index array write, and its accesses resolve locally.
* `accForm_of_accArg_tbl`: the access form of the image at any allocation table.
* `physImgB_lfundefPhysAbiOfVirtCert_split`: the call-free physical ABI export with split
  intervals is in the image class.
* `physImgB_regionExport_split`: the export body of the region route at the split
  configuration `bodySplitOpt` and at an exported code (`RegionExp`, the export or its
  webs) is in the image class at the slot map of the gate.
* `reloadOf_filter`, `physImgB_filter`: the scan and the image class are kept by a filter
  whose removed instructions are such moves.
* `physImgB_frameTrim`: the frame trim keeps the image class.
* `regionSl_slotOfReg_none`: the slot map of the gate has no array slot at the save slot of a
  register without a frame slot.
* `regionAllocFnSplit`, `regionLprogC_lp_funcs_split`: the allocated function of the region
  route at `bodySplitOpt`.
* `physImgB_printed_split`: the image conjunct of the gate on the trimmed printed body of the
  webs with split intervals.
* `regionCoStage_ne_physImgB_split`: under these hypotheses the region gate does not name
  `physImgB` as the refusing stage.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSplit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit

/-! ## 1. The expansion of one operation -/

/-- **The expansion of an operation is a block of it** under any operand renaming `rm` whose
    images of the operands are no array slots and whose images of registers are registers,
    when the operation is no constant-index array write and its accesses have the form
    `AccForm` under `rm`. -/
theorem physExpandR_blockOk {slotArr : String → Option (String × Nat)}
    (shiftImm : ShiftImmOracle) (u64 : Bool) (rm : LOperand → LOperand)
    (mbr : String → Option String) (i : Linstr)
    (hs15 : slotArr reloadScratch = none) (hs14 : slotArr reloadScratch2 = none)
    (hmem : ∀ c, slotArr ("mem." ++ c) = none)
    (hok : ∀ x ∈ lopnOperands i.li_i, OperandOk slotArr (rm x))
    (hreg : ∀ n, ∃ n', rm (.reg n) = .reg n')
    (hacc : AccForm slotArr rm mbr i.li_i)
    (hne : ∀ ds o ss, i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM") :
    BlockOk slotArr i.li_i (physExpandR shiftImm u64 rm mbr i) := by
  obtain ⟨ii, x⟩ := i
  simp only at hok hacc hne ⊢
  unfold physExpandR
  dsimp only
  cases x with
  | Lopn ds o ss =>
    have hopn : opnOf (.Lopn ds o ss) = some o := rfl
    have hokd : ∀ x ∈ ds, OperandOk slotArr (rm x) :=
      fun x hx => hok x (by simp [lopnOperands, hx])
    have hmapd : ∀ x ∈ ds.map rm, OperandOk slotArr x := by
      intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact hokd y hy
    obtain ⟨hL, hS, -, -, ht⟩ := hacc ds o ss rfl
    have h34 := hne ds o ss rfl
    have hsingle : o ≠ "LOADIDX" → o ≠ "STOREIDX" →
        BlockOk slotArr (.Lopn ds o ss)
          [⟨ii, .Lopn (ds.map rm) o (ss.map rm)⟩] := fun h1 h2 =>
      blockOk_of_arm (l := [.Lopn (ds.map rm) o (ss.map rm)]) ii hs15 hs14 hmem hmapd hopn
        ht h34 h1 h2 (fun r hr => by
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨_, _, _, rfl, Or.inl rfl, fun x hx => Or.inl hx⟩)
    rcases ds with _ | ⟨d, tail⟩
    · have h1 : o ≠ "LOADIDX" := fun h => by obtain ⟨_, _, _, h', -⟩ := hL h; cases h'
      have h2 : o ≠ "STOREIDX" := fun h => by obtain ⟨_, _, _, _, h', -⟩ := hS h; cases h'
      dsimp only
      simpa using hsingle h1 h2
    · have hd : ∀ x ∈ [rm d], OperandOk slotArr x := by simp [hokd d List.mem_cons_self]
      have hnil : ∀ x ∈ ([] : List LOperand), OperandOk slotArr x := by simp
      rcases ss with _ | ⟨s0, _ | ⟨s1, t⟩⟩
      · have h1 : o ≠ "LOADIDX" := fun h => by obtain ⟨_, _, _, -, h', -⟩ := hL h; cases h'
        have h2 : o ≠ "STOREIDX" := fun h => by
          obtain ⟨_, _, _, _, -, h', -⟩ := hS h; cases h'
        dsimp only
        simpa using hsingle h1 h2
      · rcases tail with _ | ⟨d2, tail2⟩
        · have h2 : o ≠ "STOREIDX" := fun h => by
            obtain ⟨_, _, _, _, -, h', -⟩ := hS h; cases h'
          dsimp only
          by_cases hnat : isNativeShiftRotate o = true
          · rw [ite_eq_left hnat]
            have h1 : o ≠ "LOADIDX" := by
              rintro rfl; rw [isNativeShiftRotate_loadIdx] at hnat; cases hnat
            exact blockOk_of_arm ii hs15 hs14 hmem hd hopn ht h34 h1 h2
              (lowerNativeShiftRotate_armOut _ _ _ _ (movFor_ok o))
          rw [ite_eq_right hnat]
          by_cases hld : isMemLoad o = true
          · rw [ite_eq_left hld]
            by_cases hLo : o = "LOADIDX"
            · obtain ⟨dn, b, y, hds, hss, b', y', q, hrmA, hmb, hq, hfa⟩ := hL hLo
              simp only [List.cons.injEq, and_true] at hds hss
              subst hds hss
              obtain ⟨n', hn'⟩ := hreg dn
              have hd' : ∀ x ∈ [LOperand.reg n'], OperandOk slotArr x := by
                rw [← hn']; exact hd
              rw [hrmA, hn']
              simp only [reloadMemrefBase, hmb, ptrLoad_qsave hfa]
              refine ⟨fun r hr => ?_, ?_⟩
              · rcases List.mem_append.mp hr with hr | hr
                · exact emitAll_of_arm ii hs15 hs14 hmem hnil hopn
                    (reloadMemrefBase_armOut mbr (.arrIdx b' y' 8) o) r
                    (by simpa [reloadMemrefBase, hmb, ptrLoad_qsave hfa] using hr)
                · exact emitAll_of_arm ii hs15 hs14 hmem hd' hopn
                    (legalizeMemLoad_armOut _ _ _ _ (movFor_ok o)) r hr
              · subst hLo
                exact loadIdx_accLocal hs15 hq ii _ n' y' _ rfl
            · exact blockOk_append
                (blockOk_of_arm ii hs15 hs14 hmem hnil hopn ht h34 hLo h2
                  (reloadMemrefBase_armOut mbr (rm s0) o))
                (blockOk_of_arm ii hs15 hs14 hmem hd hopn ht h34 hLo h2
                  (legalizeMemLoad_armOut _ _ _ _ (movFor_ok o)))
          · rw [ite_eq_right hld]
            have h1 : o ≠ "LOADIDX" := by
              rintro rfl; exact hld isMemLoad_loadIdx
            exact blockOk_of_arm ii hs15 hs14 hmem hd hopn ht h34 h1 h2
              (legalizeOneSrc_armOut _ _ _ _)
        · have h1 : o ≠ "LOADIDX" := fun h => by
            obtain ⟨_, _, _, h', -⟩ := hL h; simp at h'
          have h2 : o ≠ "STOREIDX" := fun h => by
            obtain ⟨_, _, _, _, -, h', -⟩ := hS h; cases h'
          dsimp only
          simpa using hsingle h1 h2
      · have h1 : o ≠ "LOADIDX" := fun h => by obtain ⟨_, _, _, -, h', -⟩ := hL h; cases h'
        dsimp only
        by_cases hbin : isTwoAddrBinop o = true
        · rw [ite_eq_left hbin]
          have h2 : o ≠ "STOREIDX" := by
            rintro rfl; rw [isTwoAddrBinop_storeIdx] at hbin; cases hbin
          split
          · exact blockOk_of_arm ii hs15 hs14 hmem hd hopn ht h34 h1 h2
              (lowerTwoAddrShiftImm_armOut _ _ _ _ _ (movFor_ok o))
          · exact blockOk_of_arm ii hs15 hs14 hmem hd hopn ht h34 h1 h2
              (lowerTwoAddr_armOut _ _ _ _ _ (movFor_ok o))
        · rw [ite_eq_right hbin]
          have hgen : (tail ≠ [] ∨ t ≠ []) → BlockOk slotArr (.Lopn (d :: tail) o (s0 :: s1 :: t))
              ((legalizeSpillDst ((d :: tail).map rm) o ((s0 :: s1 :: t).map rm)).map
                fun r => (⟨ii, r⟩ : Linstr)) := by
            intro hne
            have h2 : o ≠ "STOREIDX" := fun h => by
              obtain ⟨_, _, _, _, hds, hss, -⟩ := hS h
              simp only [List.cons.injEq] at hds hss
              rcases hne with hne | hne
              · exact hne hds.2
              · exact hne hss.2.2
            exact blockOk_of_arm ii hs15 hs14 hmem hmapd hopn ht h34 h1 h2
              (legalizeSpillDst_armOut _ _ _)
          rcases tail with _ | ⟨d2, tail2⟩ <;> rcases t with _ | ⟨s2, t2⟩
          · dsimp only
            by_cases hms : isMemStore o = true
            · rw [ite_eq_left hms]
              by_cases hSo : o = "STOREIDX"
              · obtain ⟨dn, b, y, v, hds, hss, b', y', q, hrmA, hmb, hq, hfa⟩ := hS hSo
                simp only [List.cons.injEq, and_true] at hds hss
                obtain ⟨rfl, rfl⟩ := hss
                subst hds
                obtain ⟨n', hn'⟩ := hreg dn
                obtain ⟨v', hv'⟩ := hreg v
                have hd' : ∀ x ∈ [LOperand.reg n'], OperandOk slotArr x := by
                  rw [← hn']; exact hd
                simp only [hrmA, hn', hv', reloadMemrefBase, hmb, ptrLoad_qsave hfa]
                refine ⟨fun r hr => ?_, ?_⟩
                · rcases List.mem_append.mp hr with hr | hr
                  · exact emitAll_of_arm ii hs15 hs14 hmem hnil hopn
                      (reloadMemrefBase_armOut mbr (.arrIdx b' y' 8) o) r
                      (by simpa [reloadMemrefBase, hmb, ptrLoad_qsave hfa] using hr)
                  · exact emitAll_of_arm ii hs15 hs14 hmem hd' hopn
                      (legalizeMemStoreK_armOut _ _ _ _ _ _ (movFor_ok o)) r hr
                · subst hSo
                  exact storeIdx_accLocal hs15 hq ii _ _ _ n' y' v' _ rfl rfl
              · exact blockOk_append
                  (blockOk_of_arm ii hs15 hs14 hmem hnil hopn ht h34 h1 hSo
                    (reloadMemrefBase_armOut mbr (rm s0) o))
                  (blockOk_of_arm ii hs15 hs14 hmem hd hopn ht h34 h1 hSo
                    (legalizeMemStoreK_armOut _ _ _ _ _ _ (movFor_ok o)))
            · rw [ite_eq_right hms]
              have h2 : o ≠ "STOREIDX" := by
                rintro rfl; exact hms isMemStore_storeIdx
              exact blockOk_of_arm ii hs15 hs14 hmem hd hopn ht h34 h1 h2
                (legalizeSpillDst_armOut _ _ _)
          · exact hgen (Or.inr (by simp))
          · exact hgen (Or.inl (by simp))
          · exact hgen (Or.inl (by simp))
  | _ =>
    dsimp only
    exact ⟨by simp [EmitOk], accLocal_of_noAcc (by simp [isAccB]) (by simp [isArrImmB])⟩

/-- **A block of moves**: instructions under a move mnemonic with one destination that is no
    array slot are a block of every instruction. -/
theorem blockOk_moves {slotArr : String → Option (String × Nat)} (i : LinstrR) {mov : String}
    (hmov : mov ∈ movMnems) {L : Lcmd}
    (hL : ∀ r ∈ L, ∃ x s, r.li_i = .Lopn [x] mov [s] ∧ OperandOk slotArr x) :
    BlockOk slotArr i L := by
  refine ⟨fun r hr ds o ss he => ?_, accLocal_of_noAcc (fun r hr => ?_) (fun r hr => ?_)⟩
  · obtain ⟨x, s, hx, hok⟩ := hL r hr
    rw [hx] at he
    cases he
    exact ⟨by simpa using hok, Or.inr hmov⟩
  · obtain ⟨x, s, hx, -⟩ := hL r hr
    rw [hx]; exact isAccB_of_movMnems hmov
  · obtain ⟨x, s, hx, -⟩ := hL r hr
    rw [hx]; exact isArrImmB_of_movMnems hmov

/-- An operand renamed through an allocation table is no array slot as a destination, when
    an array operand names no array slot. -/
theorem operandOk_remapOperand {slotArr : String → Option (String × Nat)}
    (hP : ∀ p, slotArr (physRegName p x86Abi) = none) (body : Lcmd) (tbl : Array Nat)
    (x : LOperand) (harr : ∀ q n, x = .arr q n → slotArr q = none) :
    OperandOk slotArr (remapOperand body tbl x) := by
  cases x with
  | reg n => exact ⟨fun q hq => by cases hq; exact hP _, nofun, nofun⟩
  | arrIdx b y s => exact ⟨nofun, nofun, fun q j sc hq => by cases hq; exact hP _⟩
  | arr q n => exact ⟨nofun, fun q' n' hq => by cases hq; exact harr q n rfl, nofun⟩
  | imm _ => exact ⟨nofun, nofun, nofun⟩

/-- **The access form is kept by a renaming that agrees on indexed operands**, for an
    operation that is no constant-index array write. -/
theorem accForm_of_agree {slotArr : String → Option (String × Nat)}
    {rm rk : LOperand → LOperand} {mbr : String → Option String} {i : LinstrR}
    (hag : ∀ b y, rk (.arrIdx b y 8) = rm (.arrIdx b y 8))
    (hne : ∀ ds o ss, i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM")
    (h : AccForm slotArr rm mbr i) : AccForm slotArr rk mbr i := by
  intro ds o ss he
  obtain ⟨hL, hS, -, -, hU⟩ := h ds o ss he
  obtain ⟨hz, hs⟩ := hne ds o ss he
  refine ⟨fun ho => ?_, fun ho => ?_, fun ho => absurd ho hz, fun ho => absurd ho hs, hU⟩
  · obtain ⟨d, b, y, h1, h2, b', y', q, h3, h4⟩ := hL ho
    exact ⟨d, b, y, h1, h2, b', y', q, by rw [hag]; exact h3, h4⟩
  · obtain ⟨d, b, y, v, h1, h2, b', y', q, h3, h4⟩ := hS ho
    exact ⟨d, b, y, v, h1, h2, b', y', q, by rw [hag]; exact h3, h4⟩

/-! ## 2. The body with split intervals -/

/-- **The class of a part of the body with split intervals**: every instruction writes no
    array slot and is no constant-index array write, and after the `LIVEPIN` instructions are
    removed its accesses resolve locally. -/
def SplitOk (slotArr : String → Option (String × Nat)) (L : Lcmd) : Prop :=
  (∀ r ∈ L, DstOk slotArr r.li_i ∧
      ∀ ds o ss, r.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM") ∧
    AccLocal slotArr
      (L.filter fun r => match r.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true)

theorem splitOk_append {slotArr : String → Option (String × Nat)} {a b : Lcmd}
    (ha : SplitOk slotArr a) (hb : SplitOk slotArr b) : SplitOk slotArr (a ++ b) := by
  refine ⟨fun r hr => (List.mem_append.mp hr).elim (ha.1 r) (hb.1 r), ?_⟩
  rw [List.filter_append]
  exact accLocal_append ha.2 hb.2

/-- A block of an operation that is no constant-index array write is `SplitOk`. -/
theorem splitOk_of_blockOk {slotArr : String → Option (String × Nat)} {i : LinstrR} {L : Lcmd}
    (hne : ∀ ds o ss, i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM")
    (h : BlockOk slotArr i L) : SplitOk slotArr L := by
  refine ⟨fun r hr => ⟨fun ds o ss he => (h.1 r hr ds o ss he).1, fun ds o ss he => ?_⟩,
    (blockOk_filter_livepin h).2⟩
  rcases (h.1 r hr ds o ss he).2 with ho | ho
  · cases hi : i with
    | Lopn ds' o' ss' =>
      rw [hi] at ho
      simp only [opnOf, Option.some.injEq] at ho
      subst ho
      exact hne _ _ _ hi
    | _ => rw [hi] at ho; simp [opnOf] at ho
  · simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide

/-- **The body with split intervals is `SplitOk`**: each chunk of an operation, the moves of
    the cells of the pieces into their registers, the expansion under the renaming to the
    registers of the pieces and the moves of the registers back into the cells, is a block of
    the operation. -/
theorem physBodySplit_splitOk {slotArr : String → Option (String × Nat)}
    (shiftImm : ShiftImmOracle) (body : Lcmd) (cfg : SplitCfg) (mbr : String → Option String)
    (hs15 : slotArr reloadScratch = none) (hs14 : slotArr reloadScratch2 = none)
    (hmem : ∀ c, slotArr ("mem." ++ c) = none)
    (hP : ∀ p, slotArr (physRegName p x86Abi) = none)
    (hacc : ∀ i ∈ body, AccForm slotArr
      (fun o => remapOperand body (physAllocTbl body [] [] x86Abi (some cfg)) o) mbr i.li_i)
    (harr : ∀ i ∈ body, ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → slotArr q = none)
    (hne : ∀ i ∈ body, ∀ ds o ss, i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM") :
    SplitOk slotArr (physBodySplit shiftImm body cfg mbr x86Abi) := by
  unfold physBodySplit
  dsimp only
  have hpos := FieldDomComplete.mem_byPos (bodySplitPieces body cfg x86Abi)
    (bodyTraceOut body []).length
  generalize (bodySplitPieces body cfg x86Abi).foldl _ _ = byPos at hpos ⊢
  refine FieldDomComplete.foldl_inv _ (fun st : Array Linstr × Nat => SplitOk slotArr st.1.toList)
    body (#[], 0) ⟨by simp, by simpa using accLocal_nil slotArr⟩ ?_
  intro st i hi hst
  have hok0 : ∀ x ∈ lopnOperands i.li_i, OperandOk slotArr
      (remapOperand body (physAllocTbl body [] [] x86Abi (some cfg)) x) := fun x hx =>
    operandOk_remapOperand hP _ _ x fun q n he => harr i hi q n (he ▸ hx)
  have hmov : (if body.any (fun i => match i.li_i with
      | .Lopn _ opn _ => hasSuffix opn ":64" | _ => false) = true then "MOV:64" else "MOV")
      ∈ movMnems := by
    split <;> decide
  split
  · simp only [Array.toList_append]
    refine splitOk_append hst (splitOk_of_blockOk (hne i hi)
      (blockOk_append (blockOk_append (blockOk_moves _ hmov fun r hr => ?_) ?_)
        (blockOk_moves _ hmov fun r hr => ?_)))
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      obtain ⟨ph, he⟩ := FieldDomComplete.reg_of_mem_bodySplitPieces
        (hpos _ p (List.mem_filter.mp hp).1)
      exact ⟨_, _, rfl, ⟨fun q hq => by cases hq; rw [he]; exact hP _, nofun, nofun⟩⟩
    · refine physExpandR_blockOk _ _ _ mbr i hs15 hs14 hmem (fun x hx => ?_) (fun n => ?_)
        (accForm_of_agree (fun b y => rfl) (hne i hi) (hacc i hi)) (hne i hi)
      · cases x with
        | reg nm =>
          dsimp only
          split
          · rename_i p hf
            obtain ⟨ph, he⟩ := FieldDomComplete.reg_of_mem_bodySplitPieces
              (hpos _ p (List.mem_of_find?_eq_some hf))
            exact ⟨fun q hq => by cases hq; rw [he]; exact hP _, nofun, nofun⟩
          · exact hok0 _ hx
        | _ => exact hok0 _ hx
      · dsimp only
        split
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hr
      exact ⟨_, _, rfl, operandOk_remapOperand hP _ _ _ nofun⟩
  · simp only [Array.toList_append]
    exact splitOk_append hst (splitOk_of_blockOk (hne i hi)
      (physExpandR_blockOk _ _ _ mbr i hs15 hs14 hmem hok0 (fun n => ⟨_, rfl⟩) (hacc i hi)
        (hne i hi)))

/-! ## 3. The physical ABI export with split intervals -/

/-- **The image class holds of the call-free physical ABI export with split intervals**, at a
    split configuration `splitCfg` with `splitCfg body1 = some cfg`: the hypotheses of
    `PhysImgEmit.physImgB_lfundefPhysAbiOfVirtCert` at the allocation table of the split scan,
    and no `ZEROARR` or `STOREIMM` in the allocator input body `body1`. -/
theorem physImgB_lfundefPhysAbiOfVirtCert_split {slotArr : String → Option (String × Nat)}
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
    (hne : ∀ i ∈ body1, ∀ ds o ss, i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM")
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    physImgB slotArr (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind [] splitCfg).1.lfd_body = true := by
  have hb : ∃ sh, (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind [] splitCfg).1.lfd_body =
      (buildPrologue { virt0 with lfd_body := body1 }
          (physTableOut body1 [] [] x86Abi (some cfg)) (fun _ => none) ++ extraSaves abiArgs) ++
        buildArgPtrMaterialize { virt0 with lfd_body := body1 }
            (physTableOut body1 [] [] x86Abi (some cfg)) abiArgs (fun _ => none) ++
          insertEpilogue (reloadArrImmBody mbr ((physBodySplit sh body1 cfg mbr x86Abi).filter
              fun r => match r.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true))
            calleeSaveRestoreEpilogue := by
    subst hb1 hmbr
    simp only [lfundefPhysAbiOfVirtCert, hcfg]
    exact ⟨_, rfl⟩
  obtain ⟨sh, hb⟩ := hb
  rw [hb, List.append_assoc]
  have hs15 : slotArr reloadScratch = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hs14 : slotArr reloadScratch2 = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hmem : ∀ c, slotArr ("mem." ++ c) = none := fun c =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_mem c)
  have hP : ∀ p, slotArr (physRegName p x86Abi) = none := fun p =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_physRegName p)
  obtain ⟨hFd, hFa⟩ := physBodySplit_splitOk sh body1 cfg mbr hs15 hs14 hmem hP hshape harr hne
  have hre : reloadArrImmBody mbr ((physBodySplit sh body1 cfg mbr x86Abi).filter
      fun r => match r.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true) =
      (physBodySplit sh body1 cfg mbr x86Abi).filter
        fun r => match r.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true :=
    reloadArrImmBody_eq_of_noArrImm mbr fun r hr => (hFd r (List.mem_of_mem_filter hr)).2
  rw [hre]
  obtain ⟨hpre, -, -⟩ := prologue_moves { virt0 with lfd_body := body1 }
    (physTableOut body1 [] [] x86Abi (some cfg)) abiArgs
  have hepiAcc : ∀ r ∈ calleeSaveRestoreEpilogue, isAccB r.li_i = false := by
    intro r hr
    simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hepiImm : ∀ r ∈ calleeSaveRestoreEpilogue, isArrImmB r.li_i = false := by
    intro r hr
    simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine physImgB_of_movePrefix hpre (prologue_hsave hslot _ _ abiArgs) ?_
    (fun k i _ hi => ?_)
  · intro j hj ds o ss he x hx
    have hD : DstOk slotArr j.li_i := by
      rcases List.mem_append.mp hj with hj | hj
      · exact buildArgPtrMaterialize_dstOk hslot _ _ _ _ j hj
      · unfold insertEpilogue at hj
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with (hj | hj) | rfl
        · exact (hFd j (List.mem_of_mem_filter (List.dropLast_subset _ hj))).1
        · exact calleeSaveRestoreEpilogue_dstOk hslot j hj
        · exact fun _ _ _ h => by cases h
    exact hD ds o ss he x hx
  · refine accLocal_append (accLocal_of_noAcc (fun r hr => ?_) (fun r hr => ?_))
      (accLocal_append (accLocal_of_noAcc (buildArgPtrMaterialize_noAcc _ _ _ _)
        (buildArgPtrMaterialize_noArrImm _ _ _ _)) ?_) k i hi
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hpre r hr)
      exact isAccB_of_slotMov hp
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hpre r hr)
      exact isArrImmB_of_slotMov hp
    · unfold insertEpilogue
      exact accLocal_append (accLocal_append (accLocal_dropLast hFa)
        (accLocal_of_noAcc hepiAcc hepiImm))
        (accLocal_of_noAcc (by simp [isAccB]) (by simp [isArrImmB]))

/-! ## 4. The access form at an allocation table -/

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImg (AccArg ArgSlot isFrameSlotName_argName
  argPair_nfAbiNames)

/-- **The base of an access at a paired name is reloaded from an array slot** at every
    allocation table `tk` of a call-free body: `RegionPhysImg.baseReloaded_of_pair` at `tk`. -/
theorem baseReloaded_of_pair_tbl {slotArr : String → Option (String × Nat)} {body1 : Lcmd}
    (tk : Array Nat) {pairs : List (String × String)}
    (hcf : bodyHasCall body1 = false)
    (hsave : ∀ p ∈ pairs, ∀ q, abiSlotOfExt p.2 = some q → (slotArr q).isSome = true)
    {b y : String} (hfr : isFrameSlotName b = false)
    (hb : ∃ p ∈ pairs, p.1 = b ∧ (abiSlotOfExt p.2).isSome = true) :
    BaseReloaded slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 tk) o)
      (fun base => ((pairs.filterMap (fun p =>
          match abiSlotOfExt p.2 with
          | some saveName => some (physNameForBody body1 tk p.1, saveName)
          | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
      b y := by
  obtain ⟨p, hp, rfl, hs⟩ := hb
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hs
  have hst : bodyStraightCall body1 = false := by
    simp [bodyStraightCall, hcf]
  have hkey : physNameForBody body1 tk p.1
      = physRegName (physMapTabled (straightCallComposeTable body1 tk)
          (nameSlot body1 p.1)) x86Abi := by
    simp [physNameForBody, hfr, hcf, straightCallComposeTable, hst]
  have hmem : (physNameForBody body1 tk p.1, s) ∈
      pairs.filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 tk p.1, saveName)
        | none => none) :=
    List.mem_filterMap.mpr ⟨p, hp, by simp [hs]⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp
    ((List.find?_isSome (p := fun e : String × String =>
      e.1 == physNameForBody body1 tk p.1)).mpr ⟨_, hmem, by simp⟩)
  obtain ⟨p', hp', hf⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some he)
  have hq : ∃ q, abiSlotOfExt p'.2 = some q ∧ e.2 = q := by
    revert hf
    cases abiSlotOfExt p'.2 with
    | none => intro hf; cases hf
    | some q => intro hf; cases hf; exact ⟨q, rfl, rfl⟩
  obtain ⟨q, hq, hqe⟩ := hq
  refine ⟨_, _, q, rfl, ?_, hsave p' hp' q hq, abiSlotOfExt_faB hq⟩
  rw [← hkey]
  simp only [he, Option.map_some, hqe]

/-- **Accesses at paired parameters have the access form of the image** at every allocation
    table `tk`, for an operation that is no constant-index array write. -/
theorem accForm_of_accArg_tbl {σ : AbiLayout} {slotArr : String → Option (String × Nat)}
    {body1 : Lcmd} (tk : Array Nat) {pairs : List (String × String)}
    (hcf : bodyHasCall body1 = false)
    (hsave : ∀ p ∈ pairs, ∀ q, abiSlotOfExt p.2 = some q → (slotArr q).isSome = true)
    (hpair : ∀ j, ArgSlot σ j → ∃ q ∈ pairs, q.1 = argName j ∧ (abiSlotOfExt q.2).isSome = true)
    {w : LinstrR} (h : AccArg σ w)
    (hne : ∀ ds o ss, w = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM") :
    AccForm slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 tk) o)
      (fun base => ((pairs.filterMap (fun p =>
          match abiSlotOfExt p.2 with
          | some saveName => some (physNameForBody body1 tk p.1, saveName)
          | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
      w := by
  intro ds o ss he
  obtain ⟨hL, hS, -, -, hU⟩ := h ds o ss he
  obtain ⟨hz, hs⟩ := hne ds o ss he
  refine ⟨fun ho => ?_, fun ho => ?_, fun ho => absurd ho hz, fun ho => absurd ho hs, hU⟩
  · obtain ⟨d, j, y, rfl, rfl, hj⟩ := hL ho
    exact ⟨d, argName j, y, rfl, rfl,
      baseReloaded_of_pair_tbl tk hcf hsave (isFrameSlotName_argName j) (hpair j hj)⟩
  · obtain ⟨d, j, y, v, rfl, rfl, hj⟩ := hS ho
    exact ⟨d, argName j, y, v, rfl, rfl,
      baseReloaded_of_pair_tbl tk hcf hsave (isFrameSlotName_argName j) (hpair j hj)⟩

/-! ## 5. The export body of the region route with split intervals -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapAlign
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotArrOf slotRen)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (slotArrC)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)

/-- **The export body of the region route with split intervals is in the image class at the
    slot map of the gate.** The allocation `calleeAllocCert none` at the split configuration
    `bodySplitOpt`, at an exported code `r` of `p` (`RegionExp`: the export or its webs), has
    its function body in the class `physImgB` at the slot map `slotArrC R (slotRen (slotArrOf σ
    exportReg) (renOf ps))`, for all cell arrays `R` and pairs `ps`, when every instruction of
    the allocator input body `regionAllocBody a Γ.length ts r` has its array accesses at array
    parameters of `σ` with a save slot (`AccArg σ`), names no `qsave.` slot in an array operand
    and is no `ZEROARR` or `STOREIMM`. -/
theorem physImgB_regionExport_split (fname : String) (σ : AbiLayout)
    {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {ex : List String} {r : Exported}
    (hr : RegionExp fname p ex r)
    (hts : ∀ w, ts ≠ [.reg w]) (fd0 : Lfundef)
    (hnd : (σ.args.map fun a => exportReg a.reg).Nodup)
    (hacc : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r, AccArg σ i.li_i)
    (harr : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r, ∀ q n,
      LOperand.arr q n ∈ lopnOperands i.li_i → hasPrefix q "qsave." = false)
    (hne : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r, ∀ ds o ss,
      i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM")
    (R : X86Backend.ImageCellFold.Slots) (ps : List (String × String)) :
    physImgB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
      (calleeAllocCert none
        { fd0 with lfd_body :=
            (arrBasePins (nfAbiNames fname σ)
                (regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code
                  r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res))
              ++ ((regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code
                  r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res)).map
                    (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩])) }
        (nfAbiNames fname σ).outArg (nfAbiNames fname σ).inArgs
        (nfAbiNames fname σ).abiArgs bodySplitOpt).1.lfd_body = true := by
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
      LOperand.arr q n ∈ lopnOperands i.li_i →
        slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)) q = none :=
    fun i hi q n hx => slotArr_none_of_prefix hslot (harr i hi q n hx)
  unfold calleeAllocCert
  exact physImgB_lfundefPhysAbiOfVirtCert_split _ _ _ [] (fun _ => none) _ _ true bodySplitOpt
    _ hb1 _ hcfg _ rfl
    (fun i hi => accForm_of_accArg_tbl _ hcf hsave (argPair_nfAbiNames fname σ) (hacc i hi)
      (hne i hi))
    harr' hne hslot

/-! ## 6. The scan of a filtered body -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (namesB opNamesB)

/-- One step of the backward scan of `reloadOf` at the instruction `j`, with the scan `f` of
    the instructions before it. -/
def reloadStep (slotArr : String → Option (String × Nat)) (j : Linstr)
    (f : String → Option String) (b : String) : Option String :=
  match slotMov? j.li_i with
  | some (d, q) =>
      if d = b then (if (slotArr q).isNone && gpNameB q then f q else some q)
      else if (slotArr d).isNone then f b else none
  | none =>
      match j.li_i with
      | .Lopn ds _ _ => if ds.any (dstHitB slotArr b) then none else f b
      | _ => none

/-- The scan at the end of a body with a last instruction `j` is the step at `j`. -/
theorem reloadOf_snoc (slotArr : String → Option (String × Nat)) (L : Lcmd) (j : Linstr)
    (b : String) :
    reloadOf slotArr (L ++ [j]) (L.length + 1) b =
      reloadStep slotArr j (fun x => reloadOf slotArr L L.length x) b := by
  have h := fun x => reloadOf_append_left slotArr L [j] L.length x le_rfl
  simp only [reloadOf, List.getElem?_concat_length, reloadStep, h]
  rfl

/-- **A step is monotone in the scan before it** at a register outside `Bad`, when no
    general-purpose name is in `Bad`. -/
theorem reloadStep_mono {slotArr : String → Option (String × Nat)} (Bad : String → Prop)
    (hgp : ∀ x, gpNameB x = true → ¬ Bad x) {f g : String → Option String} (j : Linstr)
    (hfg : ∀ x q, ¬ Bad x → f x = some q → (slotArr q).isSome = true → g x = some q)
    {b q : String} (hb : ¬ Bad b) (h : reloadStep slotArr j f b = some q)
    (hq : (slotArr q).isSome = true) : reloadStep slotArr j g b = some q := by
  unfold reloadStep at h ⊢
  cases hs : slotMov? j.li_i with
  | some p =>
    obtain ⟨d, s⟩ := p
    rw [hs] at h
    simp only at h ⊢
    split_ifs at h ⊢ with h1 h2
    · simp only [Bool.and_eq_true] at h2
      exact hfg s q (hgp s h2.2) h hq
    · exact h
    · exact hfg b q hb h hq
  | none =>
    rw [hs] at h
    simp only at h ⊢
    split at h
    · split_ifs at h ⊢
      exact hfg b q hb h hq
    · cases h

/-- **A removed step is transparent**: at a move into a name of `Bad`, or out of a name that is
    neither an array slot nor a general-purpose name, a step at a register outside `Bad` that
    finds an array slot is the scan before it. -/
theorem reloadStep_removed {slotArr : String → Option (String × Nat)} (Bad : String → Prop)
    {f : String → Option String} {j : Linstr}
    (hj : ∃ d s, slotMov? j.li_i = some (d, s) ∧ (Bad d ∨ (slotArr s = none ∧ gpNameB s = false)))
    {b q : String} (hb : ¬ Bad b) (h : reloadStep slotArr j f b = some q)
    (hq : (slotArr q).isSome = true) : f b = some q := by
  obtain ⟨d, s, hs, hd⟩ := hj
  unfold reloadStep at h
  rw [hs] at h
  simp only at h
  split_ifs at h with h1 h2 h3
  · subst h1
    rcases hd with hd | hd
    · exact absurd hd hb
    · simp [hd.2] at h2
  · subst h1
    rcases hd with hd | hd
    · exact absurd hd hb
    · cases h
      simp [hd.1] at hq
  · exact h

/-- **The scan is kept by a filter** whose removed instructions are moves into a name of `Bad`
    or out of a name that is neither an array slot nor a general-purpose name: at the end of a
    body, a register outside `Bad` that the scan finds holding an array slot is found holding
    the same slot at the end of the filtered body. -/
theorem reloadOf_filter {slotArr : String → Option (String × Nat)} (Bad : String → Prop)
    (hgp : ∀ x, gpNameB x = true → ¬ Bad x) (keep : Linstr → Bool) :
    ∀ (L : Lcmd), (∀ j ∈ L, keep j = false → ∃ d s, slotMov? j.li_i = some (d, s) ∧
        (Bad d ∨ (slotArr s = none ∧ gpNameB s = false))) →
      ∀ b q, ¬ Bad b → reloadOf slotArr L L.length b = some q → (slotArr q).isSome = true →
        reloadOf slotArr (L.filter keep) (L.filter keep).length b = some q := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _ b q _ h; cases h
  | append_singleton L j ih =>
    intro hrm b q hb h hq
    have ih' := ih (fun j' hj' => hrm j' (List.mem_append_left _ hj'))
    rw [List.length_append, List.length_singleton, reloadOf_snoc] at h
    rw [List.filter_append]
    cases hk : keep j
    · simp only [List.filter_cons, hk, Bool.false_eq_true, ite_false, List.filter_nil,
        List.append_nil]
      exact ih' b q hb (reloadStep_removed Bad (hrm j (by simp) hk) hb h hq) hq
    · simp only [List.filter_cons, hk, ite_true, List.filter_nil]
      rw [List.length_append, List.length_singleton, reloadOf_snoc]
      exact reloadStep_mono Bad hgp j (fun x q' hx h' hq' => ih' x q' hx h' hq') hb h hq

/-! ## 7. The image class of a filtered body -/

/-- The position of an element of a filtered list in the list: the prefixes before the two
    positions agree after the filter. -/
theorem getElem?_filter_take {α : Type} (p : α → Bool) :
    ∀ (l : List α) (k' : Nat) (x : α), (l.filter p)[k']? = some x →
      ∃ k, l[k]? = some x ∧ (l.filter p).take k' = (l.take k).filter p := by
  intro l
  induction l with
  | nil => intro k' x h; simp at h
  | cons a t ih =>
    intro k' x h
    cases hp : p a
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ite_false] at h ⊢
      obtain ⟨k, hk, he⟩ := ih k' x h
      exact ⟨k + 1, by simpa using hk, by
        rw [he, List.take_succ_cons, List.filter_cons]; simp [hp]⟩
    · simp only [List.filter_cons, hp, ite_true] at h ⊢
      cases k' with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        exact ⟨0, rfl, by simp⟩
      | succ k' =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨k, hk, he⟩ := ih k' x h
        exact ⟨k + 1, by simpa using hk, by
          rw [List.take_succ_cons, he, List.take_succ_cons, List.filter_cons]; simp [hp]⟩

/-- The scan at a position reads only the prefix before it. -/
theorem reloadOf_take (slotArr : String → Option (String × Nat)) (B : Lcmd) (k : Nat)
    (hk : k ≤ B.length) (x : String) :
    reloadOf slotArr B k x = reloadOf slotArr (B.take k) (B.take k).length x := by
  have h := reloadOf_append_left slotArr (B.take k) (B.drop k) k x (by simp; omega)
  rw [List.take_append_drop] at h
  rw [h, List.length_take, Nat.min_eq_left hk]

/-- **`accOkB` reads the body only through the registers the instruction names**. -/
theorem accOkB_of_named {slotArr : String → Option (String × Nat)} {b1 b2 : Lcmd}
    {k1 k2 : Nat} {i : LinstrR}
    (hmono : ∀ x, namesB x i = true → (accArr slotArr b1 k1 x).isSome = true →
      (accArr slotArr b2 k2 x).isSome = true)
    (h : accOkB slotArr b1 k1 i = true) : accOkB slotArr b2 k2 i = true := by
  revert h
  unfold accOkB
  split
  · split_ifs
    · split
      · exact hmono _ (by simp [namesB, opNamesB]; simp_all)
      · simp
    · split
      · simp only [Bool.and_eq_true]
        intro h
        refine ⟨h.1, hmono _ ?_ h.2⟩
        simp_all [namesB, opNamesB]
      · simp
    · refine arrImmImg_isSome_mono fun x ⟨ds, o, ss, he⟩ => hmono x ?_
      cases he
      simp [namesB, opNamesB]
    · simp
  · simp

/-- **The image class is kept by a filter** whose removed instructions are moves into a name
    of `Bad` or out of a name that is neither an array slot nor a general-purpose name, when
    no kept instruction names a name of `Bad` and no general-purpose name is in `Bad`. -/
theorem physImgB_filter {slotArr : String → Option (String × Nat)} (Bad : String → Prop)
    (hgp : ∀ x, gpNameB x = true → ¬ Bad x) (keep : Linstr → Bool) {B : Lcmd}
    (hrm : ∀ j ∈ B, keep j = false → ∃ d s, slotMov? j.li_i = some (d, s) ∧
        (Bad d ∨ (slotArr s = none ∧ gpNameB s = false)))
    (hkept : ∀ j ∈ B, keep j = true → ∀ x, Bad x → namesB x j.li_i = false)
    (h : physImgB slotArr B = true) : physImgB slotArr (B.filter keep) = true := by
  unfold physImgB at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro k' hk'
  rw [List.mem_range] at hk'
  cases hx : (B.filter keep)[k']? with
  | none => rfl
  | some i =>
    simp only
    obtain ⟨k, hk, htake⟩ := getElem?_filter_take keep B k' i hx
    have hkl : k < B.length := (List.getElem?_eq_some_iff.mp hk).1
    have hiB : i ∈ B := List.mem_of_getElem? hk
    have hki : keep i = true := (List.mem_filter.mp (List.mem_of_getElem? hx)).2
    have h0 := h k (List.mem_range.mpr hkl)
    rw [hk] at h0
    simp only [Bool.and_eq_true] at h0 ⊢
    have htk : ((B.filter keep).take k').length = k' := by
      rw [List.length_take]; omega
    have hrel : ∀ x q, ¬ Bad x → reloadOf slotArr B k x = some q →
        (slotArr q).isSome = true → reloadOf slotArr (B.filter keep) k' x = some q := by
      intro x q hb h1 hq
      rw [reloadOf_take slotArr B k hkl.le] at h1
      have h2 := reloadOf_filter Bad hgp keep (B.take k)
        (fun j hj => hrm j (List.mem_of_mem_take hj)) x q hb h1 hq
      rw [← htake] at h2
      rw [reloadOf_take slotArr (B.filter keep) k' hk'.le, htk]
      rwa [htk] at h2
    refine ⟨accOkB_of_named (fun x hn ha => ?_) h0.1, ?_⟩
    · have hb : ¬ Bad x := fun hb => by rw [hkept i hiB hki x hb] at hn; cases hn
      obtain ⟨q, hq, hsq⟩ : ∃ q, reloadOf slotArr B k x = some q ∧ (slotArr q).isSome = true := by
        unfold accArr at ha
        cases hr : reloadOf slotArr B k x with
        | none => rw [hr] at ha; cases ha
        | some q => rw [hr] at ha; exact ⟨q, rfl, by simpa using ha⟩
      unfold accArr
      rw [hrel x q hb hq hsq]
      simpa using hsq
    · have hent : ∀ R, entryRegB B k R = true → entryRegB (B.filter keep) k' R = true := by
        intro R hR
        unfold entryRegB at hR ⊢
        rw [htake]
        rw [List.all_eq_true] at hR ⊢
        exact fun j hj => hR j (List.mem_of_mem_filter hj)
      have h1 := h0.2
      revert h1
      unfold slotWriteB
      split
      · simp only [List.all_eq_true]
        intro h1 x hx
        have h2 := h1 x hx
        revert h2
        split
        · cases slotMov? _ with
          | none => simp
          | some p =>
            simp only [Bool.or_eq_true, Bool.and_eq_true]
            exact fun h2 => h2.imp id fun h3 => ⟨h3.1, hent _ h3.2⟩
        all_goals exact id
      · exact id

/-- A save slot is no general-purpose name. -/
theorem gpNameB_slotOfReg (X : String) : gpNameB (slotOfReg X) = false := by
  cases h : gpNameB (slotOfReg X)
  · rfl
  · have := (X86Backend.PhysImgFold.gpNameB_prefix h).1
    rw [hasPrefix_slotOfReg] at this
    cases this

/-- **The frame trim keeps the image class** at a slot map with no array slot at the save slot
    of a callee-saved register that the body does not write. The trim removes the saves of
    such registers and of dead pointer arguments, moves into a slot that no kept instruction
    names, and their restores, moves out of a slot that is no array slot. -/
theorem physImgB_frameTrim {slotArr : String → Option (String × Nat)} {B : Lcmd}
    (hcs : ∀ X ∈ unwrittenSaved B, slotArr (slotOfReg X) = none)
    (h : physImgB slotArr B = true) : physImgB slotArr (frameTrim B) = true := by
  unfold frameTrim
  refine physImgB_filter
    (fun x => ∃ X, (X ∈ unwrittenSaved B ∨ X ∈ deadArgSaves B) ∧ x = slotOfReg X)
    (fun x hx => ?_) _ (fun j hj hk => ?_) (fun j hj hk => ?_) h
  · rintro ⟨X, -, rfl⟩
    rw [gpNameB_slotOfReg] at hx
    cases hx
  · simp only [Bool.not_eq_false', Bool.or_eq_true, List.any_eq_true] at hk
    rcases hk with ⟨X, hX, hs | hs⟩ | ⟨R, hR, hs⟩
    · exact ⟨_, _, beq_iff_eq.mp hs, Or.inl ⟨X, Or.inl hX, rfl⟩⟩
    · exact ⟨_, _, beq_iff_eq.mp hs, Or.inr ⟨hcs X hX, gpNameB_slotOfReg X⟩⟩
    · exact ⟨_, _, beq_iff_eq.mp hs, Or.inl ⟨R, Or.inr hR, rfl⟩⟩
  · rintro x ⟨X, hX | hX, rfl⟩
    · have hn : (saveOfB X j.li_i || restoreOfB X j.li_i) = false := by
        simp only [Bool.not_eq_true', Bool.or_eq_false_iff, List.any_eq_false] at hk
        cases hb : (saveOfB X j.li_i || restoreOfB X j.li_i)
        · rfl
        · exact absurd hb (by simpa using hk.1 X hX)
      unfold unwrittenSaved at hX
      split at hX
      · have hall := (List.mem_filter.mp hX).2
        have hj' := List.all_eq_true.mp hall j hj
        simp only [Bool.or_eq_false_iff] at hn
        simp only [hn.1, hn.2, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hj'
        exact hj'.2
      · cases hX
    · have hn : saveOfB X j.li_i = false := by
        simp only [Bool.not_eq_true', Bool.or_eq_false_iff, List.any_eq_false] at hk
        cases hb : saveOfB X j.li_i
        · rfl
        · exact absurd hb (by simpa using hk.2 X hX)
      unfold deadArgSaves at hX
      have hj' := List.all_eq_true.mp (List.mem_filter.mp hX).2 j hj
      simp only [hn, Bool.false_or, Bool.not_eq_true'] at hj'
      exact hj'

/-! ## 8. The image conjunct of the gate on the trimmed body with split intervals -/

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate (postBody reallocStage printedBody
  physImgSideB firstBody_printedLprog_regionPostFuse)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (scratchSave)

/-- **The slot map of the gate has no array slot at the save slot of a register without a
    frame slot**, at a layout whose word-array parameters have frame slots. -/
theorem regionSl_slotOfReg_none {σ : AbiLayout} (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    (R : X86Backend.ImageCellFold.Slots) (ps : List (String × String)) {X : String}
    (hX : abiSlotOfExt X = none) :
    slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)) (slotOfReg X) = none := by
  have hi := RegionPhysImg.regionSl_isSome R (slotArrOf σ exportReg) (renOf ps) (slotOfReg X)
  cases hsl : slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)) (slotOfReg X) with
  | none => rfl
  | some x =>
    rw [hsl, Option.isSome_some] at hi
    cases hs : slotArrOf σ exportReg (slotOfReg X) with
    | none => rw [hs] at hi; cases hi
    | some An =>
      exfalso
      obtain ⟨A, n⟩ := An
      obtain ⟨j, a, ha, hk, -, he⟩ := X86Backend.ImageAddrRoute.slotArrOf_some hs
      have hw := List.all_eq_true.mp hσ a (List.mem_of_getElem? ha)
      rw [hk] at hw
      have hr : exportReg a.reg = X := by simpa [slotOfReg] using he
      rw [hr, hX] at hw
      cases hw

/-- **The allocated function of the region route at the split configuration `bodySplitOpt`**
    without a callee, at the export `r` and the function `fd0` of the export, for a result
    other than one register. -/
def regionAllocFnSplit (a : AbiNames) (ts : List JasminTy) (r : Exported) (fd0 : Lfundef) :
    Lfundef :=
  (calleeAllocCert none
    { fd0 with lfd_body :=
        (arrBasePins a (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res))
          ++ ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res)).map
            (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩])) }
    a.outArg a.inArgs a.abiArgs bodySplitOpt).1

/-- The allocated program of `regionLprogC` at its default split configuration without a
    callee, for a result other than one register, is `regionPostFuse` of the program whose
    only function is `regionAllocFnSplit` at the webs `regionWebsAt ex none r`. -/
theorem regionLprogC_lp_funcs_split (a : AbiNames) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (ex : List String) {r : Exported}
    {fd0 : Lfundef} (hr : exportR Γ.length a.fname p Γ.length 0 = some r)
    (hfd : exportRLfundef a.fname p = some fd0) (hts : ∀ w, ts ≠ [.reg w])
    {P : Lprog} {cert : List (String × String)}
    (hP : regionLprogC a p none ex = some (P, cert)) :
    ∃ P0 : Lprog, P = regionPostFuse P0
      ∧ P0.lp_funcs = [(a.fname, regionAllocFnSplit a ts (regionWebsAt ex none r) fd0)] := by
  unfold regionLprogC regionAllocC at hP
  rw [hr, hfd] at hP
  simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hP
  exact ⟨_, hP.1.symm, rfl⟩

/-- **The printed body is in the image class** when the allocated body is, every array slot of
    `sl` is a `qsave.` slot, `sl` has no slot at `scratchSave` and the side conditions
    `physImgSideB` hold: the passes of `RegionPhysImgGate.physImgB_printedBody` before the
    cell body. -/
theorem physImgB_printedBody_pre {sl : String → Option (String × Nat)}
    (hq : ∀ q, (sl q).isSome = true → hasPrefix q "qsave." = true)
    (hsave : sl scratchSave = none) {res : List String} {b0 : Lcmd}
    (h : physImgB sl b0 = true) (hside : physImgSideB sl res b0 = true) :
    physImgB sl (printedBody res b0) = true := by
  simp only [physImgSideB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hside
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsite, hhome⟩, hopt⟩, hcp⟩, hcb⟩, hres⟩, hflag⟩, hfree⟩, -⟩ := hside
  have h1 : physImgB sl (postBody b0) = true :=
    RegionPhysImgPost.physImgB_deadWriteRet
      (X86Backend.PhysImgFuse.physImgB_fuseMulHiBody true hq h hsite hhome)
  have h2 := X86Backend.PhysImgOpt.physImgB_optimizeBasicBlocks hq h1
    (List.all_eq_true.mpr hopt)
  have h3 := X86Backend.PhysImgFold.physImgB_foldIndexedBody hq hcp hcb h2
  have h4 : physImgB sl (reallocStage res b0) = true :=
    X86Backend.PhysImgFold.physImgB_reallocBody hq hres h3
  have h5 := X86Backend.PhysImgPrint.physImgB_twoAddrBody hq hsave hflag h4
  exact X86Backend.PhysImgPrint.physImgB_cmpReload hq hfree h5

/-- **The image conjunct of the region gate holds on the trimmed printed body of the webs with
    split intervals.** Let `p` pass `regionExportableB`, have no `call`, the export `r0` and the
    function `fd0`, a result other than one register, distinct export registers of the
    parameters of `σ` and save slots at its word-array parameters (`wordsSlotB`). Let
    `regionLprogC` at its default arguments (the webs `regionWebsAt ex none r0`, the split
    configuration `bodySplitOpt`) return `P`, and let `b` be the first body of the printed
    program `regionPrinted P` (the body after the frame trim). When every instruction of the
    allocator input body of the webs has its array accesses at array parameters of `σ` with a
    save slot (`AccArg σ`), names no `qsave.` slot in an array operand and is no `ZEROARR` or
    `STOREIMM`, and the side conditions `physImgSideB` hold on the allocated function
    `regionAllocFnSplit`, then `physImgB sl (cellBody sl b)` holds at every slot map `sl` of
    the gate. -/
theorem physImgB_printed_split (fname : String) (σ : AbiLayout) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    {r0 : Exported} (hr0 : exportR Γ.length fname p Γ.length 0 = some r0)
    {fd0 : Lfundef} (hfd : exportRLfundef fname p = some fd0)
    (hts : ∀ w, ts ≠ [.reg w]) (hnd : (σ.args.map fun a => exportReg a.reg).Nodup)
    (ex : List String)
    (hacc : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts (regionWebsAt ex none r0),
      AccArg σ i.li_i)
    (harr : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts (regionWebsAt ex none r0),
      ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → hasPrefix q "qsave." = false)
    (hne : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts (regionWebsAt ex none r0),
      ∀ ds o ss, i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM")
    {P : Lprog} {cert : List (String × String)}
    (hP : regionLprogC (nfAbiNames fname σ) p none ex = some (P, cert))
    {b : Lcmd} (hb : firstBody (regionPrinted P) = some b)
    (R : X86Backend.ImageCellFold.Slots) (ps : List (String × String))
    (hside : physImgSideB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
      (regionAllocFnSplit (nfAbiNames fname σ) ts (regionWebsAt ex none r0) fd0).lfd_res
      (regionAllocFnSplit (nfAbiNames fname σ) ts (regionWebsAt ex none r0) fd0).lfd_body
        = true) :
    physImgB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
      (cellBody (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps))) b) = true := by
  obtain ⟨P0, rfl, hP0⟩ := regionLprogC_lp_funcs_split (nfAbiNames fname σ) p ex hr0 hfd hts hP
  rw [firstBody_regionPrinted, firstBody_printedLprog_regionPostFuse hP0, Option.map_some,
    Option.some.injEq] at hb
  subst hb
  have hq := RegionPhysImg.regionSl_qsave R σ exportReg (renOf ps)
  have hX : RegionExp fname p ex (regionWebsAt ex none r0) := by
    rw [regionWebsAt_none]; exact regionExp_webs ex hr0
  have h0 := physImgB_regionExport_split fname σ p hp hc hX hts fd0 hnd hacc harr hne R ps
  have h6 := physImgB_printedBody_pre hq (RegionPhysImgGate.regionSl_scratchSave hσ R ps) h0 hside
  have hcell : X86Backend.PhysImgFold.cellBaseFreeB (printedBody
      (regionAllocFnSplit (nfAbiNames fname σ) ts (regionWebsAt ex none r0) fd0).lfd_res
      (regionAllocFnSplit (nfAbiNames fname σ) ts (regionWebsAt ex none r0) fd0).lfd_body)
      = true := by
    simp only [physImgSideB, Bool.and_eq_true] at hside
    exact hside.2
  have hcell' : X86Backend.PhysImgFold.cellBaseFreeB (frameTrim (printedBody
      (regionAllocFnSplit (nfAbiNames fname σ) ts (regionWebsAt ex none r0) fd0).lfd_res
      (regionAllocFnSplit (nfAbiNames fname σ) ts (regionWebsAt ex none r0) fd0).lfd_body))
      = true := by
    unfold X86Backend.PhysImgFold.cellBaseFreeB at hcell ⊢
    rw [List.all_eq_true] at hcell ⊢
    exact fun j hj => hcell j ((FieldDomComplete.frameTrim_sublist _).subset hj)
  refine X86Backend.PhysImgCell.physImgB_cellBody hq hcell' (physImgB_frameTrim (fun X hX => ?_) h6)
  have hXc : X ∈ X86Backend.LprogAsmPrinter.calleeSavedRegs := by
    unfold unwrittenSaved at hX
    split at hX
    · exact (List.mem_filter.mp hX).1
    · cases hX
  refine regionSl_slotOfReg_none hσ R ps ?_
  simp only [X86Backend.LprogAsmPrinter.calleeSavedRegs, List.mem_cons, List.not_mem_nil,
    or_false] at hXc
  rcases hXc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **The region gate does not refuse at its image conjunct** on the trimmed printed body of
    the webs with split intervals, under the hypotheses of `physImgB_printed_split` at the slot
    map of the parts `regionCoParts σ exportReg b t r.code r.res cert` of the gate, where `r` is
    the webs `regionWebsAt ex none r0` of the export. -/
theorem regionCoStage_ne_physImgB_split (fname : String) (σ : AbiLayout)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t])
    (hp : regionExportableB p = true) (hc : p.callFree = true)
    (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    {r0 : Exported} (hr0 : exportR Γ.length fname p Γ.length 0 = some r0)
    {fd0 : Lfundef} (hfd : exportRLfundef fname p = some fd0)
    (hts : ∀ w, [t] ≠ [.reg w]) (hnd : (σ.args.map fun a => exportReg a.reg).Nodup)
    (ex : List String)
    (hacc : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length [t] (regionWebsAt ex none r0),
      AccArg σ i.li_i)
    (harr : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length [t] (regionWebsAt ex none r0),
      ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → hasPrefix q "qsave." = false)
    (hne : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length [t] (regionWebsAt ex none r0),
      ∀ ds o ss, i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM")
    {P : Lprog} {cert : List (String × String)}
    (hP : regionLprogC (nfAbiNames fname σ) p none ex = some (P, cert))
    {b : Lcmd} (hb : firstBody (regionPrinted P) = some b) (fn : String)
    (hside : physImgSideB
      (slotArrC (regionCoParts σ exportReg b t (regionWebsAt ex none r0).code
          (regionWebsAt ex none r0).res cert).cells
        (slotRen (slotArrOf σ exportReg)
          (renOf (regionCoParts σ exportReg b t (regionWebsAt ex none r0).code
            (regionWebsAt ex none r0).res cert).ps)))
      (regionAllocFnSplit (nfAbiNames fname σ) [t] (regionWebsAt ex none r0) fd0).lfd_res
      (regionAllocFnSplit (nfAbiNames fname σ) [t] (regionWebsAt ex none r0) fd0).lfd_body
        = true) :
    regionCoStage σ exportReg b t (regionWebsAt ex none r0).code (regionWebsAt ex none r0).res
      cert none fn ≠ some "physImgB" :=
  RegionPhysImgGate.regionCoStage_ne_physImgB_of σ exportReg b t _ _ cert none fn
    (physImgB_printed_split fname σ p hp hc hσ hr0 hfd hts hnd ex hacc harr hne hP hb _ _ hside)

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSplit
