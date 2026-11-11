/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomNamePass

/-!
# The instructions of the allocation with split intervals

The allocation of a call-free body under a split configuration, `physBodySplit`, writes for
each instruction of the body the moves of the cells of the pieces that start or end there and
the expansion `physExpandR` of the instruction under a renaming that sends the name of a piece
to the register of the piece and every other operand through the allocation table
(`remapOperand`). The renaming of the table sends every register name to an allocated name
(`physRegName`), and so does the register of a piece.

## Main definitions

* `RkOK` — a renaming of operands that sends an operand through the table, or a register name
  to the register of a piece.
* `OpG` — an operand with good names whose indexed or displacement base is `R14`.
* `AccOK`, `BaseOK` — the operands of an instruction rename to good operands, or its access is
  covered by a good reload slot.
* `InputAcc` — the access form of an instruction of the allocator input.
* `AllocInputAcc` — the access form of the allocator input of a member of the field domain.

## Main results

* `mem_byPos` — the pieces at a position are pieces of the split.
* `mem_physBodySplit` — every instruction of the allocation with split intervals is a move
  of a piece or an instruction of the expansion of an instruction of the body.
* `physExpandR_opG` — the expansion of an instruction whose operands rename to good operands,
  or whose access is covered, is of good operands.
* `foldOK_lfundefPhysAbiOfVirtCert_split` — every instruction of the call-free physical ABI
  export with split intervals is `FoldOK` when the allocator input has the access form
  `InputAcc`.
* `allocFoldOK_of_allocInputAcc` — `AllocFoldOK` on `fieldDomB'` from `AllocInputAcc`.
* `fieldDom_cellNamesRB_of_allocInputAcc` — the stage `G20` on `fieldDomB'` from
  `AllocInputAcc`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)

/-- **The pieces at a position are pieces of the split**: the table of the pieces by position
    that `physBodySplit` builds holds at every position pieces of its list. -/
theorem mem_byPos (pcs : List SplitPiece) (n : Nat) :
    ∀ k : Nat, ∀ p ∈ (pcs.foldl (fun a p =>
      (List.range (p.last + 1 - p.first)).foldl (fun a k =>
        let q := p.first + k
        if q < a.size then a.set! q (p :: a[q]!) else a) a)
      (Array.replicate n ([] : List SplitPiece)))[k]?.getD [], p ∈ pcs := by
  refine foldl_inv _ (fun a : Array (List SplitPiece) => ∀ k : Nat, ∀ p ∈ a[k]?.getD [], p ∈ pcs) pcs _ ?_ ?_
  · intro k p hp
    simp only [Array.getElem?_replicate] at hp
    split at hp <;> simp at hp
  · intro a p hp ha
    refine foldl_inv _ (fun a : Array (List SplitPiece) => ∀ k : Nat, ∀ p ∈ a[k]?.getD [], p ∈ pcs) _ a ha ?_
    intro b k _ hb
    dsimp only
    split
    · rename_i hq
      intro k' p' hp'
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hp'
      split at hp'
      · rename_i he
        subst he
        simp only [Option.getD_some, List.mem_cons] at hp'
        rcases hp' with rfl | hp'
        · exact hp
        · refine hb (p.first + k) p' ?_
          rw [getElem!_pos b (p.first + k) hq] at hp'
          simpa [Array.getElem?_eq_getElem hq] using hp'
      · exact hb k' p' hp'
    · exact hb

/-- **The register of a piece of the split is an allocated name.** -/
theorem reg_of_mem_bodySplitPieces {body : Lcmd} {cfg : SplitCfg} {abi : IsaAbi}
    {p : SplitPiece} (hp : p ∈ bodySplitPieces body cfg abi) : ∃ ph, p.reg = physRegName ph abi := by
  unfold bodySplitPieces at hp
  obtain ⟨⟨s, x, y, ph⟩, -, hs⟩ := List.mem_filterMap.mp hp
  dsimp only at hs
  split at hs
  · cases hs
    exact ⟨ph, rfl⟩
  · cases hs

/-- **A renaming of operands through the table of a body or to the register of a piece.** -/
def RkOK (rmap : LOperand → LOperand) (pcs : List SplitPiece) (rk : LOperand → LOperand) :
    Prop :=
  ∀ o, rk o = rmap o ∨ ∃ p ∈ pcs, ∃ nm, o = .reg nm ∧ rk o = .reg p.reg

/-- **Every instruction of the allocation with split intervals** is the move of the cell of a
    piece into its register or back, or an instruction of the expansion `physExpandR` of an
    instruction of the body under a renaming through the table or to the register of a piece. -/
theorem mem_physBodySplit {shiftImm : ShiftImmOracle} {body : Lcmd} {cfg : SplitCfg}
    {mbr : String → Option String} {abi : IsaAbi} {j : Linstr}
    (hj : j ∈ physBodySplit shiftImm body cfg mbr abi) :
    (∃ p ∈ bodySplitPieces body cfg abi, ∃ mov,
      j.li_i = .Lopn [.reg p.reg] mov
          [remapOperand body (physAllocTbl body [] [] abi (some cfg)) (.reg p.name) abi] ∨
      j.li_i = .Lopn [remapOperand body (physAllocTbl body [] [] abi (some cfg)) (.reg p.name) abi]
          mov [.reg p.reg]) ∨
    ∃ i ∈ body, ∃ u64 rk,
      RkOK (fun o => remapOperand body (physAllocTbl body [] [] abi (some cfg)) o abi)
        (bodySplitPieces body cfg abi) rk ∧
      j ∈ physExpandR shiftImm u64 rk mbr i := by
  unfold physBodySplit at hj
  dsimp only at hj
  have hpos := mem_byPos (bodySplitPieces body cfg abi) (bodyTraceOut body []).length
  generalize (bodySplitPieces body cfg abi).foldl _ _ = byPos at hpos hj
  revert hj
  refine foldl_inv _ (fun st : Array Linstr × Nat => ∀ x ∈ st.1.toList,
      (∃ p ∈ bodySplitPieces body cfg abi, ∃ mov,
        x.li_i = .Lopn [.reg p.reg] mov
            [remapOperand body (physAllocTbl body [] [] abi (some cfg)) (.reg p.name) abi] ∨
        x.li_i = .Lopn
            [remapOperand body (physAllocTbl body [] [] abi (some cfg)) (.reg p.name) abi]
            mov [.reg p.reg]) ∨
      ∃ i ∈ body, ∃ u64 rk,
        RkOK (fun o => remapOperand body (physAllocTbl body [] [] abi (some cfg)) o abi)
          (bodySplitPieces body cfg abi) rk ∧
        x ∈ physExpandR shiftImm u64 rk mbr i) body (#[], 0) (by simp) ?_ j
  intro st i hi hst
  split
  · intro x hx
    simp only [Array.toList_append, List.mem_append] at hx
    rcases hx with hx | (hx | hx) | hx
    · exact hst x hx
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact Or.inl ⟨p, hpos _ p (List.mem_filter.mp hp).1, _, Or.inl rfl⟩
    · refine Or.inr ⟨i, hi, _, _, fun o => ?_, hx⟩
      dsimp only
      split
      · split
        · rename_i nm _ p hf
          exact Or.inr ⟨p, hpos _ p (List.mem_of_find?_eq_some hf), nm, rfl, rfl⟩
        · exact Or.inl rfl
      · exact Or.inl rfl
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact Or.inl ⟨p, hpos _ p (List.mem_filter.mp hp).1, _, Or.inr rfl⟩
  · intro x hx
    simp only [Array.toList_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hst x hx
    · exact Or.inr ⟨i, hi, _, _, fun o => Or.inl rfl, hx⟩

/-! ## 3. The operands of the expansion -/

section Expand

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)

/-- **A good operand**: its names are good, and the base of an indexed or a displacement
    operand is `R14`. -/
def OpG (o : LOperand) : Prop :=
  (∀ n ∈ opNames o, GoodName n) ∧ (∀ b i s, o = .arrIdx b i s → b = "R14") ∧
    ∀ a off, o = .arr a off → a = "R14"

@[simp] theorem opG_reg {x : String} : OpG (.reg x) ↔ GoodName x := by
  simp [OpG, opNames]

@[simp] theorem opG_imm {v : Nat} : OpG (.imm v) := by
  simp [OpG, opNames]

@[simp] theorem opG_arr {a : String} {off : Nat} : OpG (.arr a off) ↔ a = "R14" := by
  simp [OpG, opNames]

@[simp] theorem opG_arrIdx {b i : String} {s : Nat} :
    OpG (.arrIdx b i s) ↔ b = "R14" ∧ GoodName i := by
  simp only [OpG, opNames, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, LOperand.arrIdx.injEq, reduceCtorEq, false_imp_iff, implies_true, and_true]
  constructor
  · rintro ⟨⟨-, hi⟩, hb⟩
    exact ⟨hb b i s ⟨rfl, rfl, rfl⟩, hi⟩
  · rintro ⟨rfl, hi⟩
    exact ⟨⟨goodName_R14, hi⟩, fun _ _ _ h => h.1.symm⟩

/-- The operands of an operation; none for any other instruction. -/
def opsOf : LinstrR → List LOperand
  | .Lopn ds _ ss => ds ++ ss
  | _ => []

@[simp] theorem opsOf_lopn {ds ss : List LOperand} {o : String} :
    opsOf (.Lopn ds o ss) = ds ++ ss := rfl

/-- **An instruction of good operands is good before the fold.** -/
theorem foldOK_of_opsOf {j : Linstr} (h : ∀ a ∈ opsOf j.li_i, OpG a) : FoldOK j := by
  refine ⟨fun n hn => ?_, fun d B x sc he => ?_, fun d B x sc vn he => ?_,
    fun d B off he => ?_, fun d B off vn he => ?_⟩
  · cases hj : j.li_i with
    | Lopn ds o ss =>
      rw [hj] at hn
      obtain ⟨a, ha, hn⟩ := List.mem_flatMap.mp hn
      exact (h a (by rw [hj]; exact ha)).1 n hn
    | _ => rw [hj] at hn; simp [instrNames] at hn
  all_goals
    rw [he] at h
    simp only [opsOf_lopn, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  · exact (h _ (Or.inr rfl)).2.1 _ _ _ rfl
  · exact (h _ (Or.inr (Or.inl rfl))).2.1 _ _ _ rfl
  · exact (h _ (Or.inr rfl)).2.2 _ _ rfl
  · exact (h _ (Or.inr (Or.inl rfl))).2.2 _ _ rfl

/-- A list of instructions of good operands. -/
def LG (L : List LinstrR) : Prop := ∀ r ∈ L, ∀ a ∈ opsOf r, OpG a

theorem lG_nil : LG [] := by simp [LG]

theorem lG_append {L M : List LinstrR} (h1 : LG L) (h2 : LG M) : LG (L ++ M) := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h1 r hr
  · exact h2 r hr

theorem lG_cons {r : LinstrR} {L : List LinstrR} (h1 : ∀ a ∈ opsOf r, OpG a) (h2 : LG L) :
    LG (r :: L) := by
  intro r' hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h1
  · exact h2 r' hr

theorem lG_singleton {r : LinstrR} (h1 : ∀ a ∈ opsOf r, OpG a) : LG [r] :=
  lG_cons h1 lG_nil

end Expand

/-- Closes a goal `LG L` for a list of operations of good operands. -/
local macro "lg_close" : tactic =>
  `(tactic| (simp only [LG, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, opsOf_lopn, List.mem_append, List.cons_append, List.nil_append,
      List.append_nil, IsEmpty.forall_iff, implies_true, and_true] <;>
    simp [*, goodName_reloadScratch, goodName_reloadScratch2, goodName_R14, goodName_R15,
      LprogIsa.x86Abi_reload, LprogIsa.x86Abi_reloadSnd]))

section Expand2

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)

/-- The two reload scratches are good registers. -/
@[simp] theorem opG_reloadScratch : OpG (.reg reloadScratch) := by
  simp [goodName_reloadScratch]

@[simp] theorem opG_reloadScratch2 : OpG (.reg reloadScratch2) := by
  simp [goodName_reloadScratch2]

theorem lG_legalizeBinop {dst src : LOperand} (hd : OpG dst) (hs : OpG src) (opn mov : String) :
    LG (legalizeBinop dst src opn mov) := by
  unfold legalizeBinop
  split <;> lg_close

theorem lG_legalizeMov {dst src : LOperand} (hd : OpG dst) (hs : OpG src) (mov : String) :
    LG (legalizeMov dst src mov) := by
  unfold legalizeMov
  split <;> lg_close

theorem materializeWideImm_lG {s1 : LOperand} (hs : OpG s1) (mov : String) :
    LG (materializeWideImm s1 mov).1 ∧ OpG (materializeWideImm s1 mov).2 := by
  unfold materializeWideImm
  split
  · split
    · constructor <;> lg_close
    · exact ⟨lG_nil, hs⟩
  · exact ⟨lG_nil, hs⟩

theorem lG_scratchBinop {s0 s1 : LOperand} (h0 : OpG s0) (h1 : OpG s1) (opn mov : String) :
    LG (scratchBinop s0 s1 opn mov) := by
  unfold scratchBinop
  split <;> lg_close

theorem lG_lowerTwoAddr {dst s0 s1 : LOperand} (hd : OpG dst) (h0 : OpG s0) (h1 : OpG s1)
    (opn mov : String) : LG (lowerTwoAddr dst s0 s1 opn mov) := by
  unfold lowerTwoAddr
  obtain ⟨hp, hs⟩ := materializeWideImm_lG h1 mov
  dsimp only
  split
  · exact lG_append hp (lG_legalizeBinop hd hs _ _)
  · split
    · exact lG_append (lG_append hp (lG_scratchBinop h0 hs _ _)) (by lg_close)
    · exact lG_append (lG_append (lG_legalizeMov hd h0 _) hp) (lG_legalizeBinop hd hs _ _)

theorem lG_lowerTwoAddrShiftImm {dst s0 : LOperand} (hd : OpG dst) (h0 : OpG s0) (v : Nat)
    (opn mov : String) : LG (lowerTwoAddrShiftImm dst s0 v opn mov) := by
  unfold lowerTwoAddrShiftImm
  split
  · lg_close
  · split
    · lg_close
    · exact lG_append (lG_legalizeMov hd h0 _) (by lg_close)

theorem lG_lowerNativeShiftRotate {dst s : LOperand} (hd : OpG dst) (hs : OpG s)
    (opn mov : String) : LG (lowerNativeShiftRotate dst s opn mov) := by
  unfold lowerNativeShiftRotate
  split <;> lg_close

theorem lG_legalizeOneSrc {d s : LOperand} (hd : OpG d) (hs : OpG s) (u64 : Bool)
    (opn : String) : LG (legalizeOneSrc u64 opn d s) := by
  unfold legalizeOneSrc
  split
  · exact lG_legalizeMov hd hs _
  · lg_close

theorem lG_legalizeSpillDst {dsts srcs : List LOperand} (hd : ∀ a ∈ dsts, OpG a)
    (hs : ∀ a ∈ srcs, OpG a) (opn : String) : LG (legalizeSpillDst dsts opn srcs) := by
  unfold legalizeSpillDst
  split
  · rename_i l hl
    unfold cmovSpillDst? at hl
    split at hl
    · rename_i d c t f
      split at hl
      · cases hl
        have hd' := hd d (by simp)
        have hc := hs c (by simp)
        have ht := hs t (by simp)
        have hf := hs f (by simp)
        unfold cmovSpillSeq
        refine lG_append ?_ ?_
        · split <;> lg_close
        · split <;> split <;> lg_close
      · cases hl
    · cases hl
  · split
    · rename_i l hl
      unfold setccSpill? at hl
      split at hl
      · split at hl
        · cases hl
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
            forall_eq] at hd hs
          lg_close
        · cases hl
      · cases hl
    · split
      · rename_i l hl
        unfold andnSpill? andnSpillI? at hl
        split at hl
        · split at hl
          · cases hl
            simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
              forall_eq] at hd hs
            lg_close
          · cases hl
        · cases hl
      · intro r hr a ha
        rw [List.mem_singleton] at hr
        subst hr
        rcases List.mem_append.mp ha with ha | ha
        · exact hd a ha
        · exact hs a ha

/-- The flat cell of `R14` is good. -/
theorem goodName_memR14_0 : GoodName ("mem." ++ reloadScratch2 ++ ".0") := by
  have h : "mem." ++ reloadScratch2 ++ ".0" = memName "R14" 0 := by decide
  rw [h]
  exact goodName_memName_R14 0

theorem legalizeSibElem_lG {o : LOperand} (h : OpG o) :
    LG (legalizeSibElem o).1 ∧ OpG (legalizeSibElem o).2 := by
  unfold legalizeSibElem
  split
  · rename_i base idx scale
    simp only [opG_arrIdx] at h
    obtain ⟨rfl, hi⟩ := h
    refine ⟨lG_append ?_ ?_, ?_⟩
    · split <;> lg_close
    · split <;> lg_close
    · simp only [opG_arrIdx]
      exact ⟨by split <;> rfl, by split <;> simp [hi, goodName_reloadScratch]⟩
  · exact ⟨lG_nil, h⟩

theorem lG_legalizeMemLoad {dst src : LOperand} (hd : OpG dst) (hs : OpG src) (opn mov : String) :
    LG (legalizeMemLoad dst src opn mov) := by
  unfold legalizeMemLoad
  obtain ⟨hp, hs'⟩ := legalizeSibElem_lG hs
  dsimp only
  refine lG_append hp ?_
  split <;> lg_close

theorem lG_legalizeMemStore {dArr addr val : LOperand} (hd : OpG dArr) (ha : OpG addr)
    (hv : OpG val) (opn mov : String) : LG (legalizeMemStore dArr addr val opn mov) := by
  unfold legalizeMemStore
  obtain ⟨hp, ha'⟩ := legalizeSibElem_lG ha
  dsimp only
  split
  · rename_i b i scale he _
    rw [he] at ha'
    simp only [opG_arrIdx] at ha'
    split
    · refine lG_append hp ?_
      have := goodName_memR14_0
      lg_close
    · refine lG_append hp ?_
      rw [he]
      lg_close
  · refine lG_append hp ?_
    lg_close
  · refine lG_append hp ?_
    lg_close

theorem lG_constIdxStore {k : Option Nat} {addr val : LOperand} {l : List LinstrR}
    (ha : OpG addr) (hv : OpG val) (h : constIdxStore? k addr val = some l) : LG l := by
  unfold constIdxStore? at h
  split at h
  · rename_i b i scale
    simp only [opG_arrIdx] at ha
    obtain ⟨rfl, hi⟩ := ha
    split at h
    · split at h
      · split at h
        · cases h
          have hm : ∀ c, GoodName (memName (if sibNameSpill "R14" = true then reloadScratch2
              else "R14") c) := fun c => by
            split
            · exact goodName_memName_R14 c
            · exact goodName_memName_R14 c
          refine lG_append ?_ ?_
          · split <;> lg_close
          · intro r hr a ha
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · simp only [opsOf_lopn, List.mem_append, List.mem_cons, List.not_mem_nil,
                or_false] at ha
              rcases ha with rfl | rfl
              · exact opG_reloadScratch
              · exact hv
            · simp only [opsOf_lopn, List.mem_append, List.mem_cons, List.not_mem_nil,
                or_false] at ha
              rcases ha with rfl | rfl
              · exact opG_reg.mpr (hm _)
              · exact opG_reloadScratch
        · cases h
      · cases h
    · cases h
  · cases h

theorem lG_legalizeMemStoreK {k : Option Nat} {dArr addr val : LOperand} (hd : OpG dArr)
    (ha : OpG addr) (hv : OpG val) (opn mov : String) :
    LG (legalizeMemStoreK k dArr addr val opn mov) := by
  unfold legalizeMemStoreK
  split
  · rename_i l hl
    exact lG_constIdxStore ha hv hl
  · exact lG_legalizeMemStore hd ha hv opn mov

theorem lG_ptrLoad {q : String} (hq : GoodName q) : LG [ptrLoad q] := by
  unfold ptrLoad
  split <;> lg_close

theorem reloadScratch2_eq : reloadScratch2 = "R14" := rfl

/-- The base reload of a good operand under good reload slots is good. -/
theorem reloadMemrefBase_lG {mbr : String → Option String}
    (hq : ∀ b q, mbr b = some q → GoodName q) {o : LOperand} (h : OpG o) :
    LG (reloadMemrefBase mbr o).1 ∧ OpG (reloadMemrefBase mbr o).2 := by
  unfold reloadMemrefBase
  split
  · rename_i b y sc
    split
    · rename_i q hb
      simp only [opG_arrIdx] at h
      exact ⟨lG_ptrLoad (hq _ _ hb), by simp [h.2, reloadScratch2_eq]⟩
    · exact ⟨lG_nil, h⟩
  · exact ⟨lG_nil, h⟩

/-- **The base reload of a covered access** loads the base into `R14` from a good slot and
    addresses through `R14`. -/
theorem reloadMemrefBase_acc {mbr : String → Option String} {b y q : String}
    (hb : mbr b = some q) (hq : GoodName q) (hy : GoodName y) :
    LG (reloadMemrefBase mbr (.arrIdx b y 8)).1 ∧
      OpG (reloadMemrefBase mbr (.arrIdx b y 8)).2 := by
  simp only [reloadMemrefBase, hb]
  exact ⟨lG_ptrLoad hq, by simp [hy, reloadScratch2_eq]⟩

/-- The tagged instructions of a list of good instructions are good. -/
theorem lG_map {L : List LinstrR} (h : LG L) (ii : Nat) :
    ∀ r ∈ L.map (fun r => (⟨ii, r⟩ : Linstr)), ∀ a ∈ opsOf r.li_i, OpG a := by
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  exact h r' hr'

/-- **A covered access**: the renamed base of the access has a good reload slot, and its
    renamed index is good. -/
def BaseOK (rk : LOperand → LOperand) (mbr : String → Option String) (b y : String) : Prop :=
  ∃ b' y' q, rk (.arrIdx b y 8) = .arrIdx b' y' 8 ∧ mbr b' = some q ∧ GoodName y' ∧ GoodName q

/-- **The operands of an instruction under a renaming**: every operand renames to a good
    operand, or the instruction is an indexed load or store whose access is covered and whose
    other operands rename to good operands. -/
def AccOK (rk : LOperand → LOperand) (mbr : String → Option String) (w : LinstrR) : Prop :=
  ∀ ds o ss, w = .Lopn ds o ss →
    (∀ a ∈ ds ++ ss, OpG (rk a)) ∨
    (∃ d b y, o = "LOADIDX" ∧ ds = [.reg d] ∧ ss = [.arrIdx b y 8] ∧ OpG (rk (.reg d)) ∧
      BaseOK rk mbr b y) ∨
    (∃ d b y v, o = "STOREIDX" ∧ ds = [.reg d] ∧ ss = [.arrIdx b y 8, .reg v] ∧
      OpG (rk (.reg d)) ∧ OpG (rk (.reg v)) ∧ BaseOK rk mbr b y)

/-- **Every instruction of the expansion of an instruction is of good operands**, when its
    operands rename to good operands or its access is covered, and the reload slots are
    good. -/
theorem physExpandR_opG {shiftImm : ShiftImmOracle} {u64 : Bool} {rk : LOperand → LOperand}
    {mbr : String → Option String} (hq : ∀ b q, mbr b = some q → GoodName q) {i : Linstr}
    (hi : AccOK rk mbr i.li_i) :
    ∀ r ∈ physExpandR shiftImm u64 rk mbr i, ∀ a ∈ opsOf r.li_i, OpG a := by
  unfold physExpandR
  dsimp only
  split
  · rename_i d dt opn s0 s1 st he
    rcases hi _ _ _ he with hall | ⟨d', b, y, rfl, hd, hs, -⟩ |
        ⟨d', b, y, v, rfl, hd, hs, hdg, hvg, b', y', q, hrb, hmb, hyg, hqg⟩
    · have hd : OpG (rk d) := hall d (by simp)
      have h0 : OpG (rk s0) := hall s0 (by simp)
      have h1 : OpG (rk s1) := hall s1 (by simp)
      split
      · split
        · exact lG_map (lG_lowerTwoAddrShiftImm hd h0 _ _ _) _
        · exact lG_map (lG_lowerTwoAddr hd h0 h1 _ _) _
      · split
        · rename_i d'' opn' addr val he'
          rw [he] at he'
          simp only [LinstrR.Lopn.injEq, List.cons.injEq] at he'
          obtain ⟨⟨rfl, -⟩, rfl, rfl, rfl, -⟩ := he'
          split
          · obtain ⟨hp, ha⟩ := reloadMemrefBase_lG hq h0
            intro r hr
            rcases List.mem_append.mp hr with hr | hr
            · exact lG_map hp _ r hr
            · exact lG_map (lG_legalizeMemStoreK hd ha h1 _ _) _ r hr
          · refine lG_map (lG_legalizeSpillDst ?_ ?_ _) _
            · simpa using hd
            · simpa using ⟨h0, h1⟩
        · rename_i dsts opn' srcs _ he'
          rw [he] at he'
          simp only [LinstrR.Lopn.injEq] at he'
          obtain ⟨rfl, rfl, rfl⟩ := he'
          refine lG_map (lG_legalizeSpillDst ?_ ?_ _) _
          · intro a ha
            obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
            exact hall a' (List.mem_append_left _ ha')
          · intro a ha
            obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
            exact hall a' (List.mem_append_right _ ha')
        · rename_i hne
          exact absurd he (hne _ _ _)
    · simp at hs
    · simp only [List.cons.injEq] at hd hs
      obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨rfl, rfl, rfl⟩ := hs
      have hnb : isTwoAddrBinop "STOREIDX" = false := by decide +kernel
      simp only [hnb, Bool.false_eq_true, ite_false]
      split
      · rename_i d'' opn' addr val he'
        rw [he] at he'
        simp only [LinstrR.Lopn.injEq, List.cons.injEq] at he'
        obtain ⟨⟨rfl, -⟩, rfl, rfl, rfl, -⟩ := he'
        have hms : isMemStore "STOREIDX" = true := by decide +kernel
        simp only [hms, ite_true, hrb]
        obtain ⟨hp, ha⟩ := reloadMemrefBase_acc hmb hqg hyg
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact lG_map hp _ r hr
        · exact lG_map (lG_legalizeMemStoreK hdg ha hvg _ _) _ r hr
      · rename_i dsts opn' srcs hne he'
        rw [he] at he'
        simp only [LinstrR.Lopn.injEq] at he'
        obtain ⟨rfl, rfl, rfl⟩ := he'
        exact (hne _ _ _ rfl rfl).elim
      · rename_i hne
        exact absurd he (hne _ _ _)
  · rename_i d opn s he
    rcases hi _ _ _ he with hall | ⟨d', b, y, rfl, hd, hs, hdg, b', y', q, hrb, hmb, hyg, hqg⟩ |
        ⟨d', b, y, v, rfl, hd, hs, -⟩
    · have hd : OpG (rk d) := hall d (by simp)
      have hs : OpG (rk s) := hall s (by simp)
      split
      · exact lG_map (lG_lowerNativeShiftRotate hd hs _ _) _
      · split
        · obtain ⟨hp, ha⟩ := reloadMemrefBase_lG hq hs
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact lG_map hp _ r hr
          · exact lG_map (lG_legalizeMemLoad hd ha _ _) _ r hr
        · exact lG_map (lG_legalizeOneSrc hd hs _ _) _
    · simp only [List.cons.injEq, and_true] at hd hs
      subst hd hs
      have hns : isNativeShiftRotate "LOADIDX" = false := by decide +kernel
      have hml : isMemLoad "LOADIDX" = true := by decide +kernel
      simp only [hns, hml, Bool.false_eq_true, ite_false, ite_true, hrb]
      obtain ⟨hp, ha⟩ := reloadMemrefBase_acc hmb hqg hyg
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact lG_map hp _ r hr
      · exact lG_map (lG_legalizeMemLoad hdg ha _ _) _ r hr
    · simp at hs
  · rename_i dsts opn srcs h1 h2 he
    rcases hi _ _ _ he with hall | ⟨d', b, y, rfl, rfl, rfl, -⟩ | ⟨d', b, y, v, rfl, rfl, rfl, -⟩
    · intro r hr a ha
      rw [List.mem_singleton] at hr
      subst hr
      simp only [opsOf_lopn, List.mem_append, List.mem_map] at ha
      rcases ha with ⟨a', ha', rfl⟩ | ⟨a', ha', rfl⟩
      · exact hall a' (List.mem_append_left _ ha')
      · exact hall a' (List.mem_append_right _ ha')
    · exact (h2 _ _ rfl rfl).elim
    · exact (h1 _ _ _ _ _ rfl rfl).elim
  · rename_i h1 h2 h3
    intro r hr a ha
    rw [List.mem_singleton] at hr
    subst hr
    cases hw : i.li_i with
    | Lopn ds o ss => exact absurd hw (h3 _ _ _)
    | _ => rw [hw] at ha; simp [opsOf] at ha

end Expand2

/-! ## 4. The allocated body with split intervals -/

section Body

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)

/-- A renamed register name through the table is an allocated name. -/
theorem opG_remapOperand_reg (body : Lcmd) (tbl : Array Nat) (n : String) :
    OpG (remapOperand body tbl (.reg n)) := by
  simp only [remapOperand, opG_reg]
  exact goodName_physRegName _

/-- **A renaming through the table or to the registers of pieces keeps `AccOK`.** -/
theorem accOK_of_rkOK {body : Lcmd} {tbl : Array Nat} {pcs : List SplitPiece}
    (hpcs : ∀ p ∈ pcs, GoodName p.reg) {rk : LOperand → LOperand}
    (hrk : RkOK (fun o => remapOperand body tbl o) pcs rk) {mbr : String → Option String}
    {w : LinstrR} (h : AccOK (fun o => remapOperand body tbl o) mbr w) : AccOK rk mbr w := by
  have hreg : ∀ x, OpG (rk (.reg x)) := by
    intro x
    rcases hrk (.reg x) with he | ⟨p, hp, nm, -, he⟩
    · rw [he]; exact opG_remapOperand_reg _ _ _
    · rw [he, opG_reg]; exact hpcs p hp
  have hop : ∀ a, OpG (remapOperand body tbl a) → OpG (rk a) := by
    intro a ha
    rcases hrk a with he | ⟨p, hp, nm, rfl, -⟩
    · rw [he]; exact ha
    · exact hreg nm
  have hidx : ∀ b y, rk (.arrIdx b y 8) = remapOperand body tbl (.arrIdx b y 8) := by
    intro b y
    rcases hrk (.arrIdx b y 8) with he | ⟨p, -, nm, he, -⟩
    · exact he
    · cases he
  intro ds o ss he
  rcases h ds o ss he with hall | ⟨d, b, y, ho, hd, hs, -, hb⟩ | ⟨d, b, y, v, ho, hd, hs, -, -, hb⟩
  · exact Or.inl fun a ha => hop a (hall a ha)
  · refine Or.inr (Or.inl ⟨d, b, y, ho, hd, hs, hreg d, ?_⟩)
    obtain ⟨b', y', q, h1, h2⟩ := hb
    exact ⟨b', y', q, by rw [hidx]; exact h1, h2⟩
  · refine Or.inr (Or.inr ⟨d, b, y, v, ho, hd, hs, hreg d, hreg v, ?_⟩)
    obtain ⟨b', y', q, h1, h2⟩ := hb
    exact ⟨b', y', q, by rw [hidx]; exact h1, h2⟩

/-- **Every instruction of the allocation with split intervals is of good operands**, when
    every instruction of the body has `AccOK` under the renaming through the table and the
    reload slots are good. -/
theorem physBodySplit_opG {shiftImm : ShiftImmOracle} {body : Lcmd} {cfg : SplitCfg}
    {mbr : String → Option String} (hq : ∀ b q, mbr b = some q → GoodName q)
    (hacc : ∀ i ∈ body, AccOK (fun o => remapOperand body (physAllocTbl body [] [] x86Abi
      (some cfg)) o) mbr i.li_i) :
    ∀ j ∈ physBodySplit shiftImm body cfg mbr x86Abi, ∀ a ∈ opsOf j.li_i, OpG a := by
  intro j hj
  have hpcs : ∀ p ∈ bodySplitPieces body cfg x86Abi, GoodName p.reg := by
    intro p hp
    obtain ⟨ph, he⟩ := reg_of_mem_bodySplitPieces hp
    rw [he]
    exact goodName_physRegName ph
  rcases mem_physBodySplit hj with ⟨p, hp, mov, he | he⟩ | ⟨i, hi, u64, rk, hrk, hj⟩
  · rw [he]
    intro a ha
    simp only [opsOf_lopn, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact opG_reg.mpr (hpcs p hp)
    · exact opG_remapOperand_reg _ _ _
  · rw [he]
    intro a ha
    simp only [opsOf_lopn, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact opG_remapOperand_reg _ _ _
    · exact opG_reg.mpr (hpcs p hp)
  · exact physExpandR_opG hq (accOK_of_rkOK hpcs hrk (hacc i hi)) j hj

/-- The store through `R14` of a good value is of good operands. -/
theorem lG_storeImmVia {v : String} (hv : GoodName v) (k : Nat) : LG (storeImmVia v k) := by
  unfold storeImmVia
  split <;> lg_close

/-- **The base reloads of the constant writes keep good operands**, under good reload
    slots. -/
theorem reloadArrImmBody_opG {mbr : String → Option String}
    (hq : ∀ b q, mbr b = some q → GoodName q) {l : Lcmd}
    (h : ∀ r ∈ l, ∀ a ∈ opsOf r.li_i, OpG a) :
    ∀ r ∈ reloadArrImmBody mbr l, ∀ a ∈ opsOf r.li_i, OpG a := by
  intro r hr
  obtain ⟨r0, hr0, hr⟩ := List.mem_flatMap.mp hr
  split at hr
  · rename_i l' hl
    have h0 := h r0 hr0
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    unfold reloadArrImm at hl
    split at hl
    · rename_i b n w he
      split at hl
      · obtain ⟨q, hb, rfl⟩ := Option.map_eq_some_iff.mp hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact lG_ptrLoad (hq _ _ hb) _ (List.mem_singleton_self _)
        · intro a ha
          simp only [opsOf_lopn, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at ha
          rcases ha with rfl | rfl | rfl <;> simp [goodName_reloadScratch2]
      · cases hl
    · rename_i d b v k he
      split at hl
      · obtain ⟨q, hb, rfl⟩ := Option.map_eq_some_iff.mp hl
        have hv : GoodName v := by
          have := h0 (.reg v) (by rw [he]; simp)
          simpa using this
        rcases List.mem_cons.mp hx with rfl | hx
        · exact lG_ptrLoad (hq _ _ hb) _ (List.mem_singleton_self _)
        · exact lG_storeImmVia hv k x hx
      · cases hl
    · cases hl
  · rw [List.mem_singleton] at hr
    rw [hr]
    exact h _ hr0

/-- The insertion of the epilogue keeps good operands. -/
theorem insertEpilogue_opG {body epi : Lcmd} (h1 : ∀ r ∈ body, ∀ a ∈ opsOf r.li_i, OpG a)
    (h2 : ∀ r ∈ epi, ∀ a ∈ opsOf r.li_i, OpG a) :
    ∀ r ∈ insertEpilogue body epi, ∀ a ∈ opsOf r.li_i, OpG a := by
  intro r hr
  simp only [insertEpilogue, List.mem_append, List.mem_singleton] at hr
  rcases hr with (hr | hr) | rfl
  · exact h1 r (List.dropLast_subset _ hr)
  · exact h2 r hr
  · simp [opsOf]

/-- A save slot of an argument register is good. -/
theorem goodName_of_abiSlotOfExt {reg q : String} (h : abiSlotOfExt reg = some q) :
    GoodName q := by
  unfold abiSlotOfExt abiSaveOfExt abiSaveOf at h
  split at h
  · rename_i s hs
    simp only [Option.some.injEq] at h
    subst h
    split at hs
    · rename_i t ht
      simp only [Option.some.injEq] at hs
      subst hs
      split_ifs at ht <;> simp only [Option.some.injEq] at ht <;> subst ht <;>
        exact goodName_of_head (by decide) (by decide)
    · split_ifs at hs <;> simp only [Option.some.injEq] at hs <;> subst hs <;>
        exact goodName_of_head (by decide) (by decide)
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact goodName_of_head (by simp [String.toList_append])
      (abiStackOff?_of_head (by simp [String.toList_append]))

/-- **A base paired with a save slot is covered** at every table of a call-free body: the
    renamed base is the key of its pair in the reload map, whose slot is good. -/
theorem baseOK_of_pair {body1 : Lcmd} {tk : Array Nat} (hcf : bodyHasCall body1 = false)
    {pairs : List (String × String)} {b y : String} (hfr : isFrameSlotName b = false)
    (hb : ∃ p ∈ pairs, p.1 = b ∧ (abiSlotOfExt p.2).isSome = true) :
    BaseOK (fun o => remapOperand body1 (straightCallComposeTable body1 tk) o x86Abi)
      (fun base => ((pairs.filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 tk p.1 x86Abi, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd) b y := by
  obtain ⟨p, hp, rfl, hs⟩ := hb
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hs
  have hst : bodyStraightCall body1 = false := by
    simp [bodyStraightCall, hcf]
  have hkey : physNameForBody body1 tk p.1 x86Abi
      = physRegName (physMapTabled (straightCallComposeTable body1 tk)
          (nameSlot body1 p.1)) x86Abi := by
    simp [physNameForBody, hfr, hcf, straightCallComposeTable, hst]
  have hmem : (physNameForBody body1 tk p.1 x86Abi, s) ∈
      pairs.filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 tk p.1 x86Abi, saveName)
        | none => none) :=
    List.mem_filterMap.mpr ⟨p, hp, by simp [hs]⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp
    ((List.find?_isSome (p := fun e : String × String =>
      e.1 == physNameForBody body1 tk p.1 x86Abi)).mpr ⟨_, hmem, by simp⟩)
  obtain ⟨p', hp', hf⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some he)
  have hq : ∃ q, abiSlotOfExt p'.2 = some q ∧ e.2 = q := by
    revert hf
    cases abiSlotOfExt p'.2 with
    | none => intro hf; cases hf
    | some q => intro hf; cases hf; exact ⟨q, rfl, rfl⟩
  obtain ⟨q, hq, hqe⟩ := hq
  refine ⟨_, _, q, rfl, ?_, goodName_physRegName _, goodName_of_abiSlotOfExt hq⟩
  rw [← hkey]
  simp only [he, Option.map_some, hqe]

/-- Every slot of the reload map is good. -/
theorem goodName_of_reloadMap {body1 : Lcmd} {tk : Array Nat} {pairs : List (String × String)}
    {base q : String}
    (h : ((pairs.filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 tk p.1 x86Abi, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd = some q) :
    GoodName q := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨p', -, hf⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some he)
  revert hf
  cases hs : abiSlotOfExt p'.2 with
  | none => intro hf; cases hf
  | some q => intro hf; cases hf; exact goodName_of_abiSlotOfExt hs

/-- The allocated name of a register name of a call-free body is good. -/
theorem goodName_physNameForBody {body : Lcmd} (hcf : bodyHasCall body = false)
    (tbl : Array Nat) {n : String} (hn : GoodName n) : GoodName (physNameForBody body tbl n) := by
  unfold physNameForBody
  split
  · exact hn
  · simp only [hcf, Bool.false_eq_true, ite_false]
    exact goodName_physRegName _

/-- **The prologue, the further saves and the epilogue are of good operands**, at good
    argument registers. -/
theorem prologue_opG (virt : Lfundef) (tbl : Array Nat) {abiArgs : List String}
    (habi : ∀ a ∈ abiArgs, GoodName a) :
    ∀ r ∈ buildPrologue virt tbl (fun _ => none) ++ extraInputSaves abiArgs,
      ∀ a ∈ opsOf r.li_i, OpG a := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · simp only [buildPrologue, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      intro a ha <;>
      simp only [opsOf_lopn, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      rcases ha with rfl | rfl <;>
      exact opG_reg.mpr (goodName_of_head (by decide) (by decide))
  · obtain ⟨reg, hreg, hr⟩ := List.mem_filterMap.mp hr
    have hg : GoodName reg := habi reg (List.mem_of_mem_drop (List.mem_of_mem_filter hreg))
    split at hr
    · rename_i q hq
      cases hr
      have hq' : abiSlotOfExt reg = some q := by simp [abiSlotOfExt, hq]
      intro a ha
      simp only [opsOf_lopn, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact opG_reg.mpr (goodName_of_abiSlotOfExt hq')
      · exact opG_reg.mpr hg
    · cases hr

theorem epilogue_opG : ∀ r ∈ calleeSaveRestoreEpilogue, ∀ a ∈ opsOf r.li_i, OpG a := by
  intro r hr
  simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    intro a ha <;>
    simp only [opsOf_lopn, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
    rcases ha with rfl | rfl <;>
    exact opG_reg.mpr (goodName_of_head (by decide) (by decide))

/-- **The materialization of the argument pointers is of good operands**, at good argument
    registers of a call-free body. -/
theorem buildArgPtrMaterialize_opG {virt : Lfundef} (hcf : bodyHasCall virt.lfd_body = false)
    (tbl : Array Nat) {abiArgs : List String} (habi : ∀ a ∈ abiArgs, GoodName a) :
    ∀ r ∈ buildArgPtrMaterialize virt tbl abiArgs (fun _ => none),
      ∀ a ∈ opsOf r.li_i, OpG a := by
  intro r hr
  unfold buildArgPtrMaterialize at hr
  obtain ⟨⟨reg, j⟩, hmem, hr⟩ := List.mem_flatMap.mp hr
  have hreg : reg ∈ abiArgs := by
    obtain ⟨-, -, he⟩ := List.mem_zipIdx hmem
    rw [he]
    exact List.getElem_mem _
  have hg : GoodName reg := habi reg hreg
  have hd : GoodName (physNameForBody virt.lfd_body tbl (argName j)) :=
    goodName_physNameForBody hcf tbl (goodName_of_head (argName_head j)
      (abiStackOff?_of_head (by simp [argName, String.toList_append])))
  simp only at hr
  split at hr
  · simp at hr
  · rcases hs : abiSlotOfExt reg with _ | q
    · split_ifs at hr <;>
        simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
        (try rcases hr with rfl | rfl) <;>
        intro a ha <;>
        simp only [opsOf_lopn, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at ha <;>
        rcases ha with rfl | rfl <;> simp [hd, hg, goodName_reloadScratch]
    · have hq' := goodName_of_abiSlotOfExt hs
      split_ifs at hr <;>
        simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
        (try rcases hr with rfl | rfl) <;>
        intro a ha <;>
        simp only [opsOf_lopn, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at ha <;>
        rcases ha with rfl | rfl <;> simp [hd, hq', goodName_reloadScratch]

/-- **The body of the allocation with split intervals is of good operands**, from the frame
    code, the base reloads and a body of good operands. -/
theorem lfdBody_opG {V : Lfundef} (hcf : bodyHasCall V.lfd_body = false) (T : Array Nat)
    {abiArgs : List String} (habi : ∀ a ∈ abiArgs, GoodName a)
    {M : String → Option String} (hM : ∀ b q, M b = some q → GoodName q) {X : Lcmd}
    (hX : ∀ r ∈ X, ∀ a ∈ opsOf r.li_i, OpG a) (f : Linstr → Bool) :
    ∀ j ∈ (buildPrologue V T (fun _ => none) ++ extraInputSaves abiArgs) ++
      (buildArgPtrMaterialize V T abiArgs (fun _ => none) x86Abi ++
        insertEpilogue (reloadArrImmBody M (X.filter f)) calleeSaveRestoreEpilogue),
      ∀ a ∈ opsOf j.li_i, OpG a := by
  intro j hj
  simp only [List.mem_append] at hj
  rcases hj with hj | hj | hj
  · exact prologue_opG V T habi j (List.mem_append.mpr hj)
  · exact buildArgPtrMaterialize_opG hcf T habi j hj
  · exact insertEpilogue_opG (reloadArrImmBody_opG hM fun r hr => hX r (List.mem_of_mem_filter hr))
      epilogue_opG j hj

/-- **The access form of the allocator input**: every operation reads and writes registers and
    immediates only, or is an indexed load or store at an `8`-byte stride whose base is no
    frame-slot name and is paired with an argument register that has a save slot. -/
def InputAcc (pairs : List (String × String)) (w : LinstrR) : Prop :=
  ∀ ds o ss, w = .Lopn ds o ss →
    (∀ a ∈ ds ++ ss, (∃ x, a = .reg x) ∨ ∃ v, a = .imm v) ∨
    (∃ d b y, o = "LOADIDX" ∧ ds = [.reg d] ∧ ss = [.arrIdx b y 8] ∧
      isFrameSlotName b = false ∧ ∃ p ∈ pairs, p.1 = b ∧ (abiSlotOfExt p.2).isSome = true) ∨
    (∃ d b y v, o = "STOREIDX" ∧ ds = [.reg d] ∧ ss = [.arrIdx b y 8, .reg v] ∧
      isFrameSlotName b = false ∧ ∃ p ∈ pairs, p.1 = b ∧ (abiSlotOfExt p.2).isSome = true)

/-- **The access form gives `AccOK`** under the renaming through a table of a call-free body
    and the reload map of the pairs at that table. -/
theorem accOK_of_inputAcc {body1 : Lcmd} {tk : Array Nat} (hcf : bodyHasCall body1 = false)
    {pairs : List (String × String)} {w : LinstrR} (h : InputAcc pairs w) :
    AccOK (fun o => remapOperand body1 (straightCallComposeTable body1 tk) o x86Abi)
      (fun base => ((pairs.filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 tk p.1 x86Abi, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd) w := by
  intro ds o ss he
  rcases h ds o ss he with hall | ⟨d, b, y, ho, hd, hs, hfr, hp⟩ |
      ⟨d, b, y, v, ho, hd, hs, hfr, hp⟩
  · refine Or.inl fun a ha => ?_
    rcases hall a ha with ⟨x, rfl⟩ | ⟨v, rfl⟩
    · exact opG_remapOperand_reg _ _ _
    · simp [remapOperand]
  · exact Or.inr (Or.inl ⟨d, b, y, ho, hd, hs, opG_remapOperand_reg _ _ _,
      baseOK_of_pair hcf hfr hp⟩)
  · exact Or.inr (Or.inr ⟨d, b, y, v, ho, hd, hs, opG_remapOperand_reg _ _ _,
      opG_remapOperand_reg _ _ _, baseOK_of_pair hcf hfr hp⟩)

/-- **Every instruction of the call-free physical ABI export with split intervals is good before
    the fold**, when the allocator input has the access form at the pairs of the argument
    bases and the argument registers are good. -/
theorem foldOK_lfundefPhysAbiOfVirtCert_split (virt0 : Lfundef) (outArg' : String)
    (inArgs' : List String) (shiftImm : ShiftImmOracle) (abiArgs : List String)
    (abiTyin : List Nat) (posBind : Bool)
    (hcf : bodyHasCall ((if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread virt0.lfd_body)
        = false)
    (habi : ∀ a ∈ abiArgs, GoodName a)
    (hacc : ∀ i ∈ (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread virt0.lfd_body,
      InputAcc (argBasePairs posBind outArg' inArgs' abiArgs) i.li_i) :
    ∀ j ∈ (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' [] shiftImm abiArgs abiTyin x86Abi
      posBind [] bodySplitOpt).1.lfd_body, FoldOK j := by
  intro j hj
  refine foldOK_of_opsOf ?_
  unfold lfundefPhysAbiOfVirtCert at hj
  simp only [List.foldl_nil, faReloadPairs, List.map_nil, List.nil_append, List.mem_append,
    or_assoc] at hj
  rcases hj with hj | hj | hj | hj
  · apply prologue_opG _ _ habi j
    exact List.mem_append_left _ hj
  · exact prologue_opG virt0 #[] habi j (List.mem_append_right _ hj)
  · exact buildArgPtrMaterialize_opG hcf _ habi j hj
  · refine insertEpilogue_opG (reloadArrImmBody_opG ?_ fun r hr => ?_) epilogue_opG j hj
    · intro b q hq
      exact goodName_of_reloadMap hq
    · replace hr := List.mem_of_mem_filter hr
      revert hr r
      split
      · rename_i cfg heq
        simp only [heq]
        exact physBodySplit_opG (fun b q hq => goodName_of_reloadMap hq)
          (fun i hi => accOK_of_inputAcc hcf (hacc i hi))
      · rename_i heq
        simp [bodySplitOpt, hcf] at heq

end Body

/-! ## 5. The field domain -/

section Field

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapAlign (regionAllocBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (fieldAbi)

/-- **The access form of the allocator input of a member of the field domain**: on the
    narrowed output of the chain and its export, the result is no register, and every
    instruction of the allocator input `regionAllocBody` at the webs of the export has the
    access form `InputAcc` at the pairs of the argument bases. -/
def AllocInputAcc (e : _root_.Hax.TExpr) (σ : AbiLayout) (fname : String) : Prop :=
  ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
    (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0])
    (r0 : Exported),
    haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩ →
    NarrowWords.narrowPrep q = some q' →
    exportR ((nfCtx σ).map NarrowWords.wideTy).length fname (legalizeRegion q')
      ((nfCtx σ).map NarrowWords.wideTy).length 0 = some r0 →
    (∀ w, NarrowWords.wideTy t0 ≠ .reg w) ∧
      ∀ i ∈ regionAllocBody (nfAbiNames fname σ) ((nfCtx σ).map NarrowWords.wideTy).length
        [NarrowWords.wideTy t0] (regionWebsAt (regionWebsEx σ exportReg) none r0),
        InputAcc (argBasePairs true (nfAbiNames fname σ).outArg (nfAbiNames fname σ).inArgs
          (nfAbiNames fname σ).abiArgs) i.li_i

/-- The argument registers of the field layout are good. -/
theorem goodName_abiArgs_fieldAbi {k n : Nat} (hk : k = 1 ∨ k = 2) (fname : String) :
    ∀ a ∈ (nfAbiNames fname (fieldAbi k n)).abiArgs, GoodName a := by
  have x0 : exportReg "%rdi" = "RDI" := by decide
  have x1 : exportReg "%rsi" = "RSI" := by decide
  have x2 : exportReg "%rdx" = "RDX" := by decide
  rcases hk with rfl | rfl <;>
    simp only [nfAbiNames, fieldAbi, List.range_succ, FieldRoute.fieldArgReg,
      FieldRoute.fieldArgName] <;>
    intro a ha <;>
    simp [x0, x1, x2] at ha <;>
    rcases ha with rfl | rfl | rfl <;>
    exact goodName_of_head (by decide) (by decide)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String}

/-- **The allocated function of a member is of `FoldOK` instructions** when its allocator
    input has the access form. -/
theorem allocFoldOK_of_allocInputAcc (h : fieldDomB' e σ = true) (hA : AllocInputAcc e σ fname) :
    AllocFoldOK e σ fname := by
  intro t0 q q' P0 c hq hq' hx nf hnf j hj
  have hd := fieldDomB_of_fieldDomB' h
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal hd) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hcf0 : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree hd hq))
  have hEx : regionExportableB (legalizeRegion q') = true := fieldDom_legalize hE1
  unfold regionAllocC at hx
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
  obtain ⟨r0, hr0, fd0, -, hxe⟩ := hx
  obtain ⟨hts, hacc⟩ := hA t0 q q' r0 hq hq' hr0
  have hX : RegionExp fname (legalizeRegion q') (regionWebsEx σ exportReg)
      (regionWebsAt (regionWebsEx σ exportReg) none r0) := by
    rw [regionWebsAt_none]
    exact regionExp_webs _ hr0
  have hshape : ∀ i ∈ (regionWebsAt (regionWebsEx σ exportReg) none r0).code,
      RegionAllocMapDom.ShapeB i.1 := fun i hi => (hX.mnemDom hEx hcf0 i hi).2.2
  have hBs := RegionAllocMapDom.shapeB_regionAllocBody (nfAbiNames fname σ)
    ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] _ hshape
  have hcf := RegionAllocMapDom.bodyHasCall_of_shapeB hBs
  obtain ⟨k, n, hk, rfl, -⟩ := fieldDomB'_layout h
  have habi := goodName_abiArgs_fieldAbi (n := n) (fieldDomE_k hk) fname
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, -⟩ := hxe
  simp only [List.mem_singleton] at hnf
  subst hnf
  revert hj
  split
  · rename_i w hw
    simp only [List.cons.injEq, and_true] at hw
    exact absurd hw (hts w)
  · intro hj
    unfold regionAllocBody at hcf hacc
    split at hcf
    · rename_i w hw
      simp only [List.cons.injEq, and_true] at hw
      exact absurd hw (hts w)
    · split at hacc
      · rename_i w hw
        simp only [List.cons.injEq, and_true] at hw
        exact absurd hw (hts w)
      dsimp only at hcf hacc hj
      simp only [calleeAllocCert, calleeOutsT] at hj
      refine foldOK_lfundefPhysAbiOfVirtCert_split _ _ _ _ _ _ _ ?_ habi ?_ j hj
      · exact hcf
      · exact hacc

variable {b : Lcmd} {t : JasminTy} {r : Exported} {cert : List (String × String)}

/-- **`CellBaseScratch` on the printed body of a member** from the access form of its
    allocator input. -/
theorem cellBaseScratch_of_allocInputAcc (h : fieldDomB' e σ = true)
    (hB : FieldBody e σ fname b t r cert) (hA : AllocInputAcc e σ fname) : CellBaseScratch b :=
  cellBaseScratch_of_allocFoldOK hB (allocFoldOK_of_allocInputAcc h hA)

/-- **The printed body of a member reads no stack-argument name**, from the access form of its
    allocator input. -/
theorem stackReadFreeB_of_allocInputAcc (h : fieldDomB' e σ = true)
    (hB : FieldBody e σ fname b t r cert) (hA : AllocInputAcc e σ fname) :
    X86Backend.ImageAddrRoute.stackReadFreeB b = true :=
  stackReadFreeB_of_allocFoldOK hB (allocFoldOK_of_allocInputAcc h hA)

/-- **Stage `G20` on `fieldDomB'`** from the access form of the allocator input. -/
theorem fieldDom_cellNamesRB_of_allocInputAcc (h : fieldDomB' e σ = true)
    (hB : FieldBody e σ fname b t r cert) (hA : AllocInputAcc e σ fname) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "cellNamesRB" :=
  fieldDom_cellNamesRB_of_allocFoldOK h hB (allocFoldOK_of_allocInputAcc h hA)

end Field

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
