/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells

/-!
# The image class of the cell body

The image check `physImgB slotArr body` (`JasminLsemAddrImage`) reads each indexed access of a
body through the reload scan `reloadOf`, and each write of an array slot through the entry scan
`entryRegB`. The cell body `ImageAddrCells.cellBody` replaces each cell access of a body, whose
base holds the pointer of an array, by its frame-word move `MOVQ D, mem.A.off` or
`MOVQ mem.A.off, S`. This module proves that the cell body of a body in the class is in the
class, when no indexed access has a cell name as its base.

The proof is a rewrite at fixed positions (`PhysImgFold.physImgB_of_pointwise`) on the names
that are no cell names: a frame-word load writes the destination of the cell load, and a
frame-word store writes a cell name, which no scan of such a name meets.

## Main results

* `cellMove_cases`: the frame-word move of an instruction is the instruction, or the move of a
  cell load or a cell store.
* `slotMov?_of_cellA`: a cell load or store is no move of `slotMov?`.
* `physImgB_cellBody`: the cell body keeps the class.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgCell

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov? cellA? CellOp cellParts?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells

variable {slotArr : String → Option (String × Nat)}

/-- The frame-word move of an instruction is the instruction, the move `MOVQ D, mem.A.off` of a
    cell load into `D`, or the move `MOVQ mem.A.off, S` of a cell store of `S`. -/
theorem cellMove_cases (body : Lcmd) (k : Nat) (i : Linstr) :
    cellMove slotArr body k i = i ∨
      (∃ D B off A, cellA? i.li_i = some (.ld D B off) ∧
        cellMove slotArr body k i = ⟨i.li_ii, .Lopn [.reg D] "MOVQ" [.reg (memName A off)]⟩) ∨
      (∃ B off S A, cellA? i.li_i = some (.st B off S) ∧
        cellMove slotArr body k i = ⟨i.li_ii, .Lopn [.reg (memName A off)] "MOVQ" [.reg S]⟩) := by
  unfold cellMove
  split
  · rename_i D B off hc
    split
    · rename_i A n _
      exact Or.inr (Or.inl ⟨D, B, off, A, hc, rfl⟩)
    · exact Or.inl rfl
  · rename_i B off S hc
    split
    · rename_i A n _
      exact Or.inr (Or.inr ⟨B, off, S, A, hc, rfl⟩)
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- A cell load or a cell store is no move of `slotMov?`. -/
theorem slotMov?_of_cellA {x : LinstrR} {c : CellOp} (h : cellA? x = some c)
    (hc : ∀ D B off, c ≠ .lea D B off) : slotMov? x = none := by
  cases c with
  | ld D B off =>
    obtain ⟨m, n, rfl, hm, hn⟩ := cellA_ld h
    rcases hm with rfl | rfl <;> simp [slotMov?, hn]
  | st B off S =>
    obtain ⟨m, n, rfl, hm, hn⟩ := cellA_st h
    rcases hm with rfl | rfl <;> simp [slotMov?, hn]
  | lea D B off => exact absurd rfl (hc D B off)

/-- **The cell body keeps the class.** When every array slot is a `qsave.` slot and no indexed
    access has a cell name as its base (`cellBaseFreeB`), the cell body of a body in the class is
    in the class. -/
theorem physImgB_cellBody
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {b : Lcmd}
    (hbase : cellBaseFreeB b = true) (h : physImgB slotArr b = true) :
    physImgB slotArr (cellBody slotArr b) = true := by
  have hS : ∀ q, gpNameB q = true → hasPrefix q "mem." = false := fun q hq' =>
    (gpNameB_prefix hq').2
  have hmem : ∀ A off, slotArr (memName A off) = none := fun A off =>
    PhysImgFold.slotArr_none_of_prefix hq (memName_prefix A off).2
  have hget : ∀ k i i', b[k]? = some i → (cellBody slotArr b)[k]? = some i' →
      i' = cellMove slotArr b k i := by
    intro k i i' hb hb'
    rw [cellBody_getElem?, hb] at hb'
    simpa using hb'.symm
  refine physImgB_of_pointwise (S := fun x => hasPrefix x "mem." = false) h
    (cellBody_length slotArr b) ?_ ?_ ?_ ?_
  · intro k i i' hb hb' f g hD
    rw [hget k i i' hb hb']
    rcases cellMove_cases (slotArr := slotArr) b k i with he | ⟨D, B, off, A, hc, he⟩ |
        ⟨B, off, S, A, hc, he⟩ <;> rw [he]
    · exact domOn_step hS hD i
    · obtain ⟨m, n, hi, -, -⟩ := cellA_ld hc
      have hm := slotMov?_of_cellA hc (fun _ _ _ => CellOp.noConfusion)
      have hd : slotArr D = none :=
        slotArr_of_slotWriteB (by rw [← hi]; exact hm) (by rw [← hi]; exact (physImgB_getElem h hb).2)
      exact domOn_step_single hd hi rfl (fun x hx => by rw [hm] at hx; cases hx) hD
    · obtain ⟨m, n, hi, -, -⟩ := cellA_st hc
      have hm := slotMov?_of_cellA hc (fun _ _ _ => CellOp.noConfusion)
      refine domOn_step_transparent hm hi (fun x hx g' => ?_) hD
      refine scanStepF_single_ne (hmem A off) rfl ?_ g'
      rintro rfl
      rw [(memName_prefix A off).1] at hx
      cases hx
  · intro k i i' hb hb'
    rw [hget k i i' hb hb']
    rcases cellMove_cases (slotArr := slotArr) b k i with he | ⟨D, B, off, A, hc, he⟩ |
        ⟨B, off, S, A, hc, he⟩ <;> rw [he]
    · exact Or.inl rfl
    · obtain ⟨m, n, hi, -, -⟩ := cellA_ld hc
      have hm := slotMov?_of_cellA hc (fun _ _ _ => CellOp.noConfusion)
      have hd : slotArr D = none :=
        slotArr_of_slotWriteB (by rw [← hi]; exact hm) (by rw [← hi]; exact (physImgB_getElem h hb).2)
      exact Or.inr ⟨by simp [isAccB], dstOk_single hd⟩
    · exact Or.inr ⟨by simp [isAccB], dstOk_single (hmem A off)⟩
  · intro k i' hb' ds o x y ss hx
    obtain ⟨i, hb, -⟩ : ∃ i, b[k]? = some i ∧ True := by
      rw [cellBody_getElem?] at hb'
      cases hbk : b[k]? with
      | none => rw [hbk] at hb'; cases hb'
      | some i => exact ⟨i, rfl, trivial⟩
    rw [hget k i i' hb hb'] at hx
    rcases cellMove_cases (slotArr := slotArr) b k i with he | ⟨D, B, off, A, hc, he⟩ |
        ⟨B, off, S, A, hc, he⟩ <;> rw [he] at hx
    · exact cellBaseFreeB_at hbase (List.mem_of_getElem? hb) hx
    · simp at hx
    · simp at hx
  · intro k i i' hb hb'
    rw [hget k i i' hb hb']
    rcases cellMove_cases (slotArr := slotArr) b k i with he | ⟨D, B, off, A, hc, he⟩ |
        ⟨B, off, S, A, hc, he⟩ <;> rw [he]
    · exact Or.inl fun d s hs => ⟨s, hs⟩
    · have hm := slotMov?_of_cellA hc (fun _ _ _ => CellOp.noConfusion)
      exact Or.inl fun d s hs => by rw [hm] at hs; cases hs
    · have hm := slotMov?_of_cellA hc (fun _ _ _ => CellOp.noConfusion)
      exact Or.inl fun d s hs => by rw [hm] at hs; cases hs

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgCell
