/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCellBase

/-!
# The cell fold check on the field domain from the fold of the code

The stage `regionFoldB` of the region gate passes when the parts have no cell array, or when
the code `fused` behind the prefix has a cell fold `cellFoldLR` at the cell arrays and no source
or target of the pairs `ps` is a cell name. On the field domain the pairs are those of an
allocation certificate of a body without a call, filtered to the argument names: a source is
an argument name `a<j>`, and a target is an allocated name, a register of the pool `RAX` to
`R13`, a vector register `XMM<i>` or a spill name `k.<i>`, `kv.<i>`. A cell name
`memName A o` begins with `m`, which none of these does. So the second conjunct holds on the
field domain, and the stage reduces to the cell fold of the code.

## Main results

* `physRegName_head`, `allocName_head` — an allocated name does not begin with `m`.
* `isCellB_of_head` — a name that does not begin with `m` is no cell name.
* `certArgs_not_cell` — no source or target of the pairs of an allocation certificate of a
  body without a call is a cell name.
* `regionCoStage_ne_regionFoldB` — the stage from the condition on the parts alone.
* `fieldDom_regionFoldB_of_cellFold` — the stage `G12` on the field domain, when the parts have
  no cell array or the code behind the prefix has a cell fold.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots isCellB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg (cellFoldLR)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-! ## 1. Allocated and argument names are no cell names -/

/-- **An allocated name does not begin with `m`**: the allocation pool, the vector registers
    and the spill names `k.*`, `kv.*` do not. -/
theorem physRegName_head (p : Nat) : (physRegName p).toList.head? ≠ some 'm' := by
  unfold physRegName
  split_ifs
  · dsimp only
    split
    · rename_i x hx
      have hm := List.mem_of_getElem? hx
      clear hx
      revert x
      decide
    · simp [String.toList_append]
  · split
    · rename_i x hx
      have hm := List.mem_of_getElem? hx
      clear hx
      revert x
      decide
    · simp [String.toList_append]

/-- The allocation of a body without a call never gives a name that begins with `m`. -/
theorem allocName_head {B : Lcmd} {tbl : Array Nat} (hc : bodyHasCall B = false)
    (n : String) : (allocName B tbl n).toList.head? ≠ some 'm' := by
  unfold allocName
  rw [hc, ite_eq_right Bool.false_ne_true]
  exact physRegName_head _

/-- **A name that does not begin with `m` is no cell name**, at any slot arrays. -/
theorem isCellB_of_head {q : String} (h : q.toList.head? ≠ some 'm') (R : Slots) :
    isCellB R q = false := by
  cases hc : isCellB R q
  · rfl
  · simp only [isCellB, List.any_eq_true, List.mem_range, beq_iff_eq] at hc
    obtain ⟨p, -, j, -, he⟩ := hc
    exact absurd (he ▸ memName_head p.1 (8 * j)) h

/-- **No source or target of the pairs of an allocation certificate of a body without a call
    is a cell name**: a source is an argument name and a target an allocated name. -/
theorem certArgs_not_cell {B : Lcmd} {tbl : Array Nat} (hc : bodyHasCall B = false)
    (R : Slots) :
    (certArgs σ (allocCertOf B tbl)).all (fun p => !isCellB R p.1 && !isCellB R p.2) = true := by
  rw [List.all_eq_true]
  intro p hp
  unfold certArgs at hp
  obtain ⟨hp, ha⟩ := List.mem_filter.mp hp
  obtain ⟨-, h2⟩ := mem_allocCertOf.mp hp
  simp only [isArgNameB, List.any_eq_true, beq_iff_eq] at ha
  obtain ⟨j, -, hj⟩ := ha
  have h1 : isCellB R p.1 = false := isCellB_of_head (by rw [← hj]; exact argName_head j) R
  have h2' : isCellB R p.2 = false := isCellB_of_head (by rw [← h2]; exact allocName_head hc _) R
  rw [h1, h2']
  rfl

/-! ## 2. The stage `G12` -/

/-- The gate does not refuse at `regionFoldB` when the cell fold check accepts. -/
theorem regionCoStage_ne_regionFoldB {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h : regionFoldB (regionCoParts σ nm b t (calleeCodeT none code) res cert none) = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "regionFoldB" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **Stage `G12` on the field domain**: the gate does not refuse at the cell fold, when the
    parts have no cell array or the code behind the prefix has a cell fold at the cell
    arrays. -/
theorem fieldDom_regionFoldB_of_cellFold (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert)
    (hf : (regionCoParts σ exportReg b t r.code r.res cert).cells.isEmpty = true
      ∨ (cellFoldLR (regionCoParts σ exportReg b t r.code r.res cert).cells []
          ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
            (regionCoParts σ exportReg b t r.code r.res cert).pre.length)).isSome = true) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regionFoldB" := by
  obtain ⟨B, tbl, hc, rfl⟩ := cert_allocCertOf h hB
  refine regionCoStage_ne_regionFoldB ?_
  have hp := certArgs_not_cell (σ := σ) (tbl := tbl) hc
    (regionCoParts σ exportReg b t r.code r.res (allocCertOf B tbl)).cells
  unfold regionFoldB
  rcases hf with hf | hf
  · exact Bool.or_eq_true_iff.mpr (Or.inl hf)
  · exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.and_eq_true_iff.mpr ⟨hf, hp⟩))

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
