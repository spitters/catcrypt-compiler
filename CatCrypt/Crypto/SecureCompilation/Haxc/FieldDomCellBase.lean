/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomEntry

/-!
# The cell names on the field domain from the base of the printed cells

The stage `cellNamesRB` of the region gate passes on `fieldDomB'` when the printed body names no
cell `memName (renOf ps (argName j)) o` of a renamed parameter (`CellNameFree`). That condition
splits into a fact of the printed body alone and a fact of the allocation. The printed body
reaches memory through the address scratch register `R14`: every cell name of the body is
`memName "R14" o` (`CellBaseScratch`). The allocation pool is `RAX` to `R13`, so an allocated
name is never `R14`; the pairs `certArgs` of an allocation certificate of a body without a call
send an argument name to an allocated name or to itself, and an argument name `a<j>` is not
`R14`. So no renamed parameter is `R14`, and a body whose cells have the base `R14` names no
cell of a renamed parameter.

## Main definitions

* `CellBaseScratch` — every cell name of the printed body has the base `R14`.

## Main results

* `physRegName_ne_R14`, `allocName_ne_R14` — the allocation never names `R14`.
* `renOf_certArgs_argName_ne_R14` — no renamed parameter is `R14`.
* `cellNameFree_of_cellBase` — a body whose cells have the base `R14` names no cell of a
  renamed parameter.
* `fieldDom_cellNamesRB_of_cellBase` — the stage `G20` on `fieldDomB'` under `CellBaseScratch`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-! ## 1. The allocation never names `R14` -/

/-- **No physical index names `R14`**: the allocation pool, the vector registers and the
    spill names `k.*`, `kv.*` do not contain it. -/
theorem physRegName_ne_R14 (p : Nat) : physRegName p ≠ "R14" := by
  unfold physRegName
  split_ifs
  · dsimp only
    split
    · rename_i r hr
      have hm := List.mem_of_getElem? hr
      intro he
      subst he
      revert hm
      decide
    · intro he
      have := congrArg (fun s : String => s.toList.head?) he
      simp [String.toList_append] at this
  · split
    · rename_i r hr
      have hm := List.mem_of_getElem? hr
      intro he
      subst he
      revert hm
      decide
    · intro he
      have := congrArg (fun s : String => s.toList.head?) he
      simp [String.toList_append] at this

/-- **The allocation of a body without a call never names `R14`.** -/
theorem allocName_ne_R14 {B : Lcmd} {tbl : Array Nat} (hc : bodyHasCall B = false)
    (n : String) : allocName B tbl n ≠ "R14" := by
  unfold allocName
  rw [hc, ite_eq_right Bool.false_ne_true]
  exact physRegName_ne_R14 _

/-- An argument name is not `R14`. -/
theorem argName_ne_R14 (j : Nat) : argName j ≠ "R14" := by
  intro he
  have := congrArg (fun s : String => s.toList.head?) he
  simp [argName, String.toList_append] at this

/-- **No renamed parameter is `R14`**: the pairs of an allocation certificate of a body without
    a call send an argument name to an allocated name or to itself. -/
theorem renOf_certArgs_argName_ne_R14 {B : Lcmd} {tbl : Array Nat}
    (hc : bodyHasCall B = false) (j : Nat) :
    renOf (certArgs σ (allocCertOf B tbl)) (argName j) ≠ "R14" := by
  unfold certArgs
  rw [RegionAllocMapComplete.renOf_filter_allocCertOf B tbl _ (isArgNameB σ) (argName j)]
  split_ifs
  · exact allocName_ne_R14 hc _
  · exact argName_ne_R14 j

/-! ## 2. The cells of the printed body -/

/-- **Every cell name of the printed body has the base `R14`**, the address scratch register
    through which the printed body reaches memory. -/
def CellBaseScratch (b : Lcmd) : Prop :=
  ∀ (A : String) (o : Nat), memName A o ∈ bodyNamesI b → A = "R14"

/-- **A body whose cells have the base `R14` names no cell of a renamed parameter**, at the
    pairs of an allocation certificate of a body without a call. -/
theorem cellNameFree_of_cellBase {B : Lcmd} {tbl : Array Nat} (hc : bodyHasCall B = false)
    (hb : CellBaseScratch b) : CellNameFree σ (certArgs σ (allocCertOf B tbl)) b :=
  fun j _ o hm => renOf_certArgs_argName_ne_R14 hc j (hb _ o hm)

/-! ## 3. The stage `G20` -/

/-- **Stage `G20` on `fieldDomB'`**: the gate does not refuse at the cell names, when every
    cell name of the printed body has the base `R14`. -/
theorem fieldDom_cellNamesRB_of_cellBase (h : fieldDomB' e σ = true)
    (hB : FieldBody e σ fname b t r cert) (hb : CellBaseScratch b) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "cellNamesRB" := by
  obtain ⟨B, tbl, hc, rfl⟩ := cert_allocCertOf (fieldDomB_of_fieldDomB' h) hB
  exact fieldDom_cellNamesRB h hB (cellNameFree_of_cellBase hc hb)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
