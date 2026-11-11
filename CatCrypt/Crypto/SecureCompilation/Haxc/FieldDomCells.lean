/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomMerge
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomExport
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomRenB

/-!
# The cell regions on the field domain

The last conjunct of the region gate reads each cell array of the parts: the parameter it
stands for under the pairs, `unren ps`, is a region of the layout at the length of the cell
array, and the pairs send that parameter back to the cell array. A cell array of the parts is
the renamed name `renOf ps (argName j)` of a word-array parameter of the layout, at its length.
The renaming check `renB`, which the gate passes on the field domain (stages `G1`-`G4`), states
`unren ps (renOf ps (argName j)) = argName j` for every parameter; and every region of the
field layout has the `n` words of every parameter.

## Main results

* `renB_of_stages`: a gate that refuses at none of its first four stages passes the renaming
  check.
* `regLen_rsOf_fieldAbi`: every region of the field layout has the length of the parameters.
* `fieldDom_cellRegions`: the stage `G21` on the field domain.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (renB unren rsOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (regLen regFind)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- A step of the stage chain of the gate that does not name its stage passes its
    condition. -/
theorem cond_of_ite_ne {c : Bool} {s : String} {x : Option String}
    (h : (if c = false then some s else x) ≠ some s) : c = true := by
  cases c
  · exact absurd rfl h
  · rfl

/-- A step of the stage chain of the gate at a condition that holds is its continuation. -/
theorem ite_of_true {c : Bool} {s : String} {x : Option String} (hc : c = true) :
    (if c = false then some s else x) = x := by
  rw [hc]
  rfl

/-- **A gate that refuses at none of its first four stages passes the renaming check.** -/
theorem renB_of_stages {nm : String → String} {code : List LinstrRM} {res : List LOperand}
    {fn : String}
    (h1 : regionCoStage σ nm b t code res cert none fn ≠ some "coClass")
    (h2 : regionCoStage σ nm b t code res cert none fn ≠ some "coCfgB")
    (h3 : regionCoStage σ nm b t code res cert none fn ≠ some "coEntryFix")
    (h4 : regionCoStage σ nm b t code res cert none fn ≠ some "renB") :
    renB σ nm [] (regionCoBody σ nm t (calleeCodeT none code) res none)
      (regionCoParts σ nm b t (calleeCodeT none code) res cert none).ps = true := by
  unfold regionCoStage at h1 h2 h3 h4
  dsimp only at h1 h2 h3 h4
  simp only [Option.all_none, Bool.true_eq_false, ite_false] at h1 h2 h3 h4
  have c1 := cond_of_ite_ne h1
  rw [ite_of_true c1] at h2 h3 h4
  have c2 := cond_of_ite_ne h2
  rw [ite_of_true c2] at h3 h4
  have c3 := cond_of_ite_ne h3
  rw [ite_of_true c3] at h4
  exact cond_of_ite_ne h4

/-- **Every region of the field layout has the length of the parameters**: at a name that
    is a region, the length of the region is `n`. -/
theorem regLen_rsOf_fieldAbi {k n : Nat} (ha : σ.args = (FieldRoute.fieldAbi k n).args)
    {A : String} (hA : (regFind (rsOf σ) A).isSome = true) : regLen (rsOf σ) A = n := by
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hA
  have hmem : g ∈ rsOf σ := List.mem_of_find?_eq_some hg
  unfold rsOf at hmem
  obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp hmem
  have hlen : g.len = n := by
    cases hs : σ.args[j]? with
    | none => rw [hs] at hj; cases hj
    | some a =>
        rw [hs] at hj
        have hk : a.kind = .words n := by
          rw [ha] at hs
          simp only [FieldRoute.fieldAbi, List.getElem?_map] at hs
          obtain ⟨j', -, rfl⟩ := Option.map_eq_some_iff.mp hs
          rfl
        simp only [hk, Option.some.injEq] at hj
        rw [← hj]
  unfold regLen
  rw [hg]
  exact hlen

/-- The gate does not refuse at `cellRegions` when every cell array is a region of its
    length under the pairs, and the pairs send its parameter back to it. -/
theorem regionCoStage_ne_cellRegions {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h : (regionCoParts σ nm b t (calleeCodeT none code) res cert none).cells.all (fun p =>
      regLen (rsOf σ) (unren (regionCoParts σ nm b t (calleeCodeT none code) res cert none).ps
        p.1) == p.2
        && renOf (regionCoParts σ nm b t (calleeCodeT none code) res cert none).ps
          (unren (regionCoParts σ nm b t (calleeCodeT none code) res cert none).ps p.1)
          == p.1) = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "cellRegions" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **Stage `G21` on the field domain**: the gate does not refuse at the cell regions. -/
theorem fieldDom_cellRegions (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "cellRegions" := by
  have hR := renB_of_stages (fieldDom_coClass h hB) (fieldDom_coCfgB' h hB)
    (fieldDom_coEntryFix' h hB) (fieldDom_renB h hB)
  obtain ⟨k, n, hk, ha, -⟩ := fieldDomB_layout h
  refine regionCoStage_ne_cellRegions ?_
  simp only [renB, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hR
  have hun := hR.2
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨j, a, hj, hkd, hpj⟩ := X86Backend.ImageAddrRouteW.cellArrsR_mem
    (regionCoParts_cells_sub σ exportReg b t _ r.res cert none p hp)
  have hjl : j < σ.args.length := (List.getElem?_eq_some_iff.mp hj).1
  have hu : unren (regionCoParts σ exportReg b t (calleeCodeT none r.code) r.res cert none).ps
      p.1 = argName j := by
    rw [hpj]
    exact (hun j hjl).2
  rw [hu]
  have hpn : p.2 = n := by
    rw [ha] at hj
    simp only [FieldRoute.fieldAbi, List.getElem?_map] at hj
    obtain ⟨j', -, rfl⟩ := Option.map_eq_some_iff.mp hj
    injection hkd with hkd
    exact hkd.symm
  have hreg : (regFind (rsOf σ) (argName j)).isSome = true := by
    unfold regFind
    rw [List.find?_isSome]
    refine ⟨⟨argName j, n, 0⟩, ?_, by simp⟩
    unfold rsOf
    refine List.mem_filterMap.mpr ⟨j, List.mem_range.mpr hjl, ?_⟩
    rw [hj]
    rw [ha] at hj
    simp only [FieldRoute.fieldAbi, List.getElem?_map] at hj
    obtain ⟨j', -, he⟩ := Option.map_eq_some_iff.mp hj
    rw [← he]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨by rw [regLen_rsOf_fieldAbi ha hreg, hpn], hpj.symm⟩

example (S : FieldDomStages) : type_of% @S.cellRegions := @fieldDom_cellRegions

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
