/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomFrame
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomSites

/-!
# The cell names on the field domain

The stage `cellNamesRB` of the region gate reads the cell arrays of the parts: they are well
formed (`slotsOkB`: the empty name is no array and no cell, the array names are distinct, each
array has fewer than `2 ^ 60` words), their cells have distinct names (`cellsDistinctB`), and no
cell name is a general-purpose name, a name of the printed body or an argument name.

A cell array of the parts is the renamed name `renOf ps (argName j)` of a parameter of the
layout at its `n` words. The pairs `ps` are those of an allocation certificate of a body
without a call, so a renamed name is a physical name or the argument name itself, never
empty; the renaming check `renB`, which the gate passes on the field domain, makes the
renaming injective on the argument names; and `n < 2 ^ 60` on `fieldDomB'`. A cell name
`memName A o` is `"mem." ++ A ++ "." ++ o` with `o` in decimal, which determines `A` and `o`,
so distinct cells have distinct names whatever the array names. A cell name begins with
`mem.`, which no general-purpose name and no argument name does.

The one condition read off the printed body is that it names no cell of a renamed parameter
(`CellNameFree`).

## Main definitions

* `CellNameFree` — the printed body names no cell of a renamed parameter.

## Main results

* `memName_inj` — a cell name determines its array and its offset.
* `cert_allocCertOf` — on the field domain the certificate is that of an allocation of a body
  without a call.
* `cellNamesRB_of_fieldDom` — the cell names check passes on `fieldDomB'` when the printed
  body names no cell of a renamed parameter.
* `fieldDom_cellNamesRB` — the stage `G20` on `fieldDomB'` under `CellNameFree`.
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
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW (cellNamesRB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots slotsOkB cellsDistinctB
  isArrB isCellB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (cellNames cellArrs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk gpList)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (fieldAbi)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-! ## 1. Cell names -/

/-- Two lists that end in a dot followed by a dot-free list are equal when their parts
    before that dot and after it are. -/
theorem append_dot_inj {l₁ l₂ d₁ d₂ : List Char} (h₁ : '.' ∉ d₁) (h₂ : '.' ∉ d₂)
    (h : l₁ ++ '.' :: d₁ = l₂ ++ '.' :: d₂) : l₁ = l₂ ∧ d₁ = d₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simpa using h
    | cons c l₂ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.2 ▸ List.mem_append_right l₂ List.mem_cons_self) h₁
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.2 ▸ List.mem_append_right l₁ List.mem_cons_self) h₂
    | cons c l₂ =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl⟩

/-- The decimal digits of a number contain no dot. -/
theorem dot_not_mem_toString (o : Nat) : '.' ∉ (toString o).toList := by
  intro h
  have hd := toString_toList_isDigit o '.' h
  revert hd
  decide

/-- **A cell name determines its array and its offset.** -/
theorem memName_inj {A B : String} {o o' : Nat} (h : memName A o = memName B o') :
    A = B ∧ o = o' := by
  have hl := congrArg String.toList h
  simp only [memName, String.toList_append] at hl
  have hl' : ('m' :: 'e' :: 'm' :: '.' :: A.toList) ++ '.' :: (toString o).toList
      = ('m' :: 'e' :: 'm' :: '.' :: B.toList) ++ '.' :: (toString o').toList := by
    simpa using hl
  obtain ⟨hA, ho⟩ := append_dot_inj (dot_not_mem_toString o) (dot_not_mem_toString o') hl'
  simp only [List.cons.injEq, true_and] at hA
  refine ⟨String.toList_inj.mp hA, ?_⟩
  exact Nat.repr_inj.mp (String.toList_inj.mp ho)

/-- Distinct cells of any slot arrays have distinct names. -/
theorem cellsDistinctB_any (R : Slots) : cellsDistinctB R = true := by
  simp only [cellsDistinctB, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq]
  intro p _ q _ j _ j' _
  by_cases he : memName p.1 (8 * j) = memName q.1 (8 * j')
  · obtain ⟨h1, h2⟩ := memName_inj he
    exact Or.inr ⟨h1, by omega⟩
  · exact Or.inl he

/-- A cell name begins with `mem.`. -/
theorem memName_head (A : String) (o : Nat) : (memName A o).toList.head? = some 'm' := by
  simp [memName, String.toList_append]

/-- No general-purpose name begins with `m`. -/
theorem gpOk_head {q : String} (h : gpOk q = true) : q.toList.head? ≠ some 'm' := by
  have hm : q ∈ gpList := by simpa [gpOk] using h
  have key : ∀ z ∈ gpList, z.toList.head? ≠ some 'm' := by decide
  exact key q hm

/-- No argument name begins with `m`. -/
theorem argName_head (j : Nat) : (argName j).toList.head? ≠ some 'm' := by
  simp [argName, String.toList_append]

/-! ## 2. The certificate on the field domain -/

/-- **On the field domain the certificate is that of an allocation of a body without a
    call.** -/
theorem cert_allocCertOf (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    ∃ (B : Lcmd) (tbl : Array Nat), bodyHasCall B = false ∧ cert = allocCertOf B tbl := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, hr, hP, -, rfl⟩ := hB
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal h) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hcf : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree h hq))
  have hEx : regionExportableB (legalizeRegion q') = true := fieldDom_legalize hE1
  have hX : RegionExp fname (legalizeRegion q') (regionWebsEx σ exportReg) r := by
    rw [hr]
    exact regionExp_webs _ hr0
  obtain ⟨r1, r2, hr1, hr2, hcert⟩ :=
    RegionAllocMapAlign.regionLprogC_cert (nfAbiNames fname σ) _ _ hP
  obtain rfl : r1 = r0 := Option.some.inj (hr1.symm.trans hr0)
  rw [← hr] at hr2
  subst r2
  have hshape : ∀ i ∈ r.code, RegionAllocMapDom.ShapeB i.1 := fun i hi =>
    (hX.mnemDom hEx hcf i hi).2.2
  have hBs := RegionAllocMapDom.shapeB_regionAllocBody (nfAbiNames fname σ)
    ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r hshape
  exact ⟨_, _, RegionAllocMapDom.bodyHasCall_of_shapeB hBs, hcert⟩

/-- The pairs of an allocation certificate of a body without a call send a nonempty name to a
    nonempty name. -/
theorem renOf_certArgs_ne_empty {B : Lcmd} {tbl : Array Nat} (hc : bodyHasCall B = false)
    {n : String} (hn : n ≠ "") : renOf (certArgs σ (allocCertOf B tbl)) n ≠ "" := by
  unfold certArgs
  rw [RegionAllocMapComplete.renOf_filter_allocCertOf B tbl _ (isArgNameB σ) n]
  split_ifs
  · exact (physName_allocName hc n).ne_empty
  · exact hn

/-! ## 3. The cell names check -/

/-- **The printed body names no cell of a renamed parameter**: at the pairs `ps`, no cell
    name `memName (renOf ps (argName j)) o` of a parameter `j` of the layout is a name of the
    printed body `b`. -/
def CellNameFree (σ : AbiLayout) (ps : List (String × String)) (b : Lcmd) : Prop :=
  ∀ j, j < σ.args.length → ∀ o, memName (renOf ps (argName j)) o ∉ bodyNamesI b

/-- Argument names of distinct parameters are distinct. -/
theorem argName_inj {j j' : Nat} (h : argName j = argName j') : j = j' := by
  have hl := congrArg String.toList h
  simp only [argName, String.toList_append, List.append_cancel_left_eq] at hl
  exact Nat.repr_inj.mp (String.toList_inj.mp hl)

/-- The names of the regions of a layout are distinct. -/
theorem rsOf_names_nodup (σ : AbiLayout) : ((rsOf σ).map (·.name)).Nodup := by
  unfold rsOf
  rw [List.map_filterMap]
  refine List.Nodup.filterMap ?_ List.nodup_range
  intro j j' x hj hj'
  have key : ∀ i, x ∈ (match σ.args[i]? with
      | some a => match a.kind with
        | .words n => some (⟨argName i, n, 0⟩ : X86Backend.DecodeGenMem.Region)
        | .scalar => none
      | none => none).map X86Backend.DecodeGenMem.Region.name → x = argName i := by
    intro i hi
    split at hi
    · split at hi
      · simpa using hi.symm
      · cases hi
    · cases hi
  exact argName_inj ((key j hj).symm.trans (key j' hj'))

/-- **The cell names check on cell arrays of renamed parameters**: slot arrays with distinct
    names, each the renamed name of a parameter at fewer than `2 ^ 60` words, pass
    `cellNamesRB` against a printed body that names no cell of a renamed parameter, when the
    renaming sends no argument name to the empty name. -/
theorem cellNamesRB_of_cells {R : Slots} {ps : List (String × String)}
    (hsub : ∀ p ∈ R, ∃ j, j < σ.args.length ∧ p.1 = renOf ps (argName j) ∧ p.2 < 2 ^ 60)
    (hnd : (R.map Prod.fst).Nodup)
    (hne : ∀ j, j < σ.args.length → renOf ps (argName j) ≠ "")
    (hfree : CellNameFree σ ps b) : cellNamesRB R σ b = true := by
  have hcell : ∀ q ∈ cellNames R, ∃ j o, j < σ.args.length ∧ q = memName (renOf ps (argName j)) o
      := by
    intro q hq
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
    obtain ⟨j, hj, h1, -⟩ := hsub p hp
    exact ⟨j, 8 * i, hj, by rw [h1]⟩
  have hA : isArrB R "" = false := by
    cases hc : isArrB R ""
    · rfl
    · simp only [isArrB, List.any_eq_true, beq_iff_eq] at hc
      obtain ⟨p, hp, he⟩ := hc
      obtain ⟨j, hj, h1, -⟩ := hsub p hp
      exact absurd (h1 ▸ he) (hne j hj)
  have hC : isCellB R "" = false := by
    cases hc : isCellB R ""
    · rfl
    · simp only [isCellB, List.any_eq_true, List.mem_range, beq_iff_eq] at hc
      obtain ⟨p, -, i, -, he⟩ := hc
      have := memName_head p.1 (8 * i)
      rw [← he] at this
      cases this
  have hQ : ∀ q ∈ cellNames R, (!gpOk q && !(bodyNamesI b).contains q
      && !(List.range σ.args.length).any fun j => argName j == q) = true := by
    intro q hq
    obtain ⟨j, o, hj, rfl⟩ := hcell q hq
    have hg : gpOk (memName (renOf ps (argName j)) o) = false := by
      cases hg : gpOk (memName (renOf ps (argName j)) o)
      · rfl
      · exact absurd (memName_head _ o) (gpOk_head hg)
    have hb : (bodyNamesI b).contains (memName (renOf ps (argName j)) o) = false := by
      cases hc : (bodyNamesI b).contains (memName (renOf ps (argName j)) o)
      · rfl
      · exact absurd (List.contains_iff_mem.mp hc) (hfree j hj o)
    have ha : ((List.range σ.args.length).any fun i =>
        argName i == memName (renOf ps (argName j)) o) = false := by
      cases hc : (List.range σ.args.length).any fun i =>
          argName i == memName (renOf ps (argName j)) o
      · rfl
      · simp only [List.any_eq_true, beq_iff_eq] at hc
        obtain ⟨i, -, he⟩ := hc
        have := memName_head (renOf ps (argName j)) o
        rw [← he] at this
        exact absurd this (argName_head i)
    rw [hg, hb, ha]
    rfl
  have hL : R.all (fun p => decide (p.2 < 2 ^ 60)) = true :=
    List.all_eq_true.mpr fun p hp => by
      obtain ⟨-, -, -, h2⟩ := hsub p hp
      exact decide_eq_true h2
  simp only [cellNamesRB, slotsOkB, cellsDistinctB_any, hA, hC, hL, decide_eq_true hnd,
    List.all_eq_true.mpr hQ, Bool.not_false, Bool.and_self]

/-- The renamed names of a sublist of the cell arrays of the layout are distinct, when the
    renaming is injective on the argument names of the parameters. -/
theorem renamed_names_nodup (ps : List (String × String)) {l : Slots}
    (hl : l.Sublist (cellArrs σ))
    (hinj : ∀ j j', j < σ.args.length → j' < σ.args.length →
      renOf ps (argName j) = renOf ps (argName j') → j = j') :
    (l.map fun p => renOf ps p.1).Nodup := by
  have hn : (l.map Prod.fst).Nodup := by
    refine List.Nodup.sublist (List.Sublist.map _ hl) ?_
    have he : (cellArrs σ).map Prod.fst = (rsOf σ).map (·.name) := by
      unfold cellArrs
      rw [List.map_map]
      rfl
    rw [he]
    exact rsOf_names_nodup σ
  have hmap := List.Nodup.map_on (f := renOf ps) (fun x hx y hy hxy => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hy
    obtain ⟨j, a, hj, -, h1⟩ := X86Backend.ImageStraightCells.cellArrs_mem (hl.subset hp)
    obtain ⟨j', a', hj', -, h1'⟩ := X86Backend.ImageStraightCells.cellArrs_mem (hl.subset hp')
    rw [h1, h1'] at hxy ⊢
    rw [hinj j j' (List.getElem?_eq_some_iff.mp hj).1 (List.getElem?_eq_some_iff.mp hj').1 hxy])
    hn
  rw [List.map_map] at hmap
  exact hmap

/-- **The cell arrays of the parts have distinct names**, when the renaming is injective on
    the argument names of the parameters. -/
theorem regionCells_names_nodup (nm : String → String) (ps : List (String × String))
    (body : Lcmd) (code : List LinstrRM)
    (hinj : ∀ j j', j < σ.args.length → j' < σ.args.length →
      renOf ps (argName j) = renOf ps (argName j') → j = j') :
    ((regionCells σ nm ps body code).map Prod.fst).Nodup := by
  unfold regionCells
  dsimp only
  split
  · exact List.nodup_nil
  · rw [List.map_map]
    exact renamed_names_nodup ps List.filter_sublist hinj

/-- A cell array of the parts is the renamed name of a parameter, at the length of the
    parameter. -/
theorem regionCells_mem {nm : String → String} {ps : List (String × String)} {body : Lcmd}
    {code : List LinstrRM} {p : String × Nat} (hp : p ∈ regionCells σ nm ps body code) :
    ∃ j a, σ.args[j]? = some a ∧ a.kind = .words p.2 ∧ p.1 = renOf ps (argName j) :=
  X86Backend.ImageAddrRouteW.cellArrsR_mem (regionCells_sub σ nm ps body code p hp)

/-! ## 4. The stage `G20` -/

/-- The gate does not refuse at `cellNamesRB` when the cell names check accepts. -/
theorem regionCoStage_ne_cellNamesRB {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h : cellNamesRB (regionCoParts σ nm b t (calleeCodeT none code) res cert none).cells σ b
      = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "cellNamesRB" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **Stage `G20` on `fieldDomB'`**: the gate does not refuse at the cell names, when the
    printed body names no cell of a renamed parameter. -/
theorem fieldDom_cellNamesRB (h : fieldDomB' e σ = true) (hB : FieldBody e σ fname b t r cert)
    (hfree : CellNameFree σ (certArgs σ cert) b) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "cellNamesRB" := by
  have h' := fieldDomB_of_fieldDomB' h
  obtain ⟨k, n, -, rfl, hn⟩ := fieldDomB'_layout h
  have hR := renB_of_stages (fieldDom_coClass h' hB) (fieldDom_coCfgB' h' hB)
    (fieldDom_coEntryFix' h' hB) (fieldDom_renB h' hB)
  simp only [renB, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hR
  have hun := hR.2
  obtain ⟨B, tbl, hc, rfl⟩ := cert_allocCertOf h' hB
  refine regionCoStage_ne_cellNamesRB (cellNamesRB_of_cells ?_ ?_ ?_ hfree)
  · intro p hp
    obtain ⟨j, a, hj, hkd, hpj⟩ := X86Backend.ImageAddrRouteW.cellArrsR_mem
      (regionCoParts_cells_sub _ exportReg b t _ r.res _ none p hp)
    refine ⟨j, (List.getElem?_eq_some_iff.mp hj).1, hpj, ?_⟩
    simp only [fieldAbi, List.getElem?_map] at hj
    obtain ⟨j', -, rfl⟩ := Option.map_eq_some_iff.mp hj
    injection hkd with hkd
    omega
  · exact regionCells_names_nodup exportReg _ b _ fun j j' hj hj' he => by
      have e1 : unren (certArgs (fieldAbi k n) (allocCertOf B tbl))
          (renOf (certArgs (fieldAbi k n) (allocCertOf B tbl)) (argName j)) = argName j :=
        (hun j hj).2
      have e2 : unren (certArgs (fieldAbi k n) (allocCertOf B tbl))
          (renOf (certArgs (fieldAbi k n) (allocCertOf B tbl)) (argName j')) = argName j' :=
        (hun j' hj').2
      rw [he] at e1
      exact argName_inj (e1.symm.trans e2)
  · intro j _
    refine renOf_certArgs_ne_empty hc ?_
    intro he
    have := congrArg (fun s : String => s.toList.head?) he
    simp [argName, String.toList_append] at this

example (h : fieldDomB' e σ = true) (hB : FieldBody e σ fname b t r cert)
    (hfree : CellNameFree σ (certArgs σ cert) b) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "cellNamesRB" :=
  fieldDom_cellNamesRB h hB hfree

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
