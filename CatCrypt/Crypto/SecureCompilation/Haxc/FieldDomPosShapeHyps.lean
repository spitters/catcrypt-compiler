/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomPosShape
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomLoadsKPasses

/-!
# The hypotheses of the fold positions on the field domain

The theorem `fieldDom_foldPos_addSub_of_posShape` takes the distinct roots of the result copy
(`hR`) as a hypothesis. This module proves it on the field domain. At an array result copy
`(src, D, m)` the coalescing renaming of the code with the result copy sends every version
`copyName D jj` of the result buffer to `D`, an argument name the exported code never writes,
and the source `src` to its root in the exported code, which the copy decision found to differ
from `D`. The two roots are names of the coalesced code, on which the renaming check `renB`
makes the renaming by the pairs injective.

## Main results

* `regionCopy_resBuf`: the result buffer of an array result copy.
* `fieldDom_resCopy_alias_ne`: the coalesced source of the result copy is no coalesced version
  of the result buffer.
* `fieldDom_resCopyRoots`: the hypothesis `hR` of `fieldDom_foldPos_addSub_of_posShape`.
* `fieldDom_foldPos_addSub_of_posShape_noLoadStore`: the fold positions of the sum and the
  difference without the hypothesis `hR`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr renLoad renStore)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO resRoot?
  aliasTabRes chainAliasRes chainAliasRes_apply chainAliasRes_src)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)

/-! ## 1. The roots of the result copy -/

/-- **The result buffer of an array result copy** `(src, D, m)` is `D` with `m` words. -/
theorem regionCopy_resBuf {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    {code : List LinstrRM} {res : List LOperand} {src D : String} {m : Nat}
    (h : regionCopy σ nm t none code res = some (src, D, m)) :
    regionResBuf σ nm = some (D, m) := by
  unfold regionCopy at h
  split at h
  · rename_i D' n hb
    simp only [Option.filter_eq_some_iff, beq_iff_eq] at h
    obtain ⟨hc, hn⟩ := h
    rw [hb, RegionAllocMapPins.resCopyOf_buf hc, hn]
  · cases h

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The coalesced source of the result copy is no coalesced version of the result buffer**
    on the field domain: the coalescing renaming of the code with the result copy sends each
    version `copyName D jj`, `jj < m`, to `D`, and the source `src` to its root in the exported
    code, which differs from `D`. -/
theorem fieldDom_resCopy_alias_ne (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) {src D : String} {m : Nat}
    (hcp : regionCopy σ exportReg t none r.code r.res = some (src, D, m)) {jj : Nat}
    (hjj : jj < m) :
    regionAliasN σ exportReg t r.res
        (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res)) src
      ≠ regionAliasN σ exportReg t r.res
        (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))
        (copyName D jj) := by
  obtain ⟨-, ht, ⟨op, hres, hsrc⟩, ⟨j, a, -, -, hD⟩, -, hfr⟩ := regionCopy_some hcp
  obtain ⟨hF, hA, -⟩ := fieldDom_exportFacts h hB
  have hbuf := regionCopy_resBuf hcp
  have hret : regionRet σ exportReg t r.res = none := by
    obtain ⟨-, R, n, hR⟩ := fieldDomB_abi h
    exact regionRet_words hR
  -- the root of the source in the exported code is not the buffer
  have hc : chainAliasRes [] D src r.code src ≠ D := by
    have h1 := hcp
    unfold regionCopy at h1
    rw [hbuf] at h1
    simp only [Option.filter_eq_some_iff] at h1
    obtain ⟨h1, -⟩ := h1
    rw [ht, hres] at h1
    unfold resCopyOf at h1
    grind
  have hsrcD : (r.code.foldl (aliasStepO []) {}).getD src src ≠ D := by
    cases hr : resRoot? [] D src r.code with
    | some r' => exact absurd (chainAliasRes_src hr) hc
    | none =>
      rw [chainAliasRes_apply, hr] at hc
      exact hc
  -- the code with the copy mentions the buffer, so it has no result root
  have hroot : resRoot? [] D src (r.code ++ resCopyCode src D m) = none := by
    have hmem : ((.Lopn [.reg (copyName D 1)] "STOREIDX"
        [.arrIdx (copyName D 0) copyIdx 8, .reg copyTmp], .store 64 m) : LinstrRM)
          ∈ r.code ++ resCopyCode src D m :=
      List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨0, List.mem_range.mpr (by omega), by simp [resCopyStep]⟩)
    unfold resRoot?
    rw [ite_eq_right_iff]
    intro hcond
    exfalso
    simp only [Bool.and_eq_true, List.all_eq_true] at hcond
    have := hcond.1.2 _ hmem
    simp only [copyName, ite_true, Nat.one_ne_zero, ite_false] at this
    unfold instrNames at this
    grind [opNames]
  have hrr : resAliasOf none ((regionResBuf σ exportReg).map Prod.fst) [t] r.res
      = some (D, src) := by
    rw [hbuf, ht, hres, ← hsrc, hD]
    simp [resAliasOf, RegionAllocMapDom.argName_ne_empty]
  have hDD : (r.code.foldl (aliasStepO []) {}).getD D D = D := by
    rw [getD_foldl_of_noWrite r.code {} hF.1 (fun i hi d hd => by rw [hD]; exact hA i hi d hd j)]
    simp
  rw [hcp]
  have hnv : (∃ i, i < m ∧ src = copyName D (i + 1)) = False :=
    eq_false fun ⟨i, hi, he⟩ => hfr i hi he
  simp only [regionAliasN, regionAliasTab, resAliasTab, hrr, regionCoCode, hret, calleeOutsT,
    Option.toList_none, movesOf, List.map_nil, List.append_nil, aliasTabRes, hroot]
  unfold canonMemrefName X86Backend.ImageStraightRoute.aliasTab
  rw [List.foldl_append, getD_foldl_resCopyCode, getD_foldl_resCopyCode,
    ite_eq_right_of_eq_false _ _ hnv]
  split_ifs with hv
  · rw [hDD]
    exact hsrcD
  · cases jj with
    | zero =>
      rw [show copyName D 0 = D by simp [copyName], hDD]
      exact hsrcD
    | succ k => exact absurd ⟨k, by omega, rfl⟩ hv

/-- **The hypothesis `hR` of `fieldDom_foldPos_addSub_of_posShape`**: on the field domain, at
    an array result copy `(src, D, m)`, the coalesced source renamed by the pairs is no
    coalesced version `copyName D jj`, `jj < m`, of the result buffer renamed by the pairs.
    Both coalesced names are names of the coalesced code, on which the renaming check `renB`
    makes the renaming by the pairs injective. -/
theorem fieldDom_resCopyRoots (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    ∀ src D m, regionCopy σ exportReg t none r.code r.res = some (src, D, m) →
      ∀ jj, jj < m →
      renOf (regionCoParts σ exportReg b t r.code r.res cert).ps
          (regionAliasN σ exportReg t r.res (regionCoCode σ exportReg t r.code r.res
            (regionCopy σ exportReg t none r.code r.res)) src)
        ≠ renOf (regionCoParts σ exportReg b t r.code r.res cert).ps
          (regionAliasN σ exportReg t r.res (regionCoCode σ exportReg t r.code r.res
            (regionCopy σ exportReg t none r.code r.res)) (copyName D jj)) := by
  intro src D m hcp jj hjj he
  have hR := X86Backend.ImageAddrRoute.renB_spec (renB_of_stages (fieldDom_coClass h hB)
    (fieldDom_coCfgB' h hB) (fieldDom_coEntryFix' h hB) (fieldDom_renB h hB))
  have hstep : resCopyStep src D m jj ⊆
      regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res) := by
    intro i hi
    rw [hcp, regionCoCode]
    exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨jj, List.mem_range.mpr hjj, hi⟩)
  have hld := hstep (List.mem_cons_of_mem _ List.mem_cons_self)
  have hst := hstep (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  set ρ := regionAliasN σ exportReg t r.res
    (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))
    with hρ
  have hn1 := hR.names _ (List.mem_map_of_mem hld) (ρ src) (by
    change ρ src ∈ instrNames (.Lopn [.reg copyTmp] "LOADIDX" [.arrIdx (ρ src) copyIdx 8])
    unfold instrNames
    grind [opNames])
  have hn2 := hR.names _ (List.mem_map_of_mem hst) (ρ (copyName D jj)) (by
    change ρ (copyName D jj) ∈ instrNames (.Lopn [.reg (ρ (copyName D (jj + 1)))] "STOREIDX"
      [.arrIdx (ρ (copyName D jj)) copyIdx 8, .reg copyTmp])
    unfold instrNames
    grind [opNames])
  exact fieldDom_resCopy_alias_ne h hB hcp hjj (hR.ren.inj _ _ hn1 hn2 he)

/-- **The fold positions of the sum and the difference of the field domain** from the shape
    `LoadsChainK`, the absence of a load directly followed by a store in the exported code and
    the shape `PosShape` at every position of the code behind the prefix. The roots of the
    result copy differ on the field domain (`fieldDom_resCopyRoots`). -/
theorem fieldDom_foldPos_addSub_of_posShape_noLoadStore (h : fieldDomB'' e σ = true)
    (hA : FieldAddSub e) (hB : FieldBody e σ fname b t r cert)
    (hL : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → LoadsChainK (fun _ => none) (legalizeRegion q'))
    (hC : ∀ (k : Nat) (i j : LinstrRM), r.code[k]? = some i → r.code[k + 1]? = some j →
      loadB i = true → storeB j = false)
    (hS : ∀ (k : Nat) (i : LinstrRM),
      ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      PosShape (regionCoParts σ exportReg b t r.code r.res cert).cells i) :
    ∀ k i, ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      FoldPos (regionCoParts σ exportReg b t r.code r.res cert).cells
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) k i :=
  fieldDom_foldPos_addSub_of_posShape h hA hB hL hC
    (fieldDom_resCopyRoots (fieldDomB_of_fieldDomB'' h) hB) hS

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
