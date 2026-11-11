/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCells

/-!
# The result names of the fusion sites on the field domain

The stage `fuseResultName` of the region gate repeats the fusion check `fuseOKL`, which the
stage before it has passed, and asks that the renamed alias of each returned array and each
target of the result copy is not `R15`, the scratch register the fused code changes. On the
field domain there is no target of the result copy. The alias of a returned array is a name of
the coalesced code (stage `G5`): a name of the code, which has the shape of a name of the
export (`CodeName`), or the image of one under the coalescing renaming, which keeps that shape.
The pairs of the allocation certificate send such a name to itself or to the register the
allocation gives it, and `R15` is never an allocation target (`physRegName_ne_R15`).

## Main results

* `physRegName_ne_R15`, `allocName_ne_R15`: the allocation never names `R15`.
* `canon_codeName`: the coalescing renaming of a region export keeps the names of the code.
* `regionCoStage_ne_fuseResultName`: the stage from the condition on the result names alone.
* `fieldDom_fuseResultName`: the stage `G11` on the field domain.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (loopNames fuseRegs)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseOKL fuseLoPre)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO)

/-! ## 1. The allocation never names `R15` -/

/-- **No physical index names `R15`**: the allocation pool, the vector registers and the
    spill names `k.*`, `kv.*` do not contain it. -/
theorem physRegName_ne_R15 (p : Nat) : physRegName p ≠ "R15" := by
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

/-- **The allocation of a body without a call never names `R15`.** -/
theorem allocName_ne_R15 {B : Lcmd} {tbl : Array Nat} (hc : bodyHasCall B = false)
    (n : String) : allocName B tbl n ≠ "R15" := by
  unfold allocName
  rw [hc, ite_eq_right Bool.false_ne_true]
  exact physRegName_ne_R15 _

/-- A name of the shape of the names of the export is not `R15`. -/
theorem codeName_ne_R15 {x : String} (h : CodeName x) : x ≠ "R15" := by
  rintro rfl
  rcases h with (h | h) | h <;> simp at h

/-- **The pairs of an allocation certificate of a body without a call send no name other than
    `R15` to `R15`.** -/
theorem renOf_certArgs_ne_R15 {σ : AbiLayout} {B : Lcmd} {tbl : Array Nat}
    (hc : bodyHasCall B = false) {n : String} (hn : n ≠ "R15") :
    renOf (certArgs σ (allocCertOf B tbl)) n ≠ "R15" := by
  unfold certArgs
  rw [RegionAllocMapComplete.renOf_filter_allocCertOf B tbl _ (isArgNameB σ) n]
  split_ifs
  · exact allocName_ne_R15 hc n
  · exact hn

/-! ## 2. The coalescing renaming keeps the names of the code -/

/-- The result alias of a region export without a callee is at the result buffer. -/
theorem resAliasOf_fst {Dopt : Option String} {ts : List JasminTy} {res : List LOperand}
    {D src : String} (h : resAliasOf none Dopt ts res = some (D, src)) : Dopt = some D := by
  unfold resAliasOf at h
  split at h
  · split at h
    · cases h
    · cases h
      rfl
  · cases h

/-- **The coalescing renaming of a region export without a callee keeps the names of the
    code**, when every name of the code is a name of the export, no instruction is the shadow
    of a call and the result buffer is a name of the export. -/
theorem canon_codeName {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    {res : List LOperand} {C : List LinstrRM}
    (hL : ∀ i ∈ C, ∀ x ∈ instrNames i.1, CodeName x)
    (hs : ∀ i ∈ C, LprogIsa.shadowCall? i.1 = none)
    (hD : ∀ D n, regionResBuf σ nm = some (D, n) → CodeName D) :
    ∀ x, CodeName x → CodeName (canonMemrefName (regionAliasTab σ nm t none res C) x) := by
  have h0 : ∀ x, CodeName x →
      CodeName (canonMemrefName ({} : Std.HashMap String String) x) := by
    intro x hx
    unfold canonMemrefName
    simpa using hx
  unfold regionAliasTab resAliasTab
  split
  · rename_i D src hrr
    have hDc : CodeName D := by
      obtain ⟨⟨D', n⟩, hb, he⟩ := Option.map_eq_some_iff.mp (resAliasOf_fst hrr)
      obtain rfl : D' = D := he
      exact hD _ _ hb
    unfold X86Backend.ImageStraightRoute.aliasTabRes
    split
    · refine alias_foldl_pred [] C _ hL hs fun x hx => ?_
      unfold canonMemrefName
      rw [Std.HashMap.getD_insert]
      split
      · exact hDc
      · simpa using hx
    · exact alias_foldl_pred [] C _ hL hs h0
  · exact alias_foldl_pred [] C _ hL hs h0

/-! ## 3. The gate -/

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **A gate that refuses at none of its first five stages passes the condition of the stage
    `coResultName`.** -/
theorem coResultName_of_stages {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h1 : regionCoStage σ nm b t code res cert none fn ≠ some "coClass")
    (h2 : regionCoStage σ nm b t code res cert none fn ≠ some "coCfgB")
    (h3 : regionCoStage σ nm b t code res cert none fn ≠ some "coEntryFix")
    (h4 : regionCoStage σ nm b t code res cert none fn ≠ some "renB")
    (h5 : regionCoStage σ nm b t code res cert none fn ≠ some "coResultName") :
    (regionCoObs t (regionOut (regionCopy σ nm t none (calleeCodeT none code) res)
      res)).all (fun A =>
      (loopNames (regionCoBody σ nm t (calleeCodeT none code) res none)).contains
        (canonMemrefName (regionAliasTab σ nm t none res
          (regionCoCode σ nm t (calleeCodeT none code) res
            (regionCopy σ nm t none (calleeCodeT none code) res))) A)) = true := by
  unfold regionCoStage at h1 h2 h3 h4 h5
  dsimp only at h1 h2 h3 h4 h5
  simp only [Option.all_none, Bool.true_eq_false, ite_false] at h1 h2 h3 h4 h5
  have c1 := cond_of_ite_ne h1
  rw [ite_of_true c1] at h2 h3 h4 h5
  have c2 := cond_of_ite_ne h2
  rw [ite_of_true c2] at h3 h4 h5
  have c3 := cond_of_ite_ne h3
  rw [ite_of_true c3] at h4 h5
  have c4 := cond_of_ite_ne h4
  rw [ite_of_true c4] at h5
  exact cond_of_ite_ne h5

/-- Two steps of the stage chain at one condition are the first. -/
theorem ite_dup {c : Bool} {s s' : String} {x : Option String} :
    (if c = false then some s else if c = false then some s' else x)
      = (if c = false then some s else x) := by
  cases c <;> rfl

/-- **The gate does not refuse at `fuseResultName` when no renamed alias of a returned array
    and no target of the result copy is `R15`**: the fusion check of the stage is the one of
    the stage `fuseOKL` before it. -/
theorem regionCoStage_ne_fuseResultName {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h : ((regionCoParts σ nm b t (calleeCodeT none code) res cert none).obs.all
        (fun A => A != "R15")
      && (regionCoParts σ nm b t (calleeCodeT none code) res cert none).outs.all
        (fun y => y != "R15")) = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "fuseResultName" := by
  have hS : regionSitesB (fuseRegs σ nm) (regionCoParts σ nm b t (calleeCodeT none code) res
      cert none) =
      (!(regionCoParts σ nm b t (calleeCodeT none code) res cert none).sites
        || fuseOKL (fuseRegs σ nm)
          (fuseLoPre (regionCoParts σ nm b t (calleeCodeT none code) res cert none).pre
            ((regionCoParts σ nm b t (calleeCodeT none code) res cert none).nop.drop
              (regionCoParts σ nm b t (calleeCodeT none code) res cert none).pre.length))
          ((regionCoParts σ nm b t (calleeCodeT none code) res cert none).pre
            ++ (regionCoParts σ nm b t (calleeCodeT none code) res cert none).nop.drop
              (regionCoParts σ nm b t (calleeCodeT none code) res cert none).pre.length)) := by
    simp only [Bool.and_eq_true] at h
    unfold regionSitesB
    rw [h.1, h.2]
    simp only [Bool.and_true]
  unfold regionCoStage
  dsimp only
  rw [hS, ite_dup]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **Stage `G11` on the field domain**: the gate does not refuse at the result names of the
    fusion sites. -/
theorem fieldDom_fuseResultName (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "fuseResultName" := by
  have hG5 := coResultName_of_stages (fieldDom_coClass h hB) (fieldDom_coCfgB' h hB)
    (fieldDom_coEntryFix' h hB) (fieldDom_renB h hB) (fieldDom_coResultName h hB)
  refine regionCoStage_ne_fuseResultName ?_
  have hret : ∀ res, regionRet σ exportReg t res = none := by
    obtain ⟨-, R, n, hR⟩ := fieldDomB_abi h
    exact fun _ => regionRet_words hR
  obtain ⟨k, n, hk, ha, hres⟩ := fieldDomB_layout h
  have hbuf := fieldDom_regionResBuf hk ha hres
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
  have hsym : ∀ i ∈ r.code, RegionExportDefInit.symReads i = [] := fun i hi =>
    (hX.mnemDom hEx hcf i hi).1
  have hlen : ((nfCtx σ).map NarrowWords.wideTy).length ≤ σ.args.length := by
    rw [List.length_map]
    exact (RegionAllocMapDom.nfCtx_length σ).le
  obtain ⟨r1, r2, hr1, hr2, hcert⟩ :=
    RegionAllocMapAlign.regionLprogC_cert (nfAbiNames fname σ) _ _ hP
  obtain rfl : r1 = r0 := Option.some.inj (hr1.symm.trans hr0)
  rw [← hr] at hr2
  subst r2
  subst hcert
  have hshape : ∀ i ∈ r.code, RegionAllocMapDom.ShapeB i.1 := fun i hi =>
    (hX.mnemDom hEx hcf i hi).2.2
  have hBs := RegionAllocMapDom.shapeB_regionAllocBody (nfAbiNames fname σ)
    ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r hshape
  have hc := RegionAllocMapDom.bodyHasCall_of_shapeB hBs
  have hL := codeName_regionCoCode fname _ hEx hcf hX σ exportReg (NarrowWords.wideTy t0) hsym
    hlen (hret _)
  have hnsC := RegionCoComplete.noShadow_regionCoCode σ exportReg (NarrowWords.wideTy t0)
    r.code r.res (regionCopy σ exportReg (NarrowWords.wideTy t0) none r.code r.res)
    (hX.noShadow hEx hcf)
  have hρ := canon_codeName (t := NarrowWords.wideTy t0) (res := r.res) hL hnsC
    (fun D n' hb => by
      rw [hbuf] at hb
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hb)
      exact codeName_argName 0)
  have hcc : calleeCodeT none r.code = r.code := rfl
  rw [hcc] at hG5 ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq]
  refine ⟨fun A hA => ?_, fun y hy => ?_⟩
  · obtain ⟨A0, hA0, rfl⟩ := List.mem_map.mp hA
    refine renOf_certArgs_ne_R15 hc ?_
    have hm := List.contains_iff_mem.mp ((List.all_eq_true.mp hG5) A0 hA0)
    unfold loopNames at hm
    rcases List.mem_cons.mp hm with he | hm
    · rw [he]
      decide
    obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hm
    unfold regionCoBody at hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
    rcases under_renArr _ (hnsC i0 hi0) _ hx with hx' | ⟨y, hy, he⟩
    · exact codeName_ne_R15 (hL i0 hi0 _ hx')
    · rw [he]
      exact codeName_ne_R15 (hρ y (hL i0 hi0 y hy))
  · have hy' : y ∈ (regionRet σ exportReg (NarrowWords.wideTy t0) r.res).toList.map Prod.snd :=
      hy
    rw [hret] at hy'
    cases hy'

example (S : FieldDomStages) : type_of% @S.fuseResultName := @fieldDom_fuseResultName

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
