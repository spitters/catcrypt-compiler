/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomSites

/-!
# The fusion check on code without a high-word multiplication

The stage `fuseOKL` of the region gate asks `!d.sites || fuseOKL …` of the parts `d` of the
code. The flag `d.sites` is `fuseSites` of the code behind the prefix, which marks a position
when an instruction `MULXHI` meets a pending low multiplication on the same second operand
(`fuseLoAux`). So code with no instruction under the mnemonic `MULXHI` has no fusion site and
the stage passes.

The passes from the webs of the export to that code keep the absence of `MULXHI`: the webs and
the coalescing rename array positions instruction by instruction (`renArr`) and keep the
mnemonic of every instruction that is no shadow of a call; the renamings `renOf` of the
certificate keep every mnemonic; the result moves and copies are moves, loads and stores; and
the removal of array self-moves replaces an instruction by a 64-bit move (`selfNopI`).

## Main definitions

* `HiFree`: an instruction that is no operation under the mnemonic `MULXHI`.

## Main results

* `fuseSites_eq_false`: code of `HiFree` instructions has no fusion site.
* `regionCoStage_ne_fuseOKL_of_sites`: the gate does not refuse at `fuseOKL` when the parts
  have no fusion site.
* `sites_eq_false_of_hiFree`: the parts of code of `HiFree` instructions without shadows have
  no fusion site.
* `fieldDom_fuseOKL_of_hiFree`: the stage `G10` on the field domain when the exported code has
  no `MULXHI`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseLo fuseLoAux)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (isMulHiMnem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr renLoad renStore
  renZero renStoreImm renCallW_of_none)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoComplete (NoShadow)
open CatCrypt.Crypto.Hax (HaxModule)

/-! ## 1. No fusion site without `MULXHI` -/

/-- **An instruction that is no operation under the mnemonic `MULXHI`.** -/
def HiFree (w : LinstrR) : Prop := ∀ ds o ss, w = .Lopn ds o ss → isMulHiMnem o = false

/-- The low destinations of code of `HiFree` instructions are all `none`, from every list of
    pending low multiplications. -/
theorem fuseLoAux_none : ∀ (c : List LinstrR) (pend : List (String × String)),
    (∀ w ∈ c, HiFree w) → ∀ x ∈ fuseLoAux pend c, x = none
  | [], _, _ => by simp [fuseLoAux]
  | w :: c, pend, h => by
      have hw : HiFree w := h w (List.mem_cons_self ..)
      have hc : ∀ w ∈ c, HiFree w := fun w' hw' => h w' (List.mem_cons_of_mem _ hw')
      intro x hx
      unfold fuseLoAux at hx
      split at hx
      · have hh := hw _ _ _ rfl
        split_ifs at hx with h1 h2
        · rcases List.mem_cons.mp hx with rfl | hx
          · rfl
          · exact fuseLoAux_none c _ hc x hx
        · rw [hh] at h2
          cases h2
        · rcases List.mem_cons.mp hx with rfl | hx
          · rfl
          · exact fuseLoAux_none c _ hc x hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact fuseLoAux_none c _ hc x hx

/-- **Code of `HiFree` instructions has no fusion site.** -/
theorem fuseSites_eq_false {c : List LinstrRM} (h : ∀ i ∈ c, HiFree i.1) :
    fuseSites c = false := by
  unfold fuseSites fuseLo
  rw [List.any_eq_false]
  intro x hx
  rw [fuseLoAux_none _ [] (fun w hw => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw; exact h i hi) x hx]
  simp

/-! ## 2. The passes keep `HiFree` -/

/-- A 64-bit move is `HiFree`. -/
theorem hiFree_mov (ds ss : List LOperand) : HiFree (.Lopn ds "MOV:64" ss) := by
  intro _ o _ he
  cases he
  decide

/-- A renaming keeps `HiFree`. -/
theorem hiFree_renLinstrR (σ : String → String) {w : LinstrR} (h : HiFree w) :
    HiFree (renLinstrR σ w) := by
  intro ds o ss he
  cases w with
  | Lopn ds0 o0 ss0 =>
    simp only [renLinstrR, LinstrR.Lopn.injEq] at he
    obtain ⟨-, rfl, -⟩ := he
    exact h _ _ _ rfl
  | _ => simp [renLinstrR] at he

/-- The renamings of the base of a load, a store, a zeroing and a constant-index store keep
    the mnemonic, so they keep `HiFree`. -/
theorem hiFree_renLoad (σ : String → String) {w : LinstrR} (h : HiFree w) :
    HiFree (renLoad σ w) := by
  unfold renLoad
  split
  · split
    · intro ds o ss he
      cases he
      exact h _ _ _ rfl
    · exact h
  · exact h

theorem hiFree_renStore (σ : String → String) {w : LinstrR} (h : HiFree w) :
    HiFree (renStore σ w) := by
  unfold renStore
  split
  · split
    · intro ds o ss he
      cases he
      exact h _ _ _ rfl
    · exact h
  · exact h

theorem hiFree_renZero (σ : String → String) {w : LinstrR} (h : HiFree w) :
    HiFree (renZero σ w) := by
  unfold renZero
  split
  · split
    · intro ds o ss he
      cases he
      exact h _ _ _ rfl
    · exact h
  · exact h

theorem hiFree_renStoreImm (σ : String → String) {w : LinstrR} (h : HiFree w) :
    HiFree (renStoreImm σ w) := by
  unfold renStoreImm
  split
  · split
    · intro ds o ss he
      cases he
      exact h _ _ _ rfl
    · exact h
  · exact h

/-- The renaming of array positions keeps `HiFree` on an instruction that is no shadow of a
    call. -/
theorem hiFree_renArr (σ : String → String) {i : LinstrRM} (hs : NoShadow i) (h : HiFree i.1) :
    HiFree (renArr σ i).1 := by
  obtain ⟨w, tg⟩ := i
  unfold renArr
  split
  · exact hiFree_renLoad σ h
  · exact hiFree_renStore σ h
  · exact hiFree_renZero σ h
  · exact hiFree_renStoreImm σ h
  · rw [renCallW_of_none hs]
    exact h

/-- The removal of array self-moves keeps `HiFree`. -/
theorem hiFree_selfNop (k0 : Nat) (Lr : Nat → List String) {B : List LinstrRM}
    (h : ∀ i ∈ B, HiFree i.1) : ∀ i ∈ selfNop k0 Lr B, HiFree i.1 := by
  intro i hi
  unfold selfNop at hi
  obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hi
  split
  · unfold selfNopI
    split
    · exact hiFree_mov _ _
    · exact h _ (List.getElem_mem hk)
  · exact h _ (List.getElem_mem hk)

/-- The moves of a list of pairs are `HiFree`. -/
theorem hiFree_movesOf (ps : List (String × String)) : ∀ i ∈ movesOf ps, HiFree i.1 := by
  intro i hi
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  exact hiFree_mov _ _

/-- The code with the result moves and copies keeps `HiFree`. -/
theorem hiFree_regionCoCode (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    {code : List LinstrRM} (res : List LOperand) (cp : Option (String × String × Nat))
    (h : ∀ i ∈ code, HiFree i.1) : ∀ i ∈ regionCoCode σ nm t code res cp, HiFree i.1 := by
  have hc : ∀ src D m, ∀ i ∈ resCopyCode src D m, HiFree i.1 := by
    intro src D m i hi
    obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
    simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> intro ds o ss he <;> cases he <;> decide
  intro i hi
  unfold regionCoCode at hi
  split at hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact h i hi
    · exact hiFree_movesOf _ i hi
  · rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact h i hi
      · exact hiFree_movesOf _ i hi
    · exact hc _ _ _ i hi

/-! ## 3. The stage -/

/-- The flag of the fusion sites of the parts is `fuseSites` of the code behind the prefix. -/
theorem regionCoParts_sites (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (callee : Option CalleeTab) :
    (regionCoParts σ nm body t code res cert callee).sites
      = fuseSites ((regionCoParts σ nm body t code res cert callee).nop.drop
          (regionCoParts σ nm body t code res cert callee).pre.length) := rfl

/-- **The parts of code of `HiFree` instructions without shadows of calls have no fusion
    site.** -/
theorem sites_eq_false_of_hiFree {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {t : JasminTy} {code : List LinstrRM} {res : List LOperand} {cert : List (String × String)}
    (hs : ∀ i ∈ code, NoShadow i) (h : ∀ i ∈ code, HiFree i.1) :
    (regionCoParts σ nm body t code res cert none).sites = false := by
  rw [regionCoParts_sites]
  apply fuseSites_eq_false
  intro i hi
  replace hi := List.mem_of_mem_drop hi
  refine hiFree_selfNop _ _ ?_ i hi
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · rcases List.mem_append.mp hj with hj | hj
    · exact hiFree_movesOf _ j hj
    · exact hiFree_movesOf _ j hj
  · obtain ⟨j1, hj1, rfl⟩ := List.mem_map.mp hj
    obtain ⟨j2, hj2, rfl⟩ := List.mem_map.mp hj1
    obtain ⟨j3, hj3, rfl⟩ := List.mem_map.mp hj2
    exact hiFree_renLinstrR _ (hiFree_renLinstrR _ (hiFree_renArr _
      (RegionCoComplete.noShadow_regionCoCode _ _ _ _ _ _ hs j3 hj3)
      (hiFree_regionCoCode _ _ _ _ _ h j3 hj3)))

/-- **The gate does not refuse at `fuseOKL` when the parts have no fusion site.** -/
theorem regionCoStage_ne_fuseOKL_of_sites {σ : AbiLayout} {nm : String → String} {b : Lcmd}
    {t : JasminTy} {code : List LinstrRM} {res : List LOperand} {cert : List (String × String)}
    {fn : String} (h : (regionCoParts σ nm b t (calleeCodeT none code) res cert none).sites = false) :
    regionCoStage σ nm b t code res cert none fn ≠ some "fuseOKL" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.not_false, Bool.true_or, Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **The webs keep `HiFree`** on code without shadows of calls: they rename array positions
    instruction by instruction. -/
theorem hiFree_regionWebs {r : Exported} (hs : ∀ i ∈ r.code, NoShadow i)
    (h : ∀ i ∈ r.code, HiFree i.1) (ex : List String) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) : ∀ i ∈ (regionWebs ex r aa ao).code, HiFree i.1 := by
  unfold regionWebs
  split
  · intro i hi
    obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hi
    exact hiFree_renArr _ (hs _ (List.getElem_mem hk)) (h _ (List.getElem_mem hk))
  · exact h

/-! ## 4. The field domain -/

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The exported code of a member has no `MULXHI`**: every instruction of the export of the
    program the export receives is `HiFree`. -/
def ExportHiFree (e : _root_.Hax.TExpr) (σ : AbiLayout) (fname : String) : Prop :=
  ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
    (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0])
    (r0 : Exported),
    haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩ →
    NarrowWords.narrowPrep q = some q' →
    exportR ((nfCtx σ).map NarrowWords.wideTy).length fname (legalizeRegion q')
        ((nfCtx σ).map NarrowWords.wideTy).length 0 = some r0 →
    ∀ i ∈ r0.code, HiFree i.1

/-- **Stage `G10` on the field domain** when the exported code has no `MULXHI`
    (`ExportHiFree`): the parts have no fusion site. -/
theorem fieldDom_fuseOKL_of_hiFree (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) (hH : ExportHiFree e σ fname) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "fuseOKL" := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, hr, -, -, rfl⟩ := hB
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal h) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hcf : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree h hq))
  have hEx : regionExportableB (legalizeRegion q') = true := fieldDom_legalize hE1
  have hX0 : RegionExp fname (legalizeRegion q') [] r0 := regionExp_of_exportR _ hr0
  have hns0 : ∀ i ∈ r0.code, NoShadow i := hX0.noShadow hEx hcf
  have hc : ∀ i ∈ r.code, HiFree i.1 := by
    rw [hr]
    exact hiFree_regionWebs hns0 (hH t0 q q' r0 hq hq' hr0) _ _ _
  have hX : RegionExp fname (legalizeRegion q') (regionWebsEx σ exportReg) r := by
    rw [hr]
    exact regionExp_webs _ hr0
  exact regionCoStage_ne_fuseOKL_of_sites
    (sites_eq_false_of_hiFree (hX.noShadow hEx hcf) hc)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
