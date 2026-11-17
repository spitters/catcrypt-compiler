/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomFoldPosBack
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomInputAcc

/-!
# The hypotheses of the field fold positions

The theorem `fieldDom_foldPos_of_back` derives the field `foldPos` of `FieldDomOpen` from the
shape `LoadsChainK` of the legalized chain output and conditions on the back half of the region
gate. This module discharges the condition on the coalescing renaming on the field domain: the
alias table of the code with its result copies sends every name either to a word-array
parameter, whose name begins with `a`, or to itself, so no other name is sent to an access
index, whose name begins with `r`.

## Main results

* `canonMemrefName_aliasTab_or_self`: along code whose indexed bases are defined before use,
  the coalescing renaming sends every name into `P` or fixes it.
* `fieldDom_idxOk_regionCoCode`: on the field domain, the code with its result copies defines
  its indexed bases before use from the word-array parameters.
* `fieldBody_accIn_coCode`: the access indices of the code with its result copies begin with
  `r`.
* `fieldDom_canonMemrefName_inj`: on the field domain, the coalescing renaming sends no other
  name to an access index.
* `fieldDom_sites_addSub`: the sum and the difference have no site of the multiplication
  fusion.
* `fieldDom_foldPos_of_loadsChainK`, `fieldDom_foldPos_addSub_of_loadsChainK`: the field
  fold positions from the shape `LoadsChainK`, the absence of array self-moves, the fold class
  and, for the product and the square, the conditions of the fusion.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (wireOK fuseLo)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasTab aliasStepO
  zeroDst?)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg (IdxIn IdxOk addDst afterDst
  stPair stDst ArgSlotName ResNamed ArrNamed wordsSlotB idxIn_mono idxOk_append le_afterDst
  afterDst_append idxOk_resCopyCode)

/-! ## 1. The coalescing renaming sends a name into `P` or fixes it -/

/-- **The coalescing renaming sends every name into `P` or fixes it** when along the code every
    indexed base is defined before use (`IdxOk`) from names at which `P` holds and `P` holds at
    the destination of every zeroing. -/
theorem canonMemrefName_aliasTab_or_self (P : String → Prop) {C : List LinstrRM}
    {S : String → Prop} (hC : IdxOk S C) (hS : ∀ x, S x → P x)
    (hZ : ∀ i ∈ C, ∀ z, zeroDst? i = some z → P z) (y : String) :
    P (canonMemrefName (aliasTab [] C) y) ∨ canonMemrefName (aliasTab [] C) y = y := by
  let G : Std.HashMap String String → String → Prop := fun m x => P (canonMemrefName m x)
  let Inv : Std.HashMap String String → Prop := fun m => ∀ x, G m x ∨ m.getD x x = x
  have step : ∀ (S : String → Prop) (m : Std.HashMap String String) (i : LinstrRM),
      IdxIn S i → (∀ x, S x → G m x) → Inv m → (∀ z, zeroDst? i = some z → P z) →
      (∀ x, addDst S i x → G (aliasStepO [] m i) x) ∧ Inv (aliasStepO [] m i) := by
    intro S m i hi hSm hinv hzi
    have hzG : ∀ z, zeroDst? i = some z → G m z := by
      intro z hz
      rcases hinv z with h | h
      · exact h
      · change P (m.getD z z)
        rw [h]
        exact hzi z hz
    rw [RegionPhysImgArg.aliasStepO_nil]
    cases hp : stPair i with
    | none =>
        refine ⟨fun x hx => ?_, hinv⟩
        rcases hx with hx | hx | hx
        · exact hSm x hx
        · simp [stDst, hp] at hx
        · exact hzG x hx
    | some p =>
        obtain ⟨dst, base⟩ := p
        have hb : G m base := by
          rcases RegionPhysImgArg.stPair_some hp with ⟨opn, y, s, rest, he⟩ | ⟨rest, he⟩
          · exact hSm _ ((hi _ _ _ he).1 base y s List.mem_cons_self)
          · exact hSm _ ((hi _ _ _ he).2 rfl base rest rfl)
        have hins : ∀ x, G m x ∨ x = dst → G (m.insert dst (m.getD base base)) x := by
          intro x hx
          change P ((m.insert dst (m.getD base base)).getD x x)
          rw [Std.HashMap.getD_insert]
          by_cases h : dst = x
          · subst h
            simp only [beq_self_eq_true, ite_true]
            exact hb
          · simp only [beq_iff_eq, h, ite_false]
            rcases hx with hx | rfl
            · exact hx
            · exact absurd rfl h
        refine ⟨fun x hx => ?_, fun x => ?_⟩
        · rcases hx with hx | hx | hx
          · exact hins x (Or.inl (hSm x hx))
          · simp only [stDst, hp, Option.map_some, Option.some.injEq] at hx
            exact hins x (Or.inr hx.symm)
          · exact hins x (Or.inl (hzG x hx))
        · by_cases h : dst = x
          · exact Or.inl (hins x (Or.inr h.symm))
          · rcases hinv x with hx | hx
            · exact Or.inl (hins x (Or.inl hx))
            · right
              rw [Std.HashMap.getD_insert]
              simp only [beq_iff_eq, h, ite_false]
              exact hx
  have main : ∀ (C : List LinstrRM) (S : String → Prop) (m : Std.HashMap String String),
      IdxOk S C → (∀ x, S x → G m x) → Inv m →
      (∀ i ∈ C, ∀ z, zeroDst? i = some z → P z) → Inv (C.foldl (aliasStepO []) m) := by
    intro C
    induction C with
    | nil => exact fun _ _ _ _ hinv _ => hinv
    | cons i C ih =>
        intro S m hok hSm hinv hz
        obtain ⟨s2, s3⟩ := step S m i hok.1 hSm hinv (hz i List.mem_cons_self)
        exact ih (addDst S i) _ hok.2 s2 s3 fun j hj => hz j (List.mem_cons_of_mem _ hj)
  have hinv0 : Inv {} := fun x => Or.inr Std.HashMap.getD_empty
  exact main C S {} hC (fun x hx => by
    change P (({} : Std.HashMap String String).getD x x)
    rw [Std.HashMap.getD_empty]
    exact hS x hx) hinv0 hZ y

/-- A word-array parameter name begins with `a`, not with `r`. -/
theorem not_headR_of_argSlotName {σ : AbiLayout} {x : String} (h : ArgSlotName σ x) :
    ¬ HeadR x := by
  obtain ⟨j, rfl, -⟩ := h
  simp [HeadR, argName, String.toList_append]

/-! ## 2. The field domain -/

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- The copies of the pairs index no array. -/
theorem idxOk_movesOf (T : String → Prop) (ps : List (String × String)) :
    IdxOk T (JasminLsemRenameLoop.movesOf ps) := by
  induction ps generalizing T with
  | nil => trivial
  | cons p ps ih =>
      refine ⟨fun ds o ss he => ?_, ih _⟩
      simp only [JasminLsemExportLower.movWire, LinstrR.Lopn.injEq] at he
      obtain ⟨-, rfl, rfl⟩ := he
      exact ⟨fun b y s hm => by simp at hm, fun ho => by simp at ho⟩

/-- **The access indices of the code with its result copies begin with `r`** on the field
    domain, when the legalized chain output has the shape `LoadsChainK`. -/
theorem fieldBody_accIn_coCode (hB : FieldBody e σ fname b t r cert)
    (hL : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → LoadsChainK (fun _ => none) (legalizeRegion q')) :
    AccIn HeadR (regionCoCode σ exportReg t r.code r.res
      (regionCopy σ exportReg t none r.code r.res)) := by
  have hr : AccIn HeadR r.code := by
    obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, -⟩ := hB
    have h0 := loadsChainK_export_slotIdx (hL t0 q q' hq hq') le_rfl hr0
    have h1 : AccIn HeadR r0.code := fun k i x m hk ha => by
      obtain ⟨s, rfl⟩ := h0 k i x m hk ha
      simp [HeadR, regName, String.toList_append]
    rw [regionWebsAt_none]
    unfold regionWebs
    split
    · exact accIn_of_getElem? _ (fun j => List.getElem?_mapIdx)
        (fun _ _ _ _ ha => accIdx_of_renArr _ ha) h1
    · exact h1
  exact accIn_regionCoCode σ exportReg t r.res _ hr

/-- **On the field domain the code with its result copies defines its indexed bases before
    use** from the word-array parameters with a save slot, and has no zeroing. -/
theorem fieldDom_idxOk_regionCoCode (h : fieldDomB' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    IdxOk (ArgSlotName σ)
        (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))
      ∧ ∀ i ∈ regionCoCode σ exportReg t r.code r.res
          (regionCopy σ exportReg t none r.code r.res), zeroDst? i = none := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, rfl⟩ := hB
  have hd := fieldDomB_of_fieldDomB' h
  obtain ⟨k, n, hk, rfl, -⟩ := fieldDomB'_layout h
  have hk' := fieldDomE_k hk
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal hd) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hcf : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree hd hq))
  have hEx : regionExportableB (legalizeRegion q') = true := fieldDom_legalize hE1
  have hL := fieldDom_legalize_loadsChainS hd hq hq'
  have hw := arrW64B_loadsChainS hL hEx (ctxW64_nfCtx _)
  have hσ := wordsSlotB_fieldAbi (n := n) hk'
  have hA : ArrNamed (ArgSlotName (FieldRoute.fieldAbi k n))
      ((nfCtx (FieldRoute.fieldAbi k n)).map NarrowWords.wideTy).length
      ((nfCtx (FieldRoute.fieldAbi k n)).map NarrowWords.wideTy).length
      ((nfCtx (FieldRoute.fieldAbi k n)).map NarrowWords.wideTy) := by
    rw [List.length_map]
    exact arrNamed_map_wideTy (RegionPhysImgArg.arrNamed_nfCtx hσ)
  rw [regionWebsAt_none]
  set ex := regionWebsEx (FieldRoute.fieldAbi k n) exportReg
  set S := ArgSlotName (FieldRoute.fieldAbi k n)
  obtain ⟨k1, k2⟩ := RegionPhysImgArg.exportR_idxOk _ fname _ hEx hcf _ 0 r0 hr0 le_rfl S hA
  obtain ⟨⟨x, hE⟩, -⟩ := loadsChainS_export_class (fn := fname) hL le_rfl hr0
  have hAcc := RegionPhysImgArg.exportR_accCode _ _ _ hcf hw _ _ r0 hr0
  have hImm : ∀ i ∈ r0.code, RegionPhysImgArg.ImmCode i := fun i hi =>
    RegionPhysImgArg.exportR_immCode_copy (nfAbiNames fname (FieldRoute.fieldAbi k n)) _ hcf hr0 i
      (List.mem_append_left _ hi)
  have hplain : ∀ i ∈ r0.code, PlainTag i := fun i hi => by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    exact (hE k i hk).1
  have hsh := (regionExp_of_exportR ex hr0).noShadow hEx hcf
  have hst : ∀ (k : Nat) (i : LinstrRM), r0.code[k]? = some i → StraightOp i := fun k i hk =>
    straightOp_of_lopn (hsh i (List.mem_of_getElem? hk)) (hE k i hk).2.1
  have hF := fun i hi => accFacts (hAcc i hi) (hImm i hi) (hplain i hi)
  have hW : IdxOk S (regionWebs ex r0).code ∧
      ResNamed (afterDst S (regionWebs ex r0).code) [NarrowWords.wideTy t0] r0.res := by
    rcases RegionExportDefInit.regionWebs_webB ex r0 with he | ⟨w, hacc, he⟩ <;> rw [he]
    · exact ⟨k1, k2⟩
    · refine ⟨idxOk_webRen hacc hst hplain (fun i hi => (hF i hi).1) (fun i hi => (hF i hi).2.1)
        (fun i hi => (hF i hi).2.2.1) (fun i hi => (hF i hi).2.2.2) k1, fun j w' m hj => ?_⟩
      obtain ⟨o, ho, hS⟩ := k2 j w' m hj
      refine ⟨o, ho, afterDst_webRen hacc hst (fun i hi => (hF i hi).2.2.1)
        (fun i hi => (hF i hi).2.2.2) ?_ hS⟩
      simp only [regionWebsObs, List.mem_append, List.mem_map]
      exact .inl ⟨o, List.mem_of_getElem? ho, rfl⟩
  have hz0 : ∀ i ∈ (regionWebs ex r0).code, zeroDst? i = none := by
    refine fun i hi => (forall_mem_regionWebs
      (P := fun i => PlainTag i ∧ RegionCoComplete.NoShadow i ∧ zeroDst? i = none)
      (fun ρ i hi => ⟨by rw [PlainTag, renArr_snd]; exact hi.1,
        RegionCoComplete.noShadow_renArr ρ hi.2.1, zeroDst?_renArr ρ hi.1 hi.2.1 hi.2.2⟩)
      ex r0 _ _ (fun i hi => ?_) i hi).2.2
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    exact ⟨hplain i hi, hsh i hi, (hE k i hk).2.2.1⟩
  refine ⟨?_, regionCoCode_noZero _ _ _ _ _ hz0⟩
  rw [regionWebs_res]
  have hmv := idxOk_append hW.1 (fun _ h => h) (idxOk_movesOf _
    (regionRet (FieldRoute.fieldAbi k n) exportReg (NarrowWords.wideTy t0) r0.res).toList)
  unfold regionCoCode
  split
  · exact hmv
  · rename_i src D m hcp
    obtain ⟨-, ht, ⟨op, hres, hop⟩, ⟨j, a, hj, hka, rfl⟩, -, -⟩ := regionCopy_some hcp
    have hD : S (argName j) := ⟨j, rfl, RegionPhysImgArg.argSlot_of_wordsSlotB hσ hj hka⟩
    obtain ⟨o, ho, hso⟩ := hW.2 0 64 m (by rw [ht]; rfl)
    rw [hres] at ho
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ho
    subst ho
    refine idxOk_append hmv (fun _ h => h) (idxOk_resCopyCode m ?_ ?_)
    · rw [afterDst_append, ← hop]
      exact le_afterDst _ hso
    · rw [afterDst_append]
      exact le_afterDst _ (le_afterDst _ hD)

/-- **On the field domain the coalescing renaming sends no other name to an access index**:
    the hypothesis `hA` of `fieldDom_foldPos_of_back`. -/
theorem fieldDom_canonMemrefName_inj (h : fieldDomB' e σ = true)
    (hB : FieldBody e σ fname b t r cert)
    (hL : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → LoadsChainK (fun _ => none) (legalizeRegion q')) :
    ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat),
      (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))[k]?
        = some i → AccIdx i x m →
      ∀ y, canonMemrefName (regionAliasTab σ exportReg t none r.res
        (regionCoCode σ exportReg t r.code r.res
          (regionCopy σ exportReg t none r.code r.res))) y = x → y = x := by
  intro k i x m hk ha y hy
  obtain ⟨hok, hz⟩ := fieldDom_idxOk_regionCoCode h hB
  have hx : HeadR x := fieldBody_accIn_coCode hB hL k i x m hk ha
  rw [regionAliasTab_eq_of_noZero _ _ _ _ _ hz] at hy
  change canonMemrefName (aliasTab [] _) y = x at hy
  rcases canonMemrefName_aliasTab_or_self (ArgSlotName σ) hok (fun _ h => h)
    (fun i hi z hz' => by rw [hz i hi] at hz'; cases hz') y with h1 | h1
  · rw [hy] at h1
    exact absurd hx (not_headR_of_argSlotName h1)
  · rw [← hy, h1]

/-- **The sum and the difference of the field domain have no site of the multiplication
    fusion**, so the hypotheses `hw` and `hlo` of `fieldDom_foldPos_of_back` hold vacuously. -/
theorem fieldDom_sites_addSub (h : fieldDomB e σ = true) (hA : FieldAddSub e)
    (hB : FieldBody e σ fname b t r cert) :
    (regionCoParts σ exportReg b t r.code r.res cert).sites = false := by
  have hH := exportHiFree_addSub (fname := fname) h hA
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, hr, -, -, rfl⟩ := hB
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal h) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hcf : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree h hq))
  have hEx : regionExportableB (legalizeRegion q') = true := fieldDom_legalize hE1
  have hX0 : RegionExp fname (legalizeRegion q') [] r0 := regionExp_of_exportR _ hr0
  have hns0 : ∀ i ∈ r0.code, RegionCoComplete.NoShadow i := hX0.noShadow hEx hcf
  have hc : ∀ i ∈ r.code, HiFree i.1 := by
    rw [hr]
    exact hiFree_regionWebs hns0 (hH t0 q q' r0 hq hq' hr0) _ _ _
  have hX : RegionExp fname (legalizeRegion q') (regionWebsEx σ exportReg) r := by
    rw [hr]
    exact regionExp_webs _ hr0
  exact sites_eq_false_of_hiFree (hX.noShadow hEx hcf) hc

/-- **The fold positions of the field domain from the shape `LoadsChainK`** of the legalized
    chain output, the absence of array self-moves (`hNP`), the conditions of the
    multiplication fusion at a fusion site (`hF`) and the fold class of the code behind the
    prefix (`hP`); the condition on the coalescing renaming holds on the field domain
    (`fieldDom_canonMemrefName_inj`). -/
theorem fieldDom_foldPos_of_loadsChainK (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert)
    (hL : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → LoadsChainK (fun _ => none) (legalizeRegion q'))
    (hNP : ∀ k, selfPairB (regionCoParts σ exportReg b t r.code r.res cert).pre.length
      (liveAt (tabAt (regionCoParts σ exportReg b t r.code r.res cert).liveM)
        ((regionCoParts σ exportReg b t r.code r.res cert).pre
          ++ (regionCoParts σ exportReg b t r.code r.res cert).merged).length)
      ((regionCoParts σ exportReg b t r.code r.res cert).pre
        ++ (regionCoParts σ exportReg b t r.code r.res cert).merged) k = false)
    (hF : (regionCoParts σ exportReg b t r.code r.res cert).sites = true →
      (∀ i ∈ (regionCoParts σ exportReg b t r.code r.res cert).merged, wireOK i.1 = true) ∧
      ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat),
        (regionCoParts σ exportReg b t r.code r.res cert).merged[k]? = some i →
        AccIdx i x m → ∀ (j : Nat) (dd : String),
        (fuseLo (regionCoParts σ exportReg b t r.code r.res cert).merged)[j]? = some (some dd) →
        dd ≠ x)
    (hP : ∀ (k : Nat) (i : LinstrRM),
      ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      PosClass (regionCoParts σ exportReg b t r.code r.res cert).cells i) :
    ∀ k i, ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      FoldPos (regionCoParts σ exportReg b t r.code r.res cert).cells
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) k i :=
  fieldDom_foldPos_of_back (fieldDomB_of_fieldDomB'' h) hB hL
    (fieldDom_canonMemrefName_inj (fieldDomB'_of_fieldDomB'' h) hB hL) hNP
    (fun hs => (hF hs).1) (fun hs => (hF hs).2) hP

/-- **The fold positions of the sum and the difference of the field domain** from the shape
    `LoadsChainK`, the absence of array self-moves and the fold class: the sum and the
    difference have no site of the multiplication fusion. -/
theorem fieldDom_foldPos_addSub_of_loadsChainK (h : fieldDomB'' e σ = true) (hA : FieldAddSub e)
    (hB : FieldBody e σ fname b t r cert)
    (hL : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → LoadsChainK (fun _ => none) (legalizeRegion q'))
    (hNP : ∀ k, selfPairB (regionCoParts σ exportReg b t r.code r.res cert).pre.length
      (liveAt (tabAt (regionCoParts σ exportReg b t r.code r.res cert).liveM)
        ((regionCoParts σ exportReg b t r.code r.res cert).pre
          ++ (regionCoParts σ exportReg b t r.code r.res cert).merged).length)
      ((regionCoParts σ exportReg b t r.code r.res cert).pre
        ++ (regionCoParts σ exportReg b t r.code r.res cert).merged) k = false)
    (hP : ∀ (k : Nat) (i : LinstrRM),
      ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      PosClass (regionCoParts σ exportReg b t r.code r.res cert).cells i) :
    ∀ k i, ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      FoldPos (regionCoParts σ exportReg b t r.code r.res cert).cells
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) k i :=
  fieldDom_foldPos_of_loadsChainK h hB hL hNP
    (fun hs => by rw [fieldDom_sites_addSub (fieldDomB_of_fieldDomB'' h) hA hB] at hs; cases hs)
    hP

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
