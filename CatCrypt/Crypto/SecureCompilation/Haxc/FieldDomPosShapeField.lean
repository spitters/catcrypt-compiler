/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomAccessShape
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomPosShapeHyps

/-!
# The shape of the fold class on the field domain

The theorem `fieldDom_foldPos_addSub_of_posShape_noLoadStore` takes the shape `PosShape` of every
instruction of the code behind the prefix of the parts as its hypothesis `hS`. This module proves
it for the sum and the difference of the field domain.

There the code has no site of the multiplication fusion (`fieldDom_sites_addSub`) and no merge
pair (`fieldDom_tau_nil`), so an instruction behind the prefix is an instruction `c` of the code
with its result copies, renamed at its array positions by the coalescing renaming `ρ` and at its
names by the pairs, or its replacement `selfNopI`. The export of a program of the shape
`LoadsChainS` has a register tag, or is a `LOADIDX` at a load tag or a `STOREIDX` at a store tag
(`TagWire`), and so has the result copy. The accesses are at the tag of the `n` words of the
parameters of the layout (`fieldDom_accTag`) and their scalar operands are no parameter names
(`fieldDom_accScalar`). The coalescing renaming sends the array a store writes and the array it
reads to one root, so the renamed store writes its own base. The cell arrays are parameters of
`n` words under the names renamed by the pairs, and the pairs fix a name of the code that is no
parameter name, so no scalar operand is a cell array.

## Main definitions

* `TagWire`: an instruction has a register tag, or is a `LOADIDX` at a load tag or a `STOREIDX`
  at a store tag.
* `CoShape`: `TagWire` at the tag of `n` `64`-bit words, with scalar operands that are no
  parameter names.

## Main results

* `loadsChainS_export_tagWire`, `fieldDom_tagWire`: the export of a program of the shape
  `LoadsChainS`, and the region code of the field domain, have `TagWire`.
* `fieldDom_coShape`: every instruction of the code with the result copies has `CoShape`.
* `fieldDom_storeOwn`: the coalescing renaming sends the destination and the base of every store
  of that code to one name.
* `fieldDom_isArrB_renOf`: the pairs send no name of the code other than a parameter name to a
  cell array.
* `fieldDom_posShape`: the hypothesis `hS` of `fieldDom_foldPos_addSub_of_posShape_noLoadStore`.
* `fieldDom_foldPos_addSub_noLoadStore`: the fold positions of the sum and the difference without
  the hypothesis `hS`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr renLoad renStore)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR
  renOperand)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames dstNames_sub)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots isArrB lenOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg (noArrB readNames)
open Ctxt (Var)

/-! ## 1. The tags of the export -/

/-- **The tag shape of an instruction**: a register tag, a `LOADIDX` of one indexed operand into
    one register at a load tag, or a `STOREIDX` of a register at one indexed operand at a store
    tag. -/
def TagWire (i : LinstrRM) : Prop :=
  (∃ c, i.2 = .reg c)
  ∨ (∃ d b x s w m, i = (.Lopn [.reg d] "LOADIDX" [.arrIdx b x s], .load w m))
  ∨ (∃ d b x s v w m, i = (.Lopn [.reg d] "STOREIDX" [.arrIdx b x s, .reg v], .store w m))

/-- The renaming of the array positions keeps the tag shape. -/
theorem tagWire_renArr (ρ : String → String) {i : LinstrRM} (h : TagWire i) :
    TagWire (renArr ρ i) := by
  rcases h with ⟨c, hc⟩ | ⟨d, b, x, s, w, m, rfl⟩ | ⟨d, b, x, s, v, w, m, rfl⟩
  · exact .inl ⟨c, by rw [renArr_snd, hc]⟩
  · exact .inr (.inl ⟨d, ρ b, x, s, w, m, by simp [renArr, renLoad]⟩)
  · exact .inr (.inr ⟨ρ d, ρ b, x, s, v, w, m, by simp [renArr, renStore]⟩)

variable {nArgs : Nat} {fn : String}

/-- **The export of a chain tail has the tag shape.** -/
theorem chainTail_export_tagWire {Γ : Ctxt jasminDialect} {w m : Nat}
    {v : Var Γ (.stackArr w m)} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (h : ChainTail v p) {d k : Nat} {r : Exported} (hr : exportR nArgs fn p d k = some r) :
    ∀ i ∈ r.code, TagWire i := by
  induction h generalizing d k r with
  | ret v =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      intro i hi
      cases hi
  | free v e k' he _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      intro i hi
      simp only [Exported.prepend, List.mem_append] at hi
      rcases hi with hi | hi
      · obtain ⟨wire, c, hb⟩ := bindOps_memFree_reg nArgs d e he
        rw [hb, List.mem_singleton] at hi
        subst hi
        exact .inl ⟨c, rfl⟩
      · exact ih hk' i hi
  | store v i x k' _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      intro ins hi
      simp only [Exported.prepend, List.mem_append] at hi
      rcases hi with hi | hi
      · rw [bindOps_store_eq, List.mem_singleton] at hi
        subst hi
        exact .inr (.inr ⟨_, _, _, _, _, _, _, rfl⟩)
      · exact ih hk' ins hi

/-- **The export of a program of the shape `LoadsChainS` has the tag shape.** -/
theorem loadsChainS_export_tagWire {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) {d k : Nat} {r : Exported}
    (hr : exportR nArgs fn p d k = some r) : ∀ i ∈ r.code, TagWire i := by
  induction h generalizing d k r with
  | free e k' he _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      intro i hi
      simp only [Exported.prepend, List.mem_append] at hi
      rcases hi with hi | hi
      · obtain ⟨wire, c, hb⟩ := bindOps_memFree_reg nArgs d e he
        rw [hb, List.mem_singleton] at hi
        subst hi
        exact .inl ⟨c, rfl⟩
      · exact ih hk' i hi
  | load a i k' _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      intro ins hi
      simp only [Exported.prepend, List.mem_append] at hi
      rcases hi with hi | hi
      · rw [bindOps_load_eq, List.mem_singleton] at hi
        subst hi
        exact .inr (.inl ⟨_, _, _, _, _, _, rfl⟩)
      · exact ih hk' ins hi
  | store v i x k' hk =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      intro ins hi
      simp only [Exported.prepend, List.mem_append] at hi
      rcases hi with hi | hi
      · rw [bindOps_store_eq, List.mem_singleton] at hi
        subst hi
        exact .inr (.inr ⟨_, _, _, _, _, _, _, rfl⟩)
      · exact chainTail_export_tagWire hk hk' ins hi

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The region code of a member of the field domain has the tag shape.** -/
theorem fieldDom_tagWire (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    ∀ i ∈ r.code, TagWire i := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, -⟩ := hB
  have hL := fieldDom_legalize_loadsChainS h hq hq'
  rw [regionWebsAt_none]
  exact forall_mem_regionWebs (P := TagWire) (fun ρ i hi => tagWire_renArr ρ hi) _ r0 _ _
    (loadsChainS_export_tagWire hL hr0)

/-! ## 2. The code with the result copies -/

/-- **The access shape at `n` words with tags**: a register tag, or a load at the tag of `n`
    `64`-bit words whose destination and index are no parameter names, or a store at that tag
    whose index and value are no parameter names. -/
def CoShape (n : Nat) (c : LinstrRM) : Prop :=
  (∃ w', c.2 = .reg w')
  ∨ (∃ d b x s, c = (.Lopn [.reg d] "LOADIDX" [.arrIdx b x s], .load 64 n)
      ∧ ∀ j, d ≠ argName j ∧ x ≠ argName j)
  ∨ (∃ d b x s v, c = (.Lopn [.reg d] "STOREIDX" [.arrIdx b x s, .reg v], .store 64 n)
      ∧ ∀ j, x ≠ argName j ∧ v ≠ argName j)

/-- Every parameter of the field layout is an array of `n` words. -/
theorem fieldAbi_kind {k n : Nat} (ha : σ.args = (FieldRoute.fieldAbi k n).args) {j : Nat}
    {a : AbiArg} (hj : σ.args[j]? = some a) : a.kind = .words n := by
  rw [ha] at hj
  have hm := List.mem_of_getElem? hj
  simp only [FieldRoute.fieldAbi, List.mem_map] at hm
  obtain ⟨j', -, rfl⟩ := hm
  rfl

/-- **Every instruction of the code with the result copies of the field domain has the access
    shape with tags** at the length `n` of the parameters of the layout. -/
theorem fieldDom_coShape (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert)
    {k n : Nat} (ha : σ.args = (FieldRoute.fieldAbi k n).args) :
    ∀ c ∈ regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res),
      CoShape n c := by
  have hret : regionRet σ exportReg t r.res = none := by
    obtain ⟨-, R, n', hR⟩ := fieldDomB_abi h
    exact regionRet_words hR
  have hcode : ∀ c ∈ r.code, CoShape n c := by
    intro c hc
    rcases fieldDom_tagWire h hB c hc with ⟨w', hw⟩ | ⟨d, b0, x, s, w, m, rfl⟩ |
        ⟨d, b0, x, s, v, w, m, rfl⟩
    · exact .inl ⟨w', hw⟩
    · obtain ⟨rfl, hmn⟩ := fieldDom_accTag h hB ha _ hc w m (.inl rfl)
      subst m
      exact .inr (.inl ⟨d, b0, x, s, rfl,
        fun j => (fieldDom_accScalar h hB _ hc j).1 d b0 x s 64 n rfl⟩)
    · obtain ⟨rfl, hmn⟩ := fieldDom_accTag h hB ha _ hc w m (.inr rfl)
      subst m
      exact .inr (.inr ⟨d, b0, x, s, v, rfl,
        fun j => (fieldDom_accScalar h hB _ hc j).2 d b0 x s v 64 n rfl⟩)
  intro c hc
  unfold regionCoCode at hc
  rw [hret] at hc
  split at hc
  · simp only [Option.toList_none, movesOf, List.map_nil, List.append_nil] at hc
    exact hcode c hc
  · rename_i src D m hcp
    simp only [Option.toList_none, movesOf, List.map_nil, List.append_nil] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcode c hc
    obtain ⟨-, -, -, ⟨j, a, hj, hk, -⟩, -, -⟩ := regionCopy_some hcp
    have hmn : m = n := by
      have := fieldAbi_kind ha hj
      rw [hk] at this
      cases this
      rfl
    subst hmn
    obtain ⟨jj, -, hk⟩ := List.mem_flatMap.mp hc
    simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact .inl ⟨none, rfl⟩
    · exact .inr (.inl ⟨_, _, _, _, rfl, fun j => copyNames_ne_argName j⟩)
    · exact .inr (.inr ⟨_, _, _, _, _, rfl,
        fun j => ⟨(copyNames_ne_argName j).2, (copyNames_ne_argName j).1⟩⟩)

open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (rdArr wrArr) in
/-- **The coalescing renaming of the field domain sends the destination and the base of every
    store of the code with the result copies to one name.** -/
theorem fieldDom_storeOwn (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    ∀ c ∈ regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res),
      ∀ d0 b0 x s v w m,
        c = (.Lopn [.reg d0] "STOREIDX" [.arrIdx b0 x s, .reg v], .store w m) →
        regionAliasN σ exportReg t r.res
            (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))
            d0
          = regionAliasN σ exportReg t r.res
            (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))
            b0 := by
  obtain ⟨-, hag, hcp⟩ := (fieldDom_exportFacts h hB).1
  have hret : regionRet σ exportReg t r.res = none := by
    obtain ⟨-, R, n', hR⟩ := fieldDomB_abi h
    exact regionRet_words hR
  have hAg : AliasAgree
      (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res)) := by
    unfold regionCoCode
    rw [hret]
    split
    · simp only [Option.toList_none, movesOf, List.map_nil, List.append_nil]
      exact hag
    · rename_i src D m hcp'
      obtain ⟨-, -, -, ⟨j, a, -, -, rfl⟩, -, -⟩ := regionCopy_some hcp'
      simp only [Option.toList_none, movesOf, List.map_nil, List.append_nil]
      exact aliasAgree_append_copy hag fun i hi d b hd hb k _ =>
        hcp i hi d b hd hb _ (hash_not_mem_argName j) k
  intro c hc d0 b0 x s v w m hce
  subst hce
  have hw : wrArr (fun _ => none)
      ((.Lopn [.reg d0] "STOREIDX" [.arrIdx b0 x s, .reg v], .store w m) : LinstrRM)
      = some d0 := rfl
  have hr : rdArr (fun _ _ => none)
      ((.Lopn [.reg d0] "STOREIDX" [.arrIdx b0 x s, .reg v], .store w m) : LinstrRM)
      = [b0] := rfl
  exact RegionAllocMapFinal.resAliasTab_congr _ (hAg _ hc d0 b0 hw hr)

/-- **The code with the result copies of the field domain is built of operations.** -/
theorem fieldDom_isLopn_coCode (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    ∀ c ∈ regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res),
      JasminLsemMemLoop.IsLopn c := by
  have hF := fieldLetsOnly h
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, rfl⟩ := hB
  exact isLopn_regionCoCode_webs (exportR_isLopn_of_letsOnlyB (legalizeRegion q')
    (hF t0 q q' hq hq') _ _ _ hr0) σ exportReg _ _ _

/-- **The code with the result copies of the field domain has the forms `FormB`.** -/
theorem fieldDom_formB_coCode (hB : FieldBody e σ fname b t r cert) :
    ∀ c ∈ regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res),
      RegionExportForms.FormB c := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, -⟩ := hB
  exact RegionExportForms.formB_regionCoCode (RegionExportForms.formB_regionWebsAt hr0 _ none)
    σ exportReg _ _

/-- **The names of the code with the result copies of the field domain are names of the
    code.** -/
theorem fieldDom_codeName_coCode (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    ∀ c ∈ regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res),
      ∀ y ∈ instrNames c.1, CodeName y := by
  have hret : ∀ res, regionRet σ exportReg t res = none := by
    obtain ⟨-, R, n, hR⟩ := fieldDomB_abi h
    exact fun _ => regionRet_words hR
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, hr, -, -, rfl⟩ := hB
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
  exact codeName_regionCoCode fname _ hEx hcf hX σ exportReg (NarrowWords.wideTy t0) hsym
    hlen (hret _)

/-! ## 3. The cell arrays -/

/-- **The cell arrays of the field domain** are the parameters of `n` words under the names
    renamed by the pairs. -/
theorem fieldDom_cells {k n : Nat} (ha : σ.args = (FieldRoute.fieldAbi k n).args) :
    ∀ p ∈ (regionCoParts σ exportReg b t r.code r.res cert).cells,
      ∃ j, p = (renOf (regionCoParts σ exportReg b t r.code r.res cert).ps (argName j), n) := by
  intro p hp
  have hp' := regionCoParts_cells_sub σ exportReg b t r.code r.res cert none p hp
  unfold X86Backend.ImageAddrRouteW.cellArrsR at hp'
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp'
  obtain ⟨j, a, hj, hk, he⟩ := X86Backend.ImageStraightCells.cellArrs_mem hp0
  have hn := fieldAbi_kind ha hj
  rw [hk] at hn
  cases hn
  exact ⟨j, by rw [he]⟩

/-- The length of a slot array of slots all of length `n` is `n`. -/
theorem lenOf_of_forall {R : Slots} {n : Nat} (h : ∀ p ∈ R, p.2 = n) {B : String}
    (hb : isArrB R B = true) : lenOf R B = some n := by
  unfold isArrB at hb
  unfold lenOf
  cases hf : R.find? (·.1 == B) with
  | none => grind [List.find?_eq_none]
  | some p => grind [List.mem_of_find?_eq_some]

/-- **The pairs of the field domain send no name of the code other than a parameter name to a
    cell array.** -/
theorem fieldDom_isArrB_renOf (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert)
    {k n : Nat} (ha : σ.args = (FieldRoute.fieldAbi k n).args) {y : String} (hy : CodeName y)
    (hj : ∀ j, y ≠ argName j) :
    isArrB (regionCoParts σ exportReg b t r.code r.res cert).cells
      (renOf (regionCoParts σ exportReg b t r.code r.res cert).ps y) = false := by
  have hcl := fieldDom_cells (b := b) (t := t) (r := r) (cert := cert) ha
  obtain ⟨B, tbl, hc, rfl⟩ := cert_allocCertOf h hB
  have hya : isArgNameB σ y = false := by
    cases hb : isArgNameB σ y
    · rfl
    · simp only [isArgNameB, List.any_eq_true, beq_iff_eq] at hb
      obtain ⟨j, -, hj'⟩ := hb
      exact absurd hj'.symm (hj j)
  have hfix : renOf (regionCoParts σ exportReg b t r.code r.res (allocCertOf B tbl)).ps y = y := by
    change renOf (certArgs σ (allocCertOf B tbl)) y = y
    unfold certArgs
    rw [RegionAllocMapComplete.renOf_filter_allocCertOf]
    simp [hya]
  rw [hfix]
  cases hA : isArrB (regionCoParts σ exportReg b t r.code r.res (allocCertOf B tbl)).cells y
  · rfl
  exfalso
  unfold isArrB at hA
  obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp hA
  obtain ⟨j, rfl⟩ := hcl p hp
  simp only [beq_iff_eq] at hpe
  change renOf (certArgs σ (allocCertOf B tbl)) (argName j) = y at hpe
  unfold certArgs at hpe
  rw [RegionAllocMapComplete.renOf_filter_allocCertOf] at hpe
  split_ifs at hpe
  · exact (physName_allocName hc _).not_codeName (hpe ▸ hy)
  · exact hj j hpe.symm

/-! ## 4. The shape of one instruction -/

/-- **An operation with one register destination and plain sources.** -/
def Plain1 (i : LinstrRM) : Prop :=
  ∃ dst o ss, i.1 = .Lopn [.reg dst] o ss ∧ ∀ op ∈ ss, RegionExportForms.plainOpB op = true

/-- An operation at a register tag with one register destination and plain sources, none of
    whose names begins with `m`, has the shape of the fold class. -/
theorem posShape_regTag {R : Slots} {i : LinstrRM} (hm : NoMName i) (hp : Plain1 i)
    {c : Option Nat} (ht : i.2 = .reg c) : PosShape R i := by
  obtain ⟨w, tag⟩ := i
  obtain ⟨dst, o, ss, hw, hss⟩ := hp
  simp only at hw ht
  subst hw ht
  refine .inr (.inr (.inr (.inl ⟨rfl, rfl, fun y hy => hm y (dstNames_sub hy),
    fun y hy => ?_⟩)))
  simp only [readNames, List.mem_append, List.mem_flatMap, List.mem_filterMap] at hy
  rcases hy with ⟨op, hop, hy⟩ | ⟨op, hop, hy⟩
  · apply hm y
    change y ∈ ([LOperand.reg dst] ++ ss).flatMap opNames
    refine List.mem_flatMap.mpr ⟨op, List.mem_append_right _ hop, ?_⟩
    have := hss op hop
    cases op <;> simp_all [RegionExportForms.plainOpB, JasminLsemAddrCongr.srcNames, opNames]
  · cases op with
    | reg nn =>
        simp only [JasminLsemAddrCongr.cellBase, Option.map_eq_some_iff] at hy
        obtain ⟨p, hp, -⟩ := hy
        have hh := head_of_hasPrefix (X86Backend.ImageAddrCells.hasPrefix_of_cellParts hp)
          (c := 'm') (by decide)
        exact absurd hh (hm nn (List.mem_flatMap.mpr
          ⟨.reg nn, List.mem_append.mpr hop, by simp [opNames]⟩))
    | _ => simp [JasminLsemAddrCongr.cellBase] at hy

/-- The replacement `selfNopI` keeps an instruction or is a copy of a register onto itself. -/
theorem selfNopI_cases (i : LinstrRM) :
    selfNopI i = i ∨
      ∃ z, selfNopI i = (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none) := by
  unfold selfNopI
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl rfl

/-- A renaming of names keeps the form `Plain1`. -/
theorem plain1_renRM (f : String → String) {i : LinstrRM} (h : Plain1 i) :
    Plain1 (renRM f i) := by
  obtain ⟨dst, o, ss, hw, hss⟩ := h
  refine ⟨f dst, o, ss.map (renOperand f), by simp [renRM, hw, renLinstrR, renOperand], ?_⟩
  intro op hop
  obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hop
  have := hss o' ho'
  cases o' <;> simp_all [renOperand, RegionExportForms.plainOpB]

/-- An operation of the forms `FormB` at a register tag has the form `Plain1`. -/
theorem plain1_of_formB {i : LinstrRM} (hf : RegionExportForms.FormB i)
    (hl : JasminLsemMemLoop.IsLopn i) {c : Option Nat} (ht : i.2 = .reg c) : Plain1 i := by
  rcases hf with ⟨dst, m, ss, hw, hp⟩ | ⟨dst, b, x, sc, w, n, rfl⟩ |
      ⟨dst, b, x, sc, v, w, n, rfl⟩ | ⟨l, hw⟩ | ⟨l, hw | hw⟩
  · exact ⟨dst, m, ss, hw, hp⟩
  · cases ht
  · cases ht
  all_goals
    obtain ⟨d, o, s, he⟩ := hl
    rw [hw] at he
    cases he

/-- **The shape of the fold class of one instruction behind the prefix**: an instruction `c`
    of the access shape with tags, renamed at its array positions by `ρ` and at its names by
    `f`, or its replacement `selfNopI`, when its stores write their own base under `ρ`, `f` sends
    no scalar operand to a slot array, and every slot array has `n` words. -/
theorem posShape_of_coShape {R : Slots} {n : Nat} {f ρ : String → String} {c i : LinstrRM}
    (hco : CoShape n c) (hlo : JasminLsemMemLoop.IsLopn c) (hf : RegionExportForms.FormB c)
    (hown : ∀ d0 b0 x s v w m,
      c = (.Lopn [.reg d0] "STOREIDX" [.arrIdx b0 x s, .reg v], .store w m) → ρ d0 = ρ b0)
    (hsc : ∀ y ∈ instrNames c.1, (∀ j, y ≠ argName j) → isArrB R (f y) = false)
    (hlen : ∀ B, isArrB R B = true → lenOf R B = some n)
    (hi : i = renRM f (renArr ρ c) ∨ i = selfNopI (renRM f (renArr ρ c)))
    (hm : NoMName i) : PosShape R i := by
  have main : NoMName (renRM f (renArr ρ c)) → PosShape R (renRM f (renArr ρ c)) := by
    intro hm
    rcases hco with ⟨w', hw⟩ | ⟨d0, b0, x, s, rfl, hj⟩ | ⟨d0, b0, x, s, v, rfl, hj⟩
    · have hw' : (renArr ρ c).2 = .reg w' := by rw [renArr_snd, hw]
      exact posShape_regTag hm (plain1_renRM f (plain1_of_formB
        (RegionExportForms.formB_renArr ρ hf) (RegionExportDefInitSort.isLopn_renArr ρ hlo) hw'))
        hw'
    · refine .inl ⟨f d0, f (ρ b0), f x, s, n,
        by simp [renArr, renLoad, renRM, renLinstrR, renOperand],
        hsc d0 (by simp [instrNames, opNames]) (fun j => (hj j).1),
        hsc x (by simp [instrNames, opNames]) (fun j => (hj j).2), hlen _⟩
    · have hdb := hown d0 b0 x s v 64 n rfl
      refine .inr (.inl ⟨f (ρ b0), f x, s, f v, n,
        by simp [renArr, renStore, renRM, renLinstrR, renOperand, hdb],
        hsc x (by simp [instrNames, opNames]) (fun j => (hj j).1),
        hsc v (by simp [instrNames, opNames]) (fun j => (hj j).2), hlen _⟩)
  rcases selfNopI_cases (renRM f (renArr ρ c)) with hs | ⟨z, hs⟩
  · rw [hs, or_self] at hi
    subst hi
    exact main hm
  · rcases hi with rfl | rfl
    · exact main hm
    · rw [hs] at hm ⊢
      exact posShape_regTag hm ⟨z, _, _, rfl, by simp [RegionExportForms.plainOpB]⟩ rfl

/-! ## 5. The field domain -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseMulHiRM)

/-- **The hypothesis `hS` of `fieldDom_foldPos_addSub_of_posShape_noLoadStore`**: on the sum and
    the difference of the field domain, every instruction of the code behind the prefix of the
    parts has the shape `PosShape` of the fold class at the cell arrays of the parts. -/
theorem fieldDom_posShape (h : fieldDomB'' e σ = true) (hA : FieldAddSub e)
    (hB : FieldBody e σ fname b t r cert) :
    ∀ (k : Nat) (i : LinstrRM),
      ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      PosShape (regionCoParts σ exportReg b t r.code r.res cert).cells i := by
  have h' := fieldDomB_of_fieldDomB'' h
  obtain ⟨k0, n, -, ha, -⟩ := fieldDomB_layout h'
  have hs := fieldDom_sites_addSub h' hA hB
  have hNM := fieldDom_noMName h' hB hs
  have hτ := fieldDom_tau_nil h' hB
  have hcl := fieldDom_cells (b := b) (t := t) (r := r) (cert := cert) ha
  have hlen : ∀ B, isArrB (regionCoParts σ exportReg b t r.code r.res cert).cells B = true →
      lenOf (regionCoParts σ exportReg b t r.code r.res cert).cells B = some n :=
    fun B hb => lenOf_of_forall (fun p hp => by obtain ⟨j, rfl⟩ := hcl p hp; rfl) hb
  intro k i hk
  have hm := hNM k i hk
  set d := regionCoParts σ exportReg b t r.code r.res cert with hd
  set ρ := regionAliasN σ exportReg t r.res
    (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))
    with hρd
  have hmg : d.merged = (regionCoCode σ exportReg t r.code r.res
      (regionCopy σ exportReg t none r.code r.res)).map
      (fun c => renRM (renOf d.tau) (renRM (renOf d.ps) (renArr ρ c))) := by
    simp only [hd, regionCoParts, regionCoBody, List.map_map]
    rfl
  have hfu : d.fused = if d.sites then d.pre ++ fuseMulHiRM (d.nop.drop d.pre.length)
      else d.nop := rfl
  have hn : d.nop = selfNop d.pre.length (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length)
      (d.pre ++ d.merged) := rfl
  rw [hfu, hs, ite_eq_right Bool.false_ne_true, List.getElem?_drop, hn] at hk
  obtain ⟨i0, hi0, hii⟩ := getElem?_selfNop hk
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, hmg,
    List.getElem?_map] at hi0
  obtain ⟨c, hc0, rfl⟩ := Option.map_eq_some_iff.mp hi0
  have hc := List.mem_of_getElem? hc0
  have hnil : ∀ j : LinstrRM, renRM (renOf d.tau) j = j := by
    intro j
    rw [hτ]
    simpa using map_renRM_renOf_nil [j]
  rw [hnil] at hii
  exact posShape_of_coShape (fieldDom_coShape h' hB ha c hc) (fieldDom_isLopn_coCode h' hB c hc)
    (fieldDom_formB_coCode hB c hc) (fieldDom_storeOwn h' hB c hc)
    (fun y hy hj => fieldDom_isArrB_renOf h' hB ha (fieldDom_codeName_coCode h' hB c hc y hy) hj)
    hlen hii hm

/-- **The fold positions of the sum and the difference of the field domain** from the shape
    `LoadsChainK` and the absence of a load directly followed by a store in the exported code:
    `fieldDom_foldPos_addSub_of_posShape_noLoadStore` with its hypothesis `hS` proved by
    `fieldDom_posShape`. -/
theorem fieldDom_foldPos_addSub_noLoadStore (h : fieldDomB'' e σ = true)
    (hA : FieldAddSub e) (hB : FieldBody e σ fname b t r cert)
    (hL : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → LoadsChainK (fun _ => none) (legalizeRegion q'))
    (hC : ∀ (k : Nat) (i j : LinstrRM), r.code[k]? = some i → r.code[k + 1]? = some j →
      loadB i = true → storeB j = false) :
    ∀ k i, ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      FoldPos (regionCoParts σ exportReg b t r.code r.res cert).cells
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) k i :=
  fieldDom_foldPos_addSub_of_posShape_noLoadStore h hA hB hL hC (fieldDom_posShape h hA hB)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
