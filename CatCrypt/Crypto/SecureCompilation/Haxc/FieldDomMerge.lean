/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomResultName
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapLive
import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVComplete
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCoalesceShape

/-!
# The merge check on the field domain

The merge pairs `d.tau` of the parts of the region gate are the pairs of the allocation
certificate whose first name the reference reads at a block or call boundary before writing it
(`crossNames`) and that is no argument, hardware register, frame-slot or array name. The
reference of a member of the field domain, the prefix followed by the renamed code, is one
straight-line block without a call, so its cross names are the names it reads before it writes
them (`mem_regExposed_of_crossNames`). Under the certificate of definite assignment of the
tagged code, such a name is read by the prefix (a parameter register or an argument name) or
is the image under the pairs of an argument name; the image of an argument name under a pair
is written by the copies of the prefix, so it is read before that write only by the prefix.
No name is merged, and `regionMergeB` accepts at its first disjunct with no size bound on the
allocated body.

## Main results

* `exposed_of_mem_regExposed`: a name of `regExposed` is read at a position and not written
  before it.
* `mem_regExposed_of_crossNames`: on straight-line code without a call, a cross name is a name
  of `regExposed`.
* `exposed_cert`: under a certificate of definite assignment, a name read before it is written
  satisfies the entry predicate.
* `fieldDom_tau_nil`: the merge pairs of a member of the field domain are empty.
* `fieldDom_regMerge`: the stage `G8` on the field domain.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (cfgOf CFG)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInit (Cert Path WrittenOn img)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInitSort (tagA untag NoTag
  notTag_argName untag_of_not untag_tagA ArgS)
open CatCrypt.Crypto.Hax (HaxModule)

/-! ## 1. Names read before they are written -/

/-- The fold of `regExposed` from an accumulator: a name of the result is a name of the first
    component of the accumulator, or it is read at a position, is not in the second component,
    and is not written before that position. -/
theorem exposed_of_mem_foldl : ∀ (is : List LinstrR) (acc : List String × List String)
    {x : String},
    x ∈ (is.foldl (fun (acc : List String × List String) i =>
      (acc.1 ++ ((regReads i).filter fun x => !acc.2.contains x && !acc.1.contains x).eraseDups,
        acc.2 ++ regWrites i)) acc).1 →
    x ∈ acc.1 ∨ ∃ (j : Nat) (i : LinstrR), is[j]? = some i ∧ x ∈ regReads i ∧ x ∉ acc.2 ∧
      ∀ (m : Nat) (i' : LinstrR), m < j → is[m]? = some i' → x ∉ regWrites i'
  | [], acc, x, h => .inl h
  | i :: is, acc, x, h => by
      rw [List.foldl_cons] at h
      rcases exposed_of_mem_foldl is _ h with h1 | ⟨j, i', hj, hr, hw, hm⟩
      · rcases List.mem_append.mp h1 with h1 | h1
        · exact .inl h1
        · right
          obtain ⟨hr, hf⟩ := List.mem_filter.mp (List.mem_eraseDups.mp h1)
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
          refine ⟨0, i, rfl, hr, ?_, fun m _ hm => absurd hm (Nat.not_lt_zero _)⟩
          intro hx
          have hc := List.contains_iff_mem.mpr hx
          rw [hf.1] at hc
          cases hc
      · right
        simp only [List.mem_append, not_or] at hw
        refine ⟨j + 1, i', by simpa using hj, hr, hw.1, fun m i'' hmj hi'' => ?_⟩
        cases m with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi''
            subst hi''
            exact hw.2
        | succ m => exact hm m i'' (by omega) (by simpa using hi'')

/-- **A name of `regExposed` is read at a position and not written before it.** -/
theorem exposed_of_mem_regExposed {is : List LinstrR} {x : String} (h : x ∈ regExposed is) :
    ∃ (j : Nat) (i : LinstrR), is[j]? = some i ∧ x ∈ regReads i ∧
      ∀ (m : Nat) (i' : LinstrR), m < j → is[m]? = some i' → x ∉ regWrites i' := by
  rcases exposed_of_mem_foldl is ([], []) h with h1 | ⟨j, i, hj, hr, -, hm⟩
  · cases h1
  · exact ⟨j, i, hj, hr, hm⟩

/-- **On straight-line code without a call, a cross name is a name of `regExposed`**: the code
    is one block and one piece. -/
theorem mem_regExposed_of_crossNames {src : List LinstrRM} (hne : src ≠ [])
    (hl : ∀ i ∈ src, JasminLsemMemLoop.IsLopn i)
    (hsh : ∀ i ∈ src, LprogIsa.shadowCall? i.1 = none) {x : String}
    (hx : x ∈ crossNames src) : x ∈ regExposed (src.map Prod.fst) := by
  have hs : ∀ y ∈ src.map Prod.fst,
      X86Backend.OwnedLprogTV.straightR y = true := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    obtain ⟨d, o, s, he⟩ := hl i hi
    rw [he]
    rfl
  unfold crossNames at hx
  rw [X86Backend.OwnedLprogTV.cfgOf_straight (by simpa using hne) hs] at hx
  simp only [X86Backend.OwnedLprogTV.straightCFG, List.length_map] at hx
  have hx' := List.mem_eraseDups.mp hx
  simp only [List.mem_flatMap, List.mem_range] at hx'
  obtain ⟨k, hk, P, hP, hxP⟩ := hx'
  have hk0 : k = 0 := by simpa using hk
  subst hk0
  have hP' : P ∈ callPieces src := by
    simpa [CFG.blk] using hP
  rw [callPieces_of_noCall hsh, List.mem_singleton] at hP'
  subst hP'
  exact hxP

/-- On an operation with one register destination, the registers read are names it uses. -/
theorem regReads_sub_useNames {y o : String} {ss : List LOperand} {x : String}
    (h : x ∈ regReads (.Lopn [.reg y] o ss)) : x ∈ useNames (.Lopn [.reg y] o ss) := by
  simp only [regReads, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_flatMap] at h
  simp only [useNames, List.mem_flatMap]
  obtain ⟨op, hop, hx⟩ := h
  refine ⟨op, hop, ?_⟩
  cases op <;> simp_all [JasminLsemExportRewrites.opNames]

/-- On an operation with one register destination, the names it defines are the registers it
    writes. -/
theorem defNames_eq_regWrites {y o : String} {ss : List LOperand} :
    defNames (.Lopn [.reg y] o ss) = regWrites (.Lopn [.reg y] o ss) := by
  simp [defNames, regWrites, JasminLsemExportRewrites.opNames]

/-- **Under a certificate of definite assignment, a name read before it is written satisfies
    the entry predicate**, on straight-line code of operations with one register
    destination: it is read at a position, satisfies `E`, and is not defined before that
    position. -/
theorem exposed_cert {E : String → Prop} {src : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E src D) (hl : ∀ i ∈ src, JasminLsemMemLoop.IsLopn i)
    (hreg : ∀ i ∈ src, ∀ ds o ss, i.1 = .Lopn ds o ss → ∃ y, ds = [.reg y])
    {x : String} (hx : x ∈ regExposed (src.map Prod.fst)) :
    ∃ (j : Nat) (i : LinstrRM), src[j]? = some i ∧ x ∈ useNames i.1 ∧ E x ∧
      ∀ (m : Nat) (i' : LinstrRM), m < j → src[m]? = some i' → x ∉ defNames i'.1 := by
  obtain ⟨j, i0, hj, hr, hm⟩ := exposed_of_mem_regExposed hx
  rw [List.getElem?_map] at hj
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hj
  have hdef : ∀ (m : Nat) (i' : LinstrRM), src[m]? = some i' → x ∈ defNames i'.1 →
      x ∈ regWrites i'.1 := by
    intro m i' hi' hx'
    obtain ⟨d, o, s, he⟩ := hl i' (List.mem_of_getElem? hi')
    obtain ⟨y, rfl⟩ := hreg i' (List.mem_of_getElem? hi') d o s he
    rw [he, ← defNames_eq_regWrites]
    rw [he] at hx'
    exact hx'
  have hnd : ∀ (m : Nat) (i' : LinstrRM), m < j → src[m]? = some i' → x ∉ defNames i'.1 :=
    fun m i' hmj hi' hx' =>
    hm m i'.1 hmj (by rw [List.getElem?_map, hi']; rfl) (hdef m i' hi' hx')
  have hu : x ∈ useNames i.1 := by
    obtain ⟨d, o, s, he⟩ := hl i (List.mem_of_getElem? hi)
    obtain ⟨y, rfl⟩ := hreg i (List.mem_of_getElem? hi) d o s he
    rw [he] at hr ⊢
    exact regReads_sub_useNames hr
  refine ⟨j, i, hi, hu, ?_, hnd⟩
  rcases hC.use j i hi x hu with hD | hE
  · exfalso
    have hjl : j ≤ src.length := (List.getElem?_eq_some_iff.mp hi).1.le
    obtain ⟨ks, hp, hks⟩ := RegionAllocMapLive.path_prefix_of_isLopn (C := []) hl j hjl
    rw [List.append_nil] at hp
    obtain ⟨m, hmk, i', hi', hx'⟩ := hC.written hp x hD
    exact hnd m i' (hks m hmk) hi' hx'
  · exact hE

/-! ## 2. The gate -/

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- The merge check accepts parts without merge pairs. -/
theorem regionMergeB_of_tau_nil {d : CoParts} (h : d.tau = []) : regionMergeB d = true := by
  unfold regionMergeB
  rw [h]
  rfl

/-- The gate does not refuse at `regMerge` when the merge check accepts. -/
theorem regionCoStage_ne_regMerge {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h : regionMergeB (regionCoParts σ nm b t (calleeCodeT none code) res cert none) = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "regMerge" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **No merge pair** when every cross name of the reference is no name the merge keeps. -/
theorem tau_nil_of_crossNames {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {t : JasminTy} {code : List LinstrRM} {res : List LOperand} {cert : List (String × String)}
    (h : ∀ x ∈ crossNames ((regionCoParts σ nm body t code res cert none).pre
        ++ (regionCoParts σ nm body t code res cert none).ren),
      isArgNameB σ x = true ∨ isHwRegName x = true ∨ isFrameSlotName x = true) :
    (regionCoParts σ nm body t code res cert none).tau = [] := by
  show certMerge σ _ _ cert = []
  rw [RegionAllocMapComplete.certMerge_eq_filter, List.filter_eq_nil_iff]
  intro p _ hk
  simp only [RegionAllocMapComplete.certMergeKeep, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at hk
  obtain ⟨⟨⟨⟨⟨hX, ha⟩, hh⟩, hf⟩, -⟩, -⟩ := hk
  rcases h p.1 hX with h1 | h1 | h1
  · rw [h1] at ha; cases ha
  · rw [h1] at hh; cases hh
  · rw [h1] at hf; cases hf

/-! ## 3. The field domain -/

/-- A renaming of the register names keeps an operation one of no call, at one register
    destination. -/
theorem noShadow_renRM_of (f : String → String) {i : LinstrRM}
    (hn : RegionCoComplete.NoShadow i)
    (hs : ∀ ds o ss, i.1 = .Lopn ds o ss → ∃ x, ds = [.reg x]) :
    RegionCoComplete.NoShadow (JasminLsemExportTransfer.renRM f i) := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn ds o ss =>
      obtain ⟨x, rfl⟩ := hs ds o ss rfl
      unfold RegionCoComplete.NoShadow at hn ⊢
      simp only [JasminLsemExportTransfer.renRM, JasminLsemExportTransfer.renLinstrR,
        List.map_cons, List.map_nil, JasminLsemExportTransfer.renOperand] at hn ⊢
      simp only [LprogIsa.shadowCall?] at hn ⊢
      split at hn
      · cases hn
      · rename_i hc
        exact ite_eq_right_iff.mpr fun h' => absurd h' hc
  | _ => rfl

/-- A renaming of the register names keeps an operation. -/
theorem isLopn_renRM (f : String → String) {i : LinstrRM} (h : JasminLsemMemLoop.IsLopn i) :
    JasminLsemMemLoop.IsLopn (JasminLsemExportTransfer.renRM f i) := by
  obtain ⟨w, tag⟩ := i
  obtain ⟨ds, o, ss, he⟩ := h
  simp only at he
  subst he
  exact ⟨_, _, _, rfl⟩

/-- The names a copy reads are its source. -/
theorem useNames_movesOf {ps : List (String × String)} {i : LinstrRM} (hi : i ∈ movesOf ps)
    {x : String} (hx : x ∈ useNames i.1) : ∃ p ∈ ps, x = p.1 := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  refine ⟨p, hp, ?_⟩
  simpa [JasminLsemExportLower.movWire, useNames, JasminLsemExportRewrites.opNames] using hx

/-- The parameter registers of the field layout are hardware registers. -/
theorem hw_fieldArgReg (j : Nat) (hj : j < 3) :
    isHwRegName (exportReg (FieldRoute.fieldArgReg j)) = true := by
  interval_cases j <;> decide

/-- **The merge pairs of a member of the field domain are empty**: every cross name of the
    reference is an argument name, a hardware register name or a frame-slot name. -/
theorem fieldDom_tau_nil (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    (regionCoParts σ exportReg b t r.code r.res cert none).tau = [] := by
  obtain ⟨k, n, hk, ha, hres⟩ := fieldDomB_layout h
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, hr, hP, -, rfl⟩ := hB
  have hL := fieldDom_legalize_loadsChainS h hq hq'
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
  obtain ⟨⟨x0, hEC⟩, -⟩ := loadsChainS_export_class (fn := fname) hL le_rfl hr0
  have hl0 : ∀ i ∈ r0.code, JasminLsemMemLoop.IsLopn i := fun i hi => by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    exact (hEC k i hk).2.1
  have hsym : ∀ i ∈ r.code, RegionExportDefInit.symReads i = [] := fun i hi =>
    (hX.mnemDom hEx hcf i hi).1
  have hlen : ((nfCtx σ).map NarrowWords.wideTy).length ≤ σ.args.length := by
    rw [List.length_map]
    exact (RegionAllocMapDom.nfCtx_length σ).le
  have hRA : ∀ RA, σ.result = .reg RA → isHwRegName (exportReg RA) = true := by
    intro RA h'
    rw [hres] at h'
    cases h'
  have hArg : ∀ q ∈ σ.args, isHwRegName (exportReg q.reg) = true := by
    intro q hq
    rw [ha] at hq
    rcases hk with rfl | rfl <;>
      simp only [FieldRoute.fieldAbi, List.mem_map, List.mem_range] at hq <;>
      obtain ⟨j, hj, rfl⟩ := hq <;> exact hw_fieldArgReg j (by omega)
  have hns := hX.noShadow hEx hcf
  have hdef := hX.defsR hEx hcf
  have hco : ∀ i ∈ r.code, RegionAllocMapComplete.CoShape i := by
    rw [hr, regionWebsAt_none]
    exact forall_mem_regionWebs (P := RegionAllocMapComplete.CoShape)
      (fun σ i hi => RegionAllocMapComplete.coShape_renArr σ hi) _ r0 _ _
      (RegionAllocMapClose.exportR_coShape _ _ _ _ _ r0 hr0)
  have hlC : ∀ i ∈ regionCoCode σ exportReg (NarrowWords.wideTy t0) r.code r.res
      (regionCopy σ exportReg (NarrowWords.wideTy t0) none r.code r.res),
      JasminLsemMemLoop.IsLopn i := by
    rw [hr]
    exact isLopn_regionCoCode_webs hl0 σ exportReg _ _ _
  obtain ⟨D, hC⟩ := hX.cert_regionCoCodeS hEx hcf σ exportReg hsym hlen
  have hT := RegionAllocMapLive.noTag_regionCoCode fname _ hEx hcf hX σ exportReg
    (NarrowWords.wideTy t0) hRA hsym hlen
  set d := regionCoParts σ exportReg b (NarrowWords.wideTy t0) r.code r.res cert none with hd
  set C := regionCoCode σ exportReg (NarrowWords.wideTy t0) r.code r.res
    (regionCopy σ exportReg (NarrowWords.wideTy t0) none r.code r.res) with hCdef
  set ρ := canonMemrefName (regionAliasTab σ exportReg (NarrowWords.wideTy t0) none r.res C)
    with hρdef
  have hren : d.ren = (C.map (X86Backend.ImageCoalesceCfg.renArr ρ)).map
      (JasminLsemExportTransfer.renRM (renOf d.ps)) := rfl
  have hR := (RegionExportDefInitSort.Cert.renArrS hC hT ρ).renRM (renOf d.ps)
  rw [← hren] at hR
  have hpre : d.pre = X86Backend.ImageAddrRoute.argBind σ exportReg ++ movesOf d.ps := rfl
  have hPl : ∀ y ∈ d.pre, JasminLsemMemLoop.IsLopn y := by
    intro y hy
    rw [hpre] at hy
    rcases List.mem_append.mp hy with h' | h'
    · exact JasminLsemRenameLoop.movesOf_isLopn _ y h'
    · exact JasminLsemRenameLoop.movesOf_isLopn _ y h'
  let E' : String → Prop := fun x =>
    (∃ y, img (untag ρ) (ArgS σ.args.length) y ∧ x = renOf d.ps y)
      ∨ ∃ i ∈ d.pre, x ∈ useNames i.1
  obtain ⟨D', hC', -⟩ := (hR.monoE (E' := E') fun _ h' => .inl h').prefix d.pre hPl
    (fun y hy x hx => .inr ⟨y, hy, hx⟩)
  -- the facts of the reference
  have hcoC := RegionAllocMapClose.coShape_regionCoCode σ exportReg (NarrowWords.wideTy t0)
    r.res (regionCopy σ exportReg (NarrowWords.wideTy t0) none r.code r.res) hco
  have hnsC := RegionCoComplete.noShadow_regionCoCode σ exportReg (NarrowWords.wideTy t0)
    r.code r.res (regionCopy σ exportReg (NarrowWords.wideTy t0) none r.code r.res) hns
  have hlren : ∀ i ∈ d.ren, JasminLsemMemLoop.IsLopn i := by
    intro i hi
    rw [hren] at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hj
    exact isLopn_renRM _ (RegionExportDefInitSort.isLopn_renArr _ (hlC j' hj'))
  have hcoren := RegionAllocMapClose.coShape_regionCoParts_ren σ exportReg b
    (NarrowWords.wideTy t0) r.res cert none hco
  have hcopre : ∀ i ∈ d.pre, RegionAllocMapComplete.CoShape i := by
    intro i hi
    rw [hpre] at hi
    rcases List.mem_append.mp hi with h' | h'
    · exact RegionAllocMapComplete.coShape_movesOf _ i h'
    · exact RegionAllocMapComplete.coShape_movesOf _ i h'
  have hl : ∀ i ∈ d.pre ++ d.ren, JasminLsemMemLoop.IsLopn i := fun i hi =>
    (List.mem_append.mp hi).elim (hPl i) (hlren i)
  have hreg : ∀ i ∈ d.pre ++ d.ren, ∀ ds o ss, i.1 = .Lopn ds o ss → ∃ y, ds = [.reg y] :=
    fun i hi => (List.mem_append.mp hi).elim (fun h' => (hcopre i h').2.2)
      (fun h' => (hcoren i h').2.2)
  have hsh : ∀ i ∈ d.pre ++ d.ren, LprogIsa.shadowCall? i.1 = none := by
    intro i hi
    rcases List.mem_append.mp hi with h' | h'
    · rw [hpre] at h'
      rcases List.mem_append.mp h' with h'' | h'' <;>
      · obtain ⟨p, -, rfl⟩ := List.mem_map.mp h''
        rfl
    · rw [hren] at h'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h'
      obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hj
      exact noShadow_renRM_of _ (RegionCoComplete.noShadow_renArr _ (hnsC j' hj'))
        (RegionAllocMapComplete.coShape_renArr _ (hcoC j' hj')).2.2
  have hne : d.pre ++ d.ren ≠ [] := by
    intro h0
    have hpre0 := congrArg List.length h0
    rw [List.length_append, hpre, List.length_append] at hpre0
    have : (X86Backend.ImageAddrRoute.argBind σ exportReg).length = σ.args.length := by
      simp [X86Backend.ImageAddrRoute.argBind, X86Backend.ImageAddrRoute.argPairs, movesOf]
    rw [this, ha] at hpre0
    simp [FieldRoute.fieldAbi] at hpre0
  -- the names of the prefix
  have hpreN : ∀ i ∈ d.pre, ∀ x ∈ useNames i.1,
      isArgNameB σ x = true ∨ isHwRegName x = true ∨ isFrameSlotName x = true := by
    intro i hi x hx
    rw [hpre] at hi
    rcases List.mem_append.mp hi with h' | h'
    · obtain ⟨p, hp, rfl⟩ := useNames_movesOf h' hx
      obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp hp
      unfold X86Backend.ImageAddrRoute.srcOf
      split_ifs
      · right; right
        simp [JasminLsemAddrImage.slotOfReg, isFrameSlotName, RegionAllocMapComplete.hasPrefix_append]
      · right; left
        exact hArg _ (List.getElem_mem hj)
    · obtain ⟨p, hp, rfl⟩ := useNames_movesOf h' hx
      left
      exact (List.mem_filter.mp hp).2
  refine tau_nil_of_crossNames fun x hx => ?_
  have hxe := mem_regExposed_of_crossNames hne hl hsh hx
  obtain ⟨j, i, hi, hu, hE, hnd⟩ := exposed_cert hC' hl hreg hxe
  have hpreCase : (∃ i ∈ d.pre, x ∈ useNames i.1) →
      isArgNameB σ x = true ∨ isHwRegName x = true ∨ isFrameSlotName x = true := by
    rintro ⟨i', hi', hu'⟩
    exact hpreN i' hi' x hu'
  rcases hE with ⟨y, ⟨z, hz, rfl⟩, rfl⟩ | hE
  · obtain ⟨jj, hjj, hzj⟩ := hz
    have hjj' : jj < σ.args.length := hjj
    have hρ : ρ (argName jj) = argName jj := by
      refine RegionAllocMapLive.canonMemrefName_resAliasTab_of_not_def [] _ hnsC
        fun i hi hm => ?_
      rcases RegionAllocMapLive.regionCoCode_suffix σ exportReg _ r.code r.res _ hRA jj i hi
        with h' | ⟨h', -⟩
      · exact (hdef i h' _ hm).ne_argName jj rfl
      · exact h' hm
    have hu' : untag ρ z = argName jj := by
      rcases hzj with rfl | rfl
      · exact untag_of_not (notTag_argName jj)
      · rw [untag_tagA]
        exact hρ
    rw [hu'] at hpreCase hu hnd ⊢
    rcases renOf_exists d.ps (argName jj) with ⟨p, hp, hp1, hp2⟩ | ⟨-, hp2⟩
    · rw [hp2] at hpreCase hu hnd ⊢
      -- the copy of the pair `p` writes `p.2` in the prefix
      by_cases hjp : j < d.pre.length
      · apply hpreCase
        refine ⟨i, ?_, ?_⟩
        · rw [List.getElem?_append_left hjp] at hi
          exact List.mem_of_getElem? hi
        · exact hu
      · exfalso
        obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hp
        have hpos : (X86Backend.ImageAddrRoute.argBind σ exportReg).length + idx < j := by
          have := (List.getElem?_eq_some_iff.mp hidx).1
          have hlp : d.pre.length = (X86Backend.ImageAddrRoute.argBind σ exportReg).length
              + d.ps.length := by
            rw [hpre, List.length_append]
            simp [movesOf]
          omega
        refine hnd _ (JasminLsemExportLower.movWire p.2 p.1 "MOV:64", .reg none) hpos ?_ ?_
        · have hlt : (X86Backend.ImageAddrRoute.argBind σ exportReg).length + idx
              < d.pre.length := by
            have := (List.getElem?_eq_some_iff.mp hidx).1
            rw [hpre, List.length_append]
            simp only [movesOf, List.length_map]
            omega
          rw [List.getElem?_append_left hlt, hpre, List.getElem?_append_right (by omega),
            Nat.add_sub_cancel_left]
          simp [movesOf, hidx]
        · simp [JasminLsemExportLower.movWire, defNames, JasminLsemExportRewrites.opNames]
    · rw [hp2]
      left
      exact RegionAllocMapLive.isArgNameB_argName hjj'
  · exact hpreCase hE

/-- **Stage `G8` on the field domain**: the gate does not refuse at the merge check
    `regionMergeB`. -/
theorem fieldDom_regMerge (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regMerge" :=
  regionCoStage_ne_regMerge (regionMergeB_of_tau_nil (fieldDom_tau_nil h hB))

example (S : FieldDomStages) : type_of% @S.regMerge := @fieldDom_regMerge

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
