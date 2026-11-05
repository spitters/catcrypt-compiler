/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapPins
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg

@[expose] public section

set_option autoImplicit false

/-!
# The live ranges of the certified body at the merge check

This module proves the cover condition `hcov` of `mergeSep_regionLprogC_layout` for programs
without `call`: a name live after a write in the renamed code of the parts and the written
name, both kept by the merge, are live at one trace position of the certified body.

## Main results

* `regionCoBody_eq_allocCo`: the coalesced code of the parts is the coalesced code given to
  the allocation followed by the copy into the result register.
* `pLiveR_parts_allocCo`: a name in the liveness table of the parts is the image under the
  pairs of the renaming of a name live in the coalesced code given to the allocation.
* `regionAllocBody_split`: the certified body holds the code given to the allocation.
* `hcov_regionCoParts`: the cover condition of the merge.
* `resCopyOf_nfAbiNames`: at the export names `nfAbiNames`, the result copies of the
  allocation and of the parts agree when the result buffer has the length of the result.
* `canonicalizeMemrefThread_of_storeOwnBase`, `storeOwnBase_backEdgePins`: the store-thread
  canonicalization fixes the virtual body when every memory store of the coalesced code
  writes its own base.
* `storeOwnBase_renArr`: every memory store of the renamed code writes its own base when the
  stores agree with the roots of their bases (`StoreRootAgree`).
* `mergeSep_regionLprogC_complete`: the merge conditions at the export names `nfAbiNames`,
  with the cover condition, the copy agreement and the canonicalization premise proved.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapFinal

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findLabelMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames regDefs
  arrUse? jumpLabel? storeHit?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference (LiveAt)
open RegionAllocMapComplete RegionAllocMapPins RegionAllocMapAlign RegionAllocMapClose

/-! ## 1. Names the merge keeps -/

/-- On a body without `call`, the allocation sends no name the merge keeps to itself, when
    it names no vector register. -/
theorem allocName_ne_self_of_keep {B : Lcmd} {tbl : Array Nat} {σ : AbiLayout}
    {arrs X : List String} {y : String} (hcall : bodyHasCall B = false)
    (hvec : allocName B tbl y ∉ vectorRegNames) (hK : certMergeKeep σ arrs X y = true) :
    allocName B tbl y ≠ y := by
  intro he
  have hc : allocName B tbl y = physRegName (physMapTabled tbl (nameSlot B y)) := by
    simp [allocName, hcall]
  rcases physRegName_cases (physMapTabled tbl (nameSlot B y)) with h | h | h <;>
    rw [← hc, he] at h
  · simp [certMergeKeep, h] at hK
  · simp [certMergeKeep, h] at hK
  · rw [he] at hvec
    exact hvec h

/-- The pairs of the renaming fix a name the merge keeps, when the allocation names no vector
    register. -/
theorem eq_of_renOf_certArgs_keep_of_noVec {σ : AbiLayout} {B : Lcmd} {tbl : Array Nat}
    {arrs X : List String} {y0 y : String}
    (h : JasminLsemRenameLoop.renOf (certArgs σ (allocCertOf B tbl)) y0 = y)
    (hK : certMergeKeep σ arrs X y = true) (hvec : ∀ n, allocName B tbl n ∉ vectorRegNames) :
    y0 = y := by
  unfold certArgs at h
  rw [renOf_filter_allocCertOf B tbl _ (isArgNameB σ) y0] at h
  split_ifs at h with hc
  · exfalso
    subst h
    rcases allocName_cases B tbl y0 with h1 | h1 | h1 | h1
    · simp [certMergeKeep, h1] at hK
    · simp [certMergeKeep, h1] at hK
    · exact hvec y0 h1
    · rw [h1] at hK
      simp [certMergeKeep, hc.2] at hK
  · exact h

/-! ## 2. Touches -/

/-- A name a renamed instruction touches is the image of a name the instruction touches. -/
theorem touchW_renRM {τ : String → String} {i : LinstrRM} {y : String}
    (h : TouchW y (JasminLsemExportTransfer.renRM τ i).1) :
    ∃ y0, τ y0 = y ∧ TouchW y0 i.1 := by
  have hreg : ∀ o : LOperand, (JasminLsemExportTransfer.renOperand τ o).regName?
      = o.regName?.map τ := by
    intro o; cases o <;> rfl
  have hsrc : ∀ o : LOperand, (JasminLsemExportTransfer.renOperand τ o).srcRegNames
      = o.srcRegNames.map τ := by
    intro o; cases o <;> rfl
  obtain ⟨w, tag⟩ := i
  obtain ⟨ds, o, ss, hw, hy⟩ := h
  cases w with
  | Lopn ds0 o0 ss0 =>
    simp only [JasminLsemExportTransfer.renRM, JasminLsemExportTransfer.renLinstrR,
      LinstrR.Lopn.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    have e1 : (ds0.map (JasminLsemExportTransfer.renOperand τ)).head?.bind LOperand.regName?
        = (ds0.head?.bind LOperand.regName?).map τ := by
      cases ds0 <;> simp [hreg]
    have e2 : (ss0.map (JasminLsemExportTransfer.renOperand τ)).flatMap LOperand.srcRegNames
        = (ss0.flatMap LOperand.srcRegNames).map τ := by
      simp [List.flatMap_map, hsrc, List.map_flatMap]
    rw [e1, e2] at hy
    rcases hy with hy | hy
    · cases hd : ds0.head?.bind LOperand.regName? with
      | none => rw [hd] at hy; cases hy
      | some d =>
        rw [hd] at hy
        refine ⟨d, ?_, ds0, o0, ss0, rfl, Or.inl ?_⟩
        · simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hy
          exact hy.symm
        · simp [hd]
    · obtain ⟨y0, hy0, rfl⟩ := List.mem_map.mp hy
      exact ⟨y0, rfl, ds0, o0, ss0, rfl, Or.inr hy0⟩
  | _ => simp [JasminLsemExportTransfer.renRM, JasminLsemExportTransfer.renLinstrR] at hw

/-- An instruction of the shape `CoShape` touches every register name it writes. -/
theorem touchW_of_regDefs {i : LinstrRM} (hc : CoShape i) {x : String} (hx : x ∈ regDefs i) :
    TouchW x i.1 := by
  have hsub : x ∈ defNames i.1 := by
    unfold regDefs JasminLsemExportRegAlloc.memRegDefs at hx
    split_ifs at hx <;> simp_all
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn ds o ss =>
    obtain ⟨x', rfl⟩ := hc.2.2 ds o ss rfl
    simp [defNames, JasminLsemExportRewrites.opNames] at hsub
    subst hsub
    exact ⟨_, o, ss, rfl, Or.inl (by simp [LOperand.regName?])⟩
  | _ => simp [defNames] at hsub

/-- A name an instruction touches is touched at the same position of the code with its
    self-moves pinned. -/
theorem touchW_pinSelfMoves {C : List LinstrRM} {q : Nat} {j iP : LinstrRM} {y : String}
    (hj : C[q]? = some j) (hP : (pinSelfMoves C)[q]? = some iP) (ht : TouchW y j.1) :
    TouchW y iP.1 := by
  obtain ⟨j', hj', hc⟩ := getElem?_pinSelfMoves C q iP hP
  rw [hj] at hj'
  obtain rfl := Option.some.inj hj'
  rcases hc with rfl | ⟨t, a, z, sc, w, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact ht
  · obtain ⟨ds, o, ss, hw, hy⟩ := ht
    cases hw
    refine ⟨_, _, _, rfl, ?_⟩
    simp [LOperand.regName?, LOperand.srcRegNames] at hy ⊢
    grind
  · obtain ⟨ds, o, ss, hw, hy⟩ := ht
    cases hw
    refine ⟨_, _, _, rfl, ?_⟩
    simp [LOperand.regName?, LOperand.srcRegNames] at hy ⊢
    grind

/-- **A live name is touched before or live at the start**: in a code whose instructions at
    the positions `n + q`, `q < m`, have the shape `CoShape`, a name live at `n + m` is touched
    by one of these instructions or is live at `n`. -/
theorem touch_or_live {L : List LinstrRM} {outs : List String} {y : String} {n : Nat} :
    ∀ m, (∀ q, q < m → ∃ i, L[n + q]? = some i ∧ CoShape i) →
      PLiveR L outs (n + m) y →
      (∃ q i, q < m ∧ L[n + q]? = some i ∧ TouchW y i.1) ∨ PLiveR L outs n y := by
  intro m
  induction m with
  | zero => intro _ h; exact Or.inr (by simpa using h)
  | succ m ih =>
    intro hL h
    obtain ⟨i, hi, hc⟩ := hL m (by omega)
    by_cases ht : TouchW y i.1
    · exact Or.inl ⟨m, i, by omega, hi, ht⟩
    · have h' : PLiveR L outs (n + m) y :=
        .next hi hc.1 (fun ds o ss _ hd => ht (touchW_of_regDefs hc hd)) h
      rcases ih (fun q hq => hL q (by omega)) h' with ⟨q, i', hq, hi', ht'⟩ | h0
      · exact Or.inl ⟨q, i', by omega, hi', ht'⟩
      · exact Or.inr h0

/-! ## 3. The coalesced code of the allocation inside the coalesced code of the parts -/

/-- The code given to the allocation at one result type `t`, before its self-moves are pinned
    and its back-edge pins inserted: the exported code followed by the result copy
    `regionLprogCopy`, renamed at its array positions by its coalescing renaming at the result
    alias `resAliasOf none (some a.outArg) [t] res`. -/
def allocCo (a : AbiNames) (t : JasminTy) (code : List LinstrRM) (res : List LOperand) :
    List LinstrRM :=
  (code ++ regionLprogCopy a none [t] code res).map
    (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
      (resAliasTab [] (resAliasOf none (some a.outArg) [t] res)
        (code ++ regionLprogCopy a none [t] code res))))

/-- The names read after the code given to the allocation: the name of the returned operand
    at a register result type, and none otherwise. -/
def allocOuts (t : JasminTy) (res : List LOperand) : List String :=
  match t with
  | .reg _ => (res.map JasminLsemWidthN.operandName).head?.toList
  | _ => []

/-- **The coalesced code of the parts is the coalesced code of the allocation followed by the
    copy into the result register** (`regionCoBody_eq_allocCo`), when the output array of `a`
    is the result buffer of the layout, every result copy of the allocation is the result
    copy of the parts, and the result aliases of the parts and of the allocation agree. -/
theorem regionCoBody_eq_allocCo (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (a : AbiNames)
    (hout : ∀ D n, regionResBuf σ nm = some (D, n) → a.outArg = D)
    (hcopy : ∀ c, resCopyOf a.outArg t code res = some c →
      regionCopy σ nm t none code res = some c)
    (hrr : resAliasOf none ((regionResBuf σ nm).map Prod.fst) [t] res
      = resAliasOf none (some a.outArg) [t] res) :
    regionCoBody σ nm t code res none
      = allocCo a t code res ++ JasminLsemRenameLoop.movesOf (regionRet σ nm t res).toList := by
  rcases hc : regionCopy σ nm t none code res with _ | ⟨src, D, m⟩
  · have hn : resCopyOf a.outArg t code res = none := by
      cases h : resCopyOf a.outArg t code res with
      | none => rfl
      | some c => rw [hcopy c h] at hc; cases hc
    have hcp : regionLprogCopy a none [t] code res = [] := by simp [regionLprogCopy, hn]
    have hal0 : X86Backend.ImageStraightRoute.aliasTab []
        (code ++ JasminLsemRenameLoop.movesOf (regionRet σ nm t res).toList)
        = X86Backend.ImageStraightRoute.aliasTab [] code := by
      unfold X86Backend.ImageStraightRoute.aliasTab
      rw [List.foldl_append, foldl_aliasStepO_movesOf]
    have hal : regionAliasTab σ nm t none res
        (code ++ JasminLsemRenameLoop.movesOf (regionRet σ nm t res).toList)
        = resAliasTab [] (resAliasOf none (some a.outArg) [t] res) code := by
      unfold regionAliasTab
      rw [hrr]
      cases t with
      | stackArr w m => simp [regionRet, JasminLsemRenameLoop.movesOf, calleeOuts]
      | reg w => exact hal0
      | inlineInt => exact hal0
      | bool => exact hal0
    have hmv : (JasminLsemRenameLoop.movesOf (regionRet σ nm t res).toList).map
        (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
          (resAliasTab [] (resAliasOf none (some a.outArg) [t] res) code)))
        = JasminLsemRenameLoop.movesOf (regionRet σ nm t res).toList :=
      RegionExportDefInitSort.map_renArr_of_regTag (fun i hi =>
        ⟨by obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi; exact ⟨none, rfl⟩,
          RegionCoComplete.noShadow_movesOf _ i hi⟩)
    unfold regionCoBody allocCo
    rw [hc, hcp, List.append_nil]
    show (code ++ JasminLsemRenameLoop.movesOf (regionRet σ nm t res).toList).map
      (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
        (regionAliasTab σ nm t none res
          (code ++ JasminLsemRenameLoop.movesOf (regionRet σ nm t res).toList)))) = _
    rw [hal, List.map_append, hmv]
  · obtain ⟨-, ht, -, -, -, -⟩ := regionCopy_some hc
    have hc' := hc
    unfold regionCopy at hc'
    split at hc'
    · rename_i D' n hbuf
      obtain ⟨hc1, -⟩ := Option.filter_eq_some_iff.mp hc'
      have hD := resCopyOf_buf hc1
      subst hD
      have haD := hout _ _ hbuf
      have hcp : regionLprogCopy a none [t] code res = resCopyCode src D m := by
        simp [regionLprogCopy, haD, hc1]
      have hret : regionRet σ nm t res = none := by
        subst ht
        rfl
      have hcode : regionCoCode σ nm t code res (some (src, D, m))
          = code ++ regionLprogCopy a none [t] code res := by
        unfold regionCoCode
        rw [hret, hcp]
        simp [JasminLsemRenameLoop.movesOf]
      unfold regionCoBody allocCo regionAliasTab
      rw [hc, hcode, hret, hrr]
      simp [JasminLsemRenameLoop.movesOf, calleeOuts]
    · cases hc'

/-- **The liveness of the parts restricted to the coalesced code of the allocation**: a name in
    the liveness table of the parts at `d.pre.length + k`, `k ≤ (allocCo a t code res).length`,
    is the image under the pairs `d.ps` of a name live at `k` in `allocCo a t code res` read
    after as `allocOuts t res`. -/
theorem pLiveR_parts_allocCo (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (a : AbiNames) (hRA : ∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true)
    (hout : ∀ D n, regionResBuf σ nm = some (D, n) → a.outArg = D)
    (hcopy : ∀ c, resCopyOf a.outArg t code res = some c →
      regionCopy σ nm t none code res = some c)
    (hrr : resAliasOf none ((regionResBuf σ nm).map Prod.fst) [t] res
      = resAliasOf none (some a.outArg) [t] res)
    {k : Nat} {y : String} (hk : k ≤ (allocCo a t code res).length)
    (hy : y ∈ tabAt (regionCoParts σ nm body t code res cert none).live
      ((regionCoParts σ nm body t code res cert none).pre.length + k)) :
    ∃ y0, JasminLsemRenameLoop.renOf (regionCoParts σ nm body t code res cert none).ps y0 = y
      ∧ PLiveR (allocCo a t code res) (allocOuts t res) k y0 := by
  have hB := regionCoBody_eq_allocCo σ nm t code res a hout hcopy hrr
  have hpre : ∀ i ∈ (regionCoParts σ nm body t code res cert none).pre, ∀ l,
      JasminLsemLabeled.isLabel l i.1 = false := by
    intro i hi l
    rcases List.mem_append.mp hi with hi | hi
    · exact isLabel_movesOf _ i hi l
    · exact isLabel_movesOf _ i hi l
  have hlen : (allocCo a t code res).length
      ≤ (regionCoParts σ nm body t code res cert none).ren.length := by
    show _ ≤ ((regionCoBody σ nm t code res none).map _).length
    rw [List.length_map, hB]
    simp
  have h1 : PLiveR ((regionCoParts σ nm body t code res cert none).pre
      ++ (regionCoParts σ nm body t code res cert none).ren ++ [])
      (regionCoParts σ nm body t code res cert none).outs
      ((regionCoParts σ nm body t code res cert none).pre.length + k) y := by
    rw [List.append_nil]
    exact mem_liveRegTab_iff.mp hy
  have h2 := pLiveR_segment hpre (by simp) (by omega) h1
  rw [List.append_nil, ← List.length_append, liveRegTab_end] at h2
  obtain ⟨y0, hy0, h3⟩ := pLiveR_renRM (L := regionCoBody σ nm t code res none)
    (O0 := (regionCoParts σ nm body t code res cert none).outs)
    (fun z hz => ⟨z, hz, renOf_certArgs_of_hw
      (RegionAllocMapAlign.outs_hw_regionCoParts body t code res cert none hRA z hz)⟩) h2
  refine ⟨y0, hy0, ?_⟩
  rw [hB] at h3
  have h4 := pLiveR_segment (pre := []) (by simp) (isLabel_movesOf _) hk
    (by simpa using h3)
  refine pLiveR_mono_outs (fun z hz => ?_) h4
  have hz' := mem_liveRegTab_iff.mp hz
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hz'
  have houts : (regionCoParts σ nm body t code res cert none).outs
      = (regionRet σ nm t res).toList.map Prod.snd := rfl
  rw [houts] at hz'
  rcases hr : regionRet σ nm t res with _ | ⟨s, R⟩
  · rw [hr] at hz'
    have := pLiveR_end hz' (by simp [JasminLsemRenameLoop.movesOf])
    simp at this
  · obtain ⟨w, RA, op, rfl, -, rfl, rfl, rfl⟩ := regionRet_some hr
    rw [hr] at hz'
    have hmv : JasminLsemRenameLoop.movesOf [(JasminLsemWidthN.operandName op, nm RA)]
        = [(JasminLsemExportLower.movWire (nm RA) (JasminLsemWidthN.operandName op)
          "MOV:64", .reg none)] := rfl
    rw [Option.toList_some, hmv] at hz'
    obtain rfl := pLiveR_append_mov hz' rfl
    simp [allocOuts]

/-- **The certified body holds the code given to the allocation** (`regionAllocBody_split`),
    when `canonicalizeMemrefThread` leaves the virtual body unchanged: behind a prefix, one
    instruction per instruction, followed by a suffix, which at a register result type holds a
    liveness instruction reading the name of the returned operand. -/
theorem regionAllocBody_split (a : AbiNames) (nArgs : Nat) (ts : List JasminTy)
    (r : ExportRegions.Exported)
    (hr : ∀ i ∈ r.code, RegionAllocMapDom.ShapeB i.1)
    (hcanon : ∀ Pre : Lcmd,
      (Pre = [] ∨ Pre = arrBasePins a
        (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
          (resAliasOf none (some a.outArg) ts r.res))) →
      canonicalizeMemrefThread (Pre
        ++ ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
          (resAliasOf none (some a.outArg) ts r.res)).map
          (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]))
      = Pre ++ ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
          (resAliasOf none (some a.outArg) ts r.res)).map
          (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩])) :
    ∃ Pre Suf : Lcmd, regionAllocBody a nArgs ts r = Pre
        ++ (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
          (resAliasOf none (some a.outArg) ts r.res)).map
          (fun i => (⟨0, i.1⟩ : Linstr)) ++ Suf
      ∧ ∀ w, ts = [.reg w] → ∀ z ∈ (r.res.map JasminLsemWidthN.operandName).head?.toList,
          ∃ li ∈ Suf, TouchW z li.li_i := by
  have hacS : ∀ i ∈ regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
          (resAliasOf none (some a.outArg) ts r.res),
      RegionAllocMapDom.ShapeB i.1 := by
    refine RegionAllocMapDom.shapeB_regionAllocCode fun i hi => ?_
    rcases List.mem_append.mp hi with hi | hi
    · exact hr i hi
    · exact RegionAllocMapDom.shapeB_regionLprogCopy a ts r.code r.res i hi
  have hbody : ∀ i ∈ (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res)
      [] (resAliasOf none (some a.outArg) ts r.res)).map (fun i => (⟨0, i.1⟩ : Linstr))
        ++ [⟨0, .Lret⟩],
      RegionAllocMapDom.ShapeB i.li_i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact hacS j hj
    · rw [List.mem_singleton.mp hi]
      exact RegionAllocMapDom.shapeB_nonLopn (fun _ _ _ e => by cases e) (fun _ _ e => by cases e)
  unfold RegionAllocMapAlign.regionAllocBody
  dsimp only
  split
  · have hc0 := hcanon [] (Or.inl rfl)
    simp only [List.nil_append] at hc0
    rw [RegionAllocMapDom.expandCallShadows_of_shapeB hbody, hc0]
    refine ⟨[⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
      ((List.range nArgs).map fun j => (.reg (argName j) : LOperand))⟩],
      [⟨0, .Lret⟩] ++ resLivePin true [] (r.res.map JasminLsemWidthN.operandName),
      by simp only [List.append_assoc], fun w _ z hz => ?_⟩
    cases hh : (r.res.map JasminLsemWidthN.operandName).head? with
    | none => rw [hh] at hz; cases hz
    | some rn =>
      rw [hh, Option.toList_some, List.mem_singleton] at hz
      subst hz
      refine ⟨⟨0, .Lopn [.reg "%livepin"] "LIVEPIN" [.reg z]⟩, ?_,
        ⟨_, _, _, rfl, Or.inr (by simp [LOperand.srcRegNames])⟩⟩
      simp [resLivePin, hh]
  · rename_i hts
    refine ⟨(if a.abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range a.abiArgs.length).map fun j => (.reg (argName j) : LOperand))⟩]
       else []) ++ arrBasePins a
        (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
          (resAliasOf none (some a.outArg) ts r.res)),
      [⟨0, .Lret⟩], ?_, fun w hw => absurd hw (hts _)⟩
    rw [hcanon _ (Or.inr rfl)]
    simp only [List.append_assoc]

/-! ## 4. The cover condition -/

/-- **The cover condition of the merge** (`hcov_regionCoParts`): at the certificate of the
    certified body `B`, a name live after a write in the renamed code of the parts and the
    written name, distinct and both kept by the merge, are live at one trace position of `B`.
    The hypotheses are the result register condition, the agreement of the result copies of
    the parts and of the allocation (`hout`, `hcopy`), the shapes of the export, that
    `canonicalizeMemrefThread` leaves the virtual body unchanged, that `B` has no call and its
    allocation names no vector register, and that the merge fixes the names live at the first
    position of the renamed code. -/
theorem hcov_regionCoParts (σ : AbiLayout) (nm : String → String) (a : AbiNames) (nArgs : Nat)
    (r : ExportRegions.Exported) (body : Lcmd) (t : JasminTy)
    (hRA : ∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true)
    (hout : ∀ D n, regionResBuf σ nm = some (D, n) → a.outArg = D)
    (hcopy : ∀ c, resCopyOf a.outArg t r.code r.res = some c →
      regionCopy σ nm t none r.code r.res = some c)
    (hrr : resAliasOf none ((regionResBuf σ nm).map Prod.fst) [t] r.res
      = resAliasOf none (some a.outArg) [t] r.res)
    (hshape : ∀ i ∈ r.code, RegionAllocMapDom.ShapeB i.1) (hco : ∀ i ∈ r.code, CoShape i)
    (hcanon : ∀ Pre : Lcmd,
      (Pre = [] ∨ Pre = arrBasePins a
        (regionAllocCode (r.code ++ regionLprogCopy a none [t] r.code r.res) []
          (resAliasOf none (some a.outArg) [t] r.res))) →
      canonicalizeMemrefThread (Pre
        ++ ((regionAllocCode (r.code ++ regionLprogCopy a none [t] r.code r.res) []
          (resAliasOf none (some a.outArg) [t] r.res)).map
          (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]))
      = Pre ++ ((regionAllocCode (r.code ++ regionLprogCopy a none [t] r.code r.res) []
          (resAliasOf none (some a.outArg) [t] r.res)).map
          (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]))
    (hcall : bodyHasCall (regionAllocBody a nArgs [t] r) = false)
    (hvec : ∀ n, allocName (regionAllocBody a nArgs [t] r)
      (regionAllocTbl (regionAllocBody a nArgs [t] r)) n ∉ vectorRegNames)
    (hent : ∀ x ∈ tabAt (regionCoParts σ nm body t r.code r.res
        (allocCertOf (regionAllocBody a nArgs [t] r)
          (regionAllocTbl (regionAllocBody a nArgs [t] r))) none).live
        (regionCoParts σ nm body t r.code r.res
          (allocCertOf (regionAllocBody a nArgs [t] r)
            (regionAllocTbl (regionAllocBody a nArgs [t] r))) none).pre.length,
      JasminLsemRenameLoop.renOf (regionCoParts σ nm body t r.code r.res
        (allocCertOf (regionAllocBody a nArgs [t] r)
          (regionAllocTbl (regionAllocBody a nArgs [t] r))) none).tau x = x) :
    let B := regionAllocBody a nArgs [t] r
    let d := regionCoParts σ nm body t r.code r.res (allocCertOf B (regionAllocTbl B)) none
    let K : String → Prop := fun n => n ∈ allocCertNames B
      ∧ certMergeKeep σ d.arrs (crossNames (d.pre ++ d.ren)) n = true
    ∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
      ∀ y ∈ tabAt d.live (k + 1), ∀ x ∈ regDefs i, y ≠ x → K y → K x →
        ∃ pos, LiveAt (bodyTraceOut B []) pos (nameSlot B y)
          ∧ LiveAt (bodyTraceOut B []) pos (nameSlot B x) := by
  intro B d K k i hk hi y hy x hx hyx hKy hKx
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
  have hB := regionCoBody_eq_allocCo σ nm t r.code r.res a hout hcopy hrr
  have hren : d.ren = (allocCo a t r.code r.res
      ++ JasminLsemRenameLoop.movesOf (regionRet σ nm t r.res).toList).map
        (JasminLsemExportTransfer.renRM (JasminLsemRenameLoop.renOf d.ps)) := by
    show (regionCoBody σ nm t r.code r.res none).map _ = _
    rw [hB]
    rfl
  have hgetL : ∀ q, (d.pre ++ d.ren)[d.pre.length + q]? = d.ren[q]? := by
    intro q
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  rw [hgetL] at hi
  -- the names below
  have hvec' := hvec
  have hCo : ∀ j ∈ allocCo a t r.code r.res, CoShape j := by
    intro j hj
    obtain ⟨j0, hj0, rfl⟩ := List.mem_map.mp hj
    refine coShape_renArr _ ?_
    rcases List.mem_append.mp hj0 with hj0 | hj0
    · exact hco j0 hj0
    · have h' : j0 ∈ (match resCopyOf a.outArg t r.code r.res with
          | some (src, D, m) => resCopyCode src D m
          | none => []) := hj0
      split at h'
      · exact coShape_resCopyCode _ _ _ j0 h'
      · cases h'
  have hfix : ∀ y0 z, JasminLsemRenameLoop.renOf d.ps y0 = z → K z → y0 = z :=
    fun y0 z h hz => eq_of_renOf_certArgs_keep_of_noVec h hz.2 hvec
  by_cases hkl : k' < (allocCo a t r.code r.res).length
  swap
  · -- the copy into the result register writes a hardware register name
    exfalso
    rw [hren, List.getElem?_map, List.getElem?_append_right (by omega)] at hi
    obtain ⟨mv, hmv, rfl⟩ := Option.map_eq_some_iff.mp hi
    have hmvm := List.mem_of_getElem? hmv
    rw [RegionAllocMapLive.regDefs_renRM] at hx
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
    have hx0d : x0 ∈ defNames mv.1 := by
      unfold regDefs JasminLsemExportRegAlloc.memRegDefs at hx0
      split_ifs at hx0 <;> first | exact hx0 | simp at hx0
    obtain ⟨p, hp, rfl⟩ := RegionAllocMapLive.mem_defNames_movesOf hmvm hx0d
    obtain ⟨s, R⟩ := p
    cases hr : regionRet σ nm t r.res with
    | none => rw [hr] at hp; cases hp
    | some sr =>
      rw [hr, Option.toList_some, List.mem_singleton] at hp
      subst hp
      obtain ⟨w, RA, op, -, hRA', -, -, hR⟩ := regionRet_some hr
      have hhw : isHwRegName R = true := hR ▸ hRA RA hRA'
      have hKx2 := hKx.2
      have hfR : JasminLsemRenameLoop.renOf d.ps R = R := renOf_certArgs_of_hw hhw
      change certMergeKeep _ _ _ (JasminLsemRenameLoop.renOf d.ps R) = true at hKx2
      rw [hfR] at hKx2
      simp [certMergeKeep, hhw] at hKx2
  -- a position of the coalesced code of the allocation
  have hgetR : ∀ q, q < (allocCo a t r.code r.res).length →
      d.ren[q]? = ((allocCo a t r.code r.res)[q]?).map
        (JasminLsemExportTransfer.renRM (JasminLsemRenameLoop.renOf d.ps)) := by
    intro q hq
    rw [hren, List.getElem?_map, List.getElem?_append_left hq]
  set C := allocCo a t r.code r.res with hCdef
  set P := pinSelfMoves C with hPdef
  have hPlen : P.length = C.length := length_pinSelfMoves C
  obtain ⟨j, hj⟩ : ∃ j, C[k']? = some j := ⟨_, List.getElem?_eq_getElem hkl⟩
  obtain ⟨iP, hiP⟩ : ∃ iP, P[k']? = some iP :=
    ⟨_, List.getElem?_eq_getElem (by rw [hPlen]; exact hkl)⟩
  rw [hgetR k' hkl, hj] at hi
  obtain rfl := (Option.some.inj hi).symm
  -- the written name
  rw [RegionAllocMapLive.regDefs_renRM] at hx
  obtain ⟨x0, hx0, hx0e⟩ := List.mem_map.mp hx
  obtain rfl := hfix x0 x hx0e hKx
  have hxT : TouchW x0 iP.1 :=
    touchW_pinSelfMoves hj hiP (touchW_of_regDefs (hCo j (List.mem_of_getElem? hj)) hx0)
  -- the live name
  obtain ⟨y0, hy0, hyl⟩ := pLiveR_parts_allocCo σ nm body t r.code r.res _ a hRA hout hcopy hrr
    (k := k' + 1) (by rw [← hCdef]; omega) (by simpa [Nat.add_assoc] using hy)
  obtain rfl := hfix y0 y hy0 hKy
  have hyP : PLiveR P (allocOuts t r.res) (k' + 1) y0 :=
    pLiveR_pinSelfMoves (ne_livepin_of_keep hKy.2) hyl
  -- the certified body
  obtain ⟨Pre, Suf, hBeq, hSuf⟩ := regionAllocBody_split a nArgs [t] r hshape hcanon
  have hac : regionAllocCode (r.code ++ regionLprogCopy a none [t] r.code r.res) []
          (resAliasOf none (some a.outArg) [t] r.res)
      = backEdgePins P := rfl
  rw [hac] at hBeq
  have hBq : ∀ q, q < (backEdgePins P).length →
      B[Pre.length + q]? = ((backEdgePins P)[q]?).map fun j => (⟨0, j.1⟩ : Linstr) := by
    intro q hq
    show (regionAllocBody a nArgs [t] r)[Pre.length + q]? = _
    rw [hBeq, List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_append_left (by rw [List.length_map]; exact hq),
      List.getElem?_map]
  have hO : ∀ z ∈ allocOuts t r.res, ∃ q li, Pre.length + (backEdgePins P).length ≤ q
      ∧ B[q]? = some li ∧ TouchW z li.li_i := by
    intro z hz
    cases t with
    | reg w =>
      obtain ⟨li, hli, ht⟩ := hSuf w rfl z hz
      obtain ⟨s, hs⟩ := List.mem_iff_getElem?.mp hli
      refine ⟨Pre.length + (backEdgePins P).length + s, li, by omega, ?_, ht⟩
      show (regionAllocBody a nArgs _ r)[_]? = _
      rw [hBeq, List.getElem?_append_right (by simp)]
      simpa using hs
    | _ => simp [allocOuts] at hz
  -- the image of a position of `P` in `B`
  have hbe : backEdgePins P = insBefore (bePre (liveRegTab P []) P) P 0 := backEdgePins_eq_insBefore P
  have hlenB : (backEdgePins P).length = insPos (bePre (liveRegTab P []) P) P 0 P.length := by
    rw [hbe, insPos_length]
  have himg : ∀ q i', P[q]? = some i' →
      B[Pre.length + insPos (bePre (liveRegTab P []) P) P 0 q]?
        = some (⟨0, i'.1⟩ : Linstr) := by
    intro q i' hq
    have hql : q < P.length := (List.getElem?_eq_some_iff.mp hq).1
    have hlt : insPos (bePre (liveRegTab P []) P) P 0 q < (backEdgePins P).length := by
      rw [hlenB]; exact insPos_lt P 0 hql le_rfl
    rw [hBq _ hlt, hbe, getElem?_insPos P 0 q hql, hq]
    rfl
  -- a touch of the live name at or before the write
  have hyb : ∃ q li, q ≤ Pre.length + insPos (bePre (liveRegTab P []) P) P 0 k'
      ∧ B[q]? = some li ∧ TouchW y0 li.li_i := by
    have hL : ∀ q, q < k' + 1 →
        ∃ i, (d.pre ++ d.ren)[d.pre.length + q]? = some i ∧ CoShape i := by
      intro q hq
      obtain ⟨jq, hjq⟩ : ∃ jq, C[q]? = some jq := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      refine ⟨_, by rw [hgetL, hgetR q (by omega), hjq]; rfl,
        coShape_renRM _ (hCo jq (List.mem_of_getElem? hjq))⟩
    rcases touch_or_live (k' + 1) hL (mem_liveRegTab_iff.mp hy) with
      ⟨q, i', hq, hi', ht⟩ | h0
    · rw [hgetL, hgetR q (by omega)] at hi'
      obtain ⟨jq, hjq, rfl⟩ := Option.map_eq_some_iff.mp hi'
      obtain ⟨y1, hy1, ht1⟩ := touchW_renRM ht
      obtain rfl := hfix y1 y0 hy1 hKy
      obtain ⟨iq, hiq⟩ : ∃ iq, P[q]? = some iq :=
        ⟨_, List.getElem?_eq_getElem (by rw [hPlen]; omega)⟩
      refine ⟨_, _, ?_, himg q iq hiq, touchW_pinSelfMoves hjq hiq ht1⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hq) with hlt | rfl
      · have := insPos_lt (ins := bePre (liveRegTab P []) P) P 0 hlt (by rw [hPlen]; omega)
        omega
      · exact le_rfl
    · exfalso
      have hfx := hent y0 (mem_liveRegTab_iff.mpr h0)
      have hm : JasminLsemRenameLoop.renOf d.tau y0
          = if y0 ∈ allocCertNames B ∧ certMergeKeep σ d.arrs (crossNames (d.pre ++ d.ren)) y0
              = true then allocName B (regionAllocTbl B) y0 else y0 :=
        renOf_certMerge_allocCertOf _ _ _ _ _ _ y0
      change JasminLsemRenameLoop.renOf d.tau y0 = y0 at hfx
      rw [hm, ite_eq_left hKy] at hfx
      exact allocName_ne_self_of_keep hcall (hvec y0) hKy.2 hfx
  exact liveAt_hull hBq hiP hxT hyP hO hyb

/-! ## 5. The result copy and the store-thread canonicalization -/

/-- **The length of the result buffer from the result check**: when `regionResultB` passes at
    an array result type `.stackArr 64 m`, the result buffer of the layout has length `m`. -/
theorem regionResBuf_len_of_regionResultB {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {t : JasminTy} {res : List LOperand}
    (h : regionResultB σ nm body t res = true) :
    ∀ D n m, regionResBuf σ nm = some (D, n) → t = .stackArr 64 m → m = n := by
  intro D n m hb ht
  subst ht
  simp only [regionResultB] at h
  unfold regionResBuf at hb
  split at h
  · rename_i RA k op heq
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [heq] at hb
    simp only at hb
    rw [h.2] at hb
    cases hb
    rfl
  · cases h

/-- **The result copies of the allocation and of the parts agree at the export names of the
    direct route** (`resCopyOf_nfAbiNames`): under `layoutOkB σ`, when the result buffer of
    the layout has the length of every array result of type `t`, every result copy of the
    allocation into the output array of `nfAbiNames fname σ` is the result copy of the parts.
    Without a result buffer the output array is the empty name and the allocation copies
    nothing. -/
theorem resCopyOf_nfAbiNames {σ : AbiLayout} (hσ : RegionAllocMapDom.layoutOkB σ = true)
    (fname : String) {t : JasminTy} {code : List LinstrRM} {res : List LOperand}
    (hlen : ∀ D n m, regionResBuf σ exportReg = some (D, n) → t = .stackArr 64 m → m = n) :
    ∀ c, resCopyOf (nfAbiNames fname σ).outArg t code res = some c →
      regionCopy σ exportReg t none code res = some c := by
  intro c hc
  rcases hb : regionResBuf σ exportReg with _ | ⟨D, n⟩
  · exfalso
    have hO : (nfAbiNames fname σ).outArg = "" := by
      simp_all [RegionAllocMapDom.layoutOkB, nfAbiNames]
    rw [hO] at hc
    unfold resCopyOf at hc
    split at hc
    · simp at hc
    · cases hc
  · have hD := (RegionAllocMapDom.layoutOkB_sound hσ).2.2 fname D n hb
    rw [← hD] at hc
    have hc' := hc
    unfold resCopyOf at hc'
    split at hc'
    · rename_i _ _ w m op
      split_ifs at hc' with hif
      obtain rfl := (Option.some.inj hc').symm
      simp only [Bool.and_eq_true, beq_iff_eq] at hif
      have hmn := hlen D n m hb (by rw [hif.1.1.1.1])
      subst hmn
      unfold regionCopy
      rw [hb]
      simp [hc]
    · cases hc'

/-- An instruction wire whose memory stores write their own base: at
    `.Lopn [.reg dst] opn (.arrIdx base _ _ :: _)` with `isMemStore opn`, `dst = base`. -/
def StoreOwnBase (w : LinstrR) : Prop :=
  ∀ dst opn base x s rest, w = .Lopn [.reg dst] opn (.arrIdx base x s :: rest) →
    isMemStore opn = true → dst = base

/-- **The store-thread canonicalization fixes a body whose memory stores write their own
    base** (`canonicalizeMemrefThread_of_storeOwnBase`): the alias map `arrChainAlias` then
    sends every name to itself. -/
theorem canonicalizeMemrefThread_of_storeOwnBase {body : Lcmd}
    (h : ∀ i ∈ body, StoreOwnBase i.li_i) : canonicalizeMemrefThread body = body := by
  have key : ∀ (L : Lcmd) (l : List (String × String)), (∀ i ∈ L, StoreOwnBase i.li_i) →
      (∀ x, (l.lookup x).getD x = x) →
        ∀ x, ((L.foldl X86Backend.PhysAbiShape.aliasStepL l).lookup x).getD x = x := by
    intro L
    induction L with
    | nil => exact fun _ _ hl => hl
    | cons i L ih =>
      intro l hL hl
      rw [List.foldl_cons]
      refine ih _ (fun j hj => hL j (List.mem_cons_of_mem _ hj)) ?_
      have hn := hL i List.mem_cons_self
      unfold X86Backend.PhysAbiShape.aliasStepL
      split
      · next dst opn base _ _ rest heq =>
        split_ifs with hs
        · obtain rfl := hn dst opn base _ _ rest heq hs
          intro x
          by_cases hx : x = dst
          · subst hx
            simpa using hl x
          · have hb : (x == dst) = false := by simp [hx]
            simp only [List.lookup, hb]
            exact hl x
        · exact hl
      · exact hl
  have hid : ∀ x, canonMemrefName (arrChainAlias body) x = x := by
    intro x
    unfold canonMemrefName
    rw [(X86Backend.PhysAbiShape.arrChainAlias_spec body).1 x]
    exact key body [] h (fun y => by simp) x
  have hop : ∀ o, canonMemrefOperand (arrChainAlias body) o = o := by
    intro o
    cases o <;> simp [canonMemrefOperand, hid]
  unfold canonicalizeMemrefThread
  dsimp only
  split
  · rfl
  · conv_rhs => rw [← List.map_id body]
    refine List.map_congr_left fun i _ => ?_
    split
    · rename_i ds o ss heq
      obtain ⟨ii, w⟩ := i
      simp only at heq
      subst heq
      rw [show canonMemrefOperand (arrChainAlias body) = id from funext hop]
      simp
    · rfl

/-- A liveness instruction `LIVEPIN` is no memory store. -/
theorem storeOwnBase_livepin (ds ss : List LOperand) : StoreOwnBase (.Lopn ds "LIVEPIN" ss) := by
  intro dst opn base x s rest he hs
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨-, rfl, -⟩ := he
  exact absurd hs (by decide)

/-- **The pins keep the memory stores that write their own base**
    (`storeOwnBase_backEdgePins`): the self-move pins `pinSelfMoves` and the back-edge pins
    `backEdgePins` add only liveness instructions. -/
theorem storeOwnBase_backEdgePins {C : List LinstrRM} (h : ∀ i ∈ C, StoreOwnBase i.1) :
    ∀ i ∈ backEdgePins (pinSelfMoves C), StoreOwnBase i.1 := by
  have hP : ∀ i ∈ pinSelfMoves C, StoreOwnBase i.1 := by
    intro i hi
    rcases mem_pinSelfMoves hi with hi | ⟨t, a, z, sc, w, n, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
    · exact h i hi
    · exact storeOwnBase_livepin _ _
    · exact storeOwnBase_livepin _ _
  have hpin : ∀ T k l, ∀ i ∈ backEdgePin T (pinSelfMoves C) k l, StoreOwnBase i.1 := by
    intro T k l i hi
    unfold backEdgePin at hi
    dsimp only at hi
    split at hi
    · split at hi
      · rw [List.mem_singleton.mp hi]
        exact storeOwnBase_livepin _ _
      · cases hi
    · cases hi
  intro i hi
  obtain ⟨⟨j, k⟩, hjk, hi⟩ := List.mem_flatMap.mp hi
  have hj : j ∈ pinSelfMoves C := List.fst_mem_of_mem_zipIdx hjk
  dsimp only at hi
  split at hi
  all_goals first
    | (rw [List.mem_singleton.mp hi]; exact hP j hj)
    | (rcases List.mem_append.mp hi with hi | hi
       · exact hpin _ _ _ i hi
       · rw [List.mem_singleton.mp hi]; exact hP j hj)

/-- **The stores of the code `C` agree with the roots of their bases**: the coalescing
    renaming `canonMemrefName (aliasTab [] C)` sends the destination and the base of every
    store-tagged `STOREIDX` of `C` to one name. -/
def StoreRootAgree (C : List LinstrRM) : Prop :=
  ∀ i ∈ C, ∀ d b y s v w n,
    i = (.Lopn [.reg d] "STOREIDX" [.arrIdx b y s, .reg v], .store w n) →
      canonMemrefName (X86Backend.ImageStraightRoute.aliasTab [] C) d
        = canonMemrefName (X86Backend.ImageStraightRoute.aliasTab [] C) b

/-- **Names with one root under the coalescing renaming have one root at every result alias**:
    the renaming with the result alias is the coalescing renaming followed by the renaming of
    the result root to the result buffer. -/
theorem resAliasTab_congr {outs : List (String × Nat)} {C : List LinstrRM}
    (rr : Option (String × String)) {x y : String}
    (h : canonMemrefName (X86Backend.ImageStraightRoute.aliasTab outs C) x
      = canonMemrefName (X86Backend.ImageStraightRoute.aliasTab outs C) y) :
    canonMemrefName (resAliasTab outs rr C) x = canonMemrefName (resAliasTab outs rr C) y := by
  cases rr with
  | none => exact h
  | some p =>
    obtain ⟨D, src⟩ := p
    show X86Backend.ImageStraightRoute.chainAliasRes outs D src C x
      = X86Backend.ImageStraightRoute.chainAliasRes outs D src C y
    have h' : X86Backend.ImageStraightRoute.chainAliasO outs C x
        = X86Backend.ImageStraightRoute.chainAliasO outs C y := h
    rw [X86Backend.ImageStraightRoute.chainAliasRes_apply,
      X86Backend.ImageStraightRoute.chainAliasRes_apply, h']

/-- **The renamed code writes the base of every memory store** (`storeOwnBase_renArr`): when
    every instruction of `C` has the access form `AccCode` and the stores of `C` agree with the
    roots of their bases, every instruction of `C` renamed at its array positions by
    `canonMemrefName (resAliasTab [] rr C)`, at every result alias `rr`, has `StoreOwnBase`. -/
theorem storeOwnBase_renArr {C : List LinstrRM} {rr : Option (String × String)}
    (hC : ∀ i ∈ C, RegionPhysImgArg.AccCode i) (h : StoreRootAgree C) :
    ∀ i ∈ C.map (X86Backend.ImageCoalesceCfg.renArr
      (canonMemrefName (resAliasTab [] rr C))), StoreOwnBase i.1 := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  intro dst opn base x s rest he hs
  obtain ⟨ds, ss, hj1, hm⟩ := RegionPhysImgArg.renArr_lopn _ he
  by_cases hS : opn = "STOREIDX"
  · subst hS
    obtain ⟨d, b, y, v, w, n, rfl⟩ := (hC j hj).2.1 ds ss hj1
    have hr := resAliasTab_congr rr (h _ hj d b y 8 v w n rfl)
    simp only [X86Backend.ImageCoalesceCfg.renArr, X86Backend.ImageCoalesceCfg.renStore,
      ite_true, LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
      LOperand.arrIdx.injEq] at he
    obtain ⟨⟨rfl, -⟩, -, ⟨rfl, -, -⟩, -⟩ := he
    exact hr
  · by_cases hL : opn = "LOADIDX"
    · subst hL
      exact absurd hs (by decide)
    · obtain ⟨b0, hb0⟩ := hm base x s (by simp)
      exact absurd hb0 ((hC j hj).2.2 ds opn ss hj1 hL hS b0 x s)

/-! ## 6. The merge conditions for programs without `call` -/

/-- **The merge conditions at the allocation of a program without `call`, with the cover
    condition discharged** (`mergeSep_regionLprogC_complete`): `mergeSep_regionLprogC_layout`
    at the export names `nfAbiNames fname σ` of the direct route, the names `compileA` passes
    to `regionBack`, with its hypothesis `hcov` proved by `hcov_regionCoParts`. The
    hypotheses left are the result types `[t]`, the size bound, that the result buffer of the
    layout has the length of an array result of type `t` (`hlen`, a consequence of the result
    check `regionResultB` of the gate, `regionResBuf_len_of_regionResultB`), that the stores
    of the exported code followed by its result copy agree with the roots of their bases
    (`StoreRootAgree`; with the access form of the export at `64`-bit word arrays `arrW64B`,
    every memory store of the coalesced code `allocCo` then writes its own base, and
    `canonicalizeMemrefThread` leaves the virtual body unchanged), and the condition `hnp` on
    the names live after a write that are not plain. -/
theorem mergeSep_regionLprogC_complete (fname : String) (σ : AbiLayout) {ts : List JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) ts) (hp : regionExportableB p = true)
    (hcf : p.callFree = true) (hw : RegionPhysImgArg.arrW64B p = true) (ex : List String)
    {P : Lprog} {cert : List (String × String)}
    (hP : regionLprogC (nfAbiNames fname σ) p none ex = some (P, cert))
    (hσ : RegionAllocMapDom.layoutOkB σ = true) :
    ∃ r0 r, exportR (nfCtx σ).length fname p (nfCtx σ).length 0 x86Data = some r0
      ∧ r = regionWebsAt ex none r0
      ∧ ∀ (body : Lcmd) (t : JasminTy),
        let B := regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length ts r
        let d := regionCoParts σ exportReg body t r.code r.res cert none
        let K : String → Prop := fun n => n ∈ allocCertNames B
          ∧ certMergeKeep σ d.arrs (crossNames (d.pre ++ d.ren)) n = true
        ts = [t] →
        numGPRegs + (bodyNames B).length + 1 ≤ vectorBase →
        (∀ D n m, regionResBuf σ exportReg = some (D, n) → t = .stackArr 64 m → m = n) →
        StoreRootAgree (r.code ++ regionLprogCopy (nfAbiNames fname σ) none [t] r.code r.res) →
        (∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
          ∀ y ∈ tabAt d.live (k + 1), ∀ x ∈ regDefs i, ¬ PlainName y → K x →
            y ≠ allocName B (regionAllocTbl B) x) →
        MergeSep d := by
  obtain ⟨r, w, hr, rfl, hM⟩ :=
    RegionAllocMapDom.mergeSep_regionLprogC_layout (nfAbiNames fname σ) σ p hp hcf ex hP hσ
  obtain ⟨r1, w1, hr1, rfl, hcert⟩ := regionLprogC_cert (nfAbiNames fname σ) p ex hP
  obtain ⟨r2, w2, hr2, rfl, hE⟩ :=
    RegionAllocMapLive.entry_regionLprogC (nfAbiNames fname σ) p hp hcf ex hP
  obtain rfl : r1 = r := Option.some.inj (hr1.symm.trans hr)
  obtain rfl : r2 = r1 := Option.some.inj (hr2.symm.trans hr1)
  refine ⟨r2, _, hr, rfl, ?_⟩
  have hX : RegionExp fname p ex (regionWebsAt ex none r2) := regionExp_webs ex hr
  generalize regionWebsAt ex none r2 = r2 at hX hE hcert hM ⊢
  intro body t
  intro B d K hts hsize hlen hal hnp
  subst hts
  subst hcert
  have hst : ∀ i ∈ allocCo (nfAbiNames fname σ) t r2.code r2.res, StoreOwnBase i.1 :=
    storeOwnBase_renArr
      (hX.accCode_copy (nfAbiNames fname σ) hcf hw) hal
  obtain ⟨hRA, hArg, hbuf⟩ := RegionAllocMapDom.layoutOkB_sound hσ
  have hout : ∀ D n, regionResBuf σ exportReg = some (D, n) → (nfAbiNames fname σ).outArg = D :=
    fun D n h => (hbuf fname D n h).symm
  have hcopy := resCopyOf_nfAbiNames hσ fname (code := r2.code) (res := r2.res) hlen
  have hrr : resAliasOf none ((regionResBuf σ exportReg).map Prod.fst) [t] r2.res
      = resAliasOf none (some (nfAbiNames fname σ).outArg) [t] r2.res := by
    rcases hb : regionResBuf σ exportReg with _ | ⟨D, n⟩
    · have hO : (nfAbiNames fname σ).outArg = "" := by
        clear * - hσ hb
        simp_all [RegionAllocMapDom.layoutOkB, nfAbiNames]
      rw [hO]
      clear * -
      unfold resAliasOf
      split <;> split <;> simp_all
    · rw [hout D n hb]
      rfl
  have hcanon : ∀ Pre : Lcmd,
      (Pre = [] ∨ Pre = arrBasePins (nfAbiNames fname σ)
        (regionAllocCode (r2.code ++ regionLprogCopy (nfAbiNames fname σ) none [t] r2.code r2.res)
          [] (resAliasOf none (some (nfAbiNames fname σ).outArg) [t] r2.res))) →
      canonicalizeMemrefThread (Pre
        ++ ((regionAllocCode
            (r2.code ++ regionLprogCopy (nfAbiNames fname σ) none [t] r2.code r2.res) []
            (resAliasOf none (some (nfAbiNames fname σ).outArg) [t] r2.res)).map
          (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]))
      = Pre ++ ((regionAllocCode
            (r2.code ++ regionLprogCopy (nfAbiNames fname σ) none [t] r2.code r2.res) []
            (resAliasOf none (some (nfAbiNames fname σ).outArg) [t] r2.res)).map
          (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]) := by
    intro Pre hPre
    refine canonicalizeMemrefThread_of_storeOwnBase fun i hi => ?_
    rcases List.mem_append.mp hi with hi | hi
    · rcases hPre with rfl | rfl
      · cases hi
      · unfold arrBasePins at hi
        dsimp only at hi
        split at hi
        · cases hi
        · rw [List.mem_singleton.mp hi]
          exact storeOwnBase_livepin _ _
    · rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        exact storeOwnBase_backEdgePins hst j hj
      · rw [List.mem_singleton.mp hi]
        intro dst opn base x s rest he
        cases he
  have hshape : ∀ i ∈ r2.code, RegionAllocMapDom.ShapeB i.1 := fun i hi =>
    (hX.mnemDom hp hcf i hi).2.2
  have hco : ∀ i ∈ r2.code, CoShape i := by
    obtain ⟨r0, h0, he | he⟩ := hX <;> subst r2
    · exact exportR_coShape _ _ p _ _ r0 h0
    · exact forall_mem_regionWebs (P := CoShape) (fun σ i hi => coShape_renArr σ hi) ex r0 _ _
        (exportR_coShape _ _ p _ _ r0 h0)
  have hcall : bodyHasCall (regionAllocBody (nfAbiNames fname σ) (nfCtx σ).length [t] r2)
      = false :=
    RegionAllocMapDom.bodyHasCall_of_shapeB
      (RegionAllocMapDom.shapeB_regionAllocBody (nfAbiNames fname σ) _ [t] r2 hshape)
  have hvec :=
    ((RegionAllocMapDom.regionAllocBody_dom (nfAbiNames fname σ) p hp hcf hX).2.2 hsize).1
  have hent := hE σ exportReg body t hRA hArg (RegionAllocMapDom.nfCtx_length σ).le
    (fun n _ => hvec n) (fun i hi => (hX.mnemDom hp hcf i hi).1)
    (fun i hi => (hX.mnemDom hp hcf i hi).2.1) rfl
  exact hM body t rfl hsize
    (hcov_regionCoParts σ exportReg (nfAbiNames fname σ) (nfCtx σ).length r2 body t hRA hout
      hcopy hrr hshape hco
      hcanon hcall hvec hent) hnp

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapFinal
