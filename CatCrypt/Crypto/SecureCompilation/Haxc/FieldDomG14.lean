/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomAssemble
import CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvStraightComplete
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCoalesceShape

/-!
# The index invariant check on the field domain from the shape of the reference

The stage `idxInvCheckB` (`G14`) of the region gate checks the reference `d.ref` of the parts
`regionCoParts` with the bounds-invariant check `idxInvCheckB` from the entry facts
`boundFacts σ exportReg` and the annotation `idxAnnot`. On a non-empty straight-line reference
whose symbolic run is inside the fragment and whose index obligations are immediates of width
`64` below the lengths of their arrays, the check accepts (`idxInvCheckB_straight`).

## Main results

* `regionCoStage_ne_idxInvCheckB`: the gate does not refuse at `idxInvCheckB` when the check
  accepts the reference.
* `fieldDom_idxInvCheckB_of_ref`: stage `G14` on the field domain from the shape of the
  reference.
* `ne_nil_of_ownedCheckMC`, `symRun_ne_unk_of_ownedCheckMC`: a body that `ownedCheckMC`
  accepts is non-empty, and a straight-line one runs symbolically inside the fragment.
* `lopn_fuseMulHiAux`, `isLopn_fuseMulHiRM`, `isLopn_selfNop`, `isLopn_regionCoParts_fused`:
  the high-product fusion, the removal of the array self-moves and the code `fused` of the
  parts keep a body of operations.
* `straightR_regionCoParts_ref`: the reference is straight-line when `fused` is built of
  operations and the cell fold of its code is straight-line.
* `fieldDom_ref_straightR`, `fieldDom_ref_ne_nil`, `fieldDom_symRun_ref_ne_unk`: the facts
  `hs`, `hne` and `hunk` of `fieldDom_idxInvCheckB_of_ref` on the field domain, the last two
  from stage `G13`, and `hs` and `hunk` under the hypothesis that the cell fold is
  straight-line.
* `fieldDom_idxInvCheckB_of_ownedCheckMC`: stage `G14` from stage `G13`, that hypothesis and
  the index obligations.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (idxInvCheckB idxAnnot boundFacts
  idxInvCheckB_straight)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (symRun SSt straightR)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (symObl)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- The gate does not refuse at `idxInvCheckB` when the bounds-invariant check accepts the
    reference of the parts. -/
theorem regionCoStage_ne_idxInvCheckB {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h : idxInvCheckB (boundFacts σ nm)
      (idxAnnot (boundFacts σ nm)
        (regionCoParts σ nm b t (calleeCodeT none code) res cert none).ref)
      (regionCoParts σ nm b t (calleeCodeT none code) res cert none).ref = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "idxInvCheckB" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **Stage `G14` on the field domain from the shape of the reference**: the gate does not
    refuse at `idxInvCheckB` when the reference of the parts is a non-empty straight-line body
    whose symbolic run is inside the fragment and whose index obligations are immediates of
    width `64` below the lengths of their arrays. -/
theorem fieldDom_idxInvCheckB_of_ref
    (hne : (regionCoParts σ exportReg b t r.code r.res cert).ref ≠ [])
    (hs : ∀ p ∈ (regionCoParts σ exportReg b t r.code r.res cert).ref, straightR p.1 = true)
    (hunk : symRun (regionCoParts σ exportReg b t r.code r.res cert).ref SSt.start ≠ .unk)
    (hidx : ∀ o ∈ symObl (regionCoParts σ exportReg b t r.code r.res cert).ref SSt.start,
      ∃ c, o.1 = .immW 64 c ∧ c < o.2) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "idxInvCheckB" :=
  regionCoStage_ne_idxInvCheckB (idxInvCheckB_straight σ exportReg hne hs hunk hidx)

/-! ## The reference is non-empty and inside the fragment once `ownedCheckMC` accepts it -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC
  ownedCheckMC_checked_at blockOkS_spec factCheck_entry startC_nil)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (symSubst_x86 cfgOf_straight
  bodyAt_straight straightCFG)

/-- **A body that `ownedCheckMC` accepts is non-empty.** -/
theorem ne_nil_of_ownedCheckMC {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' = true) : B ≠ [] := by
  obtain ⟨L, A, A', G, G', hC, -⟩ := ownedCheckMC_checked_at symSubst_x86 h
  have := hC.ne
  grind

/-- **A straight-line body that `ownedCheckMC` accepts runs symbolically inside the
    fragment**: its one block falls off the end, block `0` has no must-constant fact, and the
    block check `blockOkS` of a block that does not return refuses a run outside the
    fragment from the start state of its facts. -/
theorem symRun_ne_unk_of_ownedCheckMC {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' = true) (hs : ∀ p ∈ B, straightR p.1 = true) :
    symRun B SSt.start ≠ .unk := by
  obtain ⟨L, A, A', G, G', hC, -⟩ := ownedCheckMC_checked_at symSubst_x86 h
  have hG := cfgOf_straight (wl := B.map Prod.fst) hC.ne
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hs p hp)
  have hGG : G = straightCFG (B.map Prod.fst).length := by
    rw [hC.hG] at hG
    exact Option.some.inj hG
  subst hGG
  have hA0 : A 0 = [] := factCheck_entry hC.facts
  obtain ⟨-, hb⟩ := hC.blk 0 (by simp [straightCFG])
  have hterm : ((straightCFG (B.map Prod.fst).length).blk 0).term = .fall none := rfl
  rw [hterm, hA0, startC_nil] at hb
  rcases blockOkS_spec hb (by simp) with h1 | ⟨ss, gs, -, -, h1, -⟩
  · rw [bodyAt_straight] at h1
    simp [h1]
  · rw [bodyAt_straight] at h1
    simp [h1]

/-! ## The reference is built of operations -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (IsLopn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiAux squareSite)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseMulHiRM normMulx)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg (cellFoldLR)

/-- An operation is straight-line. -/
theorem straightR_of_isLopn {i : LinstrRM} (h : IsLopn i) : straightR i.1 = true := by
  obtain ⟨d, o, s, he⟩ := h
  rw [he]
  rfl

/-- **The high-product fusion of a body of operations is a body of operations**. -/
theorem lopn_fuseMulHiAux (saveRdx : Bool) :
    ∀ (c : Lcmd) (env : X86Backend.FuseMulHi.ScratchEnv) (pend : List (String × String)),
      (∀ x ∈ c, ∃ ds o ss, x.li_i = .Lopn ds o ss) →
      ∀ y ∈ fuseMulHiAux saveRdx env pend c, ∃ ds o ss, y.li_i = .Lopn ds o ss := by
  intro c
  induction c with
  | nil => intro env pend _ y hy; simp [fuseMulHiAux] at hy
  | cons i rest ih =>
    intro env pend hc y hy
    have hi := hc i List.mem_cons_self
    have hR : ∀ env' pend', ∀ y ∈ fuseMulHiAux saveRdx env' pend' rest,
        ∃ ds o ss, y.li_i = .Lopn ds o ss :=
      fun env' pend' => ih env' pend' fun x hx => hc x (List.mem_cons_of_mem _ hx)
    rw [fuseMulHiAux] at hy
    dsimp only at hy
    repeat' split at hy
    all_goals
      simp only [squareSite, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hy
      (try split_ifs at hy) <;> grind

/-- **The fusion `fuseMulHiRM` of a body of operations is a body of operations.** -/
theorem isLopn_fuseMulHiRM {c : List LinstrRM} (h : ∀ i ∈ c, IsLopn i) :
    ∀ i ∈ fuseMulHiRM c, IsLopn i := by
  intro i hi
  simp only [fuseMulHiRM, List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  have hb : ∀ x ∈ c.mapIdx (fun k i => (⟨k, i.1⟩ : Linstr)),
      ∃ ds o ss, x.li_i = .Lopn ds o ss := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hx
    exact h _ (List.getElem_mem hk)
  obtain ⟨ds, o, ss, he⟩ := lopn_fuseMulHiAux true _ [] [] hb j hj
  exact ⟨ds, _, ss, by rw [he]; rfl⟩

/-- **The removal of the array self-moves keeps a body of operations.** -/
theorem isLopn_selfNop (k0 : Nat) (Lr : Nat → List String) {B : List LinstrRM}
    (h : ∀ i ∈ B, IsLopn i) : ∀ i ∈ selfNop k0 Lr B, IsLopn i := by
  intro i hi
  simp only [selfNop, List.mem_mapIdx] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  have hB := h B[k] (List.getElem_mem hk)
  split
  · obtain ⟨d, o, s, he⟩ := hB
    unfold selfNopI
    split <;> grind [IsLopn]
  · exact hB

/-- The prefix of the parts, the argument moves and the moves of the pairs, is built of
    operations. -/
theorem isLopn_regionCoParts_pre {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} :
    ∀ i ∈ (regionCoParts σ nm b t code res cert).pre, IsLopn i := by
  intro i hi
  change i ∈ X86Backend.ImageAddrRoute.argBind σ nm
    ++ JasminLsemRenameLoop.movesOf (regionCoParts σ nm b t code res cert).ps at hi
  rcases List.mem_append.mp hi with hi | hi
  · exact JasminLsemRenameLoop.movesOf_isLopn _ i hi
  · exact JasminLsemRenameLoop.movesOf_isLopn _ i hi

/-- **The code `fused` of the parts is built of operations** when the coalesced body is. -/
theorem isLopn_regionCoParts_fused {nm : String → String} {code : List LinstrRM}
    {res : List LOperand}
    (hC : ∀ i ∈ regionCoBody σ nm t code res, IsLopn i) :
    ∀ i ∈ (regionCoParts σ nm b t code res cert).fused, IsLopn i := by
  have hpre := isLopn_regionCoParts_pre (σ := σ) (nm := nm) (b := b) (t := t) (code := code)
    (res := res) (cert := cert)
  have hren : ∀ i ∈ (regionCoParts σ nm b t code res cert).ren, IsLopn i := by
    intro i hi
    change i ∈ (regionCoBody σ nm t code res none).map (renRM _) at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact isLopn_renRM _ (hC j hj)
  have hmer : ∀ i ∈ (regionCoParts σ nm b t code res cert).merged, IsLopn i := by
    intro i hi
    change i ∈ (regionCoParts σ nm b t code res cert).ren.map (renRM _) at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact isLopn_renRM _ (hren j hj)
  have hnop : ∀ i ∈ (regionCoParts σ nm b t code res cert).nop, IsLopn i := by
    intro i hi
    change i ∈ selfNop _ _ ((regionCoParts σ nm b t code res cert).pre
      ++ (regionCoParts σ nm b t code res cert).merged) at hi
    exact isLopn_selfNop _ _ (fun j hj => (List.mem_append.mp hj).elim (hpre j) (hmer j)) i hi
  intro i hi
  change i ∈ (if (regionCoParts σ nm b t code res cert).sites then
      (regionCoParts σ nm b t code res cert).pre ++ fuseMulHiRM
        ((regionCoParts σ nm b t code res cert).nop.drop
          (regionCoParts σ nm b t code res cert).pre.length)
    else (regionCoParts σ nm b t code res cert).nop) at hi
  split at hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact hpre i hi
    · exact isLopn_fuseMulHiRM (fun j hj => hnop j (List.mem_of_mem_drop hj)) i hi
  · exact hnop i hi

/-- **The reference of the parts is straight-line** when the code `fused` is built of
    operations and every cell fold of its code behind the prefix is straight-line. -/
theorem straightR_regionCoParts_ref {nm : String → String} {code : List LinstrRM}
    {res : List LOperand}
    (hF : ∀ i ∈ (regionCoParts σ nm b t code res cert).fused, IsLopn i)
    (hcf : ∀ L, cellFoldLR (regionCoParts σ nm b t code res cert).cells []
        ((regionCoParts σ nm b t code res cert).fused.drop
          (regionCoParts σ nm b t code res cert).pre.length) = some L →
      ∀ p ∈ L, straightR p.1 = true) :
    ∀ p ∈ (regionCoParts σ nm b t code res cert).ref, straightR p.1 = true := by
  intro p hp
  change p ∈ (if (regionCoParts σ nm b t code res cert).cells.isEmpty then
      (regionCoParts σ nm b t code res cert).fused
    else (regionCoParts σ nm b t code res cert).pre
      ++ (cellFoldLR (regionCoParts σ nm b t code res cert).cells []
        ((regionCoParts σ nm b t code res cert).fused.drop
          (regionCoParts σ nm b t code res cert).pre.length)).getD
        ((regionCoParts σ nm b t code res cert).fused.drop
          (regionCoParts σ nm b t code res cert).pre.length)) at hp
  split at hp
  · exact straightR_of_isLopn (hF p hp)
  · rcases List.mem_append.mp hp with hp | hp
    · exact straightR_of_isLopn (isLopn_regionCoParts_pre p hp)
    · cases hc : cellFoldLR (regionCoParts σ nm b t code res cert).cells []
          ((regionCoParts σ nm b t code res cert).fused.drop
            (regionCoParts σ nm b t code res cert).pre.length) with
      | none =>
          rw [hc] at hp
          exact straightR_of_isLopn (hF p (List.mem_of_mem_drop hp))
      | some L =>
          rw [hc] at hp
          exact hcf L hc p hp

/-! ## The facts of stage `G14` on the field domain -/

/-- **On the field domain the coalesced body is built of operations**: the narrowed output of
    the chain is built of bindings only (`fieldLetsOnly`), its export and the webs with the
    result copies are operations, and the alias renaming keeps them. -/
theorem fieldDom_isLopn_regionCoBody (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    ∀ i ∈ regionCoBody σ exportReg t r.code r.res, IsLopn i := by
  have hF := fieldLetsOnly (fieldDomB_of_fieldDomB'' h)
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, rfl⟩ := hB
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact RegionExportDefInitSort.isLopn_renArr _ (isLopn_regionCoCode_webs
    (exportR_isLopn_of_letsOnlyB (legalizeRegion q') (hF t0 q q' hq hq') _ _ _ hr0) σ exportReg
      _ _ _ j hj)

/-- **Fact `hs` of stage `G14` on the field domain**: the reference of the parts is
    straight-line, when every cell fold of the code of `fused` behind the prefix is
    straight-line (`hcf`). -/
theorem fieldDom_ref_straightR (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert)
    (hcf : ∀ L, cellFoldLR (regionCoParts σ exportReg b t r.code r.res cert).cells []
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) = some L →
      ∀ p ∈ L, straightR p.1 = true) :
    ∀ p ∈ (regionCoParts σ exportReg b t r.code r.res cert).ref, straightR p.1 = true :=
  straightR_regionCoParts_ref (isLopn_regionCoParts_fused (fieldDom_isLopn_regionCoBody h hB))
    hcf

/-- **Fact `hne` of stage `G14`**: the reference of the parts is non-empty once the
    translation validation `ownedCheckMC` (stage `G13`) accepts it. -/
theorem fieldDom_ref_ne_nil {outs : List String} {B' : List LinstrRM}
    (hO : ownedCheckMC outs (regionCoParts σ exportReg b t r.code r.res cert).ref B' = true) :
    (regionCoParts σ exportReg b t r.code r.res cert).ref ≠ [] :=
  ne_nil_of_ownedCheckMC hO

/-- **Fact `hunk` of stage `G14` on the field domain**: the symbolic run of the reference of
    the parts is inside the fragment once `ownedCheckMC` (stage `G13`) accepts it, when every
    cell fold of the code of `fused` behind the prefix is straight-line (`hcf`). -/
theorem fieldDom_symRun_ref_ne_unk (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert)
    (hcf : ∀ L, cellFoldLR (regionCoParts σ exportReg b t r.code r.res cert).cells []
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) = some L →
      ∀ p ∈ L, straightR p.1 = true)
    {outs : List String} {B' : List LinstrRM}
    (hO : ownedCheckMC outs (regionCoParts σ exportReg b t r.code r.res cert).ref B' = true) :
    symRun (regionCoParts σ exportReg b t r.code r.res cert).ref SSt.start ≠ .unk :=
  symRun_ne_unk_of_ownedCheckMC hO (fieldDom_ref_straightR h hB hcf)

/-- **Stage `G14` on the field domain from stage `G13`**: the gate does not refuse at
    `idxInvCheckB` when `ownedCheckMC` accepts the reference, every cell fold of the code of
    `fused` behind the prefix is straight-line and the index obligations of the reference are
    immediates of width `64` below the lengths of their arrays. -/
theorem fieldDom_idxInvCheckB_of_ownedCheckMC (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert)
    (hcf : ∀ L, cellFoldLR (regionCoParts σ exportReg b t r.code r.res cert).cells []
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) = some L →
      ∀ p ∈ L, straightR p.1 = true)
    {outs : List String} {B' : List LinstrRM}
    (hO : ownedCheckMC outs (regionCoParts σ exportReg b t r.code r.res cert).ref B' = true)
    (hidx : ∀ o ∈ symObl (regionCoParts σ exportReg b t r.code r.res cert).ref SSt.start,
      ∃ c, o.1 = .immW 64 c ∧ c < o.2) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "idxInvCheckB" :=
  fieldDom_idxInvCheckB_of_ref (fieldDom_ref_ne_nil hO) (fieldDom_ref_straightR h hB hcf)
    (fieldDom_symRun_ref_ne_unk h hB hcf hO) hidx

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
