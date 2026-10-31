/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoComplete
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCertInj
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulDepthTrace

@[expose] public section

set_option autoImplicit false

/-!
# Completeness of the register-merge check at an allocation certificate

The check `regionMergeB` of the region gate accepts a merge `τ` of register names when
`regCoB τ` holds at the register liveness table `liveRegTab` of the reference. This module
proves the parts of its completeness that do not depend on the shape of the export: the
introduction rule of `regCoB`, the closure of a stable liveness table, the instruction
check `regCoInstrB` from a closed table and the separation of names live across a write,
the merge of an allocation certificate as a case split on `allocName`, and the forward
half of the cover of the liveness table by the live ranges of the allocator.

## Main definitions

* `LiveRegStable`: one more backward pass changes no length of the table.
* `InstrCover`: the conditions on one instruction under which `regCoInstrB` holds.
* `PLiveR`: the names live at a position of a body, as an inductive predicate.
* `PlainName`: a name that is no hardware register, frame-slot or vector register name.
* `CoShape`: no unconditional jump, a conditional jump on the zero flag, one register
  destination per operation.

## Main results

* `regCoB_intro`, `regCoB_iff`: `regCoB` from its fixed-point conditions and the
  instruction check at every position, the converse of `regCoB_instr`.
* `liveRegNeed_sub_of_stable`, `liveRegTab_closed`: a stable table contains, at every
  position, the names `liveRegNeed` adds there.
* `liveRegTab_end`: the table at the end of the body is the list of names read after it.
* `regCoInstrB_of_cover`, `regCoB_of_cover`, `regionMergeB_of_cover`: the check of the merge
  from `InstrCover` at every position; `regionMergeB_regionCoParts_of_cover` at the parts of a
  region export.
* `renOf_filter_allocCertOf`, `renOf_certMerge_allocCertOf`: the merge of a filtered
  allocation certificate is `allocName` on the kept names and the identity elsewhere.
* `certMerge_ne_of_liveAt`: two names of the allocator input live at one trace position
  have distinct images under the merge, from `allocName_injOn_liveAt`.
* `pLiveR_of_liveRegTab`, `liveRegTab_of_pLiveR`: the entries of the table are live, and a
  stable table contains every live name.
* `liveRegTab_fwd`: a name in the table at a position is read at or after it, or is read by
  the `LIVEPIN` of `backEdgePins` before a back edge at or after it.
* `liveAt_of_touch_le_ge`: a slot touched before and after a trace position is live there.
* `agree_liveRegPass`, `liveRegTab_stable`: a pass treats each name separately, the positions
  of a name grow for at most `n` passes on a body of length `n`, and the fuel `n + 2` of
  `liveRegTab` reaches a stable table; `mem_liveRegTab_iff`: the table is the set of live
  names `PLiveR`.
* `allocName_cases`: the image of a name under the allocation is a hardware register name,
  a frame-slot name, a vector register name, or the name itself; `allocName_ne`,
  `renOf_certMerge_of_not`, `certMerge_ne_of_liveAt_plain`: the mixed cases of the merge for
  plain names.
* `condOKB_of_coShape`, `regDefs_length_le_of_coShape`, `coShape_renRM`, `coShape_renArr`,
  `regCallB_none`: the conditions of `InstrCover` that the shape `CoShape` of an instruction
  gives, the shape under the renamings, and the call check without a callee.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findLabelMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames regDefs arrDefs
  arrUse? jumpLabel?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (subB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference (LiveAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulDepthTrace
  (physFirstTouch_le_of_touched le_physLastTouch_of_touched)

/-! ## 1. The introduction rule of `regCoB` -/

/-- **The introduction rule of `regCoB`**: the merge `τ` passes `regCoB` on the code `C`
    behind the prefix `pre` when it fixes the empty name, the names of `AN` and the names
    live at the first position of `C`, and the instruction at every position of `C` passes
    `regCoInstrB`. -/
theorem regCoB_intro {τ : String → String} {pre C : List LinstrRM} {L : Nat → List String}
    {AN : List String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (h0 : τ "" = "") (hAN : ∀ a ∈ AN, τ a = a)
    (hent : ∀ r ∈ liveAt L (pre ++ C).length pre.length, τ r = r)
    (hI : ∀ (k : Nat) (i : LinstrRM), pre.length ≤ k → (pre ++ C)[k]? = some i →
      regCoInstrB τ (pre ++ C) (liveAt L (pre ++ C).length) AN k i aa ao = true) :
    regCoB τ pre C L AN aa ao = true := by
  simp only [regCoB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨h0, hAN⟩, hent⟩, fun j hj => ?_⟩
  have hj' : j < C.length := List.mem_range.mp hj
  rw [List.getElem?_eq_getElem hj']
  exact hI _ _ (Nat.le_add_right _ _) (by
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj'])

/-- **`regCoB` is its fixed-point conditions and the instruction check at every position**
    of the code behind the prefix. -/
theorem regCoB_iff {τ : String → String} {pre C : List LinstrRM} {L : Nat → List String}
    {AN : List String} {aa : String → Nat → Option Nat} {ao : String → Option Nat} :
    regCoB τ pre C L AN aa ao = true ↔
      τ "" = "" ∧ (∀ a ∈ AN, τ a = a) ∧ (∀ r ∈ liveAt L (pre ++ C).length pre.length, τ r = r)
        ∧ ∀ (k : Nat) (i : LinstrRM), pre.length ≤ k → (pre ++ C)[k]? = some i →
          regCoInstrB τ (pre ++ C) (liveAt L (pre ++ C).length) AN k i aa ao = true := by
  refine ⟨fun h => ⟨?_, ?_, ?_, fun k i hk hi => regCoB_instr h hk hi⟩,
    fun ⟨h0, hAN, hent, hI⟩ => regCoB_intro h0 hAN hent hI⟩
  all_goals
    simp only [regCoB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  · exact h.1.1.1
  · exact h.1.1.2
  · exact h.1.2

/-! ## 2. A stable liveness table is closed -/

/-- One update of the backward pass `liveRegPass` at the position `k`. -/
def regStep (body : List LinstrRM) (k : Nat) (A : Array (List String)) :
    Array (List String) :=
  match body[k]? with
  | some i => A.setIfInBounds k (A.getD k [] ++ liveRegNeed body A k i).eraseDups
  | none => A

theorem liveRegPass_eq (body : List LinstrRM) (A : Array (List String)) :
    liveRegPass body A = (List.range body.length).foldr (regStep body) A := rfl

theorem size_regStep {body : List LinstrRM} (k : Nat) (A : Array (List String)) :
    (regStep body k A).size = A.size := by
  unfold regStep
  split <;> simp

theorem getD_regStep_ne {body : List LinstrRM} {k j : Nat} (A : Array (List String))
    (h : j ≠ k) : (regStep body k A).getD j [] = A.getD j [] := by
  unfold regStep
  split
  · simp [Array.getD_eq_getD_getElem?, Ne.symm h]
  · rfl

theorem getD_regStep_self {body : List LinstrRM} {k : Nat} {i : LinstrRM}
    (A : Array (List String)) (hi : body[k]? = some i) (hk : k < A.size) :
    (regStep body k A).getD k [] = (A.getD k [] ++ liveRegNeed body A k i).eraseDups := by
  simp [regStep, hi, Array.getD_eq_getD_getElem?, hk]

theorem useNames_sub_liveRegNeed (body : List LinstrRM) (A : Array (List String)) (k : Nat)
    (i : LinstrRM) : ∀ x ∈ useNames i.1, x ∈ liveRegNeed body A k i := by
  intro x hx
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn ds o ss => simp only [liveRegNeed]; exact List.mem_append_left _ hx
  | _ => simp [useNames] at hx

/-- The shape of the tables of the passes: `n + 1` lists for a body of length `n`, lists
    without duplicates before the end. -/
def RegInv (body : List LinstrRM) (A : Array (List String)) : Prop :=
  A.size = body.length + 1 ∧ ∀ j < body.length, (A.getD j []).Nodup

theorem regInv_regStep {body : List LinstrRM} (k : Nat) {A : Array (List String)}
    (hA : RegInv body A) : RegInv body (regStep body k A) := by
  refine ⟨by rw [size_regStep, hA.1], fun j hj => ?_⟩
  by_cases hjk : j = k
  · subst hjk
    rcases hi : body[j]? with _ | i
    · simpa [regStep, hi] using hA.2 j hj
    rw [getD_regStep_self _ hi (by rw [hA.1]; omega)]
    exact RegionCoComplete.nodup_eraseDups _
  · rw [getD_regStep_ne _ hjk]
    exact hA.2 j hj

theorem regInv_foldr {body : List LinstrRM} :
    ∀ (l : List Nat) {A : Array (List String)}, RegInv body A →
      RegInv body (l.foldr (regStep body) A)
  | [], _, h => h
  | k :: l, _, h => regInv_regStep k (regInv_foldr l h)

theorem prefix_regStep {body : List LinstrRM} (k : Nat) {A : Array (List String)}
    (hA : RegInv body A) (j : Nat) : A.getD j [] <+: (regStep body k A).getD j [] := by
  by_cases hjk : j = k
  · subst hjk
    rcases hi : body[j]? with _ | i
    · simp [regStep, hi]
    have hk : j < body.length := (List.getElem?_eq_some_iff.mp hi).1
    rw [getD_regStep_self _ hi (by rw [hA.1]; omega)]
    exact RegionCoComplete.prefix_eraseDups_append (hA.2 j hk) _
  · rw [getD_regStep_ne _ hjk]

theorem prefix_foldr_regStep {body : List LinstrRM} :
    ∀ (l : List Nat) {A : Array (List String)}, RegInv body A → ∀ j,
      A.getD j [] <+: (l.foldr (regStep body) A).getD j []
  | [], _, _, _ => List.prefix_refl _
  | k :: l, _, hA, j => (prefix_foldr_regStep l hA j).trans
      (prefix_regStep k (regInv_foldr l hA) j)

/-- **The table is stable**: one more backward pass `liveRegPass` changes the length of no
    list of the table. -/
def LiveRegStable (body : List LinstrRM) (A : Array (List String)) : Prop :=
  ∀ j, ((liveRegPass body A).getD j []).length = (A.getD j []).length

theorem liveRegNeed_congr {body : List LinstrRM} {A B : Array (List String)} (k : Nat)
    (i : LinstrRM) (h : ∀ j, B.getD j [] = A.getD j []) :
    liveRegNeed body B k i = liveRegNeed body A k i := by
  unfold liveRegNeed
  simp only [h]

/-- **A pass that changes no length leaves a closed table**: every name `liveRegNeed` adds
    at a position is already in the table there. -/
theorem liveRegNeed_sub_of_stable {body : List LinstrRM} {A : Array (List String)}
    (hA : RegInv body A) (hst : LiveRegStable body A) {k : Nat} {i : LinstrRM}
    (hi : body[k]? = some i) : ∀ r ∈ liveRegNeed body A k i, r ∈ A.getD k [] := by
  intro r hr
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hi).1
  have hsplit : List.range body.length = (List.range k ++ [k])
      ++ List.map (fun x => k + 1 + x) (List.range (body.length - (k + 1))) := by
    rw [← List.range_succ, ← List.range_add]
    congr 1
    omega
  obtain ⟨R, hR⟩ : ∃ R : List Nat,
      R = List.map (fun x => k + 1 + x) (List.range (body.length - (k + 1))) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = R.foldr (regStep body) A := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = regStep body k B := ⟨_, rfl⟩
  have hF : liveRegPass body A = (List.range k).foldr (regStep body) C := by
    rw [liveRegPass_eq, hsplit, ← hR, List.foldr_append, List.foldr_append, ← hB, hC]
    rfl
  have hBinv : RegInv body B := hB ▸ regInv_foldr R hA
  have hCinv : RegInv body C := hC ▸ regInv_regStep k hBinv
  have hAB : ∀ j, A.getD j [] <+: B.getD j [] := hB ▸ prefix_foldr_regStep R hA
  have hBC : ∀ j, B.getD j [] <+: C.getD j [] := hC ▸ prefix_regStep k hBinv
  have hCF : ∀ j, C.getD j [] <+: (liveRegPass body A).getD j [] :=
    hF ▸ prefix_foldr_regStep (List.range k) hCinv
  have hlen : ∀ j, (C.getD j []).length = (A.getD j []).length := fun j => by
    have h1 := (hAB j).length_le
    have h2 := (hBC j).length_le
    have h3 := (hCF j).length_le
    have h4 := hst j
    omega
  have hBA : ∀ j, B.getD j [] = A.getD j [] := fun j => by
    have h1 := (hAB j).length_le
    have h2 := (hBC j).length_le
    exact ((hAB j).eq_of_length (by have := hlen j; omega)).symm
  have hCA : C.getD k [] = A.getD k [] :=
    ((hAB k).trans (hBC k)).eq_of_length (hlen k).symm |>.symm
  rw [← hCA, hC, getD_regStep_self _ hi (by rw [hBinv.1]; omega), List.mem_eraseDups,
    liveRegNeed_congr k i hBA]
  exact List.mem_append_right _ hr

theorem regInv_liveRegIter {body : List LinstrRM} :
    ∀ (fuel : Nat) {A : Array (List String)}, RegInv body A →
      RegInv body (liveRegIter body fuel A)
  | 0, _, h => h
  | fuel + 1, A, h => by
    simp only [liveRegIter]
    split
    · exact h
    · exact regInv_liveRegIter fuel (by rw [liveRegPass_eq]; exact regInv_foldr _ h)

theorem getD_init (body : List LinstrRM) (outs : List String) (j : Nat) :
    ((Array.replicate (body.length + 1) ([] : List String)).setIfInBounds body.length
      outs).getD j [] = if j = body.length then outs else [] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    Array.getElem?_replicate, Array.size_replicate]
  by_cases h : j = body.length
  · simp [h]
  · simp only [Ne.symm h, ↓reduceIte, h]
    split <;> rfl

theorem regInv_liveRegTab (body : List LinstrRM) (outs : List String) :
    RegInv body (liveRegTab body outs) :=
  regInv_liveRegIter _ ⟨by simp, fun j hj => by
    rw [getD_init, ite_eq_right (Nat.ne_of_lt hj)]
    exact List.nodup_nil⟩

/-- **A stable liveness table is closed**: at every position of the body, the names
    `liveRegNeed` adds lie in the table `liveRegTab` there. -/
theorem liveRegTab_closed {body : List LinstrRM} {outs : List String}
    (hst : LiveRegStable body (liveRegTab body outs)) {k : Nat} {i : LinstrRM}
    (hi : body[k]? = some i) :
    ∀ r ∈ liveRegNeed body (liveRegTab body outs) k i, r ∈ tabAt (liveRegTab body outs) k :=
  liveRegNeed_sub_of_stable (regInv_liveRegTab body outs) hst hi

theorem getD_foldr_regStep_of_not_mem {body : List LinstrRM} {j : Nat} :
    ∀ (l : List Nat) (A : Array (List String)), j ∉ l →
      (l.foldr (regStep body) A).getD j [] = A.getD j []
  | [], _, _ => rfl
  | k :: l, A, h => by
    rw [List.foldr_cons, getD_regStep_ne _ (fun e => h (by rw [e]; exact List.mem_cons_self))]
    exact getD_foldr_regStep_of_not_mem l A (fun hm => h (List.mem_cons_of_mem _ hm))

theorem getD_liveRegIter_end {body : List LinstrRM} :
    ∀ (fuel : Nat) (A : Array (List String)),
      (liveRegIter body fuel A).getD body.length [] = A.getD body.length []
  | 0, _ => rfl
  | fuel + 1, A => by
    simp only [liveRegIter]
    split
    · rfl
    · rw [getD_liveRegIter_end fuel, liveRegPass_eq,
        getD_foldr_regStep_of_not_mem _ _ (by simp)]

/-- **The table at the end of the body is the list of names read after it.** -/
theorem liveRegTab_end (body : List LinstrRM) (outs : List String) :
    tabAt (liveRegTab body outs) body.length = outs := by
  unfold tabAt liveRegTab
  rw [getD_liveRegIter_end, getD_init, ite_eq_left rfl]

/-! ## 3. The instruction check from a closed table -/

/-- **The conditions on the instruction `i` at position `k` of `B`** under which it passes
    `regCoInstrB` for the merge `τ` at the table `T`: the names `liveRegNeed` adds at `k` lie
    in the table there; `i` passes `condOKB` and is no unconditional jump; the array it
    reads and the arrays it writes are in `AN`; it writes at most one register name, none
    with the empty image; a name live after `k` and a name `i` writes have distinct images
    unless they are equal; and `i` passes the call check `regCallB`. -/
structure InstrCover (τ : String → String) (B : List LinstrRM) (T : Array (List String))
    (AN : List String) (aa : String → Nat → Option Nat) (ao : String → Option Nat)
    (k : Nat) (i : LinstrRM) : Prop where
  /-- The table is closed at the position. -/
  need : ∀ r ∈ liveRegNeed B T k i, r ∈ tabAt T k
  /-- The condition check. -/
  cond : condOKB i = true
  /-- No unconditional jump. -/
  noGoto : ∀ x, i.1 ≠ .Lgoto x
  /-- The array read is in `AN`. -/
  arrUse : ∀ a ∈ (arrUse? i).toList, a ∈ AN
  /-- The arrays written are in `AN`. -/
  arrDef : ∀ a ∈ arrDefs i, a ∈ AN
  /-- At most one register name is written. -/
  defs : (regDefs i).length ≤ 1
  /-- No written name has the empty image. -/
  defNe : ∀ d ∈ regDefs i, τ d ≠ ""
  /-- A name live after the position and a written name have distinct images. -/
  inj : ∀ r ∈ tabAt T (k + 1), ∀ d ∈ regDefs i, r ≠ d → τ r ≠ τ d
  /-- The call check. -/
  call : regCallB τ (liveAt (tabAt T) B.length) AN aa ao k i = true

theorem mem_liveRegNeed_succ {B : List LinstrRM} {T : Array (List String)} {k : Nat}
    {i : LinstrRM} (hg : ∀ x, i.1 ≠ .Lgoto x) {r : String} (hr : r ∈ T.getD (k + 1) [])
    (hd : r ∉ regDefs i) : r ∈ liveRegNeed B T k i := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lgoto x => exact absurd rfl (hg x)
  | Lcond c l => exact List.mem_append_left _ hr
  | Lopn ds o ss =>
    refine List.mem_append_right _ (List.mem_filter.mpr ⟨hr, ?_⟩)
    simpa using hd
  | _ => exact hr

theorem mem_liveRegNeed_jump {B : List LinstrRM} {T : Array (List String)} {k : Nat}
    {i : LinstrRM} {l : LLabel} (hj : jumpLabel? i.1 = some l) {pc : Nat}
    (hpc : findLabelMem l B = some pc) {r : String} (hr : r ∈ T.getD (pc + 1) []) :
    r ∈ liveRegNeed B T k i := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lgoto x =>
    obtain ⟨f, l'⟩ := x
    simp only [jumpLabel?, Option.some.injEq] at hj
    subst hj
    simp only [liveRegNeed, hpc]
    exact hr
  | Lcond c l' =>
    simp only [jumpLabel?, Option.some.injEq] at hj
    subst hj
    simp only [liveRegNeed, hpc]
    exact List.mem_append_right _ hr
  | _ => simp [jumpLabel?] at hj

theorem arrDefs_length_le (i : LinstrRM) : (arrDefs i).length ≤ 1 := by
  unfold arrDefs JasminLsemExportRegAlloc.memArrDefs
  split_ifs
  · simp
  · simp
  · cases JasminLsemExportRegAlloc.storeHit? i <;> simp

/-- **The instruction check from a closed table**: an instruction with `InstrCover` passes
    `regCoInstrB` for a merge that fixes the empty name and the names of `AN`. -/
theorem regCoInstrB_of_cover {τ : String → String} {B : List LinstrRM}
    {T : Array (List String)} {AN : List String} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} {k : Nat} {i : LinstrRM} (hi : B[k]? = some i)
    (h0 : τ "" = "") (hAN : ∀ a ∈ AN, τ a = a) (hc : InstrCover τ B T AN aa ao k i) :
    regCoInstrB τ B (liveAt (tabAt T) B.length) AN k i aa ao = true := by
  have hk : k < B.length := (List.getElem?_eq_some_iff.mp hi).1
  have hLk : liveAt (tabAt T) B.length k = "" :: tabAt T k := by
    simp only [liveAt, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hLk1 : liveAt (tabAt T) B.length (k + 1) = "" :: tabAt T (k + 1) := by
    simp only [liveAt, Nat.min_eq_left hk]
  simp only [regCoInstrB, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨hc.cond, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hc.call⟩
  · -- the names read are live before the instruction
    refine List.all_eq_true.mpr fun x hx => ?_
    rw [hLk]
    simpa using Or.inr (hc.need x (useNames_sub_liveRegNeed _ _ _ _ x hx))
  · -- the array read is in `AN`
    have hu := hc.arrUse
    cases h : arrUse? i with
    | none => rfl
    | some a =>
      rw [h] at hu
      simpa using hu a (by simp)
  · -- the register write condition
    refine List.all_eq_true.mpr fun r hr => ?_
    rw [hLk1] at hr
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.contains_eq_mem,
      decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq, hLk]
    rcases List.mem_cons.mp hr with rfl | hr
    · right
      refine ⟨List.mem_cons_self, fun d hd => ?_⟩
      rw [h0]
      exact fun h => hc.defNe d hd h.symm
    · by_cases hd : r ∈ regDefs i
      · left
        match hds : regDefs i, hc.defs with
        | [], _ => simp [hds] at hd
        | [d], _ =>
          rw [hds] at hd
          rw [List.mem_singleton.mp hd]
        | _ :: _ :: _, h => simp at h
      · right
        refine ⟨List.mem_cons_of_mem _ (hc.need r (mem_liveRegNeed_succ hc.noGoto hr hd)),
          fun d hd' => hc.inj r hr d hd' (fun e => hd (e ▸ hd'))⟩
  · -- the array write condition
    refine List.all_eq_true.mpr fun a ha => ?_
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.contains_eq_mem,
      decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq]
    by_cases he : arrDefs i = [a]
    · exact Or.inl he
    · refine Or.inr ⟨ha, fun d hd => ?_⟩
      rw [hAN a ha, hAN d (hc.arrDef d hd)]
      intro had
      subst had
      apply he
      match hds : arrDefs i, arrDefs_length_le i with
      | [], _ => simp [hds] at hd
      | [d'], _ =>
        rw [hds] at hd
        rw [List.mem_singleton.mp hd]
      | _ :: _ :: _, h => simp at h
  · -- the jump condition
    split
    · rename_i l hl
      split
      · rename_i pc hpc
        refine List.all_eq_true.mpr fun x hx => ?_
        have hpcl : pc < B.length := by
          have := JasminLsemLabeled.findLabel_lt_length l (B.map Prod.fst) pc hpc
          simpa using this
        simp only [liveAt, Nat.min_eq_left hpcl, List.mem_cons] at hx
        rw [hLk]
        rcases hx with rfl | hx
        · simp
        · simpa using Or.inr (hc.need x (mem_liveRegNeed_jump hl hpc hx))
      · rfl
    · rfl

/-- **The check of a merge from a closed table**: the merge `τ` passes `regCoB` on the code
    `C` behind the prefix `pre` at the table `T` when it fixes the empty name, the names of
    `AN` and the names of the table at the first position of `C`, and every instruction of
    `C` satisfies `InstrCover`. -/
theorem regCoB_of_cover {τ : String → String} {pre C : List LinstrRM}
    {T : Array (List String)} {AN : List String} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (h0 : τ "" = "") (hAN : ∀ a ∈ AN, τ a = a)
    (hent : ∀ r ∈ tabAt T pre.length, τ r = r)
    (hI : ∀ (k : Nat) (i : LinstrRM), pre.length ≤ k → (pre ++ C)[k]? = some i →
      InstrCover τ (pre ++ C) T AN aa ao k i) :
    regCoB τ pre C (tabAt T) AN aa ao = true := by
  refine regCoB_intro h0 hAN (fun r hr => ?_) fun k i hk hi =>
    regCoInstrB_of_cover hi h0 hAN (hI k i hk hi)
  simp only [liveAt, List.length_append, Nat.min_eq_left (Nat.le_add_right _ _),
    List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact h0
  · exact hent r hr

/-- **The check of the register merge from a closed table**: the parts `d` pass
    `regionMergeB` when the merge `renOf d.tau` satisfies the hypotheses of
    `regCoB_of_cover` at the table `d.live` and the array names `d.arrs`, and each target of
    the result copy is in the table at the end and fixed by the merge. -/
theorem regionMergeB_of_cover {d : CoParts} (h0 : renOf d.tau "" = "")
    (hAN : ∀ a ∈ d.arrs, renOf d.tau a = a)
    (hent : ∀ r ∈ tabAt d.live d.pre.length, renOf d.tau r = r)
    (hI : ∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
      InstrCover (renOf d.tau) (d.pre ++ d.ren) d.live d.arrs d.aa d.ao k i)
    (hout : ∀ y ∈ d.outs,
      y ∈ tabAt d.live (d.pre ++ d.ren).length ∧ renOf d.tau y = y) :
    regionMergeB d = true := by
  unfold regionMergeB
  rw [regCoB_of_cover h0 hAN hent hI]
  simp only [Bool.true_and, Bool.or_eq_true, beq_iff_eq]
  refine Or.inr (List.all_eq_true.mpr fun y hy => ?_)
  simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, beq_iff_eq]
  exact hout y hy

/-- **The check of the register merge of a region export from a closed table**: the parts
    `regionCoParts` at the certificate `cert` pass `regionMergeB` when the merge `renOf tau`
    fixes the empty name, the array names and the names of the table at the first position
    of the renamed code, every instruction of that code satisfies `InstrCover` at the table
    `live`, and the merge fixes the targets of the result copy. The targets are in the table
    at the end by `liveRegTab_end`. -/
theorem regionMergeB_regionCoParts_of_cover (σ : AbiLayout) (nm : String → String)
    (body : Lcmd) (t : JasminTy) (code : List LinstrRM) (res : List LOperand)
    (cert : List (String × String)) (callee : Option CalleeData)
    (h0 : renOf (regionCoParts σ nm body t code res cert callee).tau "" = "")
    (hAN : ∀ a ∈ (regionCoParts σ nm body t code res cert callee).arrs,
      renOf (regionCoParts σ nm body t code res cert callee).tau a = a)
    (hent : ∀ r ∈ tabAt (regionCoParts σ nm body t code res cert callee).live
        (regionCoParts σ nm body t code res cert callee).pre.length,
      renOf (regionCoParts σ nm body t code res cert callee).tau r = r)
    (hI : ∀ (k : Nat) (i : LinstrRM), (regionCoParts σ nm body t code res cert callee).pre.length ≤ k →
      ((regionCoParts σ nm body t code res cert callee).pre
        ++ (regionCoParts σ nm body t code res cert callee).ren)[k]? = some i →
      InstrCover (renOf (regionCoParts σ nm body t code res cert callee).tau)
        ((regionCoParts σ nm body t code res cert callee).pre
          ++ (regionCoParts σ nm body t code res cert callee).ren)
        (regionCoParts σ nm body t code res cert callee).live
        (regionCoParts σ nm body t code res cert callee).arrs
        (regionCoParts σ nm body t code res cert callee).aa
        (regionCoParts σ nm body t code res cert callee).ao k i)
    (hfix : ∀ y ∈ (regionCoParts σ nm body t code res cert callee).outs,
      renOf (regionCoParts σ nm body t code res cert callee).tau y = y) :
    regionMergeB (regionCoParts σ nm body t code res cert callee) = true :=
  regionMergeB_of_cover h0 hAN hent hI fun y hy => ⟨by
    show y ∈ tabAt (liveRegTab ((regionCoParts σ nm body t code res cert callee).pre
        ++ (regionCoParts σ nm body t code res cert callee).ren)
        (regionCoParts σ nm body t code res cert callee).outs)
      ((regionCoParts σ nm body t code res cert callee).pre
        ++ (regionCoParts σ nm body t code res cert callee).ren).length
    rw [liveRegTab_end]
    exact hy, hfix y hy⟩

/-! ## 4. The merge of an allocation certificate -/

/-- **The renaming of a filtered allocation certificate**: `allocName` on a covered name
    that the filter keeps, and the identity on every other name. -/
theorem renOf_filter_allocCertOf (body : Lcmd) (tbl : Array Nat) (abi : IsaAbi)
    (P : String → Bool) (n : String) :
    renOf ((allocCertOf body tbl abi).filter fun p => P p.1) n
      = if n ∈ allocCertNames body ∧ P n = true then allocName body tbl n abi else n := by
  unfold renOf
  split_ifs with h
  · obtain ⟨hn, hP⟩ := h
    cases hf : ((allocCertOf body tbl abi).filter fun p => P p.1).find? (·.1 == n) with
    | none =>
      exfalso
      have hm : (n, allocName body tbl n abi) ∈
          (allocCertOf body tbl abi).filter fun p => P p.1 :=
        List.mem_filter.mpr ⟨mem_allocCertOf.mpr ⟨hn, rfl⟩, hP⟩
      have := List.find?_eq_none.mp hf _ hm
      simp at this
    | some q =>
      have hq := List.mem_of_find?_eq_some hf
      have hq1 : q.1 = n := by simpa using List.find?_some hf
      obtain ⟨hq', -⟩ := List.mem_filter.mp hq
      obtain ⟨q1, q2⟩ := q
      obtain ⟨-, rfl⟩ := mem_allocCertOf.mp hq'
      simp only at hq1
      subst hq1
      rfl
  · cases hf : ((allocCertOf body tbl abi).filter fun p => P p.1).find? (·.1 == n) with
    | none => rfl
    | some q =>
      exfalso
      have hq := List.mem_of_find?_eq_some hf
      have hq1 : q.1 = n := by simpa using List.find?_some hf
      obtain ⟨hq', hP⟩ := List.mem_filter.mp hq
      obtain ⟨q1, q2⟩ := q
      obtain ⟨hn, -⟩ := mem_allocCertOf.mp hq'
      simp only at hq1
      subst hq1
      exact h ⟨hn, hP⟩

/-- The names whose pairs `certMerge σ arrs X` keeps: the names of `X` that are no argument
    name, no hardware register name, no frame-slot name, not `%livepin` and no name of
    `arrs`. -/
def certMergeKeep (σ : AbiLayout) (arrs X : List String) (x : String) : Bool :=
  X.contains x && !isArgNameB σ x && !isHwRegName x && !isFrameSlotName x && x != "%livepin"
    && !arrs.contains x

theorem certMerge_eq_filter (σ : AbiLayout) (arrs X : List String)
    (cert : List (String × String)) :
    certMerge σ arrs X cert = cert.filter fun p => certMergeKeep σ arrs X p.1 := rfl

/-- **The merge of an allocation certificate**: under `renOf (certMerge σ arrs X cert)` at
    the certificate `allocCertOf body tbl abi`, a covered name that `certMergeKeep` keeps
    goes to its `allocName`, and every other name to itself. -/
theorem renOf_certMerge_allocCertOf (σ : AbiLayout) (arrs X : List String) (body : Lcmd)
    (tbl : Array Nat) (abi : IsaAbi) (n : String) :
    renOf (certMerge σ arrs X (allocCertOf body tbl abi)) n
      = if n ∈ allocCertNames body ∧ certMergeKeep σ arrs X n = true then
          allocName body tbl n abi
        else n := by
  rw [certMerge_eq_filter]
  exact renOf_filter_allocCertOf body tbl abi _ n

/-- **The merge fixes the names outside the certificate's kept names**, among them the
    array names, the argument names, the hardware register names and the empty name. -/
theorem renOf_certMerge_allocCertOf_of_not {σ : AbiLayout} {arrs X : List String}
    {body : Lcmd} {tbl : Array Nat} {abi : IsaAbi} {n : String}
    (h : certMergeKeep σ arrs X n = false) :
    renOf (certMerge σ arrs X (allocCertOf body tbl abi)) n = n := by
  rw [renOf_certMerge_allocCertOf, ite_eq_right (by simp [h])]

theorem allocCertNames_mem {body : Lcmd} {n : String} (h : n ∈ allocCertNames body) :
    n ∈ bodyNames body ∧ n ≠ "%livepin" ∧ isHwRegName n = false
      ∧ isFrameSlotName n = false := by
  unfold allocCertNames at h
  obtain ⟨hb, hp⟩ := List.mem_filter.mp h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
  exact ⟨hb, hp.1.1, hp.1.2, hp.2⟩

/-- **Two names of the allocator input live at one trace position have distinct images
    under the merge of its certificate**, when each is kept by the merge or, where one is
    not kept, its own name differs from the image of the other. The case of two kept names
    is `allocName_injOn_liveAt`. -/
theorem certMerge_ne_of_liveAt {σ : AbiLayout} {arrs X : List String} {body : Lcmd}
    {outStoreMap : OutStoreMap} {reservedVec : List Nat} {r d : String} {pos : Nat}
    (hfit : numGPRegs + (physLiveItems (bodyTraceOut body outStoreMap)).length ≤ vectorBase)
    (hcls : bodyStraightCall body = true →
      ∀ (s : Nat) (h : s < (physTableOut body outStoreMap reservedVec).size),
        slotIsVec (bodyVecSlots body) s
          = decide (vectorBase ≤ (physTableOut body outStoreMap reservedVec)[s]))
    (hsp : bodyStraightCall body = true →
      gpSpillBase (bodyVecSlots body) (physTableOut body outStoreMap reservedVec) + numGPRegs
        ≤ vectorBase)
    (hrd : r ≠ d)
    (hla : r ∈ allocCertNames body → certMergeKeep σ arrs X r = true →
      d ∈ allocCertNames body → certMergeKeep σ arrs X d = true →
      LiveAt (bodyTraceOut body outStoreMap) pos (nameSlot body r)
        ∧ LiveAt (bodyTraceOut body outStoreMap) pos (nameSlot body d))
    (hrI : r ∈ allocCertNames body ∧ certMergeKeep σ arrs X r = true →
      ¬ (d ∈ allocCertNames body ∧ certMergeKeep σ arrs X d = true) →
      allocName body (straightCallComposeTable body (physTableOut body outStoreMap reservedVec))
        r ≠ d)
    (hIr : ¬ (r ∈ allocCertNames body ∧ certMergeKeep σ arrs X r = true) →
      d ∈ allocCertNames body ∧ certMergeKeep σ arrs X d = true →
      r ≠ allocName body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec)) d) :
    renOf (certMerge σ arrs X (allocCertOf body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec)))) r
      ≠ renOf (certMerge σ arrs X (allocCertOf body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec)))) d := by
  rw [renOf_certMerge_allocCertOf, renOf_certMerge_allocCertOf]
  by_cases hr : r ∈ allocCertNames body ∧ certMergeKeep σ arrs X r = true
  · by_cases hd : d ∈ allocCertNames body ∧ certMergeKeep σ arrs X d = true
    · rw [ite_eq_left hr, ite_eq_left hd]
      obtain ⟨hra, hrb, hrc, hrd'⟩ := allocCertNames_mem hr.1
      obtain ⟨hda, hdb, hdc, hdd⟩ := allocCertNames_mem hd.1
      obtain ⟨h1, h2⟩ := hla hr.1 hr.2 hd.1 hd.2
      exact X86Backend.AllocCertInj.allocName_injOn_liveAt hfit hcls hsp hra hda hrd hrb hdb hrc hdc
        hrd' hdd h1 h2
    · rw [ite_eq_left hr, ite_eq_right hd]
      exact hrI hr hd
  · rw [ite_eq_right hr]
    by_cases hd : d ∈ allocCertNames body ∧ certMergeKeep σ arrs X d = true
    · rw [ite_eq_left hd]
      exact hIr hr hd
    · rw [ite_eq_right hd]
      exact hrd

/-! ## 5. The names in the liveness table are live -/

/-- **The names live at a position of a body**, read after it as `outs`: a name the
    instruction at the position reads; a name live at the next position that an instruction
    other than an unconditional jump does not write; a name live after the label of a jump
    at the position; and a name of `outs` at the end. -/
inductive PLiveR (body : List LinstrRM) (outs : List String) : Nat → String → Prop where
  | read {k : Nat} {i : LinstrRM} {y : String} : body[k]? = some i → y ∈ useNames i.1 →
      PLiveR body outs k y
  | next {k : Nat} {i : LinstrRM} {y : String} : body[k]? = some i → (∀ x, i.1 ≠ .Lgoto x) →
      (∀ ds o ss, i.1 = .Lopn ds o ss → y ∉ regDefs i) → PLiveR body outs (k + 1) y →
      PLiveR body outs k y
  | jump {k : Nat} {i : LinstrRM} {l : LLabel} {p : Nat} {y : String} : body[k]? = some i →
      jumpLabel? i.1 = some l → findLabelMem l body = some p → PLiveR body outs (p + 1) y →
      PLiveR body outs k y
  | out {y : String} : y ∈ outs → PLiveR body outs body.length y

theorem pLiveR_of_mem_liveRegNeed {body : List LinstrRM} {outs : List String}
    {A : Array (List String)} (hA : ∀ j, ∀ y ∈ A.getD j [], PLiveR body outs j y) {k : Nat}
    {i : LinstrRM} (hi : body[k]? = some i) {y : String}
    (hy : y ∈ liveRegNeed body A k i) : PLiveR body outs k y := by
  obtain ⟨w, tag⟩ := i
  have tgt : ∀ (l : LLabel), jumpLabel? w = some l →
      y ∈ (match findLabelMem l body with
        | some p => A.getD (p + 1) []
        | none => []) → PLiveR body outs k y := by
    intro l hl hm
    split at hm
    · rename_i p hp
      exact .jump hi hl hp (hA _ _ hm)
    · simp at hm
  cases w with
  | Lgoto x =>
    obtain ⟨f, l⟩ := x
    exact tgt l rfl hy
  | Lcond c l =>
    rcases List.mem_append.mp hy with h | h
    · exact .next hi (fun x => by simp) (fun _ _ _ e => by cases e) (hA _ _ h)
    · exact tgt l rfl h
  | Lopn ds o ss =>
    rcases List.mem_append.mp hy with h | h
    · exact .read hi h
    · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
      exact .next hi (fun x => by simp) (fun _ _ _ _ => by simpa using h2) (hA _ _ h1)
  | _ => exact .next hi (fun x => by simp) (fun _ _ _ e => by cases e) (hA _ _ hy)

theorem pLiveR_regStep {body : List LinstrRM} {outs : List String} (k : Nat)
    {A : Array (List String)} (hA : ∀ j, ∀ y ∈ A.getD j [], PLiveR body outs j y) :
    ∀ j, ∀ y ∈ (regStep body k A).getD j [], PLiveR body outs j y := by
  intro j y hy
  by_cases hjk : j = k
  · subst hjk
    rcases hi : body[j]? with _ | i
    · simp only [regStep, hi] at hy
      exact hA j y hy
    by_cases hkA : j < A.size
    · rw [getD_regStep_self _ hi hkA, List.mem_eraseDups] at hy
      rcases List.mem_append.mp hy with h | h
      · exact hA j y h
      · exact pLiveR_of_mem_liveRegNeed hA hi h
    · simp only [regStep, hi, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
        hkA] at hy
      simp at hy
  · rw [getD_regStep_ne _ hjk] at hy
    exact hA j y hy

theorem pLiveR_foldr_regStep {body : List LinstrRM} {outs : List String} :
    ∀ (l : List Nat) {A : Array (List String)},
      (∀ j, ∀ y ∈ A.getD j [], PLiveR body outs j y) →
      ∀ j, ∀ y ∈ (l.foldr (regStep body) A).getD j [], PLiveR body outs j y
  | [], _, h => h
  | k :: l, _, h => pLiveR_regStep k (pLiveR_foldr_regStep l h)

theorem pLiveR_liveRegIter {body : List LinstrRM} {outs : List String} :
    ∀ (fuel : Nat) {A : Array (List String)},
      (∀ j, ∀ y ∈ A.getD j [], PLiveR body outs j y) →
      ∀ j, ∀ y ∈ (liveRegIter body fuel A).getD j [], PLiveR body outs j y
  | 0, _, h => h
  | fuel + 1, A, h => by
    simp only [liveRegIter]
    split
    · exact h
    · exact pLiveR_liveRegIter fuel (by rw [liveRegPass_eq]; exact pLiveR_foldr_regStep _ h)

/-- **Every name of the liveness table is live** at its position. -/
theorem pLiveR_of_liveRegTab {body : List LinstrRM} {outs : List String} {k : Nat}
    {y : String} (hy : y ∈ tabAt (liveRegTab body outs) k) : PLiveR body outs k y := by
  refine pLiveR_liveRegIter _ (fun j y hy => ?_) k y hy
  rw [getD_init] at hy
  split at hy
  · rename_i h
    subst h
    exact .out hy
  · simp at hy

/-- **A stable liveness table contains every live name.** -/
theorem liveRegTab_of_pLiveR {body : List LinstrRM} {outs : List String}
    (hst : LiveRegStable body (liveRegTab body outs)) {k : Nat} {y : String}
    (h : PLiveR body outs k y) : y ∈ tabAt (liveRegTab body outs) k := by
  induction h with
  | read hi hy =>
    exact liveRegTab_closed hst hi _ (useNames_sub_liveRegNeed _ _ _ _ _ hy)
  | @next k i y hi hg hd _ ih =>
    refine liveRegTab_closed hst hi _ (mem_liveRegNeed_succ hg ih fun hm => ?_)
    obtain ⟨w, tag⟩ := i
    cases w with
    | Lopn ds o ss => exact hd ds o ss rfl hm
    | _ =>
      simp only [regDefs, JasminLsemExportRegAlloc.memRegDefs, JasminLsemExportRegAlloc.defNames]
        at hm
      split_ifs at hm <;> simp at hm
  | jump hi hl hp _ ih => exact liveRegTab_closed hst hi _ (mem_liveRegNeed_jump hl hp ih)
  | out hy => rwa [liveRegTab_end]

/-! ## 6. The forward half of the cover by the live ranges -/

/-- **A name live at a position is read at or after it**, or is read after the body, or is
    live after the label of a jump at or after it to an earlier label. -/
theorem pLiveR_fwd {body : List LinstrRM} {outs : List String} {k : Nat} {y : String}
    (h : PLiveR body outs k y) :
    (∃ j i, k ≤ j ∧ body[j]? = some i ∧ y ∈ useNames i.1)
      ∨ (∃ j i l p, k ≤ j ∧ body[j]? = some i ∧ jumpLabel? i.1 = some l
          ∧ findLabelMem l body = some p ∧ p < j ∧ PLiveR body outs (p + 1) y)
      ∨ y ∈ outs := by
  induction h with
  | @read k i y hi hy => exact Or.inl ⟨k, i, le_rfl, hi, hy⟩
  | next _ _ _ _ ih =>
    rcases ih with ⟨j, i, hj, h1, h2⟩ | ⟨j, i, l, p, hj, h1, h2, h3, h4, h5⟩ | h
    · exact Or.inl ⟨j, i, by omega, h1, h2⟩
    · exact Or.inr (Or.inl ⟨j, i, l, p, by omega, h1, h2, h3, h4, h5⟩)
    · exact Or.inr (Or.inr h)
  | @jump k i l p y hi hl hp hlive ih =>
    by_cases hpk : p < k
    · exact Or.inr (Or.inl ⟨k, i, l, p, le_rfl, hi, hl, hp, hpk, hlive⟩)
    · rcases ih with ⟨j, i', hj, h1, h2⟩ | ⟨j, i', l', p', hj, h1, h2, h3, h4, h5⟩ | h
      · exact Or.inl ⟨j, i', by omega, h1, h2⟩
      · exact Or.inr (Or.inl ⟨j, i', l', p', by omega, h1, h2, h3, h4, h5⟩)
      · exact Or.inr (Or.inr h)
  | out hy => exact Or.inr (Or.inr hy)

/-- At a stable table, the label position of a jump target holds the names live after the
    label. -/
theorem liveRegTab_label {body : List LinstrRM} {outs : List String}
    (hst : LiveRegStable body (liveRegTab body outs)) {l : LLabel} {p : Nat}
    (hp : findLabelMem l body = some p) {y : String} (h : PLiveR body outs (p + 1) y) :
    y ∈ tabAt (liveRegTab body outs) p := by
  obtain ⟨li, hli, hlab⟩ := JasminLsemLabeled.findLabel_sound l (body.map Prod.fst) p hp
  have hplt : p < body.length := by
    simpa using JasminLsemLabeled.findLabel_lt_length l (body.map Prod.fst) p hp
  obtain ⟨i, hi⟩ : ∃ i, body[p]? = some i := ⟨body[p], List.getElem?_eq_getElem hplt⟩
  have hw : i.1 = li := by
    rw [List.getElem?_map, hi] at hli
    simpa using hli
  refine liveRegTab_of_pLiveR hst (.next hi (fun x hx => ?_) (fun ds o ss hx => ?_) h)
  · rw [hw] at hx
    subst hx
    simp [JasminLsemLabeled.isLabel] at hlab
  · rw [hw] at hx
    subst hx
    simp [JasminLsemLabeled.isLabel] at hlab

/-- **The forward half of the cover of the liveness table by the allocator's live
    ranges**: at a stable table `liveRegTab C []` of the code `C` given to the allocation, a
    name in the table at a position is read by an instruction at or after it, or is read by
    the `LIVEPIN` that `backEdgePins` places before a jump at or after it to an earlier
    label (`backEdgePins_live`). -/
theorem liveRegTab_fwd {C : List LinstrRM} (hst : LiveRegStable C (liveRegTab C []))
    {k : Nat} {y : String} (hy : y ∈ tabAt (liveRegTab C []) k) :
    (∃ j i, k ≤ j ∧ C[j]? = some i ∧ y ∈ useNames i.1)
      ∨ ∃ j i l p, k ≤ j ∧ C[j]? = some i ∧ jumpLabel? i.1 = some l
          ∧ findLabelMem l C = some p ∧ p < j
          ∧ ∃ ns : List String,
            backEdgePin (liveRegTab C []) C j l
              = [(.Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg), .reg none)]
            ∧ y ∈ ns := by
  rcases pLiveR_fwd (pLiveR_of_liveRegTab hy) with h | ⟨j, i, l, p, hj, h1, h2, h3, h4, h5⟩ | h
  · exact Or.inl h
  · exact Or.inr ⟨j, i, l, p, hj, h1, h2, h3, h4,
      backEdgePins_live C h3 h4 (liveRegTab_label hst h3 h5)⟩
  · simp at h

/-- **A slot touched before and after a trace position is live there.** -/
theorem liveAt_of_touch_le_ge {tr : List PhysEvent} {s p q pos : Nat} (hp : p < tr.length)
    (hps : s ∈ tr[p].touched) (hq : q < tr.length) (hqs : s ∈ tr[q].touched)
    (h1 : p ≤ pos) (h2 : pos ≤ q) : LiveAt tr pos s :=
  ⟨le_trans (physFirstTouch_le_of_touched hp hps) h1,
    le_trans h2 (le_physLastTouch_of_touched hq hqs)⟩

/-! ## 7. The liveness table is stable -/

theorem mem_liveRegNeed_congr {body : List LinstrRM} {A B : Array (List String)} {y : String}
    (h : ∀ j, y ∈ A.getD j [] ↔ y ∈ B.getD j []) (k : Nat) (i : LinstrRM) :
    y ∈ liveRegNeed body A k i ↔ y ∈ liveRegNeed body B k i := by
  have h' : ∀ j, y ∈ A[j]?.getD [] ↔ y ∈ B[j]?.getD [] := fun j => by
    simpa only [Array.getD_eq_getD_getElem?] using h j
  unfold liveRegNeed
  dsimp only
  split
  · split <;> simp [h']
  · split <;> simp [h']
  · simp [h']
  · simp [h']

theorem mem_regStep_congr {body : List LinstrRM} {A B : Array (List String)} {y : String}
    (hs : A.size = B.size) (h : ∀ j, y ∈ A.getD j [] ↔ y ∈ B.getD j []) (k : Nat) :
    ∀ j, y ∈ (regStep body k A).getD j [] ↔ y ∈ (regStep body k B).getD j [] := by
  intro j
  by_cases hjk : j = k
  · subst hjk
    rcases hi : body[j]? with _ | i
    · simp only [regStep, hi]
      exact h j
    by_cases hkA : j < A.size
    · rw [getD_regStep_self _ hi hkA, getD_regStep_self _ hi (hs ▸ hkA), List.mem_eraseDups,
        List.mem_eraseDups, List.mem_append, List.mem_append, h j, mem_liveRegNeed_congr h]
    · rw [RegionCoComplete.getD_of_size_le (by rw [size_regStep]; omega),
        RegionCoComplete.getD_of_size_le (by rw [size_regStep]; omega)]
  · rw [getD_regStep_ne _ hjk, getD_regStep_ne _ hjk]
    exact h j

theorem size_foldr_regStep {body : List LinstrRM} :
    ∀ (l : List Nat) (A : Array (List String)), (l.foldr (regStep body) A).size = A.size
  | [], _ => rfl
  | k :: l, A => by rw [List.foldr_cons, size_regStep, size_foldr_regStep l]

theorem mem_foldr_regStep_congr {body : List LinstrRM} {y : String} :
    ∀ (l : List Nat) {A B : Array (List String)}, A.size = B.size →
      (∀ j, y ∈ A.getD j [] ↔ y ∈ B.getD j []) →
      ∀ j, y ∈ (l.foldr (regStep body) A).getD j [] ↔ y ∈ (l.foldr (regStep body) B).getD j []
  | [], _, _, _, h => h
  | k :: l, _, _, hs, h => mem_regStep_congr
      (by rw [size_foldr_regStep, size_foldr_regStep, hs]) (mem_foldr_regStep_congr l hs h) k

/-- **A pass treats each name separately**: two tables of one size that hold the name `y` at
    the same positions hold it at the same positions after the pass `liveRegPass`. -/
theorem agree_liveRegPass {body : List LinstrRM} {A B : Array (List String)} {y : String}
    (hs : A.size = B.size) (h : ∀ j, y ∈ A.getD j [] ↔ y ∈ B.getD j []) :
    ∀ j, y ∈ (liveRegPass body A).getD j [] ↔ y ∈ (liveRegPass body B).getD j [] :=
  mem_foldr_regStep_congr _ hs h

theorem size_liveRegPass (body : List LinstrRM) (A : Array (List String)) :
    (liveRegPass body A).size = A.size :=
  size_foldr_regStep _ A

theorem getD_liveRegPass_end (body : List LinstrRM) (A : Array (List String)) :
    (liveRegPass body A).getD body.length [] = A.getD body.length [] := by
  rw [liveRegPass_eq, getD_foldr_regStep_of_not_mem _ _ (by simp)]

theorem prefix_liveRegPass {body : List LinstrRM} {A : Array (List String)}
    (hA : RegInv body A) (j : Nat) : A.getD j [] <+: (liveRegPass body A).getD j [] := by
  rw [liveRegPass_eq]
  exact prefix_foldr_regStep _ hA j

theorem regInv_liveRegPass {body : List LinstrRM} {A : Array (List String)}
    (hA : RegInv body A) : RegInv body (liveRegPass body A) := by
  rw [liveRegPass_eq]
  exact regInv_foldr _ hA

theorem regInv_iterate {body : List LinstrRM} {A : Array (List String)} (hA : RegInv body A) :
    ∀ t : Nat, RegInv body ((liveRegPass body)^[t] A)
  | 0 => hA
  | t + 1 => by
    rw [Function.iterate_succ_apply']
    exact regInv_liveRegPass (regInv_iterate hA t)

/-- The number of positions before the end of a body of length `n` at which the table `A`
    holds the name `y`. -/
def regCount (n : Nat) (A : Array (List String)) (y : String) : Nat :=
  ((Finset.range n).filter fun j => y ∈ A.getD j []).card

theorem regCount_le (n : Nat) (A : Array (List String)) (y : String) : regCount n A y ≤ n :=
  (Finset.card_filter_le _ _).trans (by simp)

theorem regCount_lt {n : Nat} {A B : Array (List String)} {y : String}
    (hmono : ∀ j, y ∈ A.getD j [] → y ∈ B.getD j []) {j : Nat} (hj : j < n)
    (hB : y ∈ B.getD j []) (hA : y ∉ A.getD j []) : regCount n A y < regCount n B y := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun x hx => ?_).mpr ⟨j, ?_, ?_⟩)
  · simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hmono x hx.2⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hB⟩
  · exact fun hm => hA (Finset.mem_filter.mp hm).2

/-- A pass that changes the positions of the name `y` adds `y` at a position before the end
    of the body. -/
theorem exists_new_of_change {body : List LinstrRM} {A : Array (List String)}
    (hA : RegInv body A) {y : String}
    (h : ¬ ∀ j, (y ∈ A.getD j [] ↔ y ∈ (liveRegPass body A).getD j [])) :
    ∃ j < body.length, y ∈ (liveRegPass body A).getD j [] ∧ y ∉ A.getD j [] := by
  by_contra hn
  refine h fun j => ⟨fun hy => (prefix_liveRegPass hA j).subset hy, fun hy => ?_⟩
  by_contra hy'
  rcases Nat.lt_trichotomy j body.length with hj | hj | hj
  · exact hn ⟨j, hj, hy, hy'⟩
  · subst hj
    rw [getD_liveRegPass_end] at hy
    exact hy' hy
  · rw [RegionCoComplete.getD_of_size_le (by rw [size_liveRegPass, hA.1]; omega)] at hy
    simp at hy

/-- **The positions of a name grow for at most `n` passes**: if the pass `t + 1` from a
    table of shape `RegInv` changes the positions of the name `y`, then `y` is held at
    `t + 1` or more positions before the end after it. -/
theorem le_regCount_of_change {body : List LinstrRM} {A : Array (List String)}
    (hA : RegInv body A) {y : String} :
    ∀ t : Nat, (¬ ∀ j, (y ∈ ((liveRegPass body)^[t] A).getD j []
        ↔ y ∈ ((liveRegPass body)^[t + 1] A).getD j [])) →
      t + 1 ≤ regCount body.length ((liveRegPass body)^[t + 1] A) y
  | 0, h => by
    rw [Function.iterate_succ_apply'] at h ⊢
    obtain ⟨j, hj, h1, h2⟩ := exists_new_of_change hA h
    have := regCount_lt (fun j hy => (prefix_liveRegPass hA j).subset hy) hj h1 h2
    simp only [Function.iterate_zero, id_eq] at this ⊢
    omega
  | t + 1, h => by
    have hT := regInv_iterate hA (t + 1)
    have hprev : ¬ ∀ j, (y ∈ ((liveRegPass body)^[t] A).getD j []
        ↔ y ∈ ((liveRegPass body)^[t + 1] A).getD j []) := by
      intro hall
      apply h
      have := agree_liveRegPass (body := body)
        (by rw [(regInv_iterate hA t).1, hT.1]) hall
      simpa only [Function.iterate_succ_apply'] using this
    have ih := le_regCount_of_change hA t hprev
    have h' := h
    rw [Function.iterate_succ_apply' _ (t + 1)] at h'
    obtain ⟨j, hj, h1, h2⟩ := exists_new_of_change hT h'
    have := regCount_lt (fun j hy => (prefix_liveRegPass hT j).subset hy) hj h1 h2
    rw [Function.iterate_succ_apply' _ (t + 1)]
    omega

/-- **From the pass `n` on the passes are stable**: for a body of length `n` and a table of
    shape `RegInv`, the table after `t ≥ n` passes is `LiveRegStable`. -/
theorem liveRegStable_iterate {body : List LinstrRM} {A : Array (List String)}
    (hA : RegInv body A) {t : Nat} (ht : body.length ≤ t) :
    LiveRegStable body ((liveRegPass body)^[t] A) := by
  have hT := regInv_iterate hA t
  have hsame : ∀ y j, (y ∈ ((liveRegPass body)^[t] A).getD j []
      ↔ y ∈ (liveRegPass body ((liveRegPass body)^[t] A)).getD j []) := by
    intro y
    by_contra h
    have h' : ¬ ∀ j, (y ∈ ((liveRegPass body)^[t] A).getD j []
        ↔ y ∈ ((liveRegPass body)^[t + 1] A).getD j []) := by
      rwa [Function.iterate_succ_apply']
    have := le_regCount_of_change hA t h'
    have := regCount_le body.length ((liveRegPass body)^[t + 1] A) y
    omega
  intro j
  have hp := prefix_liveRegPass hT j
  refine le_antisymm ?_ hp.length_le
  rcases Nat.lt_trichotomy j body.length with hj | hj | hj
  · exact List.Nodup.length_le_of_subset ((regInv_liveRegPass hT).2 j hj)
      fun y hy => (hsame y j).mpr hy
  · subst hj
    rw [getD_liveRegPass_end]
  · rw [RegionCoComplete.getD_of_size_le (by rw [size_liveRegPass, hT.1]; omega)]
    simp

theorem liveRegIter_stable {body : List LinstrRM} {A : Array (List String)}
    (hA : RegInv body A) :
    ∀ (fuel t : Nat), body.length ≤ t + fuel →
      LiveRegStable body (liveRegIter body fuel ((liveRegPass body)^[t] A))
  | 0, _, h => liveRegStable_iterate hA (by omega)
  | fuel + 1, t, h => by
    simp only [liveRegIter]
    split
    · rename_i hb
      exact RegionCoComplete.lengths_of_beq hb
    · rw [← Function.iterate_succ_apply' (liveRegPass body) t A]
      exact liveRegIter_stable hA fuel (t + 1) (by omega)

theorem regInv_init (body : List LinstrRM) (outs : List String) :
    RegInv body ((Array.replicate (body.length + 1) ([] : List String)).setIfInBounds
      body.length outs) :=
  ⟨by simp, fun j hj => by
    rw [getD_init, ite_eq_right (Nat.ne_of_lt hj)]
    exact List.nodup_nil⟩

/-- **The register liveness table is stable**: the fuel `body.length + 2` of `liveRegTab`
    suffices, and one more pass changes no list of the table. -/
theorem liveRegTab_stable (body : List LinstrRM) (outs : List String) :
    LiveRegStable body (liveRegTab body outs) :=
  liveRegIter_stable (regInv_init body outs) (body.length + 2) 0 (by omega)

/-- **The register liveness table is the set of live names**: a name is in
    `liveRegTab body outs` at a position exactly when it is live there (`PLiveR`). -/
theorem mem_liveRegTab_iff {body : List LinstrRM} {outs : List String} {k : Nat}
    {y : String} : y ∈ tabAt (liveRegTab body outs) k ↔ PLiveR body outs k y :=
  ⟨pLiveR_of_liveRegTab, liveRegTab_of_pLiveR (liveRegTab_stable body outs)⟩

/-! ## 8. The images of the allocation -/

theorem hasPrefix_append (p s : String) : hasPrefix (p ++ s) p = true := by
  simp [hasPrefix, String.toList_append, List.isPrefixOf_iff_prefix]

/-- **The name of a physical index is a hardware register name, a frame-slot name or a
    vector register name**: a register of the allocation pool, a spill `k.N` or `kv.N`, or one
    of `XMM0 … XMM15`. The names `XMM8 … XMM15` are not hardware register names in the sense
    of `isHwRegName`. -/
theorem physRegName_cases (p : Nat) :
    isHwRegName (physRegName p) = true ∨ isFrameSlotName (physRegName p) = true
      ∨ physRegName p ∈ vectorRegNames := by
  unfold physRegName
  split_ifs
  · dsimp only
    split
    · rename_i r hr
      exact Or.inr (Or.inr (List.mem_of_getElem? hr))
    · exact Or.inr (Or.inl (by simp [isFrameSlotName, hasPrefix_append]))
  · split
    · rename_i r hr
      refine Or.inl ?_
      have : r ∈ gpRegNames := List.mem_of_getElem? hr
      simp [isHwRegName, hwRegNames, this]
    · exact Or.inr (Or.inl (by simp [isFrameSlotName, hasPrefix_append]))

/-- **The image of a name under the allocation** (`allocName_cases`) is a hardware register
    name, a frame-slot name, a vector register name, or the name itself. -/
theorem allocName_cases (body : Lcmd) (tbl : Array Nat) (n : String) :
    isHwRegName (allocName body tbl n) = true ∨ isFrameSlotName (allocName body tbl n) = true
      ∨ allocName body tbl n ∈ vectorRegNames ∨ allocName body tbl n = n := by
  unfold allocName physNameForBody
  split_ifs <;> first
    | exact Or.inr (Or.inr (Or.inr rfl))
    | (rcases physRegName_cases _ with h | h | h
       · exact Or.inl h
       · exact Or.inr (Or.inl h)
       · exact Or.inr (Or.inr (Or.inl h)))

/-- A plain name: no hardware register name, no frame-slot name and no vector register
    name. The names the export writes and reads are plain. -/
def PlainName (x : String) : Prop :=
  isHwRegName x = false ∧ isFrameSlotName x = false ∧ x ∉ vectorRegNames

/-- **The image of a name under the allocation differs from every other plain name.** -/
theorem allocName_ne {body : Lcmd} {tbl : Array Nat} {n d : String} (hd : PlainName d)
    (hne : n ≠ d) : allocName body tbl n ≠ d := by
  intro he
  rcases allocName_cases body tbl n with h | h | h | h <;> rw [he] at h
  · rw [hd.1] at h
    exact Bool.false_ne_true h
  · rw [hd.2.1] at h
    exact Bool.false_ne_true h
  · exact hd.2.2 h
  · exact hne h.symm

/-- **The merge fixes every name that it does not keep**, at every certificate. -/
theorem renOf_certMerge_of_not {σ : AbiLayout} {arrs X : List String}
    {cert : List (String × String)} {n : String} (h : certMergeKeep σ arrs X n = false) :
    renOf (certMerge σ arrs X cert) n = n := by
  rw [certMerge_eq_filter]
  apply JasminLsemRenameLoop.renOf_of_not_mem
  intro hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  simp [(List.mem_filter.mp hp).2] at h

/-- **The mixed cases of the merge** (`certMerge_ne_of_liveAt_plain`): two distinct plain
    names of the allocator input live at one trace position, when both are kept, have
    distinct images under the merge of its certificate. A kept name goes to its
    `allocName`, which is no plain name other than itself (`allocName_ne`), and a name that
    is not kept goes to itself. -/
theorem certMerge_ne_of_liveAt_plain {σ : AbiLayout} {arrs X : List String} {body : Lcmd}
    {outStoreMap : OutStoreMap} {reservedVec : List Nat} {r d : String} {pos : Nat}
    (hfit : numGPRegs + (physLiveItems (bodyTraceOut body outStoreMap)).length ≤ vectorBase)
    (hcls : bodyStraightCall body = true →
      ∀ (s : Nat) (h : s < (physTableOut body outStoreMap reservedVec).size),
        slotIsVec (bodyVecSlots body) s
          = decide (vectorBase ≤ (physTableOut body outStoreMap reservedVec)[s]))
    (hsp : bodyStraightCall body = true →
      gpSpillBase (bodyVecSlots body) (physTableOut body outStoreMap reservedVec) + numGPRegs
        ≤ vectorBase)
    (hrd : r ≠ d) (hr : PlainName r) (hd : PlainName d)
    (hla : r ∈ allocCertNames body → certMergeKeep σ arrs X r = true →
      d ∈ allocCertNames body → certMergeKeep σ arrs X d = true →
      LiveAt (bodyTraceOut body outStoreMap) pos (nameSlot body r)
        ∧ LiveAt (bodyTraceOut body outStoreMap) pos (nameSlot body d)) :
    renOf (certMerge σ arrs X (allocCertOf body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec)))) r
      ≠ renOf (certMerge σ arrs X (allocCertOf body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec)))) d :=
  certMerge_ne_of_liveAt hfit hcls hsp hrd hla (fun _ _ => allocName_ne hd hrd)
    (fun _ _ => (allocName_ne hr (Ne.symm hrd)).symm)

/-! ## 9. The shape of the instructions of the reference -/

/-- **The shape of an instruction of the export**: no unconditional jump, a conditional jump
    on the zero flag (`Z` or `NZ`), and an operation with one register destination. -/
def CoShape (i : LinstrRM) : Prop :=
  (∀ x, i.1 ≠ .Lgoto x) ∧ (∀ c l, i.1 = .Lcond c l → c = .reg "Z" ∨ c = .reg "NZ")
    ∧ ∀ ds o ss, i.1 = .Lopn ds o ss → ∃ x, ds = [.reg x]

theorem coShape_lopn {i : LinstrRM} {x o : String} {ss : List LOperand}
    (h : i.1 = .Lopn [.reg x] o ss) : CoShape i := by
  unfold CoShape
  refine ⟨fun y e => ?_, fun c l e => ?_, fun ds o' ss' e => ?_⟩ <;> rw [h] at e <;> cases e
  exact ⟨x, rfl⟩

theorem coShape_cond {i : LinstrRM} {c : String} {l : LLabel} (h : i.1 = .Lcond (.reg c) l)
    (hc : c = "Z" ∨ c = "NZ") : CoShape i := by
  unfold CoShape
  refine ⟨fun y e => ?_, fun c' l' e => ?_, fun ds o ss e => ?_⟩ <;> rw [h] at e <;> cases e
  rcases hc with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem coShape_other {i : LinstrRM} (hg : ∀ x, i.1 ≠ .Lgoto x) (hc : ∀ c l, i.1 ≠ .Lcond c l)
    (ho : ∀ ds o ss, i.1 ≠ .Lopn ds o ss) : CoShape i :=
  ⟨hg, fun c l e => absurd e (hc c l), fun ds o ss e => absurd e (ho ds o ss)⟩

/-- **An instruction of the shape `CoShape` passes the condition check `condOKB`.** -/
theorem condOKB_of_coShape {i : LinstrRM} (h : CoShape i) : condOKB i = true := by
  obtain ⟨w, tag⟩ := i
  obtain ⟨-, hc, ho⟩ := h
  cases w with
  | Lcond c l =>
    rcases hc c l rfl with rfl | rfl <;>
      simp [condOKB, JasminLsemMemFlagGuard.flagCondCC?, JasminLsemExportRewrites.mulxFree,
        JasminLsemMemFlagGuard.wideArgs?]
  | Lopn ds o ss =>
    obtain ⟨x, rfl⟩ := ho ds o ss rfl
    simp only [condOKB, Bool.true_and]
    exact JasminLsemExportRewrites.mulxFree_of_lopn1 ⟨_, _, _, rfl⟩
  | _ =>
    simp [condOKB, JasminLsemExportRewrites.mulxFree, JasminLsemMemFlagGuard.wideArgs?]

/-- **An instruction of the shape `CoShape` writes at most one register name.** -/
theorem regDefs_length_le_of_coShape {i : LinstrRM} (h : CoShape i) :
    (regDefs i).length ≤ 1 := by
  have hd : (JasminLsemExportRegAlloc.defNames i.1).length ≤ 1 := by
    obtain ⟨w, tag⟩ := i
    cases w with
    | Lopn ds o ss =>
      obtain ⟨x, rfl⟩ := h.2.2 ds o ss rfl
      simp [JasminLsemExportRegAlloc.defNames, JasminLsemExportRewrites.opNames]
    | _ => simp [JasminLsemExportRegAlloc.defNames]
  unfold regDefs JasminLsemExportRegAlloc.memRegDefs
  split_ifs <;> simp_all

theorem coShape_renRM (τ : String → String) {i : LinstrRM} (h : CoShape i) :
    CoShape (JasminLsemExportTransfer.renRM τ i) := by
  obtain ⟨w, tag⟩ := i
  obtain ⟨hg, hc, ho⟩ := h
  cases w with
  | Lopn ds o ss =>
    obtain ⟨x, rfl⟩ := ho ds o ss rfl
    exact coShape_lopn rfl
  | _ => exact ⟨hg, hc, ho⟩

theorem coShape_renArr (σ : String → String) {i : LinstrRM} (h : CoShape i) :
    CoShape (X86Backend.ImageCoalesceCfg.renArr σ i) := by
  obtain ⟨w, tag⟩ := i
  obtain ⟨hg, hc, ho⟩ := h
  cases w with
  | Lopn ds o ss =>
    obtain ⟨x, rfl⟩ := ho ds o ss rfl
    obtain ⟨x', o', ss', he⟩ : ∃ x' o' ss', (X86Backend.ImageCoalesceCfg.renArr σ
        (.Lopn [.reg x] o ss, tag)).1 = .Lopn [.reg x'] o' ss' := by
      unfold X86Backend.ImageCoalesceCfg.renArr
      split <;> simp only [X86Backend.ImageCoalesceCfg.renLoad,
        X86Backend.ImageCoalesceCfg.renStore, X86Backend.ImageCoalesceCfg.renZero,
        X86Backend.ImageCoalesceCfg.renStoreImm, X86Backend.ImageCoalesceCfg.renCallW] <;>
        (repeat' split) <;> simp [LprogIsa.callShadow]
    exact coShape_lopn he
  | _ => cases tag <;> exact ⟨hg, hc, ho⟩

theorem coShape_movesOf (ps : List (String × String)) :
    ∀ i ∈ JasminLsemRenameLoop.movesOf ps, CoShape i := by
  intro i hi
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  exact coShape_lopn rfl

theorem regCallOpsB_none (AN : List String) :
    ∀ (j : Nat) (os : List LOperand), regCallOpsB (fun _ => none) AN j os = true
  | _, [] => rfl
  | j, _ :: os => by simp [regCallOpsB, regCallOpsB_none AN (j + 1) os]

/-- **Without a callee every instruction passes the call check `regCallB`.** -/
theorem regCallB_none (τ : String → String) (Lr : Nat → List String) (AN : List String)
    (k : Nat) (i : LinstrRM) :
    regCallB τ Lr AN (calleeAA none) (calleeAO none) k i = true := by
  unfold regCallB
  split
  · simp [calleeAA, calleeAO, regCallOpsB_none]
  · rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapComplete
