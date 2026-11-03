/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete
public import CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps

@[expose] public section

set_option autoImplicit false

/-!
# The synthesised liveness table is the least certificate

`liveArrTab C obs aa ao` iterates the backward pass `liveArrPass` over the body `C` from the
names `obs` at the end, at most a fuel of passes. This module proves that the table it
returns is a solution of the liveness equations `CoalesceComplete.NeedClosed` and lies
below the least solution `CoalesceComplete.PLive`, so that the coalescing check `coCfgB`
at this table accepts every admitted body and renaming without real aliasing.

## Main definitions

* `passStep`: one update of the backward pass at a position.
* `LiveInv`: the shape of the tables the passes reach: the size, the names at the end,
  lists without duplicates before the end, and entries among `liveArrNames`.
* `CallFix`: the conditions of `ClassOK` at the shadow instructions of calls.
* `NoShadow`: an instruction that is no shadow instruction of a call.
* `InUse`, `StorageDisjoint`: the array names in use at a position, and no two distinct
  names of one storage class (root under the alias map) in use at once.

## Main results

* `mem_liveArrNeed_of_need`, `need_of_mem_liveArrNeed`: the names `liveArrNeed` adds at
  an instruction are those of the liveness equations at it (`rdArr`, `wrArr`, `Succ`).
* `liveArrTab_needClosed`: the table solves the liveness equations.
* `liveArrTab_pLive`: on a body with no refused instruction every entry of the table is
  live.
* `liveArrCert_least`: both, for an admitted body.
* `coCfgB_liveArrTab`, `entryFix_liveArrTab`: an admitted body and a renaming without real
  aliasing pass the coalescing check at the table and fix the names of its entry.
* `regionCoStage_coalesce`: under these hypotheses on the code with the result copies, the
  region gate `regionCoStage` refuses neither at `coCfgB` nor at `coEntryFix`.
* `classOK_of`: `ClassOK` from the class check `clsB`, the absence of compile-time-offset
  tags (`TagOK`) and `CallFix`.
* `GuardsNoShadow`, `x86Data_guardsNoShadow`: the guards and the select of an instruction set
  contain no shadow instruction of a call; x86 satisfies it.
* `exportR_tagOK`, `exportR_noShadow`: the export has no compile-time-offset tag, and over
  an instruction set with `GuardsNoShadow` a program without `call` that passes
  `regionExportableB` exports no shadow instruction of a call.
* `regionCo_classOK`: `ClassOK` on the coalesced code of a region export that passes the
  stages `commonCalls` and `coClass` of `regionCoStage`.
* `regionCoStage_coalesce_of`: `regionCoStage` refuses neither at `coCfgB` nor at
  `coEntryFix` on such code without real aliasing.
* `HaxModule.refusal?_eq_none_imp_coalesce`: the same on the webs `regionWebsAt` of the
  export of the output of the chain, on every module that `refusal?` accepts, at a table and
  on the call-free arm.
* `noRealAlias_of_storageDisjoint`: disjoint storage classes (`StorageDisjoint`) give no real
  aliasing under the alias map of `resAliasTab` of the code, at every result alias; without
  one the map is `chainAliasO`. The alias map of the gate is the map of `regionAliasTab`,
  which sends the result root of the returned array to the result buffer
  (`resAliasTab_of_unassigned`: a name the code never assigns is its own root, the result
  root included, since the code zeroes it).
* `HaxModule.refusal?_eq_none_imp_coalesce_of_disjoint`: the coalescing stage on the output
  of the chain under `StorageDisjoint` in place of `NoRealAlias`.
* `HaxModule.refusal?_eq_none_imp_coalesce_x86`,
  `HaxModule.refusal?_eq_none_imp_coalesce_of_disjoint_x86`: both at x86.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findLabelMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (arrReads arrWrite
  chainAliasO chainAliasRes chainAliasRes_apply resRoot?_some zeroFirstB zeroDst?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (shadowCall?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete

/-! ## 1. Lists without duplicates -/

theorem nodup_eraseDups (l : List String) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp [List.eraseDups]
    | cons a as =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, ih _ ?_ _ rfl⟩
      · simp [List.mem_eraseDups]
      · subst h
        exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem eraseDups_of_nodup : ∀ {l : List String}, l.Nodup → l.eraseDups = l
  | [], _ => by simp [List.eraseDups]
  | a :: as, h => by
    rw [List.eraseDups_cons]
    obtain ⟨ha, has⟩ := List.nodup_cons.mp h
    have hf : List.filter (fun b => !b == a) as = as :=
      List.filter_eq_self.mpr fun b hb => by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
        rintro rfl
        exact ha hb
    rw [hf, eraseDups_of_nodup has]

theorem prefix_eraseDups_append {l : List String} (h : l.Nodup) (x : List String) :
    l <+: (l ++ x).eraseDups := by
  rw [List.eraseDups_append, eraseDups_of_nodup h]
  exact List.prefix_append _ _

/-! ## 2. The liveness equations at one instruction -/

theorem callArrOps_eq (a : Nat → Option Nat) :
    ∀ (j : Nat) (os : List LOperand), callArrOps a j os = callArrRegs a j os := by
  intro j os
  induction os generalizing j with
  | nil => rfl
  | cons o os ih =>
    cases o <;> simp only [callArrOps, callArrRegs, ih, List.nil_append]
    split <;> simp_all

theorem arrReads_of_arrShapeB {i : LinstrRM} (h : arrShapeB i = false) : arrReads i = [] := by
  rcases i with ⟨w, t⟩
  cases t <;> simp only [arrShapeB, arrReads] at h ⊢ <;> split <;> simp_all

theorem arrShapeB_of_not_lopn {i : LinstrRM} (h : ∀ d o s, i.1 ≠ .Lopn d o s) :
    arrShapeB i = false := by
  rcases i with ⟨w, t⟩
  cases w <;> first | exact absurd rfl (h _ _ _) | cases t <;> rfl

theorem armOf_goto (x : String) (l : LLabel) (t : MemTag) :
    armOf (.Lgoto (x, l), t) = .goto l := by
  have := arrShapeB_of_not_lopn (i := (.Lgoto (x, l), t)) (by simp)
  simp_all [armOf, shadowCall?, cmpArgs?, movRegArgs?, flagCondCC?]

theorem armOf_cond (c : LOperand) (l : LLabel) (t : MemTag) :
    armOf (.Lcond c l, t) = .cc l := by
  have := arrShapeB_of_not_lopn (i := (.Lcond c l, t)) (by simp)
  simp only [armOf, shadowCall?, this, cmpArgs?, movRegArgs?, Option.isSome_none,
    Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i h
    simp only [flagCondCC?] at h
    split at h <;> simp_all
  · rfl

theorem armOf_label (k : LabelKind) (l : LLabel) (t : MemTag) :
    armOf (.Llabel k l, t) = .seq := by
  have := arrShapeB_of_not_lopn (i := (.Llabel k l, t)) (by simp)
  simp_all [armOf, shadowCall?, cmpArgs?, movRegArgs?, flagCondCC?]

theorem armOf_call {i : LinstrRM} {dst f : String} {srcs : List LOperand}
    (h : shadowCall? i.1 = some (dst, f, srcs)) : armOf i = .call dst f srcs := by
  simp [armOf, h]

theorem armOf_arr {i : LinstrRM} (h : shadowCall? i.1 = none) (ha : arrShapeB i = true) :
    armOf i = .arr := by
  simp [armOf, h, ha]

theorem armOf_lopn {i : LinstrRM} {d : List LOperand} {o : String} {s : List LOperand}
    (hi : i.1 = .Lopn d o s) (h : shadowCall? i.1 = none) (ha : arrShapeB i = false) :
    armOf i = .seq ∨ armOf i = .op := by
  have hf : flagCondCC? i = none := by simp [flagCondCC?, hi]
  unfold armOf
  rw [h]
  simp only [ha, hf, hi, Bool.false_eq_true, ↓reduceIte]
  split
  · simp
  · split <;> simp

/-- **Every name `liveArrNeed` adds satisfies the liveness equations**: it is read by the
    instruction, or live at a successor and not written by it. -/
theorem need_of_mem_liveArrNeed {body : List LinstrRM} {A : Array (List String)} {k : Nat}
    {i : LinstrRM} {aa : String → Nat → Option Nat} {ao : String → Option Nat} {r : String}
    (hb : armOf i ≠ .bad) (hr : r ∈ liveArrNeed body A k i aa ao) :
    r ∈ rdArr aa i ∨ ∃ k', Succ body k i k' ∧ some r ≠ wrArr ao i ∧ r ∈ tabAt A k' := by
  rcases i with ⟨w, t⟩
  cases w with
  | Lopn d o s =>
    rcases hs : shadowCall? (LinstrR.Lopn d o s) with _ | ⟨dst, f, srcs⟩
    · by_cases ha : arrShapeB (.Lopn d o s, t) = true
      · have harm := armOf_arr hs ha
        simp only [liveArrNeed, hs, rdArr, wrArr, Succ, harm, rdArrA, wrArrA, SuccA,
          List.mem_append, List.mem_filter, tabAt] at hr ⊢
        rcases hr with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨_, rfl, by simpa using h2, h1⟩
      · have ha' : arrShapeB (.Lopn d o s, t) = false := by simpa using ha
        have hR := arrReads_of_arrShapeB ha'
        have hW := arrWrite_of_arrShapeB ha'
        rcases armOf_lopn (i := (.Lopn d o s, t)) rfl hs ha' with harm | harm <;>
        · simp only [liveArrNeed, hs, rdArr, wrArr, Succ, harm, rdArrA, wrArrA, SuccA, hR, hW,
            List.nil_append, List.mem_filter, tabAt] at hr ⊢
          exact Or.inr ⟨_, rfl, by simp, hr.1⟩
    · have harm := armOf_call (i := (.Lopn d o s, t)) hs
      simp only [liveArrNeed, hs, rdArr, wrArr, Succ, harm, rdArrA, wrArrA, SuccA,
        List.mem_append, List.mem_filter, tabAt, callArrOps_eq] at hr ⊢
      rcases hr with h | ⟨h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨_, rfl, ?_, h1⟩
        cases hf : ao f <;> simp_all
  | Lgoto x =>
    obtain ⟨x, l⟩ := x
    simp only [liveArrNeed, rdArr, wrArr, Succ, armOf_goto, rdArrA, wrArrA, SuccA, JumpTo,
      tabAt] at hr ⊢
    split at hr
    · exact Or.inr ⟨_, ⟨_, ‹_›, rfl⟩, by simp, hr⟩
    · simp at hr
  | Lcond c l =>
    simp only [liveArrNeed, rdArr, wrArr, Succ, armOf_cond, rdArrA, wrArrA, SuccA, JumpTo,
      tabAt, Bool.true_and] at hr ⊢
    rcases List.mem_append.mp hr with h | h
    · cases hg : X86Backend.ConstGuard.constTakenB body k
      · exact Or.inr ⟨_, Or.inl ⟨rfl, rfl⟩, by simp, by simpa [hg] using h⟩
      · simp [hg] at h
    · split at h
      · exact Or.inr ⟨_, Or.inr ⟨_, ‹_›, rfl⟩, by simp, h⟩
      · simp at h
  | Llabel kd l =>
    simp only [liveArrNeed, rdArr, wrArr, Succ, armOf_label, rdArrA, wrArrA, SuccA,
      tabAt] at hr ⊢
    exact Or.inr ⟨_, rfl, by simp, hr⟩
  | _ =>
    exfalso
    revert hb
    cases t <;> simp [armOf, shadowCall?, cmpArgs?, movRegArgs?, flagCondCC?, arrShapeB,
      loadStruct?, storeStruct?, zeroStruct?, storeImmStruct?]

/-- **`liveArrNeed` contains every name the liveness equations require** at an
    instruction: the names it reads, and the names live at a successor that it does not
    write. -/
theorem mem_liveArrNeed_of_need (body : List LinstrRM) (A : Array (List String)) (k : Nat)
    (i : LinstrRM) (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    (∀ r ∈ rdArr aa i, r ∈ liveArrNeed body A k i aa ao) ∧
      ∀ k' r, Succ body k i k' → some r ≠ wrArr ao i → r ∈ tabAt A k' →
        r ∈ liveArrNeed body A k i aa ao := by
  rcases i with ⟨w, t⟩
  by_cases hbad : armOf (w, t) = .bad
  · simp [rdArr, Succ, hbad, rdArrA, SuccA]
  cases w with
  | Lopn d o s =>
    rcases hs : shadowCall? (LinstrR.Lopn d o s) with _ | ⟨dst, f, srcs⟩
    · by_cases ha : arrShapeB (.Lopn d o s, t) = true
      · have harm := armOf_arr hs ha
        simp only [liveArrNeed, hs, rdArr, wrArr, Succ, harm, rdArrA, wrArrA, SuccA,
          List.mem_append, List.mem_filter, tabAt]
        refine ⟨fun r h => Or.inl h, ?_⟩
        rintro k' r rfl hw h
        exact Or.inr ⟨h, by simpa using hw⟩
      · have ha' : arrShapeB (.Lopn d o s, t) = false := by simpa using ha
        have hR := arrReads_of_arrShapeB ha'
        have hW := arrWrite_of_arrShapeB ha'
        rcases armOf_lopn (i := (.Lopn d o s, t)) rfl hs ha' with harm | harm <;>
        · simp only [liveArrNeed, hs, rdArr, wrArr, Succ, harm, rdArrA, wrArrA, SuccA, hR, hW,
            List.nil_append, List.mem_filter, tabAt]
          refine ⟨fun r h => by simp at h, ?_⟩
          rintro k' r rfl - h
          exact ⟨h, by simp⟩
    · have harm := armOf_call (i := (.Lopn d o s, t)) hs
      simp only [liveArrNeed, hs, rdArr, wrArr, Succ, harm, rdArrA, wrArrA, SuccA,
        List.mem_append, List.mem_filter, tabAt, callArrOps_eq]
      refine ⟨fun r h => Or.inl h, ?_⟩
      rintro k' r rfl hw h
      refine Or.inr ⟨h, ?_⟩
      cases hf : ao f <;> simp_all
  | Lgoto x =>
    obtain ⟨x, l⟩ := x
    simp only [liveArrNeed, rdArr, wrArr, Succ, armOf_goto, rdArrA, wrArrA, SuccA, JumpTo,
      tabAt]
    refine ⟨fun r h => by simp at h, ?_⟩
    rintro k' r ⟨p, hp, rfl⟩ - h
    simpa [hp] using h
  | Lcond c l =>
    simp only [liveArrNeed, rdArr, wrArr, Succ, armOf_cond, rdArrA, wrArrA, SuccA, JumpTo,
      tabAt, Bool.true_and]
    refine ⟨fun r h => by simp at h, ?_⟩
    rintro k' r (⟨rfl, hg⟩ | ⟨p, hp, rfl⟩) - h
    · exact List.mem_append_left _ (by simpa [hg] using h)
    · exact List.mem_append_right _ (by simpa [hp] using h)
  | Llabel kd l =>
    simp only [liveArrNeed, rdArr, wrArr, Succ, armOf_label, rdArrA, wrArrA, SuccA,
      tabAt]
    refine ⟨fun r h => by simp at h, ?_⟩
    rintro k' r rfl - h
    exact h
  | _ =>
    exfalso
    revert hbad
    cases t <;> simp [armOf, shadowCall?, cmpArgs?, movRegArgs?, flagCondCC?, arrShapeB,
      loadStruct?, storeStruct?, zeroStruct?, storeImmStruct?]

/-- A name `liveArrNeed` adds is in the table, an array operand of a call, or a name an
    operation reads. -/
theorem mem_liveArrNeed_cases {body : List LinstrRM} {A : Array (List String)} {k : Nat}
    {i : LinstrRM} {aa : String → Nat → Option Nat} {ao : String → Option Nat} {r : String}
    (hr : r ∈ liveArrNeed body A k i aa ao) :
    (∃ j, r ∈ A.getD j []) ∨
      (∃ dst f srcs, shadowCall? i.1 = some (dst, f, srcs) ∧ r ∈ callArrOps (aa f) 0 srcs) ∨
      (shadowCall? i.1 = none ∧ r ∈ arrReads i) := by
  unfold liveArrNeed at hr
  dsimp only at hr
  split at hr
  · split at hr
    · exact Or.inl ⟨_, hr⟩
    · simp at hr
  · rcases List.mem_append.mp hr with h | h
    · split at h
      · simp at h
      · exact Or.inl ⟨_, h⟩
    · split at h
      · exact Or.inl ⟨_, h⟩
      · simp at h
  · split at hr <;> rename_i hs <;> rcases List.mem_append.mp hr with h | h
    · exact Or.inr (Or.inl ⟨_, _, _, hs, h⟩)
    · exact Or.inl ⟨_, (List.mem_filter.mp h).1⟩
    · exact Or.inr (Or.inr ⟨hs, h⟩)
    · exact Or.inl ⟨_, (List.mem_filter.mp h).1⟩
  · exact Or.inl ⟨_, hr⟩

theorem mem_liveArrNames_of {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {r : String} {i : LinstrRM} (hi : i ∈ body)
    (h : (∃ dst f srcs, shadowCall? i.1 = some (dst, f, srcs) ∧ r ∈ callArrOps (aa f) 0 srcs) ∨
      (shadowCall? i.1 = none ∧ r ∈ arrReads i)) :
    r ∈ liveArrNames body obs aa := by
  simp only [liveArrNames, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
  refine Or.inr ⟨i, hi, ?_⟩
  rcases h with ⟨dst, f, srcs, hs, h⟩ | ⟨hs, h⟩ <;> simp only [hs] <;> exact h

theorem liveArrNeed_congr {body : List LinstrRM} {A B : Array (List String)} (k : Nat)
    (i : LinstrRM) (aa : String → Nat → Option Nat) (ao : String → Option Nat)
    (h : ∀ j, B.getD j [] = A.getD j []) :
    liveArrNeed body B k i aa ao = liveArrNeed body A k i aa ao := by
  unfold liveArrNeed
  simp only [h]

/-! ## 3. One update of the backward pass -/

/-- One update of the backward pass `liveArrPass` at the position `k`. -/
def passStep (body : List LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) (k : Nat) (A : Array (List String)) : Array (List String) :=
  match body[k]? with
  | some i => A.setIfInBounds k (A.getD k [] ++ liveArrNeed body A k i aa ao).eraseDups
  | none => A

theorem liveArrPass_eq (body : List LinstrRM) (A : Array (List String))
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    liveArrPass body A aa ao = (List.range body.length).foldr (passStep body aa ao) A := rfl

theorem size_passStep {body : List LinstrRM} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (k : Nat) (A : Array (List String)) :
    (passStep body aa ao k A).size = A.size := by
  unfold passStep
  split <;> simp

theorem getD_passStep_ne {body : List LinstrRM} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} {k j : Nat} (A : Array (List String)) (h : j ≠ k) :
    (passStep body aa ao k A).getD j [] = A.getD j [] := by
  unfold passStep
  split
  · simp [Array.getD_eq_getD_getElem?, Ne.symm h]
  · rfl

theorem getD_passStep_self {body : List LinstrRM} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} {k : Nat} {i : LinstrRM} (A : Array (List String))
    (hi : body[k]? = some i) (hk : k < A.size) :
    (passStep body aa ao k A).getD k [] =
      (A.getD k [] ++ liveArrNeed body A k i aa ao).eraseDups := by
  simp [passStep, hi, Array.getD_eq_getD_getElem?, hk]

/-- **The shape of the tables the passes reach**: `n + 1` lists for a body of length `n`,
    the names `obs` at the end, lists without duplicates before the end, and every entry a
    name of `liveArrNames`. -/
def LiveInv (body : List LinstrRM) (obs : List String) (aa : String → Nat → Option Nat)
    (A : Array (List String)) : Prop :=
  A.size = body.length + 1 ∧ A.getD body.length [] = obs ∧
    (∀ j < body.length, (A.getD j []).Nodup) ∧
    ∀ j, ∀ r ∈ A.getD j [], r ∈ liveArrNames body obs aa

theorem liveInv_passStep {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} (k : Nat)
    {A : Array (List String)} (hA : LiveInv body obs aa A) :
    LiveInv body obs aa (passStep body aa ao k A) := by
  obtain ⟨hs, hn, hd, hm⟩ := hA
  rcases hi : body[k]? with _ | i
  · simp only [passStep, hi]
    exact ⟨hs, hn, hd, hm⟩
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hi).1
  have hkA : k < A.size := by omega
  refine ⟨by rw [size_passStep, hs], by rw [getD_passStep_ne _ (by omega), hn], ?_, ?_⟩
  · intro j hj
    by_cases hjk : j = k
    · subst hjk
      rw [getD_passStep_self _ hi hkA]
      exact nodup_eraseDups _
    · rw [getD_passStep_ne _ hjk]
      exact hd j hj
  · intro j r hr
    by_cases hjk : j = k
    · subst hjk
      rw [getD_passStep_self _ hi hkA, List.mem_eraseDups, List.mem_append] at hr
      rcases hr with hr | hr
      · exact hm _ _ hr
      · rcases mem_liveArrNeed_cases hr with ⟨j', hj'⟩ | hc
        · exact hm _ _ hj'
        · exact mem_liveArrNames_of (List.mem_of_getElem? hi) hc
    · rw [getD_passStep_ne _ hjk] at hr
      exact hm _ _ hr

theorem prefix_passStep {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} (k : Nat)
    {A : Array (List String)} (hA : LiveInv body obs aa A) (j : Nat) :
    A.getD j [] <+: (passStep body aa ao k A).getD j [] := by
  by_cases hjk : j = k
  · subst hjk
    rcases hi : body[j]? with _ | i
    · simp [passStep, hi]
    have hk : j < body.length := (List.getElem?_eq_some_iff.mp hi).1
    rw [getD_passStep_self _ hi (by rw [hA.1]; omega)]
    exact prefix_eraseDups_append (hA.2.2.1 j hk) _
  · rw [getD_passStep_ne _ hjk]

/-- **Every entry stays live** across an update, on a body with no refused instruction. -/
theorem pLive_passStep {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hb : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → armOf i ≠ .bad) (k : Nat)
    {A : Array (List String)}
    (hA : ∀ j, ∀ r ∈ A.getD j [], PLive body aa ao obs j r) :
    ∀ j, ∀ r ∈ (passStep body aa ao k A).getD j [], PLive body aa ao obs j r := by
  intro j r hr
  by_cases hjk : j = k
  · subst hjk
    rcases hi : body[j]? with _ | i
    · simp only [passStep, hi] at hr
      exact hA _ _ hr
    by_cases hkA : j < A.size
    · rw [getD_passStep_self _ hi hkA, List.mem_eraseDups, List.mem_append] at hr
      rcases hr with hr | hr
      · exact hA _ _ hr
      · rcases need_of_mem_liveArrNeed (hb _ _ hi) hr with hr | ⟨k', hs, hw, hr⟩
        · exact .read hi hr
        · exact .step hi hs hw (hA _ _ hr)
    · simp [passStep, hi, Array.getD_eq_getD_getElem?,
        hkA] at hr
  · rw [getD_passStep_ne _ hjk] at hr
    exact hA _ _ hr

/-! ## 4. The backward pass -/

theorem foldr_passStep_preserves {body : List LinstrRM} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (P : Array (List String) → Prop)
    (hP : ∀ k A, P A → P (passStep body aa ao k A)) :
    ∀ (l : List Nat) (A : Array (List String)), P A → P (l.foldr (passStep body aa ao) A)
  | [], _, h => h
  | k :: l, A, h => hP k _ (foldr_passStep_preserves P hP l A h)

theorem prefix_foldr_passStep {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} :
    ∀ (l : List Nat) {A : Array (List String)}, LiveInv body obs aa A → ∀ j,
      A.getD j [] <+: (l.foldr (passStep body aa ao) A).getD j []
  | [], _, _, _ => List.prefix_refl _
  | k :: l, A, hA, j =>
      (prefix_foldr_passStep l hA j).trans (prefix_passStep k
        (foldr_passStep_preserves _ (fun k _ h => liveInv_passStep k h) l A hA) j)

/-- **A pass that changes no length leaves a solution**: every name `liveArrNeed` adds at a
    position is already in the table there. -/
theorem need_sub_of_stable {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {A : Array (List String)}
    (hA : LiveInv body obs aa A)
    (hst : ∀ j, ((liveArrPass body A aa ao).getD j []).length = (A.getD j []).length)
    (k : Nat) (i : LinstrRM) (hi : body[k]? = some i) :
    ∀ r ∈ liveArrNeed body A k i aa ao, r ∈ A.getD k [] := by
  intro r hr
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hi).1
  have hsplit : List.range body.length =
      (List.range k ++ [k]) ++ List.map (fun x => k + 1 + x) (List.range (body.length - (k + 1))) := by
    rw [← List.range_succ, ← List.range_add]
    congr 1
    omega
  have hinv := fun l (B : Array (List String)) (h : LiveInv body obs aa B) =>
    foldr_passStep_preserves (ao := ao) _ (fun k _ h => liveInv_passStep k h) l B h
  obtain ⟨R, hR⟩ : ∃ R : List Nat,
      R = List.map (fun x => k + 1 + x) (List.range (body.length - (k + 1))) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = R.foldr (passStep body aa ao) A := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = passStep body aa ao k B := ⟨_, rfl⟩
  have hF : liveArrPass body A aa ao = (List.range k).foldr (passStep body aa ao) C := by
    rw [liveArrPass_eq, hsplit, ← hR, List.foldr_append, List.foldr_append, ← hB, hC]
    rfl
  have hBinv : LiveInv body obs aa B := hB ▸ hinv R A hA
  have hCinv : LiveInv body obs aa C := hC ▸ liveInv_passStep k hBinv
  have hAB : ∀ j, A.getD j [] <+: B.getD j [] := hB ▸ prefix_foldr_passStep R hA
  have hBC : ∀ j, B.getD j [] <+: C.getD j [] := hC ▸ prefix_passStep k hBinv
  have hCF : ∀ j, C.getD j [] <+: (liveArrPass body A aa ao).getD j [] :=
    hF ▸ prefix_foldr_passStep (List.range k) hCinv
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
  rw [← hCA, hC, getD_passStep_self _ hi (by rw [hBinv.1]; omega), List.mem_eraseDups,
    liveArrNeed_congr k i aa ao hBA]
  exact List.mem_append_right _ hr

/-! ## 5. The passes reach the fixpoint within the fuel -/

theorem liveInv_liveArrPass {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {A : Array (List String)}
    (hA : LiveInv body obs aa A) : LiveInv body obs aa (liveArrPass body A aa ao) := by
  rw [liveArrPass_eq]
  exact foldr_passStep_preserves _ (fun k _ h => liveInv_passStep k h) _ _ hA

theorem liveArrIter_preserves {body : List LinstrRM} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (P : Array (List String) → Prop)
    (hP : ∀ A, P A → P (liveArrPass body A aa ao)) :
    ∀ (fuel : Nat) (A : Array (List String)), P A → P (liveArrIter body aa ao fuel A)
  | 0, _, h => h
  | fuel + 1, A, h => by
    simp only [liveArrIter]
    split
    · exact h
    · exact liveArrIter_preserves P hP fuel _ (hP A h)

theorem getD_of_size_le {A : Array (List String)} {j : Nat} (h : A.size ≤ j) :
    A.getD j [] = [] := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

theorem lengths_of_beq {A B : Array (List String)}
    (h : (B.toList.map List.length == A.toList.map List.length) = true) (j : Nat) :
    (B.getD j []).length = (A.getD j []).length := by
  have h' := congrArg (fun l => l[j]?.getD 0) (beq_iff_eq.mp h)
  simp only [List.getElem?_map, Array.getElem?_toList] at h'
  simp only [Array.getD_eq_getD_getElem?]
  cases hB : B[j]? <;> cases hA : A[j]? <;> simp_all

theorem beq_of_lengths {A B : Array (List String)} (hs : B.size = A.size)
    (h : ∀ j, (B.getD j []).length = (A.getD j []).length) :
    (B.toList.map List.length == A.toList.map List.length) = true := by
  refine beq_iff_eq.mpr (List.ext_getElem (by simp [hs]) fun j h1 h2 => ?_)
  have hj := h j
  simp only [List.length_map, Array.length_toList] at h1 h2
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2, Option.getD_some] at hj
  simpa using hj

/-- The total length of the lists of a table before the position `n`. -/
def lenSum (n : Nat) (A : Array (List String)) : Nat :=
  ∑ j ∈ Finset.range n, (A.getD j []).length

theorem lenSum_le {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {A : Array (List String)} (hA : LiveInv body obs aa A) :
    lenSum body.length A ≤ body.length * (liveArrNames body obs aa).length := by
  have hb : ∀ j ∈ Finset.range body.length,
      (A.getD j []).length ≤ (liveArrNames body obs aa).length := fun j hj =>
    List.Nodup.length_le_of_subset (hA.2.2.1 j (Finset.mem_range.mp hj)) (hA.2.2.2 j)
  simpa [lenSum] using Finset.sum_le_card_nsmul _ _ _ hb

/-- **A pass that changes a length increases the total length.** -/
theorem lenSum_lt {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {A : Array (List String)}
    (hA : LiveInv body obs aa A)
    (hne : ¬ ((liveArrPass body A aa ao).toList.map List.length ==
      A.toList.map List.length) = true) :
    lenSum body.length A < lenSum body.length (liveArrPass body A aa ao) := by
  have hA' := liveInv_liveArrPass (ao := ao) hA
  have hpre : ∀ j, A.getD j [] <+: (liveArrPass body A aa ao).getD j [] := fun j => by
    rw [liveArrPass_eq]
    exact prefix_foldr_passStep _ hA j
  obtain ⟨j, hj, hlt⟩ : ∃ j < body.length,
      (A.getD j []).length ≠ ((liveArrPass body A aa ao).getD j []).length := by
    by_contra hall
    push Not at hall
    refine hne (beq_of_lengths (by rw [hA'.1, hA.1]) fun j => ?_)
    rcases Nat.lt_trichotomy j body.length with h | h | h
    · exact (hall j h).symm
    · subst h
      rw [hA'.2.1, hA.2.1]
    · rw [getD_of_size_le (by rw [hA'.1]; omega), getD_of_size_le (by rw [hA.1]; omega)]
  exact Finset.sum_lt_sum (fun j _ => (hpre j).length_le)
    ⟨j, Finset.mem_range.mpr hj, lt_of_le_of_ne (hpre j).length_le hlt⟩

/-- **The passes stop at a stable table** when the fuel exceeds the room left for growth. -/
theorem liveArrIter_stable {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} :
    ∀ (fuel : Nat) (A : Array (List String)), LiveInv body obs aa A →
      body.length * (liveArrNames body obs aa).length < lenSum body.length A + fuel →
      ∀ j, ((liveArrPass body (liveArrIter body aa ao fuel A) aa ao).getD j []).length =
        ((liveArrIter body aa ao fuel A).getD j []).length
  | 0, A, hA, hf => absurd (lenSum_le hA) (by omega)
  | fuel + 1, A, hA, hf => by
    simp only [liveArrIter]
    split
    · rename_i h
      exact lengths_of_beq h
    · rename_i h
      have := lenSum_lt (ao := ao) hA h
      exact liveArrIter_stable fuel _ (liveInv_liveArrPass hA) (by omega)

theorem liveInv_init (body : List LinstrRM) (obs : List String)
    (aa : String → Nat → Option Nat) :
    LiveInv body obs aa ((Array.replicate (body.length + 1) []).setIfInBounds body.length obs) := by
  have hg : ∀ j, ((Array.replicate (body.length + 1) ([] : List String)).setIfInBounds
      body.length obs).getD j [] = if j = body.length then obs else [] := fun j => by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
      Array.getElem?_replicate, Array.size_replicate]
    by_cases h : j = body.length
    · simp [h]
    · simp only [Ne.symm h, ↓reduceIte, h]
      split <;> rfl
  refine ⟨by simp, by simp [hg], fun j hj => by simp [hg, Nat.ne_of_lt hj], fun j r hr => ?_⟩
  rw [hg] at hr
  split at hr
  · simp [liveArrNames, List.mem_eraseDups, hr]
  · simp at hr

theorem liveInv_liveArrTab (body : List LinstrRM) (obs : List String)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    LiveInv body obs aa (liveArrTab body obs aa ao) :=
  liveArrIter_preserves _ (fun _ h => liveInv_liveArrPass h) _ _ (liveInv_init body obs aa)

/-! ## 6. The table is the least certificate -/

/-- **The synthesised liveness table solves the liveness equations** of the body. -/
theorem liveArrTab_needClosed (body : List LinstrRM) (obs : List String)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    NeedClosed body aa ao (fun k r => r ∈ tabAt (liveArrTab body obs aa ao) k) obs := by
  have hT := liveInv_liveArrTab body obs aa ao
  have hst := liveArrIter_stable (ao := ao)
    ((body.length + 1) * (liveArrNames body obs aa).length + 2) _ (liveInv_init body obs aa)
    (by rw [Nat.add_mul, Nat.one_mul]; omega)
  have hsub := need_sub_of_stable hT hst
  refine ⟨fun r hr => ?_, fun k i hi => ⟨fun r hr => ?_, fun k' r hs hw hr => ?_⟩⟩
  · simp only [tabAt]
    rw [hT.2.1]
    exact hr
  · exact hsub k i hi r ((mem_liveArrNeed_of_need body _ k i aa ao).1 r hr)
  · exact hsub k i hi r ((mem_liveArrNeed_of_need body _ k i aa ao).2 k' r hs hw hr)

/-- **Every entry of the synthesised liveness table is live**, on a body with no refused
    instruction. -/
theorem liveArrTab_pLive {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hb : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → armOf i ≠ .bad) :
    ∀ k, ∀ r ∈ tabAt (liveArrTab body obs aa ao) k, PLive body aa ao obs k r := by
  refine liveArrIter_preserves (fun A => ∀ j, ∀ r ∈ A.getD j [], PLive body aa ao obs j r)
    (fun A h => ?_) _ _ ?_
  · rw [liveArrPass_eq]
    exact foldr_passStep_preserves (fun A => ∀ j, ∀ r ∈ A.getD j [], PLive body aa ao obs j r)
      (fun k _ h => pLive_passStep hb k h) _ _ h
  · intro j r hr
    by_cases h : j = body.length
    · subst h
      rw [(liveInv_init body obs aa).2.1] at hr
      exact .obs hr
    · simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, Ne.symm h] at hr
      split at hr <;> simp at hr

/-- An admitted body has no refused instruction. -/
theorem not_bad_of_classOK {σ : String → String} {body : List LinstrRM}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} (hc : ClassOK σ body aa ao) :
    ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → armOf i ≠ .bad := by
  intro k i hi h
  have := hc k i hi
  rw [h] at this
  exact this

/-- **The synthesised liveness table is the least certificate** of an admitted body: it
    solves the liveness equations `NeedClosed` and lies below their least solution
    `PLive`. -/
theorem liveArrCert_least {σ : String → String} {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} (hc : ClassOK σ body aa ao) :
    NeedClosed body aa ao (fun k r => r ∈ tabAt (liveArrTab body obs aa ao) k) obs ∧
      ∀ k, ∀ r ∈ tabAt (liveArrTab body obs aa ao) k, PLive body aa ao obs k r :=
  ⟨liveArrTab_needClosed body obs aa ao, liveArrTab_pLive (not_bad_of_classOK hc)⟩

/-- **The coalescing check accepts at the synthesised table** an admitted body and a renaming
    without real aliasing. -/
theorem coCfgB_liveArrTab {σ : String → String} {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} (hc : ClassOK σ body aa ao)
    (ha : NoRealAlias σ body aa ao obs) :
    coCfgB σ body (tabAt (liveArrTab body obs aa ao)) obs aa ao = true :=
  coCfgB_complete hc (liveArrCert_least hc).1 (liveArrCert_least hc).2 ha

/-- **A renaming without real aliasing fixes every entry of the table at the start** of an
    admitted body. -/
theorem entryFix_liveArrTab {σ : String → String} {body : List LinstrRM} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} (hc : ClassOK σ body aa ao)
    (ha : NoRealAlias σ body aa ao obs) :
    (tabAt (liveArrTab body obs aa ao) 0).all (fun x => σ x == x) = true :=
  List.all_eq_true.mpr fun x hx => beq_iff_eq.mpr (ha.2 x ((liveArrCert_least hc).2 0 x hx))

/-! ## 7. The coalescing stage of the region gate -/

theorem ite_ne_some {c : Prop} [Decidable c] {s s' : String} {x : Option String}
    (hs : s ≠ s') (hx : x ≠ some s') : (if c then some s else x) ≠ some s' := by
  split
  · exact fun h => hs (Option.some.inj h)
  · exact hx

/-- **The coalescing stage of the region gate accepts** when the code `C` with the result
    copies is admitted and its alias map `ρ` has no real aliasing: `regionCoStage` refuses
    neither at the coalescing check `coCfgB` nor at the entry condition `coEntryFix`. -/
theorem regionCoStage_coalesce (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand)
    (cert : List (String × String)) (callee : Option CalleeTab) (fn : String)
    (hc : ClassOK (canonMemrefName (regionAliasTab σ nm t callee res (regionCoCode σ nm t
        (calleeCodeT callee code) res (regionCopy σ nm t callee (calleeCodeT callee code) res))))
      (regionCoCode σ nm t (calleeCodeT callee code) res
        (regionCopy σ nm t callee (calleeCodeT callee code) res))
      (calleeAAT callee) (calleeAOT callee))
    (ha : NoRealAlias (canonMemrefName (regionAliasTab σ nm t callee res (regionCoCode σ nm t
        (calleeCodeT callee code) res (regionCopy σ nm t callee (calleeCodeT callee code) res))))
      (regionCoCode σ nm t (calleeCodeT callee code) res
        (regionCopy σ nm t callee (calleeCodeT callee code) res))
      (calleeAAT callee) (calleeAOT callee)
      (regionCoObs t (regionOut (regionCopy σ nm t callee (calleeCodeT callee code) res) res))) :
    regionCoStage σ nm body t code res cert callee fn ≠ some "coCfgB" ∧
      regionCoStage σ nm body t code res cert callee fn ≠ some "coEntryFix" := by
  have h1 := coCfgB_liveArrTab hc ha
  have h2 := entryFix_liveArrTab hc ha
  unfold regionCoStage
  dsimp only
  rw [h1, h2]
  simp only [Bool.true_eq_false, ite_false]
  constructor <;> (repeat refine ite_ne_some (by simp) ?_) <;>
    exact (Option.some_ne_none _).symm

/-! ## 8. Admitted shapes from the class check, the tags and the calls -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (clsB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (callShadow eq_callShadow_of_shadowCall?)

theorem armOf_ne_bad_of_clsB {i : LinstrRM} (h : clsB i = true) : armOf i ≠ .bad := by
  unfold armOf
  split
  · simp
  split
  · simp
  split
  · simp
  split
  · simp
  split
  · simp
  · simp
  · simp
  · split <;> simp
  · exfalso
    unfold clsB at h
    split at h <;> simp_all
    rename_i hx _
    exact hx _ _ rfl

theorem shadowCall?_of_armOf_call {i : LinstrRM} {dst f : String} {srcs : List LOperand}
    (h : armOf i = .call dst f srcs) : shadowCall? i.1 = some (dst, f, srcs) := by
  unfold armOf at h
  split at h
  · cases h; assumption
  · split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    split at h <;> try cases h
    split at h <;> cases h

theorem arrShapeB_of_armOf_arr {i : LinstrRM} (h : armOf i = .arr) : arrShapeB i = true := by
  unfold armOf at h
  split at h
  · cases h
  · split at h
    · assumption
    split at h
    · cases h
    split at h
    · cases h
    split at h <;> try cases h
    split at h <;> cases h

/-- Every label of a body is at a position `p` with `p + 1 ≤ body.length`. -/
theorem jumpOK_all (body : List LinstrRM) (lbl : LLabel) : JumpOK body lbl := by
  intro p hp
  have := JasminLsemLabeled.findLabel_lt_length lbl (body.map Prod.fst) p hp
  simp at this
  omega

/-- A runtime-indexed load or store is read by no recogniser of the flag machine, before and
    after the renaming of its array positions. -/
theorem plainArrB_of_arrShapeB {i : LinstrRM} (h : arrShapeB i = true) (σ : String → String) :
    plainArrB i = true ∧ plainArrB (renArr σ i) = true := by
  rcases i with ⟨w, t⟩
  cases t <;> simp only [arrShapeB, Bool.false_eq_true] at h
  case storeImm a n =>
    obtain ⟨⟨d, b, v, k⟩, hl⟩ := Option.isSome_iff_exists.mp h
    unfold storeImmStruct? at hl
    split at hl
    · split at hl
      · subst_vars
        simp [plainArrB, renArr, renStoreImm, isLopnB, cmpArgs?, movRegArgs?, carryArgs?,
          wideArgs?, aluFlagOp?]
      · cases hl
    · cases hl
  · obtain ⟨⟨d, b, x⟩, hl⟩ := Option.isSome_iff_exists.mp h
    unfold loadStruct? at hl
    split at hl
    · split at hl
      · subst_vars
        simp [plainArrB, renArr, renLoad, isLopnB, cmpArgs?, movRegArgs?, carryArgs?, wideArgs?,
          aluFlagOp?]
      · cases hl
    · cases hl
  · obtain ⟨⟨d, b, x, v⟩, hl⟩ := Option.isSome_iff_exists.mp h
    unfold storeStruct? at hl
    split at hl
    · split at hl
      · subst_vars
        simp [plainArrB, renArr, renStore, isLopnB, cmpArgs?, movRegArgs?, carryArgs?, wideArgs?,
          aluFlagOp?, withWidthTag]
      · cases hl
    · cases hl
  · obtain ⟨d, hl⟩ := Option.isSome_iff_exists.mp h
    unfold zeroStruct? at hl
    split at hl
    · split at hl
      · subst_vars
        refine ⟨plainArrB_zero _ _ _, ?_⟩
        simp only [renArr, renZero, ite_true]
        exact plainArrB_zero _ _ _
      · cases hl
    · cases hl

/-- The conditions of `ClassA` at the shadow instructions of calls of `body`: the tag is no
    load or store tag, `σ` fixes the word operands, and at a word result `σ` fixes the
    destination. -/
def CallFix (σ : String → String) (body : List LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) : Prop :=
  ∀ i ∈ body, ∀ dst f srcs, shadowCall? i.1 = some (dst, f, srcs) →
    callTagB i.2 = true ∧ callOpsFix σ (aa f) 0 srcs = true ∧ (ao f = none → σ dst = dst)

/-- **`ClassOK` from three instruction-wise conditions**: every instruction passes the class
    check `clsB` and has no compile-time-offset tag (`TagOK`), and the shadow instructions
    of calls meet `CallFix`. -/
theorem classOK_of {σ : String → String} {body : List LinstrRM}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hcls : ∀ i ∈ body, clsB i = true) (htag : ∀ i ∈ body, TagOK i)
    (hcall : CallFix σ body aa ao) : ClassOK σ body aa ao := by
  intro k i hi
  have hm := List.mem_of_getElem? hi
  rcases harm : armOf i with ⟨dst, f, srcs⟩ | _ | _ | lbl | lbl | _ | _
  · exact hcall i hm dst f srcs (shadowCall?_of_armOf_call harm)
  · have hs := plainArrB_of_arrShapeB (arrShapeB_of_armOf_arr harm) σ
    exact ⟨hs.1, hs.2, htag i hm⟩
  · trivial
  · exact jumpOK_all body lbl
  · exact jumpOK_all body lbl
  · exact htag i hm
  · exact armOf_ne_bad_of_clsB (hcls i hm) harm

/-! ## 9. The tags and the shadow instructions of the export -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect JasminOp JasminBinOp
  JasminCmp)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB scalarMemNB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data x86Data_loopGuard
  x86Data_zeroTripGuard)

theorem tagOK_movI (dst : String) (src : LOperand) : TagOK (movI dst src) := by
  simp [TagOK, movI]

theorem tagOK_guardI (w : LinstrR) : TagOK (guardI w) := by simp [TagOK, guardI]

theorem tagOK_labelI (l : LLabel) : TagOK (labelI l) := by simp [TagOK, labelI]

theorem tagOK_seedMoves (car : List String) (ops : List LOperand) :
    ∀ i ∈ seedMoves car ops, TagOK i := by
  intro i hi
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  exact tagOK_movI _ _

theorem tagOK_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    ∀ i ∈ parMoves D tgts ops, TagOK i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi <;> obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi <;>
    exact tagOK_movI _ _

theorem tagOK_arrMoves (z t : String) (mv : List ArrMove) : ∀ i ∈ arrMoves z t mv, TagOK i := by
  intro i hi
  obtain ⟨a, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> simp [TagOK]

theorem tagOK_typedMoves (z t : String) (tp : List (JasminTy × String × String)) :
    ∀ i ∈ typedMoves z t tp, TagOK i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact tagOK_arrMoves _ _ _ i hi
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
    exact tagOK_movI _ _

theorem tagOK_arrParMoves (z t : String) (D : Nat) (mv : List ArrMove) :
    ∀ i ∈ arrParMoves z t D mv, TagOK i := by
  intro i hi
  unfold arrParMoves at hi
  split at hi
  · exact tagOK_arrMoves _ _ _ i hi
  · rcases List.mem_append.mp hi with hi | hi <;> exact tagOK_arrMoves _ _ _ i hi

theorem tagOK_advanceOps (idx ctr : String) : ∀ i ∈ advanceOps idx ctr, TagOK i := by
  intro i hi
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> simp [TagOK]

theorem tagOK_flagWord (I : IsaData) (r z : String) (op : LOperand) :
    ∀ i ∈ flagWord I r z op, TagOK i := by
  intro i hi
  unfold flagWord at hi
  split at hi
  · split at hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> simp [TagOK, movImmI, movI]
    · cases hi
  · rw [List.mem_singleton.mp hi]
    exact tagOK_movI _ _

theorem tagOK_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    ∀ i ∈ ifResMoves rs d D ops, TagOK i := by
  intro i hi
  unfold ifResMoves at hi
  rcases List.mem_append.mp hi with hi | hi
  · split at hi
    · cases hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact tagOK_movI _ _
      · exact tagOK_arrParMoves _ _ _ _ i hi
  · exact tagOK_parMoves _ _ _ i hi

theorem tagOK_bindOps (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) : ∀ i ∈ bindOps nArgs e d, TagOK i := by
  intro i hi
  simp only [bindOps, straightOpsMem, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  split <;> simp [TagOK]

theorem forArrFrame_tagOK (I : IsaData) (d n : Nat) (cs : List JasminTy)
    (initOps : List LOperand) (countOp : LOperand) (bodyC : List LinstrRM)
    (bodyOps : List LOperand) (bodyD : Nat) (hb : ∀ i ∈ bodyC, TagOK i) :
    ∀ i ∈ forArrFrame d n cs initOps countOp bodyC bodyOps bodyD I, TagOK i := by
  intro i hi
  simp only [forArrFrame, List.mem_append, List.mem_cons, List.mem_map] at hi
  rcases hi with rfl | hi | hi | ⟨g, -, rfl⟩ | rfl | hi | rfl | hi | hi | hi | ⟨g, -, rfl⟩
    | rfl | rfl | hi
  · exact tagOK_movI _ _
  · exact tagOK_typedMoves _ _ _ i hi
  · exact tagOK_seedMoves _ _ i hi
  · exact tagOK_guardI g
  · exact tagOK_labelI _
  · exact hb i hi
  · exact tagOK_movI _ _
  · exact tagOK_arrParMoves _ _ _ _ i hi
  · exact tagOK_parMoves _ _ _ i hi
  · exact tagOK_advanceOps _ _ i hi
  · exact tagOK_guardI g
  · exact tagOK_labelI _
  · exact tagOK_movI _ _
  · exact tagOK_typedMoves _ _ _ i hi

theorem whileFrame_tagOK (I : IsaData) (d n nCar : Nat) (initOps : List LOperand)
    (bodyC : List LinstrRM) (flagOp : LOperand) (bodyOps : List LOperand) (bodyD : Nat)
    (hb : ∀ i ∈ bodyC, TagOK i) :
    ∀ i ∈ whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD I, TagOK i := by
  intro i hi
  simp only [whileFrame, List.mem_append, List.mem_cons, List.mem_map] at hi
  rcases hi with hi | rfl | hi | hi | hi | ⟨g, -, rfl⟩
  · exact tagOK_seedMoves _ _ i hi
  · exact tagOK_labelI _
  · exact hb i hi
  · exact tagOK_flagWord _ _ _ _ i hi
  · exact tagOK_parMoves _ _ _ i hi
  · exact tagOK_guardI g

theorem ifFrame_tagOK (I : IsaData) (fn : String) (d n : Nat) (rs : List JasminTy)
    (condOp : LOperand) (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat)
    (elsC : List LinstrRM) (elsOps : List LOperand) (elsD : Nat)
    (ht : ∀ i ∈ thnC, TagOK i) (he : ∀ i ∈ elsC, TagOK i) :
    ∀ i ∈ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD I, TagOK i := by
  intro i hi
  simp only [ifFrame, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
    or_false] at hi
  rcases hi with hi | ⟨g, -, rfl⟩ | rfl | hi | hi | rfl | ⟨g, -, rfl⟩ | rfl | hi | hi | rfl
  · exact tagOK_flagWord _ _ _ _ i hi
  · exact tagOK_guardI g
  · exact tagOK_labelI _
  · exact ht i hi
  · exact tagOK_ifResMoves _ _ _ _ i hi
  · exact tagOK_movI _ _
  · exact tagOK_guardI g
  · exact tagOK_labelI _
  · exact he i hi
  · exact tagOK_ifResMoves _ _ _ _ i hi
  · exact tagOK_labelI _

/-- **The export has no compile-time-offset tag**, at every instruction set. -/
theorem exportR_tagOK (nArgs : Nat) (fn : String) (I : IsaData)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n I = some r →
      ∀ i ∈ r.code, TagOK i := by
  induction p with
  | ret vs =>
      intro d n r h i hi
      simp only [exportR, Option.some.injEq] at h
      subst h
      cases hi
  | var e k ih =>
      intro d n r h i hi
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact tagOK_bindOps nArgs e d i hi
      · exact ih _ _ _ hk i hi
  | forLoop count inits body k ihb ihk =>
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact forArrFrame_tagOK I _ _ _ _ _ _ _ _ (ihb _ _ _ hb) i hi
      · exact ihk _ _ _ hk i hi
  | ifThenElse cond thn els k iht ihe ihk =>
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact ifFrame_tagOK I _ _ _ _ _ _ _ _ _ _ _ (iht _ _ _ ht) (ihe _ _ _ he) i hi
      · exact ihk _ _ _ hk i hi
  | whileLoop inits body k ihb ihk =>
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact whileFrame_tagOK I _ _ _ _ _ _ _ _ (ihb _ _ _ hb) i hi
      · exact ihk _ _ _ hk i hi
  | call f args k ih =>
      intro d n r h i hi
      obtain ⟨-, rk, hk, rfl⟩ := exportR_call_eq_some.mp h
      rcases List.mem_append.mp hi with hi | hi
      · rw [List.mem_singleton.mp hi]; simp [TagOK, callI]
      · exact ih _ _ _ hk i hi

theorem shadowCall?_lopn {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : "CALL:".toList.isPrefixOf o.toList = false) : shadowCall? (.Lopn ds o ss) = none := by
  unfold shadowCall?
  split
  · rename_i heq
    simp only [LinstrR.Lopn.injEq] at heq
    obtain ⟨-, rfl, -⟩ := heq
    rw [ite_eq_right (by rw [h]; exact Bool.false_ne_true)]
  · rfl

theorem callPre_cons {c : Char} {t : List Char} (hc : c ≠ 'C') :
    "CALL:".toList.isPrefixOf (c :: t) = false := by
  rw [show "CALL:".toList = ['C', 'A', 'L', 'L', ':'] from by decide]
  simp [List.isPrefixOf, Ne.symm hc]

theorem callPre_withWidthTag (w : Nat) {m : String} {c : Char} {t : List Char}
    (hm : m.toList = c :: t) (hc : c ≠ 'C') :
    "CALL:".toList.isPrefixOf (withWidthTag w m).toList = false := by
  unfold withWidthTag
  split
  · rw [String.toList_append, hm]; exact callPre_cons hc
  · simp only [String.toList_append, hm, List.cons_append]; exact callPre_cons hc

/-- A pattern without `'^'` is a prefix of `l ++ '^' :: t` exactly when it is a
    prefix of `l ++ ['^']`. -/
theorem isPrefixOf_append_caret {p l : List Char} (t : List Char) (hp : '^' ∉ p) :
    p.isPrefixOf (l ++ '^' :: t) = p.isPrefixOf (l ++ ['^']) := by
  induction p generalizing l with
  | nil => simp_all
  | cons a p ih =>
    cases l with
    | nil =>
      grind
    | cons b l =>
      grind

theorem callPre_withWidthTag_lit (w : Nat) {m : String}
    (h1 : "CALL:".toList.isPrefixOf (m ++ "^").toList = false)
    (h2 : "CALL:".toList.isPrefixOf (m ++ ":64").toList = false) :
    "CALL:".toList.isPrefixOf (withWidthTag w m).toList = false := by
  by_cases hw : w = 64
  · subst hw
    assumption
  · rw [toList_withWidthTag_of_ne hw, isPrefixOf_append_caret _ (by decide)]
    simp_all

theorem callPre_binOpName (w : Nat) (b : JasminBinOp) :
    "CALL:".toList.isPrefixOf (withWidthTag w (binOpName b)).toList = false := by
  cases b <;> exact callPre_withWidthTag_lit w (by decide) (by decide)

theorem callPre_cmpName (w : Nat) (c : JasminCmp) :
    "CALL:".toList.isPrefixOf (withWidthTag w (cmpName c)).toList = false := by
  cases c <;> exact callPre_withWidthTag_lit w (by decide) (by decide)

theorem callPre_castWMnem (w w' : Nat) :
    "CALL:".toList.isPrefixOf (castWMnem w w').toList = false := by
  unfold castWMnem
  repeat' split
  all_goals decide

theorem callPre_imm {s : String} {c : Char} {t : List Char} (hs : s.toList = c :: t)
    (hc : c ≠ 'C') (w n : Nat) :
    "CALL:".toList.isPrefixOf (withWidthTag w (s ++ toString n)).toList = false :=
  callPre_withWidthTag w (by rw [String.toList_append, hs]; rfl) hc

/-- **An operation of the stack-memory fragment is no shadow instruction of a call.** -/
theorem shadowCall?_opToLinstrR {op : JasminOp} (hop : opMemB op = true) (dst : String)
    (srcs : List LOperand) : shadowCall? (opToLinstrR op dst srcs) = none := by
  cases op <;> simp only [opMemB, Bool.false_eq_true] at hop <;> simp only [opToLinstrR]
  case stackZero => exact shadowCall?_lopn (by decide)
  case stackStoreImm => exact shadowCall?_lopn (by decide)
  all_goals (try split) <;> (try split) <;> apply shadowCall?_lopn
  · exact callPre_binOpName _ _
  · decide
  · decide
  · decide
  · decide
  · exact callPre_castWMnem _ _
  · decide
  · decide
  · exact callPre_withWidthTag_lit _ (by decide) (by decide)
  · exact callPre_withWidthTag_lit _ (by decide) (by decide)
  · exact callPre_withWidthTag_lit _ (by decide) (by decide)
  · exact callPre_withWidthTag_lit _ (by decide) (by decide)
  · exact callPre_imm (show "SHR:".toList = ['S', 'H', 'R', ':'] from by decide) (by decide) _ _
  · exact callPre_imm (show "SAR:".toList = ['S', 'A', 'R', ':'] from by decide) (by decide) _ _
  · exact callPre_imm (show "SHL:".toList = ['S', 'H', 'L', ':'] from by decide) (by decide) _ _
  · exact callPre_withWidthTag_lit _ (by decide) (by decide)
  · exact callPre_cmpName _ _
  · exact callPre_cmpName _ _

/-- The instruction is no shadow instruction of a call. -/
def NoShadow (i : LinstrRM) : Prop := shadowCall? i.1 = none

theorem noShadow_movI (dst : String) (src : LOperand) : NoShadow (movI dst src) :=
  shadowCall?_lopn (callPre_withWidthTag_lit 64 (by decide) (by decide))

theorem noShadow_labelI (l : LLabel) : NoShadow (labelI l) := rfl

theorem noShadow_x86Guards :
    (∀ c t e, ∀ i ∈ (x86Data.zeroTripGuard c t e).map guardI, NoShadow i) ∧
      ∀ c t, ∀ i ∈ (x86Data.loopGuard c t).map guardI, NoShadow i := by
  constructor
  · intro c t e i hi
    rw [x86Data_zeroTripGuard] at hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact shadowCall?_lopn (callPre_withWidthTag_lit 64 (by decide) (by decide))
    · rfl
  · intro c t i hi
    rw [x86Data_loopGuard] at hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact shadowCall?_lopn (callPre_withWidthTag_lit 64 (by decide) (by decide))
    · rfl

/-- **The guards and the select of an instruction set contain no shadow instruction of a
    call.** The instructions of the zero-trip guard and of the back-edge guard, and the select
    `Lopn [r] m [f, r, z]` at the select mnemonic `m`, are no shadow instruction of a call. -/
structure GuardsNoShadow (I : IsaData) : Prop where
  /-- The zero-trip guard contains no shadow instruction of a call. -/
  zeroTrip : ∀ (c : String) (t e : LLabel), ∀ i ∈ (I.zeroTripGuard c t e).map guardI,
    NoShadow i
  /-- The back-edge guard contains no shadow instruction of a call. -/
  loop : ∀ (c : String) (t : LLabel), ∀ i ∈ (I.loopGuard c t).map guardI, NoShadow i
  /-- The select at the select mnemonic is no shadow instruction of a call. -/
  select : ∀ m, I.selectMnemonic = some m → ∀ r f z : String,
    NoShadow (.Lopn [.reg r] (withWidthTag 64 m) [.reg f, .reg r, .reg z], .reg none)

/-- The guards and the select of x86 satisfy `GuardsNoShadow`. -/
theorem x86Data_guardsNoShadow : GuardsNoShadow x86Data where
  zeroTrip := noShadow_x86Guards.1
  loop := noShadow_x86Guards.2
  select m hm _ _ _ := by
    rw [show x86Data.selectMnemonic = some "CMOV" from rfl, Option.some.injEq] at hm
    subst hm
    exact shadowCall?_lopn (callPre_withWidthTag_lit 64 (by decide) (by decide))

theorem noShadow_seedMoves (car : List String) (ops : List LOperand) :
    ∀ i ∈ seedMoves car ops, NoShadow i := by
  intro i hi
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  exact noShadow_movI _ _

theorem noShadow_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    ∀ i ∈ parMoves D tgts ops, NoShadow i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi <;> obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi <;>
    exact noShadow_movI _ _

theorem noShadow_arrMoves (z t : String) (mv : List ArrMove) :
    ∀ i ∈ arrMoves z t mv, NoShadow i := by
  intro i hi
  obtain ⟨a, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact shadowCall?_lopn (by decide)

theorem noShadow_typedMoves (z t : String) (tp : List (JasminTy × String × String)) :
    ∀ i ∈ typedMoves z t tp, NoShadow i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact noShadow_arrMoves _ _ _ i hi
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
    exact noShadow_movI _ _

theorem noShadow_arrParMoves (z t : String) (D : Nat) (mv : List ArrMove) :
    ∀ i ∈ arrParMoves z t D mv, NoShadow i := by
  intro i hi
  unfold arrParMoves at hi
  split at hi
  · exact noShadow_arrMoves _ _ _ i hi
  · rcases List.mem_append.mp hi with hi | hi <;> exact noShadow_arrMoves _ _ _ i hi

theorem noShadow_advanceOps (idx ctr : String) : ∀ i ∈ advanceOps idx ctr, NoShadow i := by
  intro i hi
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;>
    exact shadowCall?_lopn (callPre_withWidthTag_lit 64 (by decide) (by decide))

theorem noShadow_flagWord {I : IsaData} (hI : GuardsNoShadow I) (r z : String)
    (op : LOperand) : ∀ i ∈ flagWord I r z op, NoShadow i := by
  intro i hi
  unfold flagWord at hi
  split at hi
  · split at hi
    · rename_i m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact noShadow_movI _ _
      · exact noShadow_movI _ _
      · exact hI.select m hm _ _ _
    · cases hi
  · rw [List.mem_singleton.mp hi]
    exact noShadow_movI _ _

theorem noShadow_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    ∀ i ∈ ifResMoves rs d D ops, NoShadow i := by
  intro i hi
  unfold ifResMoves at hi
  rcases List.mem_append.mp hi with hi | hi
  · split at hi
    · cases hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact noShadow_movI _ _
      · exact noShadow_arrParMoves _ _ _ _ i hi
  · exact noShadow_parMoves _ _ _ i hi

theorem noShadow_bindOps (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (hop : opMemB e.op = true) (d : Nat) :
    ∀ i ∈ bindOps nArgs e d, NoShadow i := by
  intro i hi
  simp only [bindOps, straightOpsMem, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  split <;> try exact shadowCall?_opToLinstrR hop _ _
  split
  all_goals first
    | exact shadowCall?_opToLinstrR hop _ _
    | exact shadowCall?_lopn (callPre_withWidthTag_lit _ (by decide) (by decide))

theorem opMemB_of_bindMemNB {Γ : Ctxt jasminDialect} {t : JasminTy}
    {e : Expr jasminDialect Γ t} (h : bindMemNB e = true) : opMemB e.op = true := h

theorem forArrFrame_noShadow {I : IsaData} (hI : GuardsNoShadow I) (d n : Nat)
    (cs : List JasminTy) (initOps : List LOperand) (countOp : LOperand) (bodyC : List LinstrRM)
    (bodyOps : List LOperand) (bodyD : Nat) (hb : ∀ i ∈ bodyC, NoShadow i) :
    ∀ i ∈ forArrFrame d n cs initOps countOp bodyC bodyOps bodyD I, NoShadow i := by
  intro i hi
  simp only [forArrFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with rfl | hi | hi | hi | rfl | hi | rfl | hi | hi | hi | hi | rfl | rfl | hi
  · exact noShadow_movI _ _
  · exact noShadow_typedMoves _ _ _ i hi
  · exact noShadow_seedMoves _ _ i hi
  · exact hI.zeroTrip _ _ _ i hi
  · exact noShadow_labelI _
  · exact hb i hi
  · exact noShadow_movI _ _
  · exact noShadow_arrParMoves _ _ _ _ i hi
  · exact noShadow_parMoves _ _ _ i hi
  · exact noShadow_advanceOps _ _ i hi
  · exact hI.loop _ _ i hi
  · exact noShadow_labelI _
  · exact noShadow_movI _ _
  · exact noShadow_typedMoves _ _ _ i hi

theorem whileFrame_noShadow {I : IsaData} (hI : GuardsNoShadow I) (d n nCar : Nat)
    (initOps : List LOperand) (bodyC : List LinstrRM) (flagOp : LOperand)
    (bodyOps : List LOperand) (bodyD : Nat) (hb : ∀ i ∈ bodyC, NoShadow i) :
    ∀ i ∈ whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD I, NoShadow i := by
  intro i hi
  simp only [whileFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with hi | rfl | hi | hi | hi | hi
  · exact noShadow_seedMoves _ _ i hi
  · exact noShadow_labelI _
  · exact hb i hi
  · exact noShadow_flagWord hI _ _ _ i hi
  · exact noShadow_parMoves _ _ _ i hi
  · exact hI.loop _ _ i hi

theorem ifFrame_noShadow {I : IsaData} (hI : GuardsNoShadow I) (fn : String) (d n : Nat)
    (rs : List JasminTy) (condOp : LOperand) (thnC : List LinstrRM) (thnOps : List LOperand)
    (thnD : Nat) (elsC : List LinstrRM) (elsOps : List LOperand) (elsD : Nat)
    (ht : ∀ i ∈ thnC, NoShadow i) (he : ∀ i ∈ elsC, NoShadow i) :
    ∀ i ∈ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD I, NoShadow i := by
  intro i hi
  simp only [ifFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | rfl | hi | hi | rfl | hi | rfl | hi | hi | rfl
  · exact noShadow_flagWord hI _ _ _ i hi
  · exact hI.zeroTrip _ _ _ i hi
  · exact noShadow_labelI _
  · exact ht i hi
  · exact noShadow_ifResMoves _ _ _ _ i hi
  · exact noShadow_movI _ _
  · exact hI.loop _ _ i hi
  · exact noShadow_labelI _
  · exact he i hi
  · exact noShadow_ifResMoves _ _ _ _ i hi
  · exact noShadow_labelI _

/-- **The export of a program without `call` that passes `regionExportableB` has no shadow
    instruction of a call**, over an instruction set whose guards and select
    (`GuardsNoShadow`) contain none. -/
theorem exportR_noShadow {I : IsaData} (hI : GuardsNoShadow I) (nArgs : Nat) (fn : String)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (hp : regionExportableB p = true) (hc : p.callFree = true) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n I = some r →
      ∀ i ∈ r.code, NoShadow i := by
  induction p with
  | ret vs =>
      intro d n r h i hi
      simp only [exportR, Option.some.injEq] at h
      subst h
      cases hi
  | var e k ih =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree] at hc
      intro d n r h i hi
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact noShadow_bindOps nArgs e (opMemB_of_bindMemNB hp.1) d i hi
      · exact ih hp.2 hc _ _ _ hk i hi
  | forLoop count inits body k ihb ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact forArrFrame_noShadow hI _ _ _ _ _ _ _ _ (ihb hp.1 hc.1 _ _ _ hb) i hi
      · exact ihk hp.2 hc.2 _ _ _ hk i hi
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact ifFrame_noShadow hI _ _ _ _ _ _ _ _ _ _ _ (iht hp.1.1 hc.1.1 _ _ _ ht)
          (ihe hp.1.2 hc.1.2 _ _ _ he) i hi
      · exact ihk hp.2 hc.2 _ _ _ hk i hi
  | whileLoop inits body k ihb ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact whileFrame_noShadow hI _ _ _ _ _ _ _ _ (ihb hp.1.2 hc.1 _ _ _ hb) i hi
      · exact ihk hp.2 hc.2 _ _ _ hk i hi
  | call f args k ih =>
      simp [NFProg.callFree] at hc

/-! ## 10. The coalesced code of a region export -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (CallShape commonCallsT? commonCallT?
  commonSeq commonOps commonFreshB shadowCall?_movI)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (shadowCall?_callShadow)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (mulxFree)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (movesOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (canonMemrefName)

theorem tagOK_movesOf (ps : List (String × String)) : ∀ i ∈ movesOf ps, TagOK i := by
  intro i hi
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  simp [TagOK]

theorem noShadow_movesOf (ps : List (String × String)) : ∀ i ∈ movesOf ps, NoShadow i := by
  intro i hi
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  exact shadowCall?_lopn (by decide)

theorem tagOK_resCopyCode (src D : String) (m : Nat) : ∀ i ∈ resCopyCode src D m, TagOK i := by
  intro i hi
  obtain ⟨j, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp [TagOK, movImmI, movI]

theorem noShadow_resCopyCode (src D : String) (m : Nat) :
    ∀ i ∈ resCopyCode src D m, NoShadow i := by
  intro i hi
  obtain ⟨j, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact noShadow_movI _ _
  · exact shadowCall?_lopn (by decide)
  · exact shadowCall?_lopn (by decide)

theorem tagOK_regionCoCode (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cp : Option (String × String × Nat))
    (h : ∀ i ∈ code, TagOK i) : ∀ i ∈ regionCoCode σ nm t code res cp, TagOK i := by
  intro i hi
  unfold regionCoCode at hi
  split at hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact h i hi
    · exact tagOK_movesOf _ i hi
  · rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact h i hi
      · exact tagOK_movesOf _ i hi
    · exact tagOK_resCopyCode _ _ _ i hi

theorem noShadow_regionCoCode (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cp : Option (String × String × Nat))
    (h : ∀ i ∈ code, NoShadow i) : ∀ i ∈ regionCoCode σ nm t code res cp, NoShadow i := by
  intro i hi
  unfold regionCoCode at hi
  split at hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact h i hi
    · exact noShadow_movesOf _ i hi
  · rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact h i hi
      · exact noShadow_movesOf _ i hi
    · exact noShadow_resCopyCode _ _ _ i hi

/-- **The instructions of a body rewritten onto the common names of a table**: an instruction
    of the body that is no shadow instruction, a copy, or the shadow instruction of a call of
    a symbol `g` with an entry `(sh, args, res)` in `tab` on the operands `commonOps`, whose
    destination is the destination of a call of `g` in the body at an out result and `res` at
    a word result. -/
theorem mem_commonCallsT? {tab : String → Option (CallShape × List String × String)} :
    ∀ {B B' : List LinstrRM}, commonCallsT? tab B = some B' → ∀ j ∈ B',
      (j ∈ B ∧ shadowCall? j.1 = none) ∨ (∃ x y, j = LprogCallCut.movI x y) ∨
        ∃ d g sh args res xs, tab g = some (sh, args, res) ∧
          j = (callShadow d g ((commonOps sh 0 args xs).map LOperand.reg), .reg none) ∧
          (sh.out = true → ∃ j0 ∈ B, ∃ srcs, shadowCall? j0.1 = some (d, g, srcs)) ∧
          (sh.out = false → d = res)
  | [], _, h, j, hj => by cases h; cases hj
  | i :: B, _, h, j, hj => by
      obtain ⟨is, his, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨B₁, hB₁, rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_append.mp hj with hj | hj
      · unfold commonCallT? at his
        split at his
        · rename_i hn
          cases his
          rw [List.mem_singleton.mp hj]
          exact Or.inl ⟨List.mem_cons_self, hn⟩
        · rename_i d g srcs hs
          split at his
          · rename_i sh args res xs htab hxs
            split at his
            · cases his
              simp only [commonSeq, List.mem_append, List.mem_map] at hj
              rcases hj with ⟨p, -, rfl⟩ | hj
              · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
              · split at hj
                · rename_i ho
                  rw [List.mem_singleton.mp hj]
                  exact Or.inr (Or.inr ⟨d, g, sh, args, res, xs, htab, rfl,
                    fun _ => ⟨i, List.mem_cons_self, srcs, hs⟩, fun h' => by simp [ho] at h'⟩)
                · rename_i ho
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                  rcases hj with rfl | rfl
                  · exact Or.inr (Or.inr ⟨res, g, sh, args, res, xs, htab, rfl,
                      fun h' => absurd h' ho, fun _ => rfl⟩)
                  · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
            · cases his
          · cases his
      · rcases mem_commonCallsT? hB₁ j hj with ⟨h1, h2⟩ | h |
          ⟨d, g, sh, args, res, xs, ht, h1, h2, h3⟩
        · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
        · exact Or.inr (Or.inl h)
        · refine Or.inr (Or.inr ⟨d, g, sh, args, res, xs, ht, h1, fun ho => ?_, h3⟩)
          obtain ⟨j0, hj0, hs⟩ := h2 ho
          exact ⟨j0, List.mem_cons_of_mem _ hj0, hs⟩

/-- The function a table holds at a symbol is a function of the table with that name. -/
theorem calleeTab_lookup_some {T : CalleeTab} {g : String} {c : CalleeData}
    (h : T.lookup g = some c) : c ∈ T.fns ∧ c.name = g := by
  unfold CalleeTab.lookup at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- An entry of the common names of a table is the shape, the argument names and the result
    register of the function the table holds at the symbol. -/
theorem calleeTab_common_some {T : CalleeTab} {g : String} {sh : CallShape}
    {args : List String} {res : String} (h : T.common g = some (sh, args, res)) :
    ∃ c, T.lookup g = some c ∧ c.shape = sh ∧ c.args = args ∧ c.resReg = res := by
  simp only [CalleeTab.common, Option.map_eq_some_iff, Prod.mk.injEq] at h
  exact h

/-- **The out symbols of a table with distinct names**: a symbol at which the table holds a
    function with a word result is no out symbol. -/
theorem calleeTab_outs_lookup {T : CalleeTab} (hnd : T.names.Nodup) {g : String}
    {c : CalleeData} (hc : T.lookup g = some c) (ho : c.shape.out = false) :
    T.outs.lookup g = none := by
  have hinj : ∀ x ∈ T.fns, ∀ y ∈ T.fns, x.name = y.name → x = y :=
    fun x hx y hy h => List.inj_on_of_nodup_map hnd hx hy h
  obtain ⟨hm, hn⟩ := calleeTab_lookup_some hc
  grind [CalleeTab.outs, CalleeData.shape]

theorem getD_aliasStepO_of_call (outs : List (String × Nat)) (M : Std.HashMap String String)
    {i : LinstrRM} {d f : String} {srcs : List LOperand} {r : String}
    (hs : shadowCall? i.1 = some (d, f, srcs)) (hr : d ≠ r) :
    (aliasStepO outs M i).getD r r = M.getD r r := by
  have hne : (d == r) = false := by simpa using hr
  unfold aliasStepO
  rw [hs]
  dsimp only
  split
  · split
    · rw [Std.HashMap.getD_insert, hne]; rfl
    · rfl
  · rfl

theorem aliasStepO_of_lookup (outs : List (String × Nat)) (M : Std.HashMap String String)
    {i : LinstrRM} {d f : String} {srcs : List LOperand}
    (hs : shadowCall? i.1 = some (d, f, srcs)) (hf : outs.lookup f = none) :
    aliasStepO outs M i = M := by
  unfold aliasStepO
  rw [hs]
  simp only [hf]

/-- An alias step keeps the image of every name the instruction does not mention. -/
theorem getD_aliasStepO_fresh (outs : List (String × Nat)) (M : Std.HashMap String String)
    {i : LinstrRM} {r : String} (hr : r ∉ LprogCallCut.instrNames i.1) :
    (aliasStepO outs M i).getD r r = M.getD r r := by
  rcases hs : shadowCall? i.1 with _ | ⟨d, f, srcs⟩
  · unfold aliasStepO
    rw [hs]
    dsimp only
    split
    · rename_i dst opn base x sc rest hw
      split
      · have hne : (dst == r) = false := by
          simp only [beq_eq_false_iff_ne]
          rintro rfl
          exact hr (by rw [hw]; simp [LprogCallCut.instrNames, LprogCallCut.opNames])
        rw [Std.HashMap.getD_insert, hne]
        rfl
      · rfl
    · rename_i dst opn base rest hw
      split
      · have hne : (dst == r) = false := by
          simp only [beq_eq_false_iff_ne]
          rintro rfl
          exact hr (by rw [hw]; simp [LprogCallCut.instrNames, LprogCallCut.opNames])
        rw [Std.HashMap.getD_insert, hne]
        rfl
      · rfl
    · rfl
  · refine getD_aliasStepO_of_call outs M hs fun hd => hr ?_
    rw [eq_callShadow_of_shadowCall? hs, ← hd]
    simp [callShadow, LprogCallCut.instrNames, LprogCallCut.opNames]

theorem aliasStepO_movI (outs : List (String × Nat)) (M : Std.HashMap String String)
    (x y : String) : aliasStepO outs M (LprogCallCut.movI x y) = M := by
  unfold aliasStepO
  rw [shadowCall?_movI]
  simp [LprogCallCut.movI, withWidthTag]

theorem getD_foldl_aliasStepO_of {outs : List (String × Nat)} {r : String} :
    ∀ (L : List LinstrRM) (M : Std.HashMap String String),
      (∀ j ∈ L, ∀ M : Std.HashMap String String, (aliasStepO outs M j).getD r r = M.getD r r) →
      (L.foldl (aliasStepO outs) M).getD r r = M.getD r r
  | [], _, _ => rfl
  | j :: L, M, h => by
      rw [List.foldl_cons, getD_foldl_aliasStepO_of L _ (fun j' hj' => h j' (by simp [hj'])),
        h j (by simp)]

theorem callOpsFix_commonOps {σ : String → String} (sh : CallShape) {args : List String}
    (hσ : ∀ a ∈ args, σ a = a) :
    ∀ (i : Nat) (as : List String), (∀ a ∈ as, a ∈ args) → ∀ xs : List String,
      callOpsFix σ sh.arrArgs i ((commonOps sh i as xs).map LOperand.reg) = true
  | _, [], _, _ => by simp [commonOps, callOpsFix]
  | _, _ :: _, _, [] => by simp [commonOps, callOpsFix]
  | i, a :: as, ha, x :: xs => by
      simp only [commonOps, List.map_cons, callOpsFix, Bool.and_eq_true]
      refine ⟨?_, callOpsFix_commonOps sh hσ (i + 1) as (fun b hb => ha b (by simp [hb])) xs⟩
      split
      · simp_all
      · simp [hσ a (ha a (by simp))]

theorem tagOK_calleeCode (callee : Option CalleeTab) (code : List LinstrRM)
    (h : ∀ i ∈ code, TagOK i) : ∀ i ∈ calleeCodeT callee code, TagOK i := by
  intro i hi
  cases callee with
  | none => exact h i hi
  | some T =>
    simp only [calleeCodeT] at hi
    rcases hB : commonCallsT? T.common code with _ | B'
    · simp only [hB, Option.getD_none] at hi
      exact h i hi
    · simp only [hB, Option.getD_some] at hi
      rcases mem_commonCallsT? hB i hi with ⟨h1, -⟩ | ⟨x, y, rfl⟩ |
        ⟨d, g, sh, args, r, xs, -, rfl, -, -⟩
      · exact h i h1
      · simp [TagOK, LprogCallCut.movI]
      · simp [TagOK]

/-- **`ClassOK` on the coalesced code of a region export.** For code without a
    compile-time-offset tag, without a shadow instruction of a call when there is no
    table, which passes the stage `commonCalls` of `regionCoStage` and whose coalesced code
    passes the class check `clsB`, the coalesced code is admitted under the alias map of
    `regionAliasTab`, the map `chainAliasO` of its out symbols at a table. The stage makes the
    symbols of a table distinct, so a symbol with a word result is no out symbol. The common
    names of each function are fresh in the code, so the alias map fixes them, and every call
    of the rewritten code reads its word operands from those names and returns a word result
    in its result name. -/
theorem regionCo_classOK {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    {code : List LinstrRM} {res : List LOperand} {callee : Option CalleeTab}
    (htag : ∀ i ∈ code, TagOK i) (hsh : callee = none → ∀ i ∈ code, NoShadow i)
    (hcc : callee.all (fun T => decide T.names.Nodup
      && (commonCallsT? T.common code).isSome
      && LprogCallCut.commonFreshT T.common T.names (regionCoCode σ nm t code res)) = true)
    (hcls : ∀ i ∈ regionCoCode σ nm t (calleeCodeT callee code) res
      (regionCopy σ nm t callee (calleeCodeT callee code) res), clsB i = true) :
    ClassOK (canonMemrefName (regionAliasTab σ nm t callee res (regionCoCode σ nm t
        (calleeCodeT callee code) res (regionCopy σ nm t callee (calleeCodeT callee code) res))))
      (regionCoCode σ nm t (calleeCodeT callee code) res
        (regionCopy σ nm t callee (calleeCodeT callee code) res))
      (calleeAAT callee) (calleeAOT callee) := by
  refine classOK_of hcls (tagOK_regionCoCode _ _ _ _ _ _ (tagOK_calleeCode _ _ htag)) ?_
  cases callee with
  | none =>
    intro i hi dst f srcs hs
    have h0 : NoShadow i := noShadow_regionCoCode σ nm t code res _ (hsh rfl) i hi
    rw [show shadowCall? i.1 = none from h0] at hs
    cases hs
  | some T =>
    simp only [Option.all_some, Bool.and_eq_true, Option.isSome_iff_exists,
      decide_eq_true_eq] at hcc
    obtain ⟨⟨hnd, B', hB⟩, hfr⟩ := hcc
    have hcode : calleeCodeT (some T) code = B' := by simp [calleeCodeT, hB]
    rw [hcode, regionCopy_some_callee]
    have hfresh : ∀ j ∈ regionCoCode σ nm t code res, ∀ g c, T.lookup g = some c →
        ∀ r ∈ c.resReg :: c.args, r ∉ LprogCallCut.instrNames j.1 := by
      intro j hj g c hc r hr hn
      have hg : g ∈ T.names := by
        obtain ⟨hm, hname⟩ := calleeTab_lookup_some hc
        exact List.mem_map.mpr ⟨c, hm, hname⟩
      have hent : T.common g = some (c.shape, c.args, c.resReg) := by
        simp [CalleeTab.common, hc]
      have hfb := LprogCallCut.commonFreshT_entry hfr hg hent
      simp only [commonFreshB, Bool.and_eq_true, List.all_eq_true] at hfb
      have := hfb.1.2 j hj r hn
      simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, bne_iff_ne,
        ne_eq] at this
      rcases List.mem_cons.mp hr with rfl | hr
      · exact this.2 rfl
      · exact this.1 hr
    have hfix : ∀ g c, T.lookup g = some c → ∀ r ∈ c.resReg :: c.args,
        chainAliasO (calleeOutsT (some T)) (regionCoCode σ nm t B' res none) r = r := by
      intro g0 c0 hc0 r hr
      unfold chainAliasO canonMemrefName
      rw [getD_foldl_aliasStepO_of _ _ ?_]
      · simp
      intro j hj M
      unfold regionCoCode at hj
      rcases List.mem_append.mp hj with hj | hj
      · rcases mem_commonCallsT? hB j hj with ⟨h1, -⟩ | ⟨x, y, rfl⟩ |
          ⟨d, g, sh, args, r', xs, htab, rfl, hout, -⟩
        · exact getD_aliasStepO_fresh _ _ (hfresh j (List.mem_append_left _ h1) g0 c0 hc0 r hr)
        · rw [aliasStepO_movI]
        · obtain ⟨c, hc, rfl, rfl, rfl⟩ := calleeTab_common_some htab
          cases ho : c.shape.out
          · rw [aliasStepO_of_lookup (calleeOutsT (some T)) _ (shadowCall?_callShadow _ _ _)
              (calleeTab_outs_lookup hnd hc ho)]
          · obtain ⟨j0, hj0, srcs, hs0⟩ := hout ho
            refine getD_aliasStepO_of_call _ _ (shadowCall?_callShadow _ _ _) fun hd =>
              hfresh j0 (List.mem_append_left _ hj0) g0 c0 hc0 r hr ?_
            rw [eq_callShadow_of_shadowCall? hs0, hd]
            simp [callShadow, LprogCallCut.instrNames, LprogCallCut.opNames]
      · exact getD_aliasStepO_fresh _ _ (hfresh j (List.mem_append_right _ hj) g0 c0 hc0 r hr)
    intro i hi dst f srcs hs
    unfold regionCoCode at hi
    rcases List.mem_append.mp hi with hi | hi
    · rcases mem_commonCallsT? hB i hi with ⟨-, h0⟩ | ⟨x, y, rfl⟩ |
        ⟨d, g, sh, args, r', xs, htab, rfl, -, hres⟩
      · rw [h0] at hs
        cases hs
      · rw [shadowCall?_movI] at hs
        cases hs
      · rw [shadowCall?_callShadow] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl, rfl⟩ := hs
        obtain ⟨c, hc, rfl, rfl, rfl⟩ := calleeTab_common_some htab
        refine ⟨rfl, ?_, fun hao => ?_⟩
        · have haa : calleeAAT (some T) g = c.shape.arrArgs := by
            simp [calleeAAT, hc, CalleeData.shape]
          rw [haa]
          exact callOpsFix_commonOps c.shape (fun a ha => hfix g c hc a (List.mem_cons_of_mem _ ha))
            0 c.args (fun a h => h) xs
        · have ho : c.shape.out = false := by
            cases hr : c.res <;> simp_all [calleeAOT, CalleeData.shape]
          rw [hres ho]
          exact hfix g c hc _ List.mem_cons_self
    · rw [show shadowCall? i.1 = none from noShadow_movesOf _ i hi] at hs
      cases hs

/-- **The coalescing stage of the region gate accepts code without real aliasing** that has
    no compile-time-offset tag and, without a table, no shadow instruction of a call:
    `regionCoStage` refuses neither at `coCfgB` nor at `coEntryFix`. -/
theorem regionCoStage_coalesce_of (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand)
    (cert : List (String × String)) (callee : Option CalleeTab) (fn : String)
    (htag : ∀ i ∈ code, TagOK i) (hsh : callee = none → ∀ i ∈ code, NoShadow i)
    (ha : NoRealAlias (canonMemrefName (regionAliasTab σ nm t callee res (regionCoCode σ nm t
        (calleeCodeT callee code) res (regionCopy σ nm t callee (calleeCodeT callee code) res))))
      (regionCoCode σ nm t (calleeCodeT callee code) res
        (regionCopy σ nm t callee (calleeCodeT callee code) res))
      (calleeAAT callee) (calleeAOT callee)
      (regionCoObs t (regionOut (regionCopy σ nm t callee (calleeCodeT callee code) res) res))) :
    regionCoStage σ nm body t code res cert callee fn ≠ some "coCfgB" ∧
      regionCoStage σ nm body t code res cert callee fn ≠ some "coEntryFix" := by
  by_cases hcc : callee.all (fun T => decide T.names.Nodup
      && (commonCallsT? T.common code).isSome
      && LprogCallCut.commonFreshT T.common T.names (regionCoCode σ nm t code res)) = false
  · unfold regionCoStage
    simp only [hcc, ↓reduceIte]
    simp
  by_cases hcls : (regionCoCode σ nm t (calleeCodeT callee code) res
      (regionCopy σ nm t callee (calleeCodeT callee code) res)).all
        (fun i => clsB i && mulxFree i) = false
  · unfold regionCoStage
    simp only [hcc, hcls, ↓reduceIte]
    simp
  have hcls' : ∀ i ∈ regionCoCode σ nm t (calleeCodeT callee code) res
      (regionCopy σ nm t callee (calleeCodeT callee code) res), clsB i = true := fun i hi => by
    have h' := hcls
    simp only [Bool.not_eq_false, List.all_eq_true, Bool.and_eq_true] at h'
    exact (h' i hi).1
  exact regionCoStage_coalesce σ nm body t code res cert callee fn
    (regionCo_classOK htag hsh (by simpa using hcc) hcls') ha

theorem renArr_snd (σ : String → String) (i : LinstrRM) : (renArr σ i).2 = i.2 := by
  unfold renArr
  split <;> rfl

/-- The webs of the export keep the tags. -/
theorem tagOK_regionWebsAt (ex : List String) (callee : Option CalleeTab) (r : Exported)
    (h : ∀ i ∈ r.code, TagOK i) : ∀ i ∈ (regionWebsAt ex callee r).code, TagOK i := by
  cases callee with
  | none => exact h
  | some T =>
    intro i hi
    simp only [regionWebsAt_some] at hi
    unfold regionWebs at hi
    split at hi
    · simp only [X86Backend.ArrWebs.webRen] at hi
      obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hi
      have := h _ (List.getElem_mem hk)
      unfold TagOK at this ⊢
      rw [renArr_snd]
      exact this
    · exact h i hi

/-! ## 9. Disjoint storage classes -/

/-- The register an instruction assigns: the single register destination of `.Lopn`. -/
def lopnDst : LinstrR → Option String
  | .Lopn [.reg d] _ _ => some d
  | _ => none

/-- An alias step keeps the image of every name the instruction does not assign. -/
theorem getD_aliasStepO_of_lopnDst (outs : List (String × Nat)) (M : Std.HashMap String String)
    {i : LinstrRM} {r : String} (hr : lopnDst i.1 ≠ some r) :
    (aliasStepO outs M i).getD r r = M.getD r r := by
  rcases hs : shadowCall? i.1 with _ | ⟨d, f, srcs⟩
  · unfold aliasStepO
    rw [hs]
    dsimp only
    split
    · rename_i dst opn base x sc rest hw
      split
      · have hne : (dst == r) = false := by
          simp only [beq_eq_false_iff_ne]
          rintro rfl
          exact hr (by rw [hw]; rfl)
        rw [Std.HashMap.getD_insert, hne]
        rfl
      · rfl
    · rename_i dst opn base rest hw
      split
      · have hne : (dst == r) = false := by
          simp only [beq_eq_false_iff_ne]
          rintro rfl
          exact hr (by rw [hw]; rfl)
        rw [Std.HashMap.getD_insert, hne]
        rfl
      · rfl
    · rfl
  · refine getD_aliasStepO_of_call outs M hs fun hd => hr ?_
    rw [eq_callShadow_of_shadowCall? hs, ← hd]
    rfl

/-- **A name the code never assigns is its own root** under the alias map `chainAliasO`. -/
theorem chainAliasO_of_unassigned {outs : List (String × Nat)} {body : List LinstrRM}
    {r : String} (h : ∀ i ∈ body, lopnDst i.1 ≠ some r) : chainAliasO outs body r = r := by
  unfold chainAliasO canonMemrefName
  rw [getD_foldl_aliasStepO_of body _ fun j hj M => getD_aliasStepO_of_lopnDst outs M (h j hj)]
  simp

/-- The array names in use at position `k` of `body`: the names live at `k`, and at
    `k = j + 1` the name the instruction at position `j` writes. -/
def InUse (body : List LinstrRM) (aa : String → Nat → Option Nat) (ao : String → Option Nat)
    (obs : List String) (k : Nat) (r : String) : Prop :=
  PLive body aa ao obs k r ∨ ∃ j i, k = j + 1 ∧ body[j]? = some i ∧ wrArr ao i = some r

/-- **Disjoint storage classes.** The storage class of an array name is its root under the
    alias map `ρ`. No two distinct names of one class are in use at the same position of
    `body` (`InUse`: live there, or written by the instruction before it), and no array
    name live at the entry is assigned by an instruction of `body`. -/
def StorageDisjoint (ρ : String → String) (body : List LinstrRM)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) (obs : List String) : Prop :=
  (∀ k r r', InUse body aa ao obs k r → InUse body aa ao obs k r' → ρ r = ρ r' → r = r') ∧
    ∀ r, PLive body aa ao obs 0 r → ∀ i ∈ body, lopnDst i.1 ≠ some r

/-- The name that the code zeroes before it mentions it otherwise is assigned by the code. -/
theorem exists_lopnDst_of_zeroFirstB {r : String} :
    ∀ {body : List LinstrRM}, zeroFirstB r body = true → ∃ i ∈ body, lopnDst i.1 = some r
  | [], h => by simp [zeroFirstB] at h
  | i :: is, h => by
    unfold zeroFirstB at h
    by_cases h1 : zeroDst? i = some r
    · refine ⟨i, List.mem_cons_self, ?_⟩
      unfold zeroDst? at h1; split at h1 <;> simp_all [lopnDst]
    · rw [ite_eq_right h1] at h
      split at h
      · cases h
      · obtain ⟨j, hj, hd⟩ := exists_lopnDst_of_zeroFirstB h
        exact ⟨j, List.mem_cons_of_mem _ hj, hd⟩

/-- **A name the code never assigns is its own root** under the alias map of `resAliasTab`,
    at every result alias: the result root is zeroed by the code, so a name the code never
    assigns is not the result root. -/
theorem resAliasTab_of_unassigned {outs : List (String × Nat)} {rr : Option (String × String)}
    {body : List LinstrRM} {r : String} (h : ∀ i ∈ body, lopnDst i.1 ≠ some r) :
    canonMemrefName (resAliasTab outs rr body) r = r := by
  have h0 : chainAliasO outs body r = r := chainAliasO_of_unassigned h
  cases rr with
  | none => exact h0
  | some p =>
    obtain ⟨D, src⟩ := p
    show chainAliasRes outs D src body r = r
    rw [chainAliasRes_apply]
    split
    · rename_i r0 hr0
      obtain ⟨-, -, -, hz⟩ := resRoot?_some hr0
      obtain ⟨i, hi, hd⟩ := exists_lopnDst_of_zeroFirstB hz
      rw [h0, ite_eq_right]
      rintro rfl
      exact h i hi hd
    · exact h0

/-- **Disjoint storage classes give no real aliasing** under the alias map of `resAliasTab` of
    the code at every result alias; without a result alias the map is `chainAliasO`. -/
theorem noRealAlias_of_storageDisjoint {outs : List (String × Nat)}
    {rr : Option (String × String)} {body : List LinstrRM}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {obs : List String}
    (h : StorageDisjoint (canonMemrefName (resAliasTab outs rr body)) body aa ao obs) :
    NoRealAlias (canonMemrefName (resAliasTab outs rr body)) body aa ao obs :=
  ⟨fun k i hi d hd r hr hne heq =>
    hne (h.1 (k + 1) r d (.inl hr) (.inr ⟨k, i, rfl, hi, hd⟩) heq),
   fun r hr => resAliasTab_of_unassigned (h.2 r hr)⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoComplete

/-! ## 8. The coalescing stage on the output of the chain -/

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (chainAliasO)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoComplete
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)

/-- **The coalescing stage on the output of the chain, on both arms of `compileRegion`.** On a
    module `refusal?` accepts, the front returns a program `p`, at every table `bi` the chain
    `extChain` returns a program `q` on `p`, and the export `exportR` returns code `r` on `q`
    at every number of arguments, name, depth, label and instruction set. Take the webs
    `regionWebsAt ex callee r` of `r` at the names `ex` and an optional table of callees (`r`
    itself without a table). Without a table, let the guards and the select of the instruction
    set contain no shadow instruction of a call (`GuardsNoShadow`) and `q` pass
    `regionExportableB` and have no `call`, as on the call-free arm of `compileRegion`. When
    the alias map of the coalesced code of the webs has no real aliasing, `regionCoStage` on
    the webs refuses neither at `coCfgB` nor at `coEntryFix`, at every printed body, result
    type and function name. The checker theorems of `CoalesceComplete` this rests on name no
    instruction set; the instruction set enters only through `GuardsNoShadow`. -/
theorem CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_coalesce
    {σ : AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule} (hr : m.refusal? σ = none) :
    ∃ (t : _) (p : _), haxToNF σ m = some ⟨t, p⟩ ∧
      ∀ bi, ∃ q, (extChain (linkedDecls m bi) _ t).run p = some q ∧
        ∀ nArgs fn d n I, ∃ r, exportR nArgs fn q d n I = some r ∧
          ∀ (ex : List String) (nm : String → String) (body : Lcmd) (t' : JasminTy)
            (cert : List (String × String)) (callee : Option CalleeTab) (fn' : String),
            (callee = none →
              GuardsNoShadow I ∧ regionExportableB q = true ∧ q.callFree = true) →
            NoRealAlias (canonMemrefName (regionAliasTab σ nm t' callee
                (regionWebsAt ex callee r).res (regionCoCode σ nm t'
                (calleeCodeT callee (regionWebsAt ex callee r).code) (regionWebsAt ex callee r).res
                (regionCopy σ nm t' callee (calleeCodeT callee (regionWebsAt ex callee r).code)
                  (regionWebsAt ex callee r).res))))
              (regionCoCode σ nm t' (calleeCodeT callee (regionWebsAt ex callee r).code)
                (regionWebsAt ex callee r).res
                (regionCopy σ nm t' callee (calleeCodeT callee (regionWebsAt ex callee r).code)
                  (regionWebsAt ex callee r).res))
              (calleeAAT callee) (calleeAOT callee)
              (regionCoObs t' (regionOut (regionCopy σ nm t' callee
                (calleeCodeT callee (regionWebsAt ex callee r).code) (regionWebsAt ex callee r).res)
                (regionWebsAt ex callee r).res)) →
            regionCoStage σ nm body t' (regionWebsAt ex callee r).code
                (regionWebsAt ex callee r).res cert callee fn' ≠ some "coCfgB" ∧
              regionCoStage σ nm body t' (regionWebsAt ex callee r).code
                (regionWebsAt ex callee r).res cert callee fn' ≠ some "coEntryFix" := by
  obtain ⟨t, p, hp, h⟩ := CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_export_isSome hr
  refine ⟨t, p, hp, fun bi => ?_⟩
  obtain ⟨q, hq, -, -, -, he⟩ := h bi
  refine ⟨q, hq, fun nArgs fn d n I => ?_⟩
  obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp (he nArgs fn d n I)
  refine ⟨r, hr', fun ex nm body t' cert callee fn' hcf ha => ?_⟩
  refine regionCoStage_coalesce_of σ nm body t' _ _ cert callee fn'
    (tagOK_regionWebsAt ex callee r (exportR_tagOK nArgs fn I q d n r hr')) ?_ ha
  intro hc
  subst hc
  obtain ⟨hI, h1, h2⟩ := hcf rfl
  exact exportR_noShadow hI nArgs fn q h1 h2 d n r hr'

/-- **The coalescing stage on the output of the chain over x86.** The instance of
    `refusal?_eq_none_imp_coalesce` at x86 (`x86Data_guardsNoShadow`): without a callee, the
    instruction set is x86. -/
theorem CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_coalesce_x86
    {σ : AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule} (hr : m.refusal? σ = none) :
    ∃ (t : _) (p : _), haxToNF σ m = some ⟨t, p⟩ ∧
      ∀ bi, ∃ q, (extChain (linkedDecls m bi) _ t).run p = some q ∧
        ∀ nArgs fn d n I, ∃ r, exportR nArgs fn q d n I = some r ∧
          ∀ (ex : List String) (nm : String → String) (body : Lcmd) (t' : JasminTy)
            (cert : List (String × String)) (callee : Option CalleeTab) (fn' : String),
            (callee = none → I = x86Data ∧ regionExportableB q = true ∧ q.callFree = true) →
            NoRealAlias (canonMemrefName (regionAliasTab σ nm t' callee
                (regionWebsAt ex callee r).res (regionCoCode σ nm t'
                (calleeCodeT callee (regionWebsAt ex callee r).code) (regionWebsAt ex callee r).res
                (regionCopy σ nm t' callee (calleeCodeT callee (regionWebsAt ex callee r).code)
                  (regionWebsAt ex callee r).res))))
              (regionCoCode σ nm t' (calleeCodeT callee (regionWebsAt ex callee r).code)
                (regionWebsAt ex callee r).res
                (regionCopy σ nm t' callee (calleeCodeT callee (regionWebsAt ex callee r).code)
                  (regionWebsAt ex callee r).res))
              (calleeAAT callee) (calleeAOT callee)
              (regionCoObs t' (regionOut (regionCopy σ nm t' callee
                (calleeCodeT callee (regionWebsAt ex callee r).code) (regionWebsAt ex callee r).res)
                (regionWebsAt ex callee r).res)) →
            regionCoStage σ nm body t' (regionWebsAt ex callee r).code
                (regionWebsAt ex callee r).res cert callee fn' ≠ some "coCfgB" ∧
              regionCoStage σ nm body t' (regionWebsAt ex callee r).code
                (regionWebsAt ex callee r).res cert callee fn' ≠ some "coEntryFix" := by
  obtain ⟨t, p, hp, h⟩ := CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_coalesce hr
  refine ⟨t, p, hp, fun bi => ?_⟩
  obtain ⟨q, hq, h⟩ := h bi
  refine ⟨q, hq, fun nArgs fn d n I => ?_⟩
  obtain ⟨r, hr', h⟩ := h nArgs fn d n I
  refine ⟨r, hr', fun ex nm body t' cert callee fn' hcf =>
    h ex nm body t' cert callee fn' fun hc => ?_⟩
  obtain ⟨rfl, h1, h2⟩ := hcf hc
  exact ⟨x86Data_guardsNoShadow, h1, h2⟩

/-- **The coalescing stage on the output of the chain under disjoint storage classes.** As
    `refusal?_eq_none_imp_coalesce`, with the hypothesis on the coalesced code of the webs
    `StorageDisjoint`: the storage class of an array name is its root under the alias map
    of `regionAliasTab` of that code, no two distinct names of one class are in use at the same
    position, and no array name live at the entry is assigned by the code. -/
theorem CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_coalesce_of_disjoint
    {σ : AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule} (hr : m.refusal? σ = none) :
    ∃ (t : _) (p : _), haxToNF σ m = some ⟨t, p⟩ ∧
      ∀ bi, ∃ q, (extChain (linkedDecls m bi) _ t).run p = some q ∧
        ∀ nArgs fn d n I, ∃ r, exportR nArgs fn q d n I = some r ∧
          ∀ (ex : List String) (nm : String → String) (body : Lcmd) (t' : JasminTy)
            (cert : List (String × String)) (callee : Option CalleeTab) (fn' : String),
            (callee = none →
              GuardsNoShadow I ∧ regionExportableB q = true ∧ q.callFree = true) →
            StorageDisjoint (canonMemrefName (regionAliasTab σ nm t' callee
                (regionWebsAt ex callee r).res (regionCoCode σ nm t'
                (calleeCodeT callee (regionWebsAt ex callee r).code) (regionWebsAt ex callee r).res
                (regionCopy σ nm t' callee (calleeCodeT callee (regionWebsAt ex callee r).code)
                  (regionWebsAt ex callee r).res))))
              (regionCoCode σ nm t' (calleeCodeT callee (regionWebsAt ex callee r).code)
                (regionWebsAt ex callee r).res
                (regionCopy σ nm t' callee (calleeCodeT callee (regionWebsAt ex callee r).code)
                  (regionWebsAt ex callee r).res))
              (calleeAAT callee) (calleeAOT callee)
              (regionCoObs t' (regionOut (regionCopy σ nm t' callee
                (calleeCodeT callee (regionWebsAt ex callee r).code) (regionWebsAt ex callee r).res)
                (regionWebsAt ex callee r).res)) →
            regionCoStage σ nm body t' (regionWebsAt ex callee r).code
                (regionWebsAt ex callee r).res cert callee fn' ≠ some "coCfgB" ∧
              regionCoStage σ nm body t' (regionWebsAt ex callee r).code
                (regionWebsAt ex callee r).res cert callee fn' ≠ some "coEntryFix" := by
  obtain ⟨t, p, hp, h⟩ := CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_coalesce hr
  refine ⟨t, p, hp, fun bi => ?_⟩
  obtain ⟨q, hq, h⟩ := h bi
  refine ⟨q, hq, fun nArgs fn d n I => ?_⟩
  obtain ⟨r, hr', h⟩ := h nArgs fn d n I
  exact ⟨r, hr', fun ex nm body t' cert callee fn' hcf hs =>
    h ex nm body t' cert callee fn' hcf (noRealAlias_of_storageDisjoint hs)⟩

/-- **The coalescing stage on the output of the chain under disjoint storage classes over
    x86.** The instance of `refusal?_eq_none_imp_coalesce_of_disjoint` at x86
    (`x86Data_guardsNoShadow`): without a callee, the instruction set is x86. -/
theorem CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_coalesce_of_disjoint_x86
    {σ : AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule} (hr : m.refusal? σ = none) :
    ∃ (t : _) (p : _), haxToNF σ m = some ⟨t, p⟩ ∧
      ∀ bi, ∃ q, (extChain (linkedDecls m bi) _ t).run p = some q ∧
        ∀ nArgs fn d n I, ∃ r, exportR nArgs fn q d n I = some r ∧
          ∀ (ex : List String) (nm : String → String) (body : Lcmd) (t' : JasminTy)
            (cert : List (String × String)) (callee : Option CalleeTab) (fn' : String),
            (callee = none → I = x86Data ∧ regionExportableB q = true ∧ q.callFree = true) →
            StorageDisjoint (canonMemrefName (regionAliasTab σ nm t' callee
                (regionWebsAt ex callee r).res (regionCoCode σ nm t'
                (calleeCodeT callee (regionWebsAt ex callee r).code) (regionWebsAt ex callee r).res
                (regionCopy σ nm t' callee (calleeCodeT callee (regionWebsAt ex callee r).code)
                  (regionWebsAt ex callee r).res))))
              (regionCoCode σ nm t' (calleeCodeT callee (regionWebsAt ex callee r).code)
                (regionWebsAt ex callee r).res
                (regionCopy σ nm t' callee (calleeCodeT callee (regionWebsAt ex callee r).code)
                  (regionWebsAt ex callee r).res))
              (calleeAAT callee) (calleeAOT callee)
              (regionCoObs t' (regionOut (regionCopy σ nm t' callee
                (calleeCodeT callee (regionWebsAt ex callee r).code) (regionWebsAt ex callee r).res)
                (regionWebsAt ex callee r).res)) →
            regionCoStage σ nm body t' (regionWebsAt ex callee r).code
                (regionWebsAt ex callee r).res cert callee fn' ≠ some "coCfgB" ∧
              regionCoStage σ nm body t' (regionWebsAt ex callee r).code
                (regionWebsAt ex callee r).res cert callee fn' ≠ some "coEntryFix" := by
  obtain ⟨t, p, hp, h⟩ :=
    CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_coalesce_of_disjoint hr
  refine ⟨t, p, hp, fun bi => ?_⟩
  obtain ⟨q, hq, h⟩ := h bi
  refine ⟨q, hq, fun nArgs fn d n I => ?_⟩
  obtain ⟨r, hr', h⟩ := h nArgs fn d n I
  refine ⟨r, hr', fun ex nm body t' cert callee fn' hcf =>
    h ex nm body t' cert callee fn' fun hc => ?_⟩
  obtain ⟨rfl, h1, h2⟩ := hcf hc
  exact ⟨x86Data_guardsNoShadow, h1, h2⟩
