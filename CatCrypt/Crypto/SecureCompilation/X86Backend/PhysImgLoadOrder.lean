/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideOpt

/-!
# The order of the array-slot saves under the basic-block optimiser

The rewrite check `PhysImgOpt.loadChkB` of the load CSE fails when the scan redirects a move
`MOV q ← X` into an array slot `q` onto a holder of `X`. This module states a decidable order
condition on a body, `saveFreshB`: at every 64-bit move `MOV q ← X` into an array slot `q`, no
earlier instruction other than such a move names `X`. Under it the only binding of `X` in the
environment of the scan is an array slot, and the redirect is declined.

The condition is closed under sublists, so the redundant-reload elimination, the spill-reload
elimination and the dead-move elimination keep it. The scheduler keeps it because it transposes
only instructions that are no barriers, and these write no `qsave.` slot. The move propagation
keeps it because the names of every fact are names of the output in front of the fact, so no
source of an array-slot move is rewritten. The condition `slotAfterSlotReloadFreeB` is kept by
the same two passes.

The fused export body of `lfundefPhysAbiOfVirtCert` satisfies `saveFreshB`: the prologue parks
`RSI` in `R14` before the saves of `extraSaves`, and these save no register the fixed prologue
saves (`mem_extraSaves_ne`), so no array-slot save behind the park reads `RSI`.

## Main results

* `saveFreshB_sublist`: the condition on sublists, from a smaller set of names.
* `saveFreshB_scheduleBody`, `slotAfterSlotReloadFreeB_scheduleBody`: the scheduler.
* `saveFreshB_copyPropagateBody`, `slotAfterSlotReloadFreeB_copyPropagateBody`: the copy
  propagation.
* `slotAfterSlotLoadFreeB_of_reload`: the order condition of `loadSideB` from that of
  `elimSideB`.
* `saveFreshB_lfundefPhysAbiOfVirtCert`: the condition on the fused export body.
* `loadChkB_of_fresh`: `loadChkB` from `saveFreshB`, on a body with no move between two memory
  names whose 64-bit moves move into general-purpose or memory names.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgLoadOrder

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov? cellParts?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgOpt
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideOpt
open CatCrypt.Crypto.Optimizer.LoadCSE (asWideReload asWideReload_eq isMov64Mnem)

variable {slotArr : String → Option (String × Nat)}

/-! ## 1. The condition -/

theorem isMov64Mnem_MOVQ : isMov64Mnem "MOVQ" = true := by decide +kernel

/-- The source `X` of a 64-bit move `MOV q ← X` into an array slot `q`. -/
def slotSaveSrc? (slotArr : String → Option (String × Nat)) (j : Linstr) : Option String :=
  match asWideReload j.li_i with
  | some (q, X, _) => if (slotArr q).isSome then some X else none
  | none => none

/-- **No array-slot move reads a name met before.** At every 64-bit move `MOV q ← X` into an
    array slot `q`, the name `X` is not in `seen`; `seen` grows by the names of every
    instruction that is no such move. -/
def saveFreshB (slotArr : String → Option (String × Nat)) : List String → Lcmd → Bool
  | _, [] => true
  | seen, i :: is =>
      match slotSaveSrc? slotArr i with
      | some X => !seen.contains X && saveFreshB slotArr seen is
      | none => saveFreshB slotArr (seen ++ instrNames i.li_i) is

theorem saveFreshB_cons_some {S : List String} {i : Linstr} {is : Lcmd} {X : String}
    (h : slotSaveSrc? slotArr i = some X) :
    saveFreshB slotArr S (i :: is) = (!S.contains X && saveFreshB slotArr S is) := by
  simp [saveFreshB, h]

theorem saveFreshB_cons_none {S : List String} {i : Linstr} {is : Lcmd}
    (h : slotSaveSrc? slotArr i = none) :
    saveFreshB slotArr S (i :: is) = saveFreshB slotArr (S ++ instrNames i.li_i) is := by
  simp [saveFreshB, h]

theorem append_subset {S T : List String} (h : S ⊆ T) (n : List String) : S ++ n ⊆ T ++ n := by
  intro x hx
  simp only [List.mem_append] at hx ⊢
  exact hx.imp_left fun hx => h hx

/-- **`saveFreshB` on sublists**, from a set of names inside that of the body. -/
theorem saveFreshB_sublist {l' l : Lcmd} (hs : l'.Sublist l) :
    ∀ {S T : List String}, S ⊆ T → saveFreshB slotArr T l = true →
      saveFreshB slotArr S l' = true := by
  induction hs with
  | slnil => intros; rfl
  | cons a _ ih =>
    intro S T hST h
    cases ha : slotSaveSrc? slotArr a with
    | some X =>
      rw [saveFreshB_cons_some ha, Bool.and_eq_true] at h
      exact ih hST h.2
    | none =>
      rw [saveFreshB_cons_none ha] at h
      exact ih (fun x hx => List.mem_append_left _ (hST hx)) h
  | cons_cons a _ ih =>
    intro S T hST h
    cases ha : slotSaveSrc? slotArr a with
    | some X =>
      rw [saveFreshB_cons_some ha, Bool.and_eq_true] at h
      rw [saveFreshB_cons_some ha, Bool.and_eq_true]
      refine ⟨?_, ih hST h.2⟩
      have hT : X ∉ T := by simpa [List.contains_iff_mem] using h.1
      simpa [List.contains_iff_mem] using fun hx => hT (hST hx)
    | none =>
      rw [saveFreshB_cons_none ha] at h
      rw [saveFreshB_cons_none ha]
      exact ih (append_subset hST _) h

theorem slotSaveSrc?_eq_some {j : Linstr} {X : String} (h : slotSaveSrc? slotArr j = some X) :
    ∃ q mn, j.li_i = .Lopn [.reg q] mn [.reg X] ∧ isMov64Mnem mn = true ∧
      (slotArr q).isSome = true := by
  unfold slotSaveSrc? at h
  cases hr : asWideReload j.li_i with
  | none => rw [hr] at h; cases h
  | some p =>
    obtain ⟨q, Y, mn⟩ := p
    rw [hr] at h
    obtain ⟨he, hm⟩ := asWideReload_eq hr
    by_cases hs : (slotArr q).isSome = true
    · simp only [hs, ite_true, Option.some.injEq] at h
      subst h
      exact ⟨q, mn, he, hm, hs⟩
    · simp [hs] at h

theorem slotSaveSrc?_of_shape {j : Linstr} {q mn X : String}
    (h : j.li_i = .Lopn [.reg q] mn [.reg X]) (hm : isMov64Mnem mn = true)
    (hs : (slotArr q).isSome = true) : slotSaveSrc? slotArr j = some X := by
  simp [slotSaveSrc?, CatCrypt.Crypto.Optimizer.LoadCSE.asWideReload, h, hm, hs]

/-- An instruction that writes no array slot is no array-slot move. -/
theorem slotSaveSrc?_of_noWrite {j : Linstr} (h : noSlotWriteB slotArr j = true) :
    slotSaveSrc? slotArr j = none := by
  unfold slotSaveSrc?
  cases hr : asWideReload j.li_i with
  | none => rfl
  | some p =>
    obtain ⟨q, X, mn⟩ := p
    obtain ⟨he, -⟩ := asWideReload_eq hr
    simp [noSlotWriteB, he, writtenNames] at h
    simp [h]

/-- A body that writes no array slot satisfies `saveFreshB` from every set of names. -/
theorem saveFreshB_of_noWrite :
    ∀ (S : List String) (l : Lcmd), (∀ j ∈ l, noSlotWriteB slotArr j = true) →
      saveFreshB slotArr S l = true
  | _, [], _ => rfl
  | S, i :: is, h => by
    rw [saveFreshB_cons_none (slotSaveSrc?_of_noWrite (h i List.mem_cons_self))]
    exact saveFreshB_of_noWrite _ is fun j hj => h j (List.mem_cons_of_mem _ hj)

/-! ## 2. The scheduler -/

section Sched

open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSched

/-- An instruction that is no barrier writes no array slot, when every array slot is a frame
    slot. -/
theorem noWrite_of_not_isBarrierOp (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {j : Linstr} (hb : isBarrierOp j.li_i = false) : noSlotWriteB slotArr j = true := by
  unfold noSlotWriteB
  cases hj : j.li_i with
  | Lopn ds o ss =>
    rw [hj] at hb
    simp only [writtenNames, List.all_eq_true, List.mem_filterMap]
    rintro q ⟨x, hx, hxq⟩
    cases x with
    | reg n =>
      cases hxq
      simp [slotArr_none_of_prefix hq (slotDst_of_not_isBarrierOp hb hx)]
    | _ => cases hxq
  | _ => simp [writtenNames]

/-- Both instructions of an independent pair are no barriers. -/
theorem not_isBarrierOp_of_indep {i i' : LinstrR} (hind : indep i i' = true) :
    isBarrierOp i = false ∧ isBarrierOp i' = false := by
  have h1 : ∀ {a b : LinstrR}, indep a b = true → isBarrierOp a = false := by
    intro a b h
    simp only [indep, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1.1.2
  exact ⟨h1 hind, h1 (by rw [indep_symm]; exact hind)⟩

theorem saveFreshB_swap (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    ∀ (A : Lcmd) {C : Lcmd} {x y : Linstr} {S : List String}, indep x.li_i y.li_i = true →
      saveFreshB slotArr S (A ++ x :: y :: C) = true →
      saveFreshB slotArr S (A ++ y :: x :: C) = true
  | [], C, x, y, S, hind, h => by
    obtain ⟨hbx, hby⟩ := not_isBarrierOp_of_indep hind
    have hx := slotSaveSrc?_of_noWrite (noWrite_of_not_isBarrierOp hq hbx)
    have hy := slotSaveSrc?_of_noWrite (noWrite_of_not_isBarrierOp hq hby)
    simp only [List.nil_append, saveFreshB_cons_none hx, saveFreshB_cons_none hy] at h ⊢
    refine saveFreshB_sublist (List.Sublist.refl C) (fun z hz => ?_) h
    simp only [List.mem_append] at hz ⊢
    tauto
  | a :: A, C, x, y, S, hind, h => by
    simp only [List.cons_append] at h ⊢
    cases ha : slotSaveSrc? slotArr a with
    | some X =>
      rw [saveFreshB_cons_some ha, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, saveFreshB_swap hq A hind h.2⟩
    | none =>
      rw [saveFreshB_cons_none ha] at h ⊢
      exact saveFreshB_swap hq A hind h

theorem slotAfter_swap (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    ∀ (A : Lcmd) {C : Lcmd} {x y : Linstr} {s : Bool}, indep x.li_i y.li_i = true →
      slotAfterSlotReloadFreeB slotArr s (A ++ x :: y :: C) = true →
      slotAfterSlotReloadFreeB slotArr s (A ++ y :: x :: C) = true
  | [], C, x, y, s, hind, h => by
    obtain ⟨hbx, hby⟩ := not_isBarrierOp_of_indep hind
    have hx := noWrite_of_not_isBarrierOp (slotArr := slotArr) hq hbx
    have hy := noWrite_of_not_isBarrierOp (slotArr := slotArr) hq hby
    simp only [noSlotWriteB] at hx hy
    simp only [List.nil_append, slotAfterSlotReloadFreeB, hx, hy, Bool.or_true, Bool.true_and]
      at h ⊢
    rwa [Bool.or_assoc, Bool.or_comm (slotSrcReloadB slotArr y), ← Bool.or_assoc]
  | a :: A, C, x, y, s, hind, h => by
    simp only [List.cons_append, slotAfterSlotReloadFreeB, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, slotAfter_swap hq A hind h.2⟩

/-- **The scheduler keeps `saveFreshB`**, when every array slot is a frame slot. -/
theorem saveFreshB_scheduleBody (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {b : Lcmd} {S : List String} (h : saveFreshB slotArr S b = true) :
    saveFreshB slotArr S (scheduleBody b) = true := by
  have hr := scheduleBody_schedSwap b
  generalize scheduleBody b = b' at hr ⊢
  induction hr with
  | refl => exact h
  | tail _ hs ih =>
    obtain ⟨A, C, x, y, rfl, rfl, hind⟩ := hs
    exact saveFreshB_swap hq A hind ih

/-- **The scheduler keeps `slotAfterSlotReloadFreeB`**, when every array slot is a frame
    slot. -/
theorem slotAfterSlotReloadFreeB_scheduleBody
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {b : Lcmd} {s : Bool} (h : slotAfterSlotReloadFreeB slotArr s b = true) :
    slotAfterSlotReloadFreeB slotArr s (scheduleBody b) = true := by
  have hr := scheduleBody_schedSwap b
  generalize scheduleBody b = b' at hr ⊢
  induction hr with
  | refl => exact h
  | tail _ hs ih =>
    obtain ⟨A, C, x, y, rfl, rfl, hind⟩ := hs
    exact slotAfter_swap hq A hind ih

end Sched

/-! ## 3. The copy propagation -/

section Propagate

open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate

theorem mem_foldl_killFacts : ∀ (rs : List String) {facts : List MoveFact} {f : MoveFact},
    f ∈ rs.foldl killFacts facts → f ∈ facts
  | [], _, _, h => h
  | _ :: rs, _, _, h => (mem_killFacts (mem_foldl_killFacts rs h)).1

theorem mem_moveFacts (i' : Linstr) (facts₁ : List MoveFact) {f : MoveFact}
    (hf : f ∈ (match moveShape i' with
      | some (d, src, w) => if src == LOperand.reg d then facts₁ else (d, src, w) :: facts₁
      | none => facts₁)) : f ∈ facts₁ ∨ moveShape i' = some f := by
  split at hf
  · rename_i d src w hm
    split_ifs at hf
    · exact Or.inl hf
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact Or.inr hm
      · exact Or.inl hf
  · exact Or.inl hf

/-- One step of `propagateAux` returns the instruction with no fact, or rewrites the sources of
    an operation, each to itself or to the source of a fact for a general-purpose name, behind
    facts that are facts of the input or the move of the output. -/
theorem propStep_cases (facts : List MoveFact) (i : Linstr) :
    propStep facts i = (i, []) ∨
      ∃ (ds : List LOperand) (o : String) (ss : List LOperand) (rw : LOperand → LOperand),
        i.li_i = .Lopn ds o ss ∧
        (∀ x, rw x = x ∨ ∃ u v fw, x = .reg u ∧ (u, v, fw) ∈ facts ∧ isPhysGP u = true ∧
          rw x = v) ∧
        (propStep facts i).1 = { i with li_i := .Lopn ds o (ss.map rw) } ∧
        ∀ f ∈ (propStep facts i).2, f ∈ facts ∨ moveShape (propStep facts i).1 = some f := by
  unfold propStep
  cases hi : i.li_i with
  | Lopn ds o ss =>
    simp only
    split_ifs with hrec
    · right
      refine ⟨ds, o, ss, _, rfl, fun x => ?_, rfl, fun f hf => ?_⟩
      · rcases rewriteOperand_cases facts (effWidth o) _ _ x with h | ⟨u, v, fw, h1, h2, h3, -, h5⟩
        · exact Or.inl h
        · exact Or.inr ⟨u, v, fw, h1, h2, h3, h5⟩
      · exact (mem_moveFacts _ _ hf).imp_left (mem_foldl_killFacts _)
    · left; rfl
  | _ => left; rfl

/-- The names of a fact lie in `S`. -/
def FactsIn (S : List String) (facts : List MoveFact) : Prop :=
  ∀ f ∈ facts, f.1 ∈ S ∧ (∀ x ∈ opNames f.2.1, x ∈ S) ∧ isFactSrc f.2.1 = true

theorem moveShape_names {i : Linstr} {f : MoveFact} (h : moveShape i = some f) :
    f.1 ∈ instrNames i.li_i ∧ (∀ x ∈ opNames f.2.1, x ∈ instrNames i.li_i) ∧
      isFactSrc f.2.1 = true := by
  unfold moveShape at h
  split at h
  · rename_i d o src hi
    simp only [Bool.and_eq_true, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨-, h2⟩, -, rfl⟩ := h
    refine ⟨by simp [hi, instrNames, opNames], fun x hx => ?_, h2⟩
    simp [hi, instrNames, hx]
  · cases h

theorem moveShape_dst {i : Linstr} {f : MoveFact} (h : moveShape i = some f) :
    ∃ o src, i.li_i = .Lopn [.reg f.1] o [src] ∧ isPhysGP f.1 = true := by
  unfold moveShape at h
  split at h
  · rename_i d o src hi
    simp only [Bool.and_eq_true, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨⟨-, h2⟩, -⟩, -, rfl⟩ := h
    exact ⟨o, src, hi, h2⟩
  · cases h

/-- The move propagation keeps `saveFreshB`, from a set of names `S` of the output inside the
    set `T` of the input, when the names of every fact lie in `S`. -/
theorem saveFreshB_propagateAux
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    ∀ (b : Lcmd) (facts : List MoveFact) {S T : List String}, S ⊆ T → FactsIn S facts →
      saveFreshB slotArr T b = true → saveFreshB slotArr S (propagateAux facts b) = true
  | [], _, _, _, _, _, _ => rfl
  | i :: is, facts, S, T, hST, hF, h => by
    rw [propagateAux_cons]
    rcases propStep_cases facts i with hst | ⟨ds, o, ss, rw, hi, hrw, h1, h2⟩
    · rw [hst]
      cases ha : slotSaveSrc? slotArr i with
      | some X =>
        rw [saveFreshB_cons_some ha, Bool.and_eq_true] at h ⊢
        have hT : X ∉ T := by simpa [List.contains_iff_mem] using h.1
        refine ⟨by simpa [List.contains_iff_mem] using fun hx => hT (hST hx), ?_⟩
        exact saveFreshB_propagateAux hq is [] hST (fun f hf => by cases hf) h.2
      | none =>
        rw [saveFreshB_cons_none ha] at h ⊢
        exact saveFreshB_propagateAux hq is [] (append_subset hST _) (fun f hf => by cases hf) h
    · rw [h1]
      have hF' : ∀ f ∈ (propStep facts i).2, f ∈ facts ∨
          moveShape { i with li_i := .Lopn ds o (ss.map rw) } = some f := by
        rw [← h1]; exact h2
      have hnames : ∀ z ∈ instrNames (.Lopn ds o (ss.map rw)), z ∈ S ∨ z ∈ instrNames i.li_i := by
        intro z hz
        rw [hi]
        simp only [instrNames, List.mem_flatMap, List.mem_append, List.mem_map] at hz ⊢
        obtain ⟨x, hx | ⟨y, hy, rfl⟩, hzx⟩ := hz
        · exact Or.inr ⟨x, Or.inl hx, hzx⟩
        · rcases hrw y with he | ⟨u, v, fw, rfl, hmem, -, he⟩
          · rw [he] at hzx; exact Or.inr ⟨_, Or.inr hy, hzx⟩
          · rw [he] at hzx; exact Or.inl ((hF _ hmem).2.1 z hzx)
      cases ha : slotSaveSrc? slotArr i with
      | some X =>
        rw [saveFreshB_cons_some ha, Bool.and_eq_true] at h
        have hT : X ∉ T := by simpa [List.contains_iff_mem] using h.1
        obtain ⟨q, mn, hj, hm, hs⟩ := slotSaveSrc?_eq_some ha
        rw [hi] at hj
        cases hj
        have hX : rw (.reg X) = .reg X := by
          rcases hrw (.reg X) with he | ⟨u, v, fw, hu, hmem, -, -⟩
          · exact he
          · cases hu; exact absurd (hST (hF _ hmem).1) hT
        have ho : slotSaveSrc? slotArr { i with li_i := .Lopn [.reg q] o ([LOperand.reg X].map rw) }
            = some X := slotSaveSrc?_of_shape (by simp [hX]) hm hs
        rw [saveFreshB_cons_some ho, Bool.and_eq_true]
        refine ⟨by simpa [List.contains_iff_mem] using fun hx => hT (hST hx),
          saveFreshB_propagateAux hq is _ hST (fun f hf => ?_) h.2⟩
        rcases hF' f hf with hf | hf
        · exact hF f hf
        · obtain ⟨o', src, he, hg⟩ := moveShape_dst hf
          cases he
          rw [slotArr_physGP hq hg] at hs
          cases hs
      | none =>
        rw [saveFreshB_cons_none ha] at h
        have ho : slotSaveSrc? slotArr { i with li_i := .Lopn ds o (ss.map rw) } = none := by
          cases hc : slotSaveSrc? slotArr { i with li_i := .Lopn ds o (ss.map rw) } with
          | none => rfl
          | some Y =>
            obtain ⟨q, mn, hj, hm, hs⟩ := slotSaveSrc?_eq_some hc
            simp only [LinstrR.Lopn.injEq] at hj
            obtain ⟨rfl, rfl, hss⟩ := hj
            obtain ⟨x, rfl, hx⟩ : ∃ x, ss = [x] ∧ rw x = .reg Y := by
              rcases ss with _ | ⟨x, _ | ⟨y, ys⟩⟩
              · cases hss
              · exact ⟨x, rfl, by simpa using hss⟩
              · simp at hss
            rcases hrw x with he | ⟨u, v, fw, rfl, -, -, -⟩
            · rw [he] at hx
              subst hx
              rw [slotSaveSrc?_of_shape hi hm hs] at ha
              cases ha
            · rw [slotSaveSrc?_of_shape hi hm hs] at ha
              cases ha
        rw [saveFreshB_cons_none ho]
        refine saveFreshB_propagateAux hq is _ (fun z hz => ?_) (fun f hf => ?_) h
        · simp only [List.mem_append] at hz ⊢
          rcases hz with hz | hz
          · exact Or.inl (hST hz)
          · exact (hnames z hz).imp_left fun hz => hST hz
        · rcases hF' f hf with hf | hf
          · obtain ⟨a1, a2, a3⟩ := hF f hf
            exact ⟨List.mem_append_left _ a1, fun x hx => List.mem_append_left _ (a2 x hx), a3⟩
          · obtain ⟨a1, a2, a3⟩ := moveShape_names hf
            exact ⟨List.mem_append_right _ a1, fun x hx => List.mem_append_right _ (a2 x hx), a3⟩

/-- **The copy propagation keeps `saveFreshB`**, when every array slot is a frame slot. -/
theorem saveFreshB_copyPropagateBody
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {b : Lcmd} {S : List String} (h : saveFreshB slotArr S b = true) :
    saveFreshB slotArr S (copyPropagateBody b) = true :=
  saveFreshB_sublist (deadElimBody_sublist _) (fun _ hx => hx)
    (saveFreshB_propagateAux hq b [] (fun _ hx => hx) (fun _ hf => by cases hf) h)

/-- The move propagation keeps `slotAfterSlotReloadFreeB`: it keeps the destinations, and a
    reload of its output from an array slot is a reload of the input, since a rewritten source
    is a general-purpose name or an immediate. -/
theorem slotAfter_propagateAux
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    ∀ (b : Lcmd) (facts : List MoveFact) {s s' : Bool}, (s' = true → s = true) →
      (∀ f ∈ facts, isFactSrc f.2.1 = true) →
      slotAfterSlotReloadFreeB slotArr s b = true →
      slotAfterSlotReloadFreeB slotArr s' (propagateAux facts b) = true
  | [], _, _, _, _, _, _ => rfl
  | i :: is, facts, s, s', hss, hF, h => by
    rw [propagateAux_cons]
    simp only [slotAfterSlotReloadFreeB, Bool.and_eq_true] at h ⊢
    have hcheck : ∀ j : Linstr, writtenNames j.li_i = writtenNames i.li_i →
        (!s' || (writtenNames j.li_i).all fun q => (slotArr q).isNone) = true := by
      intro j hj
      rw [hj]
      cases s' with
      | false => rfl
      | true => simpa [hss rfl] using h.1
    rcases propStep_cases facts i with hst | ⟨ds, o, ss, rw, hi, hrw, h1, h2⟩
    · rw [hst]
      exact ⟨hcheck i rfl, slotAfter_propagateAux hq is [] (fun h' => by
        simp only [Bool.or_eq_true] at h' ⊢; exact h'.imp hss id) (fun f hf => by cases hf) h.2⟩
    · rw [h1]
      refine ⟨hcheck _ (by rw [hi]; rfl), slotAfter_propagateAux hq is _ (fun h' => ?_)
        (fun f hf => ?_) h.2⟩
      · simp only [Bool.or_eq_true] at h' ⊢
        refine h'.imp hss fun hsr => ?_
        unfold slotSrcReloadB at hsr ⊢
        cases hr : asReload (LinstrR.Lopn ds o (ss.map rw)) with
        | none => simp only [hr] at hsr; cases hsr
        | some p =>
          obtain ⟨d, src⟩ := p
          simp only [hr] at hsr
          obtain ⟨o', he⟩ := asReload_eq hr
          simp only [LinstrR.Lopn.injEq] at he
          obtain ⟨rfl, rfl, hss'⟩ := he
          have hmap : ss.map rw = ss := by
            rcases ss with _ | ⟨x, _ | ⟨y, ys⟩⟩
            · rfl
            · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hss' ⊢
              rcases hrw x with hx | ⟨u, v, fw, rfl, hmem, -, hx⟩
              · exact hx
              · rw [hx] at hss'
                subst hss'
                have := hF _ hmem
                simp only [isFactSrc] at this
                rw [slotArr_physGP hq this] at hsr
                cases hsr
            · simp at hss'
          rw [hi, ← hmap, hr]
          exact hsr
      · rcases h2 f (by rw [← h1] at *; exact hf) with hf | hf
        · exact hF f hf
        · rw [h1] at hf; exact (moveShape_names hf).2.2

/-- **The copy propagation keeps `slotAfterSlotReloadFreeB`**, when every array slot is a frame
    slot. -/
theorem slotAfterSlotReloadFreeB_copyPropagateBody
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {b : Lcmd} {s : Bool} (h : slotAfterSlotReloadFreeB slotArr s b = true) :
    slotAfterSlotReloadFreeB slotArr s (copyPropagateBody b) = true :=
  slotAfterSlotReloadFreeB_sublist (deadElimBody_sublist _) id
    (slotAfter_propagateAux hq b [] id (fun _ hf => by cases hf) h)

end Propagate

/-- **The order condition of `loadSideB` from that of `elimSideB`**: a 64-bit move from an
    array slot is a reload from it. -/
theorem slotAfterSlotLoadFreeB_of_reload :
    ∀ (b : Lcmd) {s' s : Bool}, (s' = true → s = true) →
      slotAfterSlotReloadFreeB slotArr s b = true → slotAfterSlotLoadFreeB slotArr s' b = true
  | [], _, _, _, _ => rfl
  | i :: is, s', s, hss, h => by
    simp only [slotAfterSlotReloadFreeB, slotAfterSlotLoadFreeB, Bool.and_eq_true] at h ⊢
    refine ⟨?_, slotAfterSlotLoadFreeB_of_reload is (fun h' => ?_) h.2⟩
    · cases s' with
      | false => rfl
      | true => simpa [hss rfl] using h.1
    · simp only [Bool.or_eq_true] at h' ⊢
      refine h'.imp hss fun hl => ?_
      unfold slotLoadB at hl
      unfold slotSrcReloadB
      cases hr : asWideReload i.li_i with
      | none => simp only [hr] at hl; cases hl
      | some p =>
        obtain ⟨d, src, mn⟩ := p
        simp only [hr] at hl
        rw [asReload_of_asWideReload hr]
        exact hl

/-! ## 4. The export -/

section Export

open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFuse
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (physExpand physRmap notLivePin)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc

/-- **The fusion keeps `saveFreshB`**, under the invariants of `fuse_step`. -/
theorem fuse_saveFresh (s : Bool)
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    ∀ (rest : Lcmd) (ef ep : ScratchEnv) (pend : List (String × String)) (seen : List String),
      fuseSiteOkB slotArr rest = true → homeOkB slotArr ep rest = true → EnvAgree ef ep →
      EnvScratch ef → (∀ p ∈ pend, slotArr p.1 = none) →
      saveFreshB slotArr seen rest = true →
      saveFreshB slotArr seen (fuseMulHiAux s ef pend rest) = true
  | [], _, _, _, _, _, _, _, _, _, _ => by rw [fuseMulHiAux_nil]; rfl
  | i :: rest, ef, ep, pend, seen, hs, hh, hag, hes, hp, hsa => by
    obtain ⟨L, ef', pend', he, hs', hh', hag', hes', hp', hc⟩ :=
      fuse_step s hq i rest ef ep pend hs hh hag hes hp
    rw [he]
    rcases hc with rfl | ⟨hL, hR⟩
    · rw [List.singleton_append]
      cases ha : slotSaveSrc? slotArr i with
      | some X =>
        rw [saveFreshB_cons_some ha, Bool.and_eq_true] at hsa ⊢
        exact ⟨hsa.1, fuse_saveFresh s hq rest ef' _ pend' _ hs' hh' hag' hes' hp' hsa.2⟩
      | none =>
        rw [saveFreshB_cons_none ha] at hsa ⊢
        exact fuse_saveFresh s hq rest ef' _ pend' _ hs' hh' hag' hes' hp' hsa
    · refine saveFreshB_of_noWrite _ _ fun j hj => ?_
      rcases List.mem_append.mp hj with hj | hj
      · exact noWrite_of_dstOkB (hL j hj)
      · rcases fuse_mem s hq rest ef' _ pend' hs' hh' hag' hes' hp' j hj with hj | hj
        · exact noWrite_of_dstOkB (hR j hj)
        · exact noWrite_of_dstOkB hj

/-- The check of `saveFreshB` with every `qsave.` destination taken as an array slot and the
    names of every instruction added to `seen`; it does not depend on the slot layout. -/
def saveFreshMaxB : List String → Lcmd → Bool
  | _, [] => true
  | seen, i :: is =>
      (match asWideReload i.li_i with
        | some (q, X, _) => !hasPrefix q "qsave." || !seen.contains X
        | none => true) && saveFreshMaxB (seen ++ instrNames i.li_i) is

/-- **`saveFreshB` on a body with a prefix checked by `saveFreshMaxB`**, when every array slot
    is a frame slot: the rest is checked from every set of names inside those of the prefix. -/
theorem saveFreshB_append_of_max
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    ∀ (l1 : Lcmd) {l2 : Lcmd} {S T : List String}, S ⊆ T → saveFreshMaxB T l1 = true →
      (∀ S', S' ⊆ T ++ l1.flatMap (fun j => instrNames j.li_i) →
        saveFreshB slotArr S' l2 = true) →
      saveFreshB slotArr S (l1 ++ l2) = true
  | [], _, S, T, hST, _, h2 => h2 S (by simpa using hST)
  | i :: l1, l2, S, T, hST, h1, h2 => by
    simp only [saveFreshMaxB, Bool.and_eq_true] at h1
    have h2' : ∀ S', S' ⊆ (T ++ instrNames i.li_i) ++ l1.flatMap (fun j => instrNames j.li_i) →
        saveFreshB slotArr S' l2 = true :=
      fun S' hS => h2 S' (by simpa [List.flatMap_cons, List.append_assoc] using hS)
    rw [List.cons_append]
    cases ha : slotSaveSrc? slotArr i with
    | some X =>
      obtain ⟨q, mn, hi, hmn, hqs⟩ := slotSaveSrc?_eq_some ha
      have hX : X ∉ T := by
        have := h1.1
        simp only [hi, CatCrypt.Crypto.Optimizer.LoadCSE.asWideReload, hmn, ite_true, hq q hqs,
          Bool.not_true, Bool.false_or] at this
        simpa [List.contains_iff_mem] using this
      rw [saveFreshB_cons_some ha, Bool.and_eq_true]
      exact ⟨by simpa [List.contains_iff_mem] using fun hx => hX (hST hx),
        saveFreshB_append_of_max hq l1 (fun x hx => List.mem_append_left _ (hST hx)) h1.2 h2'⟩
    | none =>
      rw [saveFreshB_cons_none ha]
      exact saveFreshB_append_of_max hq l1 (append_subset hST _) h1.2 h2'

/-- The argument registers met before a save in `seen` whose save slot is an array slot are
    `RSI`. -/
def ArgSeenOk (slotArr : String → Option (String × Nat)) (S : List String) : Prop :=
  ∀ R ∈ S, ∀ s, abiSaveOfExt R = some s → (slotArr s).isSome = true → R = "RSI"

theorem abiSaveOfExt_slot {R : String} (h : R ∈ ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]) :
    abiSaveOfExt (slotOfReg R) = none := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- **The saves of `extraSaves` satisfy `saveFreshB`** in front of a body that writes no array
    slot, from names whose argument registers with an array save slot are `RSI`, when `RSI`
    is no parameter of the saves or its slot is no array slot. -/
theorem saveFreshB_extraSaves :
    ∀ (l : List String) {Y : Lcmd} {S : List String}, ArgSeenOk slotArr S →
      ("RSI" ∈ l → slotArr "qsave.RSI" = none) → (∀ j ∈ Y, noSlotWriteB slotArr j = true) →
      saveFreshB slotArr S (argRegSaves l ++ Y) = true
  | [], Y, S, _, _, hY => saveFreshB_of_noWrite S Y hY
  | a :: l, Y, S, hS, hrsi, hY => by
    have hrsi' : "RSI" ∈ l → slotArr "qsave.RSI" = none :=
      fun h => hrsi (List.mem_cons_of_mem _ h)
    cases hs : abiSaveOfExt a with
    | none =>
      simp only [argRegSaves, List.filterMap_cons, hs]
      exact saveFreshB_extraSaves l hS hrsi' hY
    | some s =>
      simp only [argRegSaves, List.filterMap_cons, hs, List.cons_append]
      obtain ⟨rfl, ha⟩ := abiSaveOfExt_spec hs
      cases hsa : (slotArr (slotOfReg a)).isSome with
      | true =>
        rw [saveFreshB_cons_some (slotSaveSrc?_of_shape rfl (by decide +kernel) hsa),
          Bool.and_eq_true]
        refine ⟨?_, saveFreshB_extraSaves l hS hrsi' hY⟩
        have : a ∉ S := by
          intro haS
          have hR := hS a haS _ hs hsa
          subst hR
          rw [show slotOfReg "RSI" = "qsave.RSI" from rfl, hrsi List.mem_cons_self] at hsa
          cases hsa
        simpa [List.contains_iff_mem] using this
      | false =>
        have hn : slotSaveSrc? slotArr (⟨0, .Lopn [.reg (slotOfReg a)] "MOVQ" [.reg a]⟩ : Linstr)
            = none := by
          simp [slotSaveSrc?, CatCrypt.Crypto.Optimizer.LoadCSE.asWideReload, hsa,
            isMov64Mnem_MOVQ]
        rw [saveFreshB_cons_none hn]
        refine saveFreshB_extraSaves l (fun R hR s' hs' hss => ?_) hrsi' hY
        simp only [instrNames, opNames, List.cons_append, List.nil_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hR
        rcases hR with hR | rfl | rfl
        · exact hS R hR s' hs' hss
        · rw [abiSaveOfExt_slot ha] at hs'; cases hs'
        · rw [hs] at hs'; cases hs'; rw [hsa] at hss; cases hss

/-- The first save of the prologue. -/
abbrev prologueHead : Linstr := ⟨0, .Lopn [.reg "qsave.RDI"] "MOVQ" [.reg "RDI"]⟩

theorem buildPrologue_eq (virt : Lfundef) (tbl : Array Nat) :
    buildPrologue virt tbl (fun _ => none) =
      prologueHead :: (buildPrologue {} #[] (fun _ => none)).tail := rfl

theorem prologueTail_max_nil : saveFreshMaxB [] (buildPrologue {} #[] (fun _ => none)).tail = true :=
  by decide +kernel

theorem prologueTail_max_head :
    saveFreshMaxB ["qsave.RDI", "RDI"] (buildPrologue {} #[] (fun _ => none)).tail = true := by
  decide +kernel

theorem prologueTail_names :
    ((buildPrologue {} #[] (fun _ => none)).tail.flatMap (fun j => instrNames j.li_i)).all
      (fun R => !(abiSaveOfExt R).isSome || R == "RSI") = true := by
  decide +kernel

/-- **The prologue and its saves satisfy `saveFreshB`** in front of a body that writes no array
    slot, when every array slot is a frame slot. -/
theorem saveFreshB_prologue (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    (virt : Lfundef) (tbl : Array Nat) (abiArgs : List String) {Y : Lcmd}
    (hY : ∀ j ∈ Y, noSlotWriteB slotArr j = true) :
    saveFreshB slotArr [] ((buildPrologue virt tbl (fun _ => none) ++ extraSaves abiArgs) ++ Y)
      = true := by
  have hrsi : "RSI" ∈ extraSaveRegs abiArgs → slotArr "qsave.RSI" = none :=
    fun h => absurd rfl (not_mem_extraSaveRegs h).2
  have hT : ∀ R ∈ (buildPrologue {} #[] (fun _ => none)).tail.flatMap (fun j => instrNames j.li_i),
      ∀ s, abiSaveOfExt R = some s → R = "RSI" := by
    intro R hR s hs
    have := List.all_eq_true.mp prologueTail_names R hR
    simpa [hs] using this
  rw [buildPrologue_eq]
  simp only [List.cons_append, List.append_assoc]
  cases hrdi : (slotArr "qsave.RDI").isSome with
  | true =>
    rw [saveFreshB_cons_some (slotSaveSrc?_of_shape rfl (by decide +kernel) hrdi)]
    simp only [List.contains_nil, Bool.not_false, Bool.true_and]
    refine saveFreshB_append_of_max hq _ (fun _ hx => hx) prologueTail_max_nil fun S' hS => ?_
    refine saveFreshB_extraSaves (extraSaveRegs abiArgs)
      (fun R hR s hs _ => hT R (by simpa using hS hR) s hs) hrsi hY
  | false =>
    have hn : slotSaveSrc? slotArr prologueHead = none := by
      simp [slotSaveSrc?, CatCrypt.Crypto.Optimizer.LoadCSE.asWideReload, hrdi, isMov64Mnem_MOVQ]
    rw [saveFreshB_cons_none hn]
    have hnm : instrNames prologueHead.li_i = ["qsave.RDI", "RDI"] := rfl
    rw [hnm]
    refine saveFreshB_append_of_max hq _ (fun _ hx => hx) prologueTail_max_head fun S' hS => ?_
    refine saveFreshB_extraSaves (extraSaveRegs abiArgs) (fun R hR s hs hss => ?_) hrsi hY
    rcases List.mem_append.mp (hS hR) with hR | hR
    · simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · rw [show abiSaveOfExt "qsave.RDI" = none by decide +kernel] at hs
        cases hs
      · have : s = "qsave.RDI" := by
          have h' : abiSaveOfExt "RDI" = some "qsave.RDI" := by decide +kernel
          rw [h'] at hs; cases hs; rfl
        subst this
        rw [hrdi] at hss; cases hss
    · exact hT R hR s hs

/-- **The array-slot saves of the fused export body read fresh names.** Under the hypotheses of
    `order_lfundefPhysAbiOfVirtCert`, the fusion of the export body of
    `lfundefPhysAbiOfVirtCert` satisfies `saveFreshB`. The prologue parks `RSI` in `R14` by
    `MOVQ R14, RSI`, and no save of `extraSaves` behind the park reads `RSI`
    (`mem_extraSaves_ne`). -/
theorem saveFreshB_lfundefPhysAbiOfVirtCert {slotArr : String → Option (String × Nat)}
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (mbr : String → Option String)
    (hmbr : mbr = fun base =>
      (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSaveOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false)
    (hshape : ∀ i ∈ body1, AccForm slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      mbr i.li_i)
    (harr : ∀ i ∈ body1, ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → slotArr q = none)
    (hidx : ∀ i ∈ body1, isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true)
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    let b0 := (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body
    saveFreshB slotArr [] (fuseMulHiBody b0 true) = true := by
  intro b0
  have hsite := fuseSiteOkB_lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm
    abiArgs abiTyin posBind body1 hb1 mbr hmbr hcf hshape harr hidx hslot
  have hhome := homeOkB_lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm
    abiArgs abiTyin posBind body1 hb1 mbr hmbr hcf hshape harr hidx hslot
  have hb : saveFreshB slotArr [] b0 = true := by
    simp only [b0]
    rw [lfundefPhysAbiOfVirtCert_body virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin
      posBind body1 hb1 mbr hmbr hcf, reloadArrImmBody_filter_flatMap]
    obtain ⟨-, -, -, hD⟩ := physExpand_flatMap_side (certShiftImm shiftImm body1) body1 mbr hcf
      hshape harr hidx hslot
    refine saveFreshB_prologue hslot _ _ abiArgs fun j hj => ?_
    rcases List.mem_append.mp hj with hj | hj
    · exact noWrite_of_dstOkB (dstOkB_of_dstOk
        (buildArgPtrMaterialize_dstOk hslot _ _ _ _ j hj))
    · unfold insertEpilogue at hj
      simp only [List.mem_append, List.mem_singleton] at hj
      rcases hj with (hj | hj) | hj
      · exact noWrite_of_dstOkB (hD j (List.dropLast_subset _ hj))
      · exact noWrite_of_dstOkB (dstOkB_of_dstOk (calleeSaveRestoreEpilogue_dstOk hslot j hj))
      · subst hj; rfl
  exact fuse_saveFresh true hslot b0 [] [] [] [] hsite hhome (EnvAgree.refl _)
    (fun _ hp => by cases hp) (fun _ hp => by cases hp) hb

end Export

/-! ## 5. The rewrite check of the load CSE -/

section LoadChk

open CatCrypt.Crypto.Optimizer.LoadCSE (LoadEnv stepLoad stepLoad_cases isMemName isMemToMemMov
  MemHolderRegKey holder_not_mem stepLoad_memHolderRegKey stepLoad_env_of_wideReload
  stepLoad_env_of_not_wideReload)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass (memMovFreeB memMovFreeB_iff)

/-- Every binding after a step of the scan is a binding before it, or the binding `s ↦ d` of a
    64-bit move `MOV d ← s`. -/
theorem mem_stepLoad {env : LoadEnv} {i : Linstr} {p : String × String}
    (hp : p ∈ (stepLoad env i).2) : p ∈ env ∨ ∃ mn, asWideReload i.li_i = some (p.2, p.1, mn) := by
  cases hr : asWideReload i.li_i with
  | none =>
    rw [stepLoad_env_of_not_wideReload env i hr] at hp
    exact Or.inl (Optimizer.LoadCSE.mem_foldl_killReg _ _ _
      (Optimizer.LoadCSE.mem_foldl_killSlot _ _ _ hp).1).1
  | some dsm =>
    obtain ⟨d, s, mn⟩ := dsm
    rw [stepLoad_env_of_wideReload env i hr] at hp
    rcases mem_set hp with ⟨hmem, -⟩ | rfl
    · exact Or.inl (Optimizer.LoadCSE.mem_killReg (Optimizer.LoadCSE.mem_killSlot hmem).1).1
    · exact Or.inr ⟨mn, rfl⟩

/-- An instruction the scan keeps passes the rewrite check. -/
theorem loadRewriteOkB_self (i : Linstr) : loadRewriteOkB slotArr i i = true := by
  unfold loadRewriteOkB
  cases hr : asWideReload i.li_i with
  | none => simp
  | some p =>
    obtain ⟨d, s, mn⟩ := p
    rw [(asWideReload_eq hr).1]
    simp

theorem slotMov?_of_isSome {d o u : String} (h : (slotMov? (.Lopn [.reg d] o [.reg u])).isSome = true) :
    slotMov? (.Lopn [.reg d] o [.reg u]) = some (d, u) := by
  simp only [slotMov?] at h ⊢
  split_ifs at h ⊢ <;> simp_all

/-- **The scan invariant of `loadChkB_of_fresh`.** Every binding of the environment has a holder
    that is no memory name when its key is a register name, a holder that is a general-purpose
    or memory name, and a key in `seen` or an array-slot holder. -/
theorem loadChkB_scan (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    ∀ (b : Lcmd) (seen : List String) (env : LoadEnv),
      saveFreshB slotArr seen b = true → memMovFreeB b = true →
      (∀ j ∈ b, ∀ d s mn, asWideReload j.li_i = some (d, s, mn) →
        gpNameB d = true ∨ isMemName d = true) →
      MemHolderRegKey env →
      (∀ k r, (k, r) ∈ env → gpNameB r = true ∨ isMemName r = true) →
      (∀ k r, (k, r) ∈ env → k ∈ seen ∨ (slotArr r).isSome = true) →
      loadChkB slotArr env b = true
  | [], _, _, _, _, _, _, _, _ => rfl
  | i :: is, seen, env, hf, hm, hd, hh, hg, hk => by
    simp only [loadChkB, Bool.and_eq_true]
    have hmi : isMemToMemMov i.li_i = false := memMovFreeB_iff.mp hm i List.mem_cons_self
    have hm' : memMovFreeB is = true :=
      memMovFreeB_iff.mpr fun j hj => memMovFreeB_iff.mp hm j (List.mem_cons_of_mem _ hj)
    have hd' : ∀ j ∈ is, ∀ d s mn, asWideReload j.li_i = some (d, s, mn) →
        gpNameB d = true ∨ isMemName d = true := fun j hj => hd j (List.mem_cons_of_mem _ hj)
    have hg' : ∀ k r, (k, r) ∈ (stepLoad env i).2 → gpNameB r = true ∨ isMemName r = true := by
      intro k r hkr
      rcases mem_stepLoad hkr with hkr | ⟨mn, hr⟩
      · exact hg k r hkr
      · exact hd i List.mem_cons_self r k mn hr
    refine ⟨?_, ?_⟩
    · rcases stepLoad_cases env i with he | ⟨d, s, r, mn, hr, hfind, ⟨-, -, hsr⟩, he⟩
      · rw [he]; exact loadRewriteOkB_self i
      · rw [he]
        have hmem : (s, r) ∈ env := mem_of_find hfind
        have hrm : isMemName r = false := holder_not_mem hh hfind hsr
        have hrg : gpNameB r = true := (hg s r hmem).resolve_right (by simp [hrm])
        have hrs : slotArr r = none :=
          slotArr_physGP hq (by rwa [PhysImgFold.isPhysGP_eq_gpNameB])
        obtain ⟨hi, hmn⟩ := asWideReload_eq hr
        have hds : (slotArr d).isNone = true := by
          cases hdq : (slotArr d).isSome with
          | false => simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using hdq
          | true =>
            exfalso
            rw [saveFreshB_cons_some (slotSaveSrc?_of_shape hi hmn hdq), Bool.and_eq_true] at hf
            have hs : s ∉ seen := by simpa [List.contains_iff_mem] using hf.1
            rcases hk s r hmem with hk | hk
            · exact hs hk
            · rw [hrs] at hk; cases hk
        unfold loadRewriteOkB
        rw [hr]
        cases hsm0 : slotMov? i.li_i with
        | none => simp [hds, goodHoldB, hrg, hrs]
        | some p =>
          have hsm : slotMov? i.li_i = some (d, s) := by
            have := asReload_of_slotMov hsm0
            rw [asReload_of_asWideReload hr] at this
            rw [hsm0, Option.some.inj this]
          rw [hi] at hsm
          have hsm' := slotMov?_resrc hsm
            (cellParts?_physGP (by rwa [PhysImgFold.isPhysGP_eq_gpNameB]))
          simp [hds, goodHoldB, hrg, hrs, hsm']
    · have hh' := stepLoad_memHolderRegKey env i hh hmi
      cases ha : slotSaveSrc? slotArr i with
      | some X =>
        rw [saveFreshB_cons_some ha, Bool.and_eq_true] at hf
        obtain ⟨q, mn, hi, hmn, hqs⟩ := slotSaveSrc?_eq_some ha
        have hr : asWideReload i.li_i = some (q, X, mn) := by
          simp [hi, CatCrypt.Crypto.Optimizer.LoadCSE.asWideReload, hmn]
        refine loadChkB_scan hq is seen _ hf.2 hm' hd' hh' hg' fun k r hkr => ?_
        rcases mem_stepLoad hkr with hkr | ⟨mn', hr'⟩
        · exact hk k r hkr
        · rw [hr] at hr'
          simp only [Option.some.injEq, Prod.mk.injEq] at hr'
          obtain ⟨rfl, -, -⟩ := hr'
          exact Or.inr hqs
      | none =>
        rw [saveFreshB_cons_none ha] at hf
        refine loadChkB_scan hq is _ _ hf hm' hd' hh' hg' fun k r hkr => ?_
        rcases mem_stepLoad hkr with hkr | ⟨mn', hr'⟩
        · exact (hk k r hkr).imp_left (List.mem_append_left _)
        · obtain ⟨hi, -⟩ := asWideReload_eq hr'
          left
          apply List.mem_append_right
          simp [hi, instrNames, opNames]

/-- **`loadChkB` from `saveFreshB`.** On a body with no 64-bit move between two memory names,
    whose 64-bit moves move into general-purpose or memory names, and in which no array-slot
    move reads a name met before, every redirect of the load CSE passes the rewrite check: a
    redirect onto a holder of the source of an array-slot move is declined, since the holder
    is an array slot, and every other holder is a general-purpose name that is no array
    slot. -/
theorem loadChkB_of_fresh {b : Lcmd}
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    (hf : saveFreshB slotArr [] b = true) (hm : memMovFreeB b = true)
    (hd : ∀ j ∈ b, ∀ d s mn, asWideReload j.li_i = some (d, s, mn) →
      gpNameB d = true ∨ isMemName d = true) : loadChkB slotArr [] b = true :=
  loadChkB_scan hq b [] [] hf hm hd Optimizer.LoadCSE.memHolderRegKey_nil
    (fun _ _ h => by cases h) (fun _ _ h => by cases h)

end LoadChk

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgLoadOrder
