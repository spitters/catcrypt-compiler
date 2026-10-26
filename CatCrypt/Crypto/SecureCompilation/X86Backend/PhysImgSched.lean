/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler

/-!
# The image class under the scheduler

The scheduler `LprogScheduler.scheduleBody` reorders a body by adjacent transpositions of
independent instructions (`LprogScheduler.indep`), none of which is a barrier
(`LprogScheduler.isBarrierOp`). A write of a frame slot `qsave.R` is a barrier, so when every
array slot is a frame slot, an instruction that the scheduler moves writes no array slot.

The reload scan `reloadOf` passes an `Lopn` that writes neither the carried name nor an array
slot, and at a move into the carried name continues with a source of that move. Two independent
instructions that write no array slot therefore give the same scan in either order
(`reloadOf_swap`). The entry scan `entryRegB` reads the prefix only as a set, and the
transposed instructions themselves are no accesses and write no array slot, so a transposition
keeps the image class `physImgB` (`physImgB_schedSwap`), and so does the scheduler.

## Main results

* `SchedSwap`, `scheduleBody_schedSwap`: the scheduled body is reached from the input by
  transpositions of adjacent independent instructions.
* `reloadOf_swap`: the reload scan behind a transposed pair of independent instructions that
  write no array slot is unchanged.
* `physImgB_schedSwap`, `physImgB_scheduleBody`: the scheduler keeps the image class when every
  array slot is a frame slot `qsave.R`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSched

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass

variable {slotArr : String → Option (String × Nat)}

/-! ## 1. The scan at one instruction -/

/-- The scan passes an operation with no indexed operand and no array-slot destination that
    does not write the carried name. -/
theorem scan_one_pass {j : Linstr} (hop : isOpn j.li_i = true) (har : hasArrIdx j.li_i = false)
    (hd : DstOk slotArr j.li_i) {z : String} (hz : z ∉ writeToks j.li_i) :
    scanExit slotArr [j] 1 z = some z ∧ reloadOf slotArr [j] 1 z = none := by
  cases hj : j.li_i with
  | Lopn ds o ss =>
    rw [hj] at har hd hz
    cases hm : slotMov? (.Lopn ds o ss) with
    | some p =>
      obtain ⟨d, q⟩ := p
      obtain ⟨_, he⟩ := slotMov?_eq hm
      cases he
      have hdz : d ≠ z := by
        rintro rfl; exact hz (by simp [writeToks, opTok])
      have hdn : slotArr d = none := (hd _ _ _ rfl _ (by simp)).1 d rfl
      simp [scanExit, reloadOf, hj, hm, hdz, hdn]
    | none =>
      have hany : ds.any (dstHitB slotArr z) = false := by
        rw [List.any_eq_false]
        intro x hx
        have hok := hd _ _ _ rfl x hx
        cases x with
        | reg q =>
          have hqz : q ≠ z := by
            rintro rfl; exact hz (List.mem_filterMap.mpr ⟨_, hx, rfl⟩)
          simp [dstHitB, hqz, hok.1 q rfl]
        | arrIdx q i sc =>
          simp only [hasArrIdx, Bool.or_eq_false_iff, List.any_eq_false] at har
          exact absurd rfl (har.1.2 _ hx)
        | _ => simp [dstHitB]
      simp [scanExit, reloadOf, hj, hm, hany]
  | _ => simp [hj, isOpn] at hop

/-- The name the scan carries out of one instruction is the carried name or a source of the
    instruction. -/
theorem scan_one_exit {j : Linstr} {z w : String} (h : scanExit slotArr [j] 1 z = some w) :
    w = z ∨ w ∈ readToksSem j.li_i := by
  simp only [scanExit, List.getElem?_cons_zero] at h
  cases hm : slotMov? j.li_i with
  | some p =>
    obtain ⟨d, q⟩ := p
    rw [hm] at h
    simp only at h
    split_ifs at h with h1 h2 h3 <;> try cases h
    · right
      cases hj : j.li_i with
      | Lopn ds o ss =>
        rw [hj] at hm
        obtain ⟨_, he⟩ := slotMov?_eq hm
        cases he
        simp [readToksSem, srcTok]
      | _ => simp [hj, slotMov?] at hm
    · left; rfl
  | none =>
    rw [hm] at h
    simp only at h
    cases hj : j.li_i with
    | Lopn ds o ss =>
      rw [hj] at h
      simp only at h
      split_ifs at h
      cases h; left; rfl
    | _ => rw [hj] at h; cases h

/-- The scan that carries a name out of one instruction finds no result inside it. -/
theorem scan_one_excl {j : Linstr} {z w : String} (h : scanExit slotArr [j] 1 z = some w) :
    reloadOf slotArr [j] 1 z = none := by
  simp only [scanExit, List.getElem?_cons_zero] at h
  simp only [reloadOf, List.getElem?_cons_zero]
  cases hm : slotMov? j.li_i with
  | some p =>
    obtain ⟨d, q⟩ := p
    rw [hm] at h
    simp only at h ⊢
    split_ifs at h ⊢ <;> rfl
  | none =>
    rw [hm] at h
    simp only at h ⊢
    cases hj : j.li_i with
    | Lopn ds o ss =>
      rw [hj] at h
      simp only at h ⊢
      split_ifs at h ⊢
      rfl
    | _ => rfl

/-! ## 2. Two instructions in either order -/

/-- The scans of a pair whose first instruction passes the carried name and every source of
    the second instruction are those of the transposed pair. -/
theorem scan_pair_swap_of_pass {x y : Linstr} {z : String}
    (hpz : scanExit slotArr [x] 1 z = some z ∧ reloadOf slotArr [x] 1 z = none)
    (hpr : ∀ w ∈ readToksSem y.li_i,
      scanExit slotArr [x] 1 w = some w ∧ reloadOf slotArr [x] 1 w = none) :
    scanExit slotArr [x, y] 2 z = scanExit slotArr [y, x] 2 z ∧
      reloadOf slotArr [x, y] 2 z = reloadOf slotArr [y, x] 2 z := by
  have r1 := reloadOf_append_scanExit slotArr [x] [y] 1 z
  have r2 := reloadOf_append_scanExit slotArr [y] [x] 1 z
  have s1 := scanExit_snoc slotArr [x] y z
  have s2 := scanExit_snoc slotArr [y] x z
  simp only [List.singleton_append, List.length_singleton] at r1 r2 s1 s2
  rw [r1, r2, s1, s2, hpz.1]
  cases hs : scanExit slotArr [y] 1 z with
  | none => simp [hs]
  | some w =>
    have hw : scanExit slotArr [x] 1 w = some w ∧ reloadOf slotArr [x] 1 w = none := by
      rcases scan_one_exit hs with rfl | hr
      · exact hpz
      · exact hpr w hr
    simp [hs, hw.1, hw.2, scan_one_excl hs]

/-- The scans of two independent instructions that write no array slot do not depend on
    their order. -/
theorem scan_pair_swap {x y : Linstr} (hind : indep x.li_i y.li_i = true)
    (hx : DstOk slotArr x.li_i) (hy : DstOk slotArr y.li_i) (z : String) :
    scanExit slotArr [x, y] 2 z = scanExit slotArr [y, x] 2 z ∧
      reloadOf slotArr [x, y] 2 z = reloadOf slotArr [y, x] 2 z := by
  have hind' : indep y.li_i x.li_i = true := by rw [indep_symm]; exact hind
  have passX : ∀ w, w ∉ writeToks x.li_i →
      scanExit slotArr [x] 1 w = some w ∧ reloadOf slotArr [x] 1 w = none :=
    fun w hw => scan_one_pass (indep_isOpn_left hind) (indep_arrIdx_left hind) hx hw
  have passY : ∀ w, w ∉ writeToks y.li_i →
      scanExit slotArr [y] 1 w = some w ∧ reloadOf slotArr [y] 1 w = none :=
    fun w hw => scan_one_pass (indep_isOpn_right hind) (indep_arrIdx_right hind) hy hw
  by_cases hzx : z ∈ writeToks x.li_i
  · have hzy : z ∉ writeToks y.li_i := fun hzy =>
      (disjointL_iff _ _).mp (indep_ww hind) z hzx z hzy rfl
    have := scan_pair_swap_of_pass (passY z hzy) (fun w hw => passY w fun hwy =>
      (disjointL_iff _ _).mp (indep_wr hind') w hwy w hw rfl)
    exact ⟨this.1.symm, this.2.symm⟩
  · exact scan_pair_swap_of_pass (passX z hzx) (fun w hw => passX w fun hwx =>
      (disjointL_iff _ _).mp (indep_wr hind) w hwx w hw rfl)

/-- **The reload scan behind a transposed pair.** Transposing two adjacent independent
    instructions that write no array slot keeps the reload scan at every position behind them
    and for every name. -/
theorem reloadOf_swap {A C : Lcmd} {x y : Linstr} (hind : indep x.li_i y.li_i = true)
    (hx : DstOk slotArr x.li_i) (hy : DstOk slotArr y.li_i) (k : Nat) (z : String) :
    reloadOf slotArr (A ++ y :: x :: C) (A.length + 2 + k) z =
      reloadOf slotArr (A ++ x :: y :: C) (A.length + 2 + k) z := by
  have e1 : A ++ x :: y :: C = (A ++ [x, y]) ++ C := by simp
  have e2 : A ++ y :: x :: C = (A ++ [y, x]) ++ C := by simp
  have l1 : A.length + 2 + k = (A ++ [x, y]).length + k := by simp
  have l2 : A.length + 2 + k = (A ++ [y, x]).length + k := by simp
  rw [e1, e2, l1, reloadOf_append_scanExit, ← l1, l2, reloadOf_append_scanExit]
  cases scanExit slotArr C k z with
  | none => rfl
  | some w =>
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [reloadOf_append_scanExit slotArr A [y, x] 2 w,
      reloadOf_append_scanExit slotArr A [x, y] 2 w]
    obtain ⟨hs, hr⟩ := scan_pair_swap hind hx hy w
    rw [hs, hr]

/-! ## 3. The class under one transposition -/

/-- `b'` is `b` with two adjacent independent instructions transposed. -/
def SchedSwap (b b' : Lcmd) : Prop :=
  ∃ A C x y, b = A ++ x :: y :: C ∧ b' = A ++ y :: x :: C ∧ indep x.li_i y.li_i = true

theorem SchedSwap.cons {b b' : Lcmd} (a : Linstr) (h : SchedSwap b b') :
    SchedSwap (a :: b) (a :: b') := by
  obtain ⟨A, C, x, y, rfl, rfl, hi⟩ := h
  exact ⟨a :: A, C, x, y, rfl, rfl, hi⟩

/-- One bubble pass is reached by transpositions of adjacent independent instructions. -/
theorem bubble_schedSwap : ∀ b : Lcmd, Relation.ReflTransGen SchedSwap b (bubble b) := by
  intro b
  induction b using bubble.induct with
  | case1 => simp only [bubble]; exact .refl
  | case2 i => simp only [bubble]; exact .refl
  | case3 i1 i2 rest hcond ih =>
    simp only [bubble, ite_eq_left hcond]
    simp only [Bool.and_eq_true] at hcond
    refine Relation.ReflTransGen.head ⟨[], rest, i1, i2, rfl, rfl, hcond.1⟩ ?_
    exact ih.lift (List.cons i2) fun a b (h : SchedSwap a b) => h.cons i2
  | case4 i1 i2 rest hcond ih =>
    simp only [bubble, ite_eq_right hcond]
    exact ih.lift (List.cons i1) fun a b (h : SchedSwap a b) => h.cons i1

/-- The scheduled body is reached by transpositions of adjacent independent instructions. -/
theorem scheduleBody_schedSwap (b : Lcmd) :
    Relation.ReflTransGen SchedSwap b (scheduleBody b) := by
  rw [scheduleBody_eq_bubbleN]
  generalize b.length = n
  induction n generalizing b with
  | zero => exact .refl
  | succ n ih => exact (bubble_schedSwap b).trans (ih (bubble b))

/-- An instruction that the scheduler moves writes no array slot when every array slot is a
    frame slot and the instruction passes `slotWriteB`. -/
theorem dstOk_of_indep_left {i i' : LinstrR} (hind : indep i i' = true)
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {b : Lcmd} {k : Nat} (hw : slotWriteB slotArr b k i = true) : DstOk slotArr i := by
  have hbar : isBarrierOp i = false := by
    simp only [indep, Bool.and_eq_true, Bool.not_eq_true'] at hind; exact hind.1.1.1.1.2
  have har := indep_arrIdx_left hind
  intro ds o ss hi x hx
  subst hi
  simp only [slotWriteB, List.all_eq_true] at hw
  have hwx := hw x hx
  refine ⟨?_, ?_, ?_⟩
  · rintro q rfl
    have hp := slotDst_of_not_isBarrierOp hbar hx
    cases h : slotArr q with
    | none => rfl
    | some _ => have := hq q (by simp [h]); rw [hp] at this; cases this
  · rintro q n rfl
    simpa using hwx
  · rintro q j sc rfl
    simp only [hasArrIdx, Bool.or_eq_false_iff, List.any_eq_false] at har
    exact absurd rfl (har.1.2 _ hx)

/-- A mnemonic that reads as `ZEROARR` or `STOREIMM` after `untagCaret` has that base as its
    part before the first `^`. -/
theorem takeWhile_caret_of_untagCaret {o b : String} (hu : LprogAsmPrinter.untagCaret o = b)
    (hb : b = "ZEROARR" ∨ b = "STOREIMM") :
    String.ofList (o.toList.takeWhile (· != '^')) = b := by
  by_cases hc : '^' ∈ o.toList
  · have hcc : o.toList.contains '^' = true := by simpa using hc
    unfold LprogAsmPrinter.untagCaret at hu
    simp only [hcc, ↓reduceIte] at hu
    split at hu
    · exfalso
      have := congrArg (fun s => s.toList.getLast?) hu
      rcases hb with rfl | rfl <;> simp at this
    · unfold stripWidthTag at hu
      simp only [hcc, ↓reduceIte] at hu
      exact hu
  · rw [LprogAsmPrinter.untagCaret_of_caret_free hc] at hu
    subst hu
    rcases hb with h | h <;> rw [h] <;> decide +kernel

/-- **The class under one transposition.** When every array slot is a frame slot, transposing
    two adjacent independent instructions keeps `physImgB`. -/
theorem physImgB_schedSwap (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {b b' : Lcmd} (hs : SchedSwap b b') (h : physImgB slotArr b = true) :
    physImgB slotArr b' = true := by
  obtain ⟨A, C, x, y, rfl, rfl, hind⟩ := hs
  have hind' : indep y.li_i x.li_i = true := by rw [indep_symm]; exact hind
  have gx : (A ++ x :: y :: C)[A.length]? = some x := by simp
  have gy : (A ++ x :: y :: C)[A.length + 1]? = some y := by simp
  have hpos : ∀ m (i : Linstr), (A ++ x :: y :: C)[m]? = some i →
      slotWriteB slotArr (A ++ x :: y :: C) m i.li_i = true := by
    intro m i hm
    have := List.all_eq_true.mp h m
      (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hm).1)
    rw [hm] at this
    simp only [Bool.and_eq_true] at this
    exact this.2
  have hx : DstOk slotArr x.li_i := dstOk_of_indep_left hind hq (hpos _ _ gx)
  have hy : DstOk slotArr y.li_i := dstOk_of_indep_left hind' hq (hpos _ _ gy)
  have noAcc : ∀ (j : Linstr) (z : String), hasArrIdx j.li_i = false →
      ¬ AccBase z j.li_i := by
    rintro j z hj (⟨ds, o, y', ss, he⟩ | ⟨ds, o, ss, he, hai⟩)
    · rw [he] at hj
      simp [hasArrIdx, opIsArrIdx] at hj
    · rw [he] at hj hai
      simp only [isArrImmB, Bool.or_eq_true, beq_iff_eq] at hai
      have hw : String.ofList (o.toList.takeWhile (· != '^')) = "ZEROARR" ∨
          String.ofList (o.toList.takeWhile (· != '^')) = "STOREIMM" := by
        rcases hai with h | h
        · exact Or.inl (takeWhile_caret_of_untagCaret h (Or.inl rfl))
        · exact Or.inr (takeWhile_caret_of_untagCaret h (Or.inr rfl))
      rw [hasArrIdx_of_untag hw] at hj
      cases hj
  refine physImgB_of_embed h fun k i hk => ?_
  rcases Nat.lt_or_ge k A.length with hlt | hge
  · -- in front of the pair
    right
    refine ⟨k, ?_, ?_, Or.inl ?_⟩
    · rw [List.getElem?_append_left hlt] at hk ⊢; exact hk
    · intro z _ ha
      rw [accArr_append_left slotArr A _ k z hlt.le] at ha ⊢
      exact ha
    · intro R he
      unfold entryRegB at he ⊢
      rw [List.take_append_of_le_length hlt.le] at he ⊢
      exact he
  rcases Nat.lt_or_ge k (A.length + 2) with hlt2 | hge2
  · -- one of the pair
    right
    have hpos : k = A.length ∨ k = A.length + 1 := by omega
    rcases hpos with rfl | rfl
    · have : i = y := by simpa using hk.symm
      subst this
      exact ⟨A.length + 1, gy, fun z hz => absurd hz (noAcc _ z (indep_arrIdx_right hind)),
        Or.inr (slotWriteB_of_dstOk hy _ _)⟩
    · have : i = x := by simpa using hk.symm
      subst this
      exact ⟨A.length, gx, fun z hz => absurd hz (noAcc _ z (indep_arrIdx_left hind)),
        Or.inr (slotWriteB_of_dstOk hx _ _)⟩
  · -- behind the pair
    right
    obtain ⟨j, rfl⟩ : ∃ j, k = A.length + 2 + j := ⟨k - (A.length + 2), by omega⟩
    refine ⟨A.length + 2 + j, ?_, ?_, Or.inl ?_⟩
    · rw [← hk, List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        show A.length + 2 + j - A.length = j + 2 by omega]
      rfl
    · intro z _ ha
      simpa only [accArr, reloadOf_swap hind hx hy j z] using ha
    · intro R he
      unfold entryRegB at he ⊢
      have e : ∀ u v : Linstr, (A ++ u :: v :: C).take (A.length + 2 + j) =
          A ++ u :: v :: C.take j := by
        intro u v
        rw [List.take_append, List.take_of_length_le (by omega)]
        simp [show A.length + 2 + j - A.length = j + 2 by omega]
      rw [e] at he ⊢
      simp only [List.all_append, List.all_cons] at he ⊢
      rw [← he]
      ac_rfl

/-- **The scheduler keeps the image class.** When every array slot is a frame slot `qsave.R`,
    `scheduleBody` keeps `physImgB`. -/
theorem physImgB_scheduleBody {sl : String → Option (String × Nat)}
    (hq : ∀ q, (sl q).isSome = true → hasPrefix q "qsave." = true) {b : Lcmd}
    (h : physImgB sl b = true) : physImgB sl (scheduleBody b) = true := by
  have hr := scheduleBody_schedSwap b
  generalize scheduleBody b = b' at hr ⊢
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact physImgB_schedSwap hq hs ih

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSched
