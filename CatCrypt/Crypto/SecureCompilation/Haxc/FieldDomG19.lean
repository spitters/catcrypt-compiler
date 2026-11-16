/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomAssemble
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomEntrySlot
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomArgReallocBody

/-!
# Readers of a save slot through the fusion post-pass

A reader of the save slot of a register (`SlotReader`) is a move with one source. The
high-product fusion rewrites only operations with two sources, so it keeps every reader. The
dead-write elimination of `deadWriteRet` drops a pure register write whose destination is next
accessed by a write of a widening multiply; it keeps a reader whose destination is not so
killed. In a straight-line run of the optimizer, the scheduler permutes the run, and the copy
propagation rewrites only physical-register sources and drops only candidate moves between
physical registers, so both keep a reader of the save slot of a parameter register.

## Main results

* `slotReader_fuseMulHiBody`: the high-product fusion keeps a reader.
* `mem_dropDeadWriteBody`: the dead-write elimination keeps an instruction whose mark is false.
* `slotReader_deadWriteRet`: `deadWriteRet` keeps a reader whose destination is not killed by
  a widening multiply.
* `mem_scheduleBody`: the scheduler keeps every instruction.
* `slotReader_copyPropagateBody`: the copy propagation keeps a reader of the save slot of a
  parameter register.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiAux fuseMulHiBody
  ScratchEnv)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (deadWriteMarks keptL
  dropDeadWriteBody killedByMulx pureWrDst?)

/-! ## 1. The high-product fusion -/

/-- **The high-product fusion keeps every reader of a save slot**: a reader has one source. -/
theorem slotReader_fuseMulHiAux {R : String} (s : Bool) :
    ∀ (c : Lcmd) (env : ScratchEnv) (pend : List (String × String)) (x : Linstr), x ∈ c →
      SlotReader R x.li_i → x ∈ fuseMulHiAux s env pend c := by
  intro c
  induction c with
  | nil => intro _ _ x hx; cases hx
  | cons i rest ih =>
    intro env pend x hx hr
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨d, o, he, -, -⟩ := hr
      rw [fuseMulHiAux]
      split
      · next heq => rw [he] at heq; simp at heq
      · exact List.mem_cons_self
    · have hr' := fun e p => ih e p x hx hr
      rw [fuseMulHiAux]
      try dsimp only
      repeat' split
      all_goals simp [hr']

/-- **The high-product fusion keeps every reader of a save slot.** -/
theorem slotReader_fuseMulHiBody {R : String} (s : Bool) {b : Lcmd} {x : Linstr} (hx : x ∈ b)
    (hr : SlotReader R x.li_i) : x ∈ fuseMulHiBody b s :=
  slotReader_fuseMulHiAux s b [] [] x hx hr

/-! ## 2. The dead-write elimination -/

/-- The marks of a body end with the marks of each of its suffixes. -/
theorem deadWriteMarks_append (xs zs : Lcmd) :
    ∃ M, deadWriteMarks (xs ++ zs) = M ++ deadWriteMarks zs := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨M, hM⟩ := ih
    rw [List.cons_append, deadWriteMarks, hM]
    exact ⟨_ :: M, rfl⟩

/-- **The dead-write elimination keeps an instruction whose destination is not killed by a
    widening multiply** among the unmarked instructions after it. -/
theorem mem_dropDeadWriteBody {xs ys : Lcmd} {li : Linstr}
    (hk : ∀ d, pureWrDst? li.li_i = some d → killedByMulx d (deadWriteMarks ys) = false) :
    li ∈ dropDeadWriteBody (xs ++ li :: ys) := by
  obtain ⟨M, hM⟩ := deadWriteMarks_append xs (li :: ys)
  unfold dropDeadWriteBody
  rw [hM, deadWriteMarks]
  simp only [keptL, List.filter_append, List.map_append, List.mem_append]
  right
  cases h : pureWrDst? li.li_i with
  | none => simp
  | some d => simp [hk d h]

/-- **`deadWriteRet` keeps a reader of a save slot whose destination is not killed by a
    widening multiply** among the unmarked instructions after it. -/
theorem slotReader_deadWriteRet {R : String} {xs ys : Lcmd} {li : Linstr}
    (hr : SlotReader R li.li_i)
    (hk : ∀ d, pureWrDst? li.li_i = some d →
      killedByMulx d (deadWriteMarks ys.dropLast) = false) :
    li ∈ deadWriteRet (xs ++ li :: ys) := by
  obtain ⟨d, o, he, -, -⟩ := hr
  unfold deadWriteRet
  split
  · next r hlast =>
    split
    · next hc =>
      cases ys with
      | nil =>
        rw [List.getLast?_append_of_ne_nil _ (by simp)] at hlast
        simp only [List.getLast?_singleton, Option.some.injEq] at hlast
        subst hlast
        simp [he] at hc
      | cons y ys' =>
        have hd : (xs ++ li :: y :: ys').dropLast = xs ++ li :: (y :: ys').dropLast := by
          rw [List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil (by simp)]
        rw [hd]
        exact List.mem_append_left _ (mem_dropDeadWriteBody hk)
    · simp
  · simp

/-! ## 3. The scheduler and the copy propagation -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate (propagateAux deadElimStep
  deadElimBody copyPropagateBody moveShape isPhysGP rewriteOperand MoveFact)

/-- **The scheduler keeps every instruction**: it permutes the body. -/
theorem mem_scheduleBody {b : Lcmd} {x : Linstr} (hx : x ∈ b) :
    x ∈ VIR.LprogScheduler.scheduleBody b :=
  (VIR.LprogScheduler.scheduleBody_perm b).mem_iff.mpr hx

/-- The save slot of a parameter register is no physical register. -/
theorem isPhysGP_slotOfReg {R : String} (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX") :
    isPhysGP (JasminLsemAddrImage.slotOfReg R) = false := by
  rcases hR with rfl | rfl | rfl <;> decide

/-- **The forward move propagation keeps a reader of the save slot of a parameter register**:
    its source is no physical register, so no fact rewrites it. -/
theorem slotReader_propagateAux {R : String} (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX") :
    ∀ (c : Lcmd) (facts : List MoveFact) (x : Linstr), x ∈ c → SlotReader R x.li_i →
      x ∈ propagateAux facts c := by
  intro c
  induction c with
  | nil => intro _ x hx; cases hx
  | cons i rest ih =>
    intro facts x hx hr
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨d, o, he, -, -⟩ := hr
      rw [propagateAux, he]
      dsimp only
      split
      · have hs : ∀ w a ds, rewriteOperand facts w a ds
            (.reg (JasminLsemAddrImage.slotOfReg R)) = .reg (JasminLsemAddrImage.slotOfReg R) := by
          intro w a ds
          simp [rewriteOperand, isPhysGP_slotOfReg hR]
        simp only [List.map_cons, List.map_nil, hs]
        rw [← he]
        exact List.mem_cons_self
      · exact List.mem_cons_self
    · have hr' := fun f => ih f x hx hr
      rw [propagateAux]
      repeat' split
      all_goals simp [hr']

/-- One backward step of the dead-move elimination keeps the processed suffix. -/
theorem deadElimStep_mono (i : Linstr) (p : List String × Lcmd) :
    ∀ y ∈ p.2, y ∈ (deadElimStep i p).2 := by
  intro y hy
  obtain ⟨live, acc⟩ := p
  unfold deadElimStep
  split
  · split
    · grind
    · simp_all

/-- A reader of the save slot of a parameter register is no candidate move. -/
theorem moveShape_of_slotReader {R : String} (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX")
    {x : Linstr} (hr : SlotReader R x.li_i) : moveShape x = none := by
  obtain ⟨d, o, he, -, -⟩ := hr
  unfold moveShape
  rw [he]
  simp [X86Backend.LcmdCopyPropagate.isFactSrc, isPhysGP_slotOfReg hR]

/-- **The dead-move elimination keeps a reader of the save slot of a parameter register.** -/
theorem slotReader_foldr_deadElimStep {R : String} (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX") :
    ∀ (c : Lcmd) (p : List String × Lcmd),
      (∀ y ∈ p.2, y ∈ (c.foldr deadElimStep p).2) ∧
      ∀ x ∈ c, SlotReader R x.li_i → x ∈ (c.foldr deadElimStep p).2 := by
  intro c p
  induction c with
  | nil => exact ⟨fun y hy => hy, fun x hx => by cases hx⟩
  | cons i rest ih =>
    obtain ⟨k1, k2⟩ := ih
    rw [List.foldr_cons]
    refine ⟨fun y hy => deadElimStep_mono i _ y (k1 y hy), fun x hx hr => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨d, o, he, -, -⟩ := id hr
      have hm := moveShape_of_slotReader hR hr
      generalize rest.foldr deadElimStep p = q
      obtain ⟨live, acc⟩ := q
      unfold deadElimStep
      rw [he]
      dsimp only
      split
      · rw [hm]
        simp
      · simp
    · exact deadElimStep_mono i _ x (k2 x hx hr)

/-- **The copy propagation keeps a reader of the save slot of a parameter register.** -/
theorem slotReader_copyPropagateBody {R : String} (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX")
    {b : Lcmd} {x : Linstr} (hx : x ∈ b) (hr : SlotReader R x.li_i) :
    x ∈ copyPropagateBody b :=
  (slotReader_foldr_deadElimStep hR _ _).2 x (slotReader_propagateAux hR b [] x hx hr) hr

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
