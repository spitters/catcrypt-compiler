/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomArgReaders

/-!
# Readers of a save slot through the re-allocation of a run

The re-allocation of a run checks a list of location decisions against the run annotated with
the names live after each instruction, and materializes it (`goAcc`). A reader of the save slot
of a parameter register reads a frame cell, which is no location, so its source is kept. When
its destination is live after it, the check neither drops it as a dead move nor coalesces it
as a copy (its source is no register), so the materialized run has a reader at the location of
its destination. When no decision list passes the check, the run is kept.

## Main results

* `goAcc_slotReader`: the materialization keeps a reader whose destination is live after it.
* `mem_annotate`: every instruction of a run is annotated.
* `reallocRun_slotReader`: the re-allocation of a run keeps a reader whose destination is live
  after it.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc (FI goAcc annotate
  reallocRun reallocWith isLoc isPool okLoc renOp look Cur)

/-- The save slot of a parameter register is no location. -/
theorem isLoc_slot {R : String} (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX") :
    isLoc (slotOfReg R) = false := by
  rcases hR with rfl | rfl | rfl <;> decide +kernel

/-- The save slot of a parameter register is no pool register. -/
theorem isPool_slot {R : String} (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX") :
    isPool (slotOfReg R) = false := by
  rcases hR with rfl | rfl | rfl <;> decide +kernel

/-- **The materialization of the re-allocation keeps a reader of the save slot of a
    parameter register whose destination is live after it**, at a location of its
    destination; and it keeps the instructions already materialized. -/
theorem goAcc_slotReader {lend : List String} {R : String}
    (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX") :
    ∀ (ann : List (FI × List String)) (m : Cur) (cs : List String) (acc out : List FI),
      goAcc lend m ann cs acc = some out →
      (∀ x ∈ acc, x ∈ out) ∧
      (∀ i la, (i, la) ∈ ann → SlotReader R i.toR → la.contains i.d = true →
        ∃ j ∈ out, SlotReader R j.toR)
  | [], m, [], acc, out, h => by
      simp only [goAcc] at h
      split at h
      · cases h
        exact ⟨fun x hx => List.mem_reverse.mpr hx, fun i la hi => nomatch hi⟩
      · cases h
  | [], _, _ :: _, _, _, h => by simp [goAcc] at h
  | _ :: _, _, [], _, _, h => by simp [goAcc] at h
  | (i, la) :: rest, m, c :: cs, acc, out, h => by
      have hsrc : ∀ (s : String), isLoc s = false → renOp m (.reg s) = .reg s := by
        intro s hs
        simp [renOp, hs]
      -- the recursive call keeps `acc` or `x :: acc`
      have key : ∀ (m' : Cur) (acc' : List FI),
          goAcc lend m' rest cs acc' = some out → (∀ x ∈ acc, x ∈ acc') →
          (∀ x ∈ acc, x ∈ out) ∧
          (∀ i' la', (i', la') ∈ rest → SlotReader R i'.toR → la'.contains i'.d = true →
            ∃ j ∈ out, SlotReader R j.toR) ∧ (∀ x ∈ acc', x ∈ out) := by
        intro m' acc' h' hacc
        obtain ⟨h1, h2⟩ := goAcc_slotReader hR rest m' cs acc' out h'
        exact ⟨fun x hx => h1 x (hacc x hx), h2, h1⟩
      unfold goAcc at h
      split at h
      · split at h
        · split at h
          · rename_i hloc hok
            split at h
            · -- a coalesced copy
              rename_i hcp
              obtain ⟨k1, k2, -⟩ := key _ _ h (fun x hx => hx)
              refine ⟨k1, fun i' la' hi' hr hl => ?_⟩
              rcases List.mem_cons.mp hi' with he | hi'
              · cases he
                exfalso
                obtain ⟨d, o, hd, -, hne⟩ := hr
                simp only [FI.toR, LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
                  and_true] at hd
                obtain ⟨rfl, -, hs⟩ := hd
                simp only [Bool.and_eq_true, beq_iff_eq] at hcp
                rw [hs] at hcp
                simp only [List.map_cons, List.map_nil, hsrc _ (isLoc_slot hR),
                  List.cons.injEq, LOperand.reg.injEq, and_true] at hcp
                simp only [okLoc, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
                rcases hok.1 with hp | hp
                · rw [← hcp.2] at hp
                  rw [isPool_slot hR] at hp
                  cases hp
                · exact hne (hcp.2.trans hp).symm
              · exact k2 i' la' hi' hr hl
            · split at h
              · -- a dead move
                rename_i hdead
                obtain ⟨k1, k2, -⟩ := key _ _ h (fun x hx => hx)
                refine ⟨k1, fun i' la' hi' hr hl => ?_⟩
                rcases List.mem_cons.mp hi' with he | hi'
                · cases he
                  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hdead
                  rw [hl] at hdead
                  cases hdead.2
                · exact k2 i' la' hi' hr hl
              · split at h
                · -- an emitted instruction at the location `c`
                  obtain ⟨k1, k2, k3⟩ := key _ _ h (fun x hx => List.mem_cons_of_mem _ hx)
                  refine ⟨k1, fun i' la' hi' hr hl => ?_⟩
                  rcases List.mem_cons.mp hi' with he | hi'
                  · cases he
                    refine ⟨_, k3 _ List.mem_cons_self, ?_⟩
                    obtain ⟨d, o, hd, ho, hne⟩ := hr
                    simp only [FI.toR, LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
                      and_true] at hd
                    obtain ⟨rfl, rfl, hs⟩ := hd
                    refine ⟨c, i.opn, ?_, ho, ?_⟩
                    · simp [FI.toR, hs, hsrc _ (isLoc_slot hR)]
                    · intro hc
                      simp only [okLoc, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
                      rcases hok.1 with hp | hp
                      · rw [hc, isPool_slot hR] at hp
                        cases hp
                      · exact hne (hp ▸ hc)
                  · exact k2 i' la' hi' hr hl
                · cases h
          · cases h
        · split at h
          · -- an emitted instruction at its own name
            obtain ⟨k1, k2, k3⟩ := key _ _ h (fun x hx => List.mem_cons_of_mem _ hx)
            refine ⟨k1, fun i' la' hi' hr hl => ?_⟩
            rcases List.mem_cons.mp hi' with he | hi'
            · cases he
              refine ⟨_, k3 _ List.mem_cons_self, ?_⟩
              obtain ⟨d, o, hd, ho, hne⟩ := hr
              simp only [FI.toR, LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
                and_true] at hd
              obtain ⟨rfl, rfl, hs⟩ := hd
              exact ⟨i.d, i.opn, by simp [FI.toR, hs, hsrc _ (isLoc_slot hR)], ho, hne⟩
            · exact k2 i' la' hi' hr hl
          · cases h
      · cases h

/-- **Every instruction of a run is annotated** with the names live after it. -/
theorem mem_annotate (lend : List String) :
    ∀ (is : List FI) (i : FI), i ∈ is → ∃ la, (i, la) ∈ (annotate lend is).1
  | [], _, h => nomatch h
  | j :: is, i, h => by
      rw [X86Backend.LprogGpRealloc.annotate_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨_, List.mem_cons_self⟩
      · obtain ⟨la, hla⟩ := mem_annotate lend is i h
        exact ⟨la, List.mem_cons_of_mem _ hla⟩

/-- **The re-allocation of a run keeps a reader of the save slot of a parameter register
    whose destination is live after it.** -/
theorem reallocRun_slotReader {lend : List String} {is : List FI} {R : String}
    (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX") {i : FI} (hi : i ∈ is) (hr : SlotReader R i.toR)
    (hl : ∀ la, (i, la) ∈ (annotate lend is).1 → la.contains i.d = true) :
    ∃ j ∈ reallocRun lend is, SlotReader R j.toR := by
  unfold reallocRun reallocWith
  split
  · rename_i out hout
    obtain ⟨cs, -, hcs⟩ := List.exists_of_findSome?_eq_some hout
    obtain ⟨la, hla⟩ := mem_annotate lend is i hi
    exact (goAcc_slotReader hR _ _ _ _ _ hcs).2 i la hla hr (hl la hla)
  · exact ⟨i, hi, hr⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
