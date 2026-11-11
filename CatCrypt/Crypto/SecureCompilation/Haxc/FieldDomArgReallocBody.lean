/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomArgRealloc
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg

/-!
# Readers of a save slot through the re-allocation of a body

The re-allocation of a body splits it into runs of fragment instructions and the instructions
between, keeps every instruction between, and re-allocates every run at the live-out set the
instructions after it give. An instruction of the body lies in one of the pieces. So a reader
of the save slot of a parameter register is kept when it lies between runs, and has a reader
in the re-allocation of its run when its destination is live after it in the run at every
live-out set (`LiveInRun`).

## Main definitions

* `LiveInRun`: the destination of an instruction of a run is live after it, at every live-out
  set of the run.

## Main results

* `mem_pieces_of_mem`: an instruction of a body is an instruction between runs or the
  instruction of a fragment instruction of a run.
* `reallocBody_slotReader`: the re-allocation of a body keeps a reader whose destination is
  live after it in its run.
* `slotReader_printedBody_of_foldBody`: such a reader of the body after the optimizer and the
  constant-index fold is a reader of the printed body.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc (FI annotate reallocRun
  reallocBody pieces Piece)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg (pieceSrc pieces_spec rstep
  reallocBody_eq)

/-- **The destination of the instruction `i` of the run `is` is live after it**, at every
    live-out set of the run. -/
def LiveInRun (i : FI) (is : List FI) : Prop :=
  ∀ lend la, (i, la) ∈ (annotate lend is).1 → la.contains i.d = true

/-- **An instruction of a body is an instruction between runs or the instruction of a
    fragment instruction of a run.** -/
theorem mem_pieces_of_mem {recog : String → Bool} {body : Lcmd} {li : Linstr} (h : li ∈ body) :
    Piece.bar li ∈ pieces body recog ∨
      ∃ is, Piece.run is ∈ pieces body recog ∧ ∃ i ∈ is, i.toL = li := by
  have h1 := (pieces_spec (recog := recog) body).1
  rw [← h1] at h
  obtain ⟨p, hp, hl⟩ := List.mem_flatMap.mp h
  cases p with
  | run is =>
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
      exact Or.inr ⟨is, hp, i, hi, rfl⟩
  | bar li' =>
      obtain rfl := List.mem_singleton.mp hl
      exact Or.inl hp

/-- The fold of the re-allocation keeps every instruction between runs and the
    re-allocation of every run, at some live-out set. -/
theorem foldr_rstep_mem (res : List String) :
    ∀ (ps : List Piece) (acc : Lcmd × Std.HashSet String),
      (∀ li ∈ acc.1, li ∈ (ps.foldr (rstep res X86Backend.LprogAsmPrinter.x86Abi) acc).1) ∧
      (∀ li, Piece.bar li ∈ ps → li ∈ (ps.foldr (rstep res X86Backend.LprogAsmPrinter.x86Abi) acc).1) ∧
      (∀ is, Piece.run is ∈ ps → ∃ lend, ∀ j ∈ reallocRun lend is,
        j.toL ∈ (ps.foldr (rstep res X86Backend.LprogAsmPrinter.x86Abi) acc).1)
  | [], acc => ⟨fun li h => h, fun li h => by simp at h, fun is h => by simp at h⟩
  | p :: ps, acc => by
      obtain ⟨k1, k2, k3⟩ := foldr_rstep_mem res ps acc
      rw [List.foldr_cons]
      generalize hA : ps.foldr (rstep res X86Backend.LprogAsmPrinter.x86Abi) acc = A at k1 k2 k3
      cases p with
      | run is =>
          simp only [rstep]
          refine ⟨fun li h => List.mem_append_right _ (k1 li h), fun li h => ?_, fun is' h => ?_⟩
          · rcases List.mem_cons.mp h with he | h
            · cases he
            · exact List.mem_append_right _ (k2 li h)
          · rcases List.mem_cons.mp h with he | h
            · cases he
              exact ⟨_, fun j hj => List.mem_append_left _ (List.mem_map_of_mem hj)⟩
            · obtain ⟨lend, hl⟩ := k3 is' h
              exact ⟨lend, fun j hj => List.mem_append_right _ (hl j hj)⟩
      | bar li' =>
          simp only [rstep]
          refine ⟨fun li h => List.mem_cons_of_mem _ (k1 li h), fun li h => ?_, fun is' h => ?_⟩
          · rcases List.mem_cons.mp h with he | h
            · cases he
              exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (k2 li h)
          · rcases List.mem_cons.mp h with he | h
            · cases he
            · obtain ⟨lend, hl⟩ := k3 is' h
              exact ⟨lend, fun j hj => List.mem_cons_of_mem _ (hl j hj)⟩

/-- **The re-allocation of a body keeps a reader of the save slot of a parameter register**
    that lies between runs, or whose destination is live after it in its run. -/
theorem reallocBody_slotReader {res : List String} {body : Lcmd} {R : String}
    (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX") {li : Linstr} (hli : li ∈ body)
    (hr : SlotReader R li.li_i)
    (hl : ∀ is, Piece.run is ∈ pieces body → ∀ i ∈ is, i.toL = li → LiveInRun i is) :
    ∃ j ∈ reallocBody res body, SlotReader R j.li_i := by
  rw [reallocBody_eq]
  obtain ⟨-, k2, k3⟩ := foldr_rstep_mem res (pieces body)
    ([], X86Backend.LprogGpRealloc.labelLiveFrames body)
  rcases mem_pieces_of_mem (recog := X86Backend.LcmdCopyPropagate.isRecognizedOpn) hli with
    hb | ⟨is, hp, i, hi, rfl⟩
  · exact ⟨li, k2 li hb, hr⟩
  · obtain ⟨lend, hlend⟩ := k3 is hp
    obtain ⟨j, hj, hjr⟩ := reallocRun_slotReader hR hi hr (hl is hp i hi rfl lend)
    exact ⟨j.toL, hlend j hj, hjr⟩

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate (printedBody foldBody) in
/-- **A reader of the save slot of a parameter register in the body after the optimizer and
    the constant-index fold is a reader of the printed body**, when it lies between runs or its
    destination is live after it in its run. -/
theorem slotReader_printedBody_of_foldBody {res : List String} {b0 : Lcmd} {R : String}
    (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX") {li : Linstr} (hli : li ∈ foldBody b0)
    (hr : SlotReader R li.li_i)
    (hl : ∀ is, Piece.run is ∈ pieces (foldBody b0) → ∀ i ∈ is, i.toL = li → LiveInRun i is) :
    ∃ j ∈ printedBody res b0, SlotReader R j.li_i :=
  slotReader_printedBody (reallocBody_slotReader hR hli hr hl)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
