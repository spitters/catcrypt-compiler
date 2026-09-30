/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

/-!
# Block paths of the flag-extended memref semantics

The flag-extended memref semantics `lsemFuelMemF` (the flag `CMP`, the register-copy
`MOV` and the condition-code `Lcond` in front of the memref loop semantics) as a labelled
machine over the wire projection of its body, and the two directions of the path theorem
for it. The flag arms are straight-line (`CMP`, `MOV`) or a branch on `zf` that jumps like
a register `Lcond` or falls through, so a flag branch and a register branch have the same
edges. `Lret` takes no step, so a halting run leaves the body by falling off its end.

## Main definitions

* `memFMachine P`: `lsemFuelMemF` on program `P` as an `LMachine`.

## Main results

* `evalInstrPMemF_next`: a successful flag-machine step keeps the function and reaches a
  pc allowed by `NextPc`.
* `memFMachine_sound`: the flag-extended semantics satisfies `LMachine.Sound`.
* `lsem_path`: a halting `lsemFuelMemF` run of a singleton program from a state inside a
  block is a `BlockPath` of `cfgOf` of its wire projection.
* `path_lsem`: a `BlockPath` of the flag machine is a halting `lsemFuelMemF` run.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

theorem cmpArgs?_lopn {i : LinstrRM} {a b : LOperand} (h : cmpArgs? i = some (a, b)) :
    ∃ d o x, i.1 = .Lopn d o x := by
  unfold cmpArgs? at h
  split at h
  · exact ⟨_, _, _, ‹_›⟩
  · cases h

theorem movRegArgs?_lopn {i : LinstrRM} {d s : String} (h : movRegArgs? i = some (d, s)) :
    ∃ d o x, i.1 = .Lopn d o x := by
  unfold movRegArgs? at h
  split at h
  · exact ⟨_, _, _, ‹_›⟩
  · cases h

theorem flagCondCC?_cond {i : LinstrRM} {pol : Bool} {l : LLabel}
    (h : flagCondCC? i = some (pol, l)) : ∃ c, i.1 = .Lcond c l := by
  unfold flagCondCC? at h
  split at h <;> first | (cases h; exact ⟨_, ‹_›⟩) | cases h

/-- A successful step of the flag-extended semantics keeps the function and reaches a pc
    allowed by `NextPc`. -/
theorem evalInstrPMemF_next (P : LprogM) (i : LinstrRM) (s t : LstateMF)
    (h : evalInstrPMemF P i s = some t) :
    t.prog.lfn = s.prog.lfn ∧
      NextPc (P.body.map Prod.fst) i.1 s.prog.base.lpc t.prog.base.lpc := by
  unfold evalInstrPMemF at h
  split at h
  · rename_i a b hc
    obtain ⟨d, o, x, hi⟩ := cmpArgs?_lopn hc
    split at h
    · cases h
      rw [hi]
      exact ⟨rfl, by simp [NextPc]⟩
    · cases h
  · split at h
    · rename_i dst src hm
      obtain ⟨d, o, x, hi⟩ := movRegArgs?_lopn hm
      split at h
      · cases h
        rw [hi]
        exact ⟨rfl, by simp [NextPc]⟩
      · cases h
    · split at h
      · rename_i pol lbl hf
        obtain ⟨c, hi⟩ := flagCondCC?_cond hf
        rw [hi]
        split at h
        · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨h1, h2⟩ := evalJumpMem_spec P lbl s.prog p hp
          exact ⟨h1, Or.inr h2⟩
        · cases h
          exact ⟨rfl, Or.inl (by simp)⟩
      · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
        exact evalInstrPMemL_next P i s.prog p hp

/-- The flag-extended memref semantics of program `P` as a labelled machine. -/
def memFMachine (P : LprogM) : LMachine LstateMF where
  pc s := s.prog.base.lpc
  step := lsemStepPMemF P
  run := lsemFuelMemF P
  inv s := s.prog.lfn = P.lfn

/-- **The flag-extended semantics satisfies `LMachine.Sound`.** -/
theorem memFMachine_sound (P : LprogM) : (memFMachine P).Sound (P.body.map Prod.fst) where
  step_inv s s' hs h := by
    simp only [memFMachine, lsemStepPMemF] at h hs ⊢
    split at h
    · rw [(evalInstrPMemF_next P _ s s' h).1, hs]
    · cases h
  step_lt s s' hs h := by
    simp only [memFMachine, lsemStepPMemF, List.length_map] at h hs ⊢
    split at h
    · rename_i i hi
      unfold findInstrMem at hi
      rw [if_pos hs] at hi
      exact (List.getElem?_eq_some_iff.mp hi).1
    · cases h
  step_next s s' i hs h hi := by
    simp only [memFMachine, lsemStepPMemF] at h hs hi ⊢
    split at h
    · rename_i j hj
      unfold findInstrMem at hj
      rw [if_pos hs] at hj
      rw [List.getElem?_map, hj] at hi
      cases hi
      exact (evalInstrPMemF_next P j s s' h).2
    · cases h
  run_zero s hs hlt := by
    simp only [memFMachine, List.length_map] at hs hlt ⊢
    rw [lsemFuelMemF, findInstrMem_of_lt P s.prog hs hlt]
  run_succ f s hs hlt := by
    simp only [memFMachine, List.length_map] at hs hlt ⊢
    rw [lsemFuelMemF, lsemStepPMemF, findInstrMem_of_lt P s.prog hs hlt]
    dsimp only
    cases evalInstrPMemF P _ s <;> rfl
  run_halt f s _ hge := by
    simp only [memFMachine, List.length_map] at hge ⊢
    exact lsemFuelMemF_halt P f s (findInstrMem_of_ge P s.prog hge)

/-- **A halting `lsemFuelMemF` run of a singleton program is a path of blocks.** -/
theorem lsem_path {fn : String} {body : List LinstrRM} {G : CFG}
    (hG : cfgOf (body.map Prod.fst) = some G) (fuel b : Nat) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hb : b < G.blocks.size)
    (h1 : (G.blk b).start ≤ s.prog.base.lpc) (h2 : s.prog.base.lpc < (G.blk b).stop)
    (hrun : lsemFuelMemF (singletonProgM fn body) fuel s = some t) :
    BlockPath (memFMachine (singletonProgM fn body)) (body.map Prod.fst) G b s t :=
  blockPath_of_run (memFMachine_sound (singletonProgM fn body)) hG t fuel b s hfn hb h1 h2
    hrun

/-- **A path of blocks of the flag machine is a halting `lsemFuelMemF` run.** -/
theorem path_lsem {fn : String} {body : List LinstrRM} {G : CFG} {b : Nat}
    {s t : LstateMF} (hfn : s.prog.lfn = fn)
    (h : BlockPath (memFMachine (singletonProgM fn body)) (body.map Prod.fst) G b s t) :
    ∃ fuel, lsemFuelMemF (singletonProgM fn body) fuel s = some t :=
  run_of_blockPath (memFMachine_sound (singletonProgM fn body)) h hfn

end CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
