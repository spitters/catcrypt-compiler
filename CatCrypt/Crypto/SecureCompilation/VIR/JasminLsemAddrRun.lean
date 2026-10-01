/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem

@[expose] public section

set_option autoImplicit false

/-!
# Physical bodies on the address machine

A physical-ABI body addresses memory through registers: a word array is reached by reloading
its pointer from a frame slot into a scratch register and accessing `(%scratch, %idx, 8)`.
`JasminLsemAddrMem.fstepA` is the straight step of this form over a register file and a byte
memory. This module runs a whole body on it, with the program counter in the register file:
an `Lopn` steps by `fstepA` at the memory tag `tagA` of its mnemonic, a label moves to the
next instruction, and a conditional branch on the zero flag (`Lcond Z` or `Lcond NZ`) moves
to its target label or to the next instruction. The run halts at `Lret` and past the end of
the body.

The printer writes the widening multiply without a width tag (`MULX`); `normA` reads it as
the 64-bit `MULX:64` that the flag machine steps, the only width the encoder emits for it.

## Main results

* `tagA`, `normA`, `stepA`, `haltedA`, `runA`: the address machine on a body.
* `runA_halt`, `runA_step`: the unfolding of a run.
* `runA_det`: two terminating runs from one state end in one state.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem

/-- The memory tag of a physical instruction: the indexed load and store at the word width,
    the register tag otherwise. `fstepA` reads only the kind of the tag. -/
def tagA : LinstrR → MemTag
  | .Lopn _ o _ =>
      if o = "LOADIDX" then .load 64 0 else if o = "STOREIDX" then .store 64 0 else .reg none
  | _ => .reg none

/-- The widening multiply `MULX` read at its width `MULX:64`; every other instruction
    unchanged. -/
def normA : LinstrR → LinstrR
  | .Lopn ds o ss => .Lopn ds (if o = "MULX" then withWidthTag 64 "MULX" else o) ss
  | i => i

/-- The instruction defines the label `l`. -/
def isLabelB (l : LLabel) : LinstrR → Bool
  | .Llabel _ l' => l' == l
  | _ => false

/-- The position of the first definition of the label `l` in `c`. -/
def labelAt (c : Lcmd) (l : LLabel) : Option Nat := c.findIdx? (fun i => isLabelB l i.li_i)

/-- The polarity of a condition-code name: `Z` branches when the zero flag is set, `NZ` when
    it is clear. -/
def condPol : String → Option Bool
  | "Z" => some true
  | "NZ" => some false
  | _ => none

/-- One step of the address machine on the body `c`, at the program counter of `s`, with the
    frame-slot addresses `frame` and the zero flag `zf`. -/
def stepA (frame : String → Option (BitVec 64)) (c : Lcmd) (s : LstateA) (zf : Bool) :
    Option (LstateA × Bool) :=
  match c[s.reg.lpc]? with
  | some ⟨_, .Lopn ds o ss⟩ =>
      fstepA frame (normA (.Lopn ds o ss), tagA (.Lopn ds o ss)) s zf
  | some ⟨_, .Llabel _ _⟩ => some (s.setLpc (s.reg.lpc + 1), zf)
  | some ⟨_, .Lcond (.reg cc) l⟩ =>
      match condPol cc with
      | some pol =>
          if zf = pol then (labelAt c l).map fun p => (s.setLpc p, zf)
          else some (s.setLpc (s.reg.lpc + 1), zf)
      | none => none
  | _ => none

/-- The run has halted: the program counter is at `Lret` or past the end of the body. -/
def haltedA (c : Lcmd) (s : LstateA) : Bool :=
  match c[s.reg.lpc]? with
  | none => true
  | some ⟨_, .Lret⟩ => true
  | _ => false

/-- Run the body `c` for at most `fuel` steps; the state and the zero flag at the halt. -/
def runA (frame : String → Option (BitVec 64)) (c : Lcmd) :
    Nat → LstateA → Bool → Option (LstateA × Bool)
  | 0, s, zf => if haltedA c s then some (s, zf) else none
  | fuel + 1, s, zf =>
      if haltedA c s then some (s, zf)
      else (stepA frame c s zf).bind fun bz => runA frame c fuel bz.1 bz.2

theorem runA_halt (frame : String → Option (BitVec 64)) (c : Lcmd) (fuel : Nat) (s : LstateA)
    (zf : Bool) (h : haltedA c s = true) : runA frame c fuel s zf = some (s, zf) := by
  cases fuel <;> simp [runA, h]

theorem runA_step (frame : String → Option (BitVec 64)) (c : Lcmd) (fuel : Nat) (s : LstateA)
    (zf : Bool) (h : haltedA c s = false) :
    runA frame c (fuel + 1) s zf
      = (stepA frame c s zf).bind fun bz => runA frame c fuel bz.1 bz.2 := by
  simp [runA, h]

/-- Two terminating runs of the address machine from one state end in one state. -/
theorem runA_det (frame : String → Option (BitVec 64)) (c : Lcmd) :
    ∀ (k k' : Nat) (s : LstateA) (zf : Bool) (t t' : LstateA × Bool),
      runA frame c k s zf = some t → runA frame c k' s zf = some t' → t = t' := by
  intro k
  induction k with
  | zero =>
    intro k' s zf t t' h h'
    cases hh : haltedA c s
    · simp [runA, hh] at h
    · rw [runA_halt _ _ _ _ _ hh] at h h'
      exact (Option.some.inj h).symm.trans (Option.some.inj h')
  | succ k ih =>
    intro k' s zf t t' h h'
    cases hh : haltedA c s
    · cases k' with
      | zero => simp [runA, hh] at h'
      | succ k' =>
        rw [runA_step _ _ _ _ _ hh] at h h'
        cases hs : stepA frame c s zf with
        | none => rw [hs] at h; cases h
        | some bz =>
          rw [hs, Option.bind_some] at h h'
          exact ih k' _ _ t t' h h'
    · rw [runA_halt _ _ _ _ _ hh] at h h'
      exact (Option.some.inj h).symm.trans (Option.some.inj h')

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
