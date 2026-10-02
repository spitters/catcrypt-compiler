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
an `Lopn` steps by `fstepA` at the memory tag `tagAt` of its position, a label moves to the
next instruction, and a conditional branch on the zero flag (`Lcond Z` or `Lcond NZ`) moves
to its target label or to the next instruction. The run halts at `Lret` and past the end of
the body.

The printer writes the widening multiply without a width tag (`MULX`); `normA` reads it as
the 64-bit `MULX:64` that the flag machine steps, the only width the encoder emits for it.

The printer writes a carry constant, the zero or one a carry chain reads as its first
carry-in, as an untagged `MOV d, #n`, which the register tag steps at width `32`. `tagAt`
tags such a move with the one-bit descriptor `.reg (some 1)` when the next instruction that
names `d` reads it only as a carry-in (`carryInNext`); its bytes `mov r32, imm32` clear the
upper bits of the machine register, which then holds the zero-extension of the bit.

## Main results

* `tagA`, `tagAt`, `normA`, `stepA`, `haltedA`, `runA`: the address machine on a body.
* `tagAt_of_ne`: off the untagged immediate move, `tagAt` is `tagA`.
* `runA_halt`, `runA_step`: the unfolding of a run.
* `runA_det`: two terminating runs from one state end in one state.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (movImmStruct?)

/-- The memory tag of a physical instruction: the indexed load and store at the word width,
    the register tag otherwise. `fstepA` reads only the kind of the tag. -/
def tagA : LinstrR → MemTag
  | .Lopn _ o _ =>
      if o = "LOADIDX" then .load 64 0 else if o = "STOREIDX" then .store 64 0 else .reg none
  | _ => .reg none

/-- The operand names the register `d`: as a register, an array base, or the base or index
    of an indexed access. -/
def opNamesB (d : String) : LOperand → Bool
  | .reg r => r == d
  | .arr a _ => a == d
  | .arrIdx b i _ => b == d || i == d
  | .imm _ => false

/-- The instruction names the register `d` among its destination or source operands. -/
def namesB (d : String) : LinstrR → Bool
  | .Lopn ds _ ss => ds.any (opNamesB d) || ss.any (opNamesB d)
  | _ => false

/-- The instruction reads `d` only as the carry-in of a carry-chain add `ADCX:64` or of its
    carry-out binding `ADCXHI:64` on three register sources, and names it nowhere else. -/
def carryUseB (d : String) : LinstrR → Bool
  | .Lopn [.reg x] o [.reg a, .reg s, .reg c] =>
      (o == "ADCX:64" || o == "ADCXHI:64") && c == d && x != d && a != d && s != d
  | _ => false

/-- The first instruction of `is` that names `d` reads it only as a carry-in (`carryUseB`). -/
def carryInFirst (d : String) : List Linstr → Bool
  | [] => false
  | j :: js => carryUseB d j.li_i || (!namesB d j.li_i && carryInFirst d js)

/-- The first instruction after position `k` of `body` that names `d` reads it only as a
    carry-in. -/
def carryInNext (body : Lcmd) (k : Nat) (d : String) : Bool :=
  carryInFirst d (body.drop (k + 1))

/-- `carryInFirst` reads of each instruction only whether it names `d` and whether it reads
    `d` only as a carry-in. -/
theorem carryInFirst_congr (d : String) :
    ∀ (L L' : List Linstr), L'.length = L.length →
      (∀ i (h : i < L.length) (h' : i < L'.length), namesB d L'[i].li_i = namesB d L[i].li_i
        ∧ carryUseB d L'[i].li_i = carryUseB d L[i].li_i) →
      carryInFirst d L' = carryInFirst d L
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | j :: js, j' :: js', hl, h => by
      obtain ⟨h1, h2⟩ := h 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at h1 h2
      have ih := carryInFirst_congr d js js' (by simpa using hl)
        (fun i hi hi' => by
          have := h (i + 1) (by simp; omega) (by simp; omega)
          simpa only [List.getElem_cons_succ] using this)
      simp only [carryInFirst, h1, h2, ih]

/-- The instruction at position `k` of `body` is a carry constant: an untagged immediate move
    `MOV d, #n` with `n < 2` into a name `d` that is no cell name, whose next use is a
    carry-in (`carryInNext`). -/
def bitMovB (body : Lcmd) (k : Nat) (i : LinstrR) : Bool :=
  match movImmStruct? i with
  | some (d, n) => decide (n < 2) && !hasPrefix d "mem." && carryInNext body k d
  | none => false

/-- The memory tag of instruction `k` of `body`: the one-bit register tag `.reg (some 1)` for
    a carry constant (`bitMovB`), `tagA` otherwise. -/
def tagAt (body : Lcmd) (k : Nat) (i : LinstrR) : MemTag :=
  if bitMovB body k i then .reg (some 1) else tagA i

theorem tagAt_of_not {body : Lcmd} {k : Nat} {i : LinstrR} (h : bitMovB body k i = false) :
    tagAt body k i = tagA i := by
  simp [tagAt, h]

theorem bitMovB_of_ne {body : Lcmd} {k : Nat} {i : LinstrR} (h : movImmStruct? i = none) :
    bitMovB body k i = false := by
  simp [bitMovB, h]

/-- Off the untagged immediate move, the tag of an instruction at a position is `tagA`. -/
theorem tagAt_of_ne {body : Lcmd} {k : Nat} {i : LinstrR} (h : movImmStruct? i = none) :
    tagAt body k i = tagA i :=
  tagAt_of_not (bitMovB_of_ne h)

/-- A carry constant is the untagged move of `0` or `1` into a name that is no cell name. -/
theorem bitMovB_spec {body : Lcmd} {k : Nat} {i : LinstrR} (h : bitMovB body k i = true) :
    ∃ d n, i = .Lopn [.reg d] "MOV" [.imm n] ∧ n < 2 ∧ hasPrefix d "mem." = false
      ∧ carryInNext body k d = true := by
  unfold bitMovB at h
  split at h
  · rename_i d n hm
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    refine ⟨d, n, ?_, h.1.1, h.1.2, h.2⟩
    unfold movImmStruct? at hm
    split at hm
    · cases hm; rfl
    · cases hm
  · cases h

/-- **The carry constant on the address machine.** At the one-bit tag, the untagged move
    `MOV D, #n` writes the bit `n` to `D`. -/
theorem fstepA_bitMov (frame : String → Option (BitVec 64)) (D : String) (n : Nat)
    (s : LstateA) (zf : Bool) :
    fstepA frame (.Lopn [.reg D] "MOV" [.imm n], .reg (some 1)) s zf
      = some ({ s with reg := (s.reg.setReg D (BitVec.ofNat 1 n)).nextPc }, zf) := by
  simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, cellA?, slotCarry?,
    slotImm?, slotCmov?, regStepA, JasminLsemMemFlagNestJoin.fstepF, JasminLsemMemFlagGuard.cmpArgs?,
    JasminLsemMemFlagGuard.movRegArgs?, JasminLsemMemFlagGuard.stepMemF, lsemStepMem,
    JasminLsemCast.lsemStepCast, JasminLsemCast.castStruct?, movImmStruct?,
    JasminLsemMemFlagGuard.withALUFlags, JasminLsemMemFlagGuard.aluFlagOp?]

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
      fstepA frame (normA (.Lopn ds o ss), tagAt c s.reg.lpc (.Lopn ds o ss)) s zf
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
