/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenSim
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic

@[expose] public section

set_option autoImplicit false

/-!
# Checked decoded-instruction simulations with word-array memory

`DecodeGenSim.stepOK` checks the register classes of a flag-machine body against its
decoded machine instructions. This module extends the check with the word-array memory
classes: indexed loads and stores through a pointer register, the pointer reloaded from a
frame slot, the index held in a register or in a machine copy of it.

## Regions

The arrays are keyed on both machines by the ABI parameter they belong to. A region
`⟨A, n, off⟩` is the array `A` of `n` words whose pointer sits in the frame slot at
`off(%SP)`. The runtime data is a base map `base` (the pointer of each region) and the stack
pointer `rsp`; the layout `regLay`, the frame `regFrame` and the cells `regK` (every word of
every region) are computed from them. The separation conditions of a store
(`JasminLsemAddrMem.Layout.Sep` and distinct addresses for distinct cells) are the fields of
`MemSep`, stated once for the regions.

## The correspondence

`MCorr E base rsp (Ls, a) zl` is `DecLsemCorr` on the live list `Ls`, the layout, frame and
cells of the regions, together with machine facts: the stack register holds `rsp`, and the
abstract machine state `a` holds (`Abs.Holds`): register copies `eqs`, registers whose value
is a valid index below the bound `E.nb` (`bnd`), and registers holding the base address of a
region (`ptr`).

## The classes

A flag-machine instruction is matched against a group of machine instructions: a prefix of
machine-only instructions (`machStep`: a register copy into a register, a pointer reload
`mov off(%SP), %S` from the slot of a region) followed by the instructions of one class
(`coreStep`):

* the register classes of `regStep`: copies and count-`0` shifts (also elided), the right
  shift in place, the immediate move, the two-address operations `ADD`, `SUB`, `AND`,
  `XOR`, `OR`, `MUL` in place or through a copy, the immediate `ADD` and `SUB` in place,
  and the compares;
* the load `LOADIDX d, (A, idx, 8)` against `mov (%B, %X, 8), %D`, where `B` holds the base
  of the region `A`, `X` holds the value of `idx` and a valid index, and `D` is the register
  of `d`;
* the in-place store `STOREIDX A, (A, idx, 8), v` against `mov %V, (%B, %X, 8)`.

No machine instruction of a group writes the stack register. `mbodyOK` finds the groups of a
body by search and returns the final live list and abstract state; `loopOK` checks that the
live list at the end of the body contains the one at its start.

## Main results

* `regStep_sound`, `machStep_sound`, `coreStep_sound`, `grpStep_sound`: the classes
  simulate their machine instructions.
* `mbodyOK_sound`: an accepted body simulates its machine instructions from `MCorr` at the
  start state to `MCorr` at the returned state.
* `decSim_of_loopOK`: an accepted loop body simulates its machine instructions from the live
  list and abstract state at its start back to the live list with no machine facts.
* `decSim_of_loopOK_idx`: the same from a loop head whose index register holds a value below
  the bound.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenSim (unaryOK)

/-! ## 1. Regions -/

/-- A word-array region: the array `name` of `len` words whose pointer sits in the frame
    slot at offset `off` from the stack pointer. -/
structure Region where
  /-- The array name, the ABI parameter the array belongs to. -/
  name : String
  /-- The number of 64-bit words. -/
  len : Nat
  /-- The offset of the pointer's frame slot from the stack pointer. -/
  off : Int
  deriving DecidableEq, Repr

/-- The first region of the name `A`. -/
def regFind (rs : List Region) (A : String) : Option Region := rs.find? (·.name == A)

/-- The word count of the region `A`, `0` for a name that is no region. -/
def regLen (rs : List Region) (A : String) : Nat := ((regFind rs A).map (·.len)).getD 0

/-- The layout of the regions at the base map `base`: the slot of a region is its name. -/
def regLay (rs : List Region) (base : String → BitVec 64) : Layout where
  base := base
  len := regLen rs
  slot A := if (regFind rs A).isSome then some A else none

/-- The frame of the regions at the stack pointer `rsp`: the slot of the region `A` at
    `rsp + off`. -/
def regFrame (rs : List Region) (rsp : BitVec 64) (q : String) : Option (BitVec 64) :=
  (regFind rs q).map (fun r => rsp + BitVec.ofInt 64 r.off)

/-- The cells of the regions: every word of every region. -/
def regK (rs : List Region) (A : String) (j : Nat) : Prop := j < regLen rs A

/-- The separation conditions of the regions, established once: cells and pointer slots
    are separated (`Layout.Sep`), and distinct cells lie at distinct addresses. -/
structure MemSep (rs : List Region) (base : String → BitVec 64) (rsp : BitVec 64) : Prop where
  /-- Cells are equal or disjoint, and disjoint from the pointer slots. -/
  sep : (regLay rs base).Sep (regFrame rs rsp)
  /-- Distinct cells lie at distinct addresses. -/
  inj : ∀ A j A' j', regK rs A j → regK rs A' j' →
    (regLay rs base).addr A j = (regLay rs base).addr A' j' → A = A' ∧ j = j'

/-- Under `MemSep`, a store to the cell `(A, j)` of a region keeps every cell of the
    regions. -/
theorem afterStore_regK {rs : List Region} {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : MemSep rs base rsp) {A : String} {j : Nat} (hj : regK rs A j) :
    ∀ A' j', regK rs A' j' → afterStore (regLay rs base) (regK rs) A A j A' j' := by
  intro A' j' hk
  by_cases hA : A' = A
  · subst hA
    by_cases hjj : j' = j
    · exact Or.inl ⟨rfl, Or.inl hjj⟩
    · exact Or.inl ⟨rfl, Or.inr ⟨hk, fun he => hjj (hsep.inj A' j' A' j hk hj he).2⟩⟩
  · exact Or.inr ⟨hA, hk, fun he => hA (hsep.inj A' j' A j hk hj he).1⟩

/-! ## 2. The abstract machine state -/

/-- Facts about machine registers: copies `eqs` (`X` holds the value of `Y`), registers of
    `bnd` holding a valid index, and registers of `ptr` holding the base of a region. -/
structure Abs where
  /-- `(X, Y)`: the register `X` holds the value of the register `Y`. -/
  eqs : List (String × String)
  /-- Registers holding a value below the index bound. -/
  bnd : List String
  /-- `(B, A)`: the register `B` holds the base address of the region `A`. -/
  ptr : List (String × String)
  deriving DecidableEq, Repr

/-- The abstract state with no facts. -/
def Abs.empty : Abs := ⟨[], [], []⟩

/-- The facts of `a` hold in the machine state `sa`, for the base map `base` and the index
    bound `nb`. -/
def Abs.Holds (a : Abs) (base : String → BitVec 64) (nb : Nat) (sa : AState) : Prop :=
  (∀ p ∈ a.eqs, sa.regs p.1 = sa.regs p.2) ∧ (∀ R ∈ a.bnd, (sa.regs R).toNat < nb)
    ∧ (∀ p ∈ a.ptr, sa.regs p.1 = base p.2)

/-- The facts of `a` that mention none of the registers `Ws`. -/
def Abs.kill (a : Abs) (Ws : List String) : Abs where
  eqs := a.eqs.filter (fun p => !decide (p.1 ∈ Ws) && !decide (p.2 ∈ Ws))
  bnd := a.bnd.filter (fun R => !decide (R ∈ Ws))
  ptr := a.ptr.filter (fun p => !decide (p.1 ∈ Ws))

/-- The facts after the copy `mov %Y, %X`. -/
def Abs.movTo (a : Abs) (X Y : String) : Abs where
  eqs := (X, Y) :: (a.kill [X]).eqs
  bnd := if decide (Y ∈ a.bnd) then X :: (a.kill [X]).bnd else (a.kill [X]).bnd
  ptr := (a.ptr.filter (fun p => p.1 == Y)).map (fun p => (X, p.2)) ++ (a.kill [X]).ptr

/-- The facts after the reload of the pointer of the region `A` into `S`. -/
def Abs.reload (a : Abs) (S A : String) : Abs :=
  { a.kill [S] with ptr := (S, A) :: (a.kill [S]).ptr }

theorem Abs.holds_empty (base : String → BitVec 64) (nb : Nat) (sa : AState) :
    Abs.empty.Holds base nb sa :=
  ⟨fun _ h => by simp [Abs.empty] at h, fun _ h => by simp [Abs.empty] at h,
    fun _ h => by simp [Abs.empty] at h⟩

theorem Abs.Holds.of_regs {a : Abs} {base : String → BitVec 64} {nb : Nat} {sa sa' : AState}
    (h : a.Holds base nb sa) (hr : ∀ R, sa'.regs R = sa.regs R) : a.Holds base nb sa' :=
  ⟨fun p hp => by rw [hr, hr]; exact h.1 p hp, fun R hR => by rw [hr]; exact h.2.1 R hR,
    fun p hp => by rw [hr]; exact h.2.2 p hp⟩

/-- The facts that mention no written register survive a write. -/
theorem Abs.Holds.kill {a : Abs} {base : String → BitVec 64} {nb : Nat} {sa sa' : AState}
    {Ws : List String} (h : a.Holds base nb sa) (hr : ∀ R, R ∉ Ws → sa'.regs R = sa.regs R) :
    (a.kill Ws).Holds base nb sa' := by
  refine ⟨fun p hp => ?_, fun R hR => ?_, fun p hp => ?_⟩
  · simp only [Abs.kill, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at hp
    rw [hr _ hp.2.1, hr _ hp.2.2]; exact h.1 p hp.1
  · simp only [Abs.kill, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hR
    rw [hr _ hR.2]; exact h.2.1 R hR.1
  · simp only [Abs.kill, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hp
    rw [hr _ hp.2]; exact h.2.2 p hp.1

/-- The facts after a register copy `mov %Y, %X` hold after it. -/
theorem Abs.Holds.movTo {a : Abs} {base : String → BitVec 64} {nb : Nat} {sa sa' : AState}
    {X Y : String} (h : a.Holds base nb sa)
    (hr : ∀ R, sa'.regs R = if R = X then sa.regs Y else sa.regs R) :
    (a.movTo X Y).Holds base nb sa' := by
  have hk : (a.kill [X]).Holds base nb sa' :=
    h.kill (fun R hR => by rw [hr, if_neg (by simpa using hR)])
  have hX : sa'.regs X = sa.regs Y := by rw [hr, if_pos rfl]
  have hY : sa'.regs Y = sa.regs Y := by rw [hr]; split <;> simp_all
  refine ⟨fun p hp => ?_, fun R hR => ?_, fun p hp => ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · rw [hX, hY]
    · exact hk.1 p hp
  · simp only [Abs.movTo] at hR
    split at hR
    · rename_i hYb
      rcases List.mem_cons.mp hR with rfl | hR
      · rw [hX]; exact h.2.1 Y (by simpa using hYb)
      · exact hk.2.1 R hR
    · exact hk.2.1 R hR
  · simp only [Abs.movTo, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at hp
    rcases hp with ⟨q, ⟨hq, hqY⟩, rfl⟩ | hp
    · rw [hX, ← hqY]; exact h.2.2 q hq
    · exact hk.2.2 p hp

/-! ## 3. The correspondence -/

/-- The static data of the check: the register map `pi`, the stack register `sp`, the
    regions `rs` and the index bound `nb`. -/
structure MemEnv where
  /-- The machine register of each name. -/
  pi : String → String
  /-- The stack register. -/
  sp : String
  /-- The word-array regions. -/
  rs : List Region
  /-- The index bound: a register of `bnd` holds a value below it. -/
  nb : Nat

/-- The state of the check: the live list and the abstract machine state. -/
abbrev St : Type := List String × Abs

/-- The machine facts of the state `s`: the stack register holds `rsp`, and the abstract
    machine state holds. -/
def MachOK (E : MemEnv) (base : String → BitVec 64) (rsp : BitVec 64) (s : St)
    (sa : AState) : Prop :=
  sa.regs E.sp = rsp ∧ s.2.Holds base E.nb sa

/-- **The correspondence with memory.** `DecLsemCorr` on the live list of `s` at the layout,
    frame and cells of the regions, and the machine facts of `s`. -/
abbrev MCorr (E : MemEnv) (base : String → BitVec 64) (rsp : BitVec 64) (s : St) (zl : Prop) :
    AState → LstateM → Bool → Prop :=
  fun sa b zf => DecLsemCorr E.pi (· ∈ s.1) (regLay E.rs base) (regFrame E.rs rsp) (regK E.rs)
    zl sa b zf ∧ MachOK E base rsp s sa

/-- The live list after a write of the name `d` to the register `D`. -/
def liveW (π : String → String) (Ls : List String) (d D : String) : List String :=
  d :: Ls.filter (fun r => π r != D)

/-- The live list after a machine write to the register `D`. -/
def liveO (π : String → String) (Ls : List String) (D : String) : List String :=
  Ls.filter (fun r => π r != D)

theorem mem_liveW {π : String → String} {Ls : List String} {d D r : String} :
    r ∈ liveW π Ls d D ↔ r = d ∨ (r ∈ Ls ∧ π r ≠ D) := by
  simp [liveW]

theorem mem_liveO {π : String → String} {Ls : List String} {D r : String} :
    r ∈ liveO π Ls D ↔ r ∈ Ls ∧ π r ≠ D := by
  simp [liveO]

variable {Lay : Layout} {frame : String → Option (BitVec 64)} {K : String → Nat → Prop}

/-- A machine block keeps every register it does not write. -/
theorem runBlock_regs_of_not_flat (js : List (JInstr 64)) (sa : AState) (R : String)
    (h : R ∉ js.flatMap dsts) : (aMachine.runBlock sa js).regs R = sa.regs R :=
  runBlock_regs_of_not_mem [R] js sa (fun j hj R' hR' hd => by
    rw [List.mem_singleton] at hR'
    subst hR'
    exact h (List.mem_flatMap.mpr ⟨j, hj, hd⟩)) R (List.mem_singleton_self R)

/-! ## 4. Register classes -/

/-- The two-address operations with their machine instruction, in place (`d` and `a` in one
    register) or through a copy of `a` into the register of `d`, distinct from that of
    `c`. -/
def opOK (π : String → String) (d opn a c : String) (js : List (JInstr 64)) : Bool :=
  (π d == π a &&
    ((opn == "ADD:64" && js == [.add (π d) (.reg (π c))])
    || (opn == "SUB:64" && js == [.sub (π d) (.reg (π c))])
    || (opn == "AND:64" && js == [.and_ (π d) (.reg (π c))])
    || (opn == "XOR:64" && js == [.xor_ (π d) (.reg (π c))])
    || (opn == "OR:64" && js == [.or_ (π d) (.reg (π c))])
    || (opn == "MUL:64" && js == [.imul (π d) (.reg (π c))])))
  || (π c != π d &&
    ((opn == "ADD:64" && js == [.mov (π d) (.reg (π a)), .add (π d) (.reg (π c))])
    || (opn == "SUB:64" && js == [.mov (π d) (.reg (π a)), .sub (π d) (.reg (π c))])
    || (opn == "AND:64" && js == [.mov (π d) (.reg (π a)), .and_ (π d) (.reg (π c))])
    || (opn == "XOR:64" && js == [.mov (π d) (.reg (π a)), .xor_ (π d) (.reg (π c))])
    || (opn == "OR:64" && js == [.mov (π d) (.reg (π a)), .or_ (π d) (.reg (π c))])
    || (opn == "MUL:64" && js == [.mov (π d) (.reg (π a)), .imul (π d) (.reg (π c))])))

/-- **The register classes.** A flag-machine register instruction over live names against its
    machine instructions, with the live list after it. -/
def regStep (π : String → String) (Ls : List String) (i : LinstrRM) (js : List (JInstr 64)) :
    Option (List String) :=
  match i with
  | (.Lopn [.reg d] opn [.reg a], .reg none) =>
      if decide (a ∈ Ls) && unaryOK π d opn a js then some (liveW π Ls d (π d)) else none
  | (.Lopn [.reg d] opn [.imm n], .reg none) =>
      if opn == withWidthTag 64 "MOV" && js == [.mov (π d) (.imm n)] then
        some (liveW π Ls d (π d))
      else none
  | (.Lopn [.reg d] opn [.reg a, .reg c], .reg none) =>
      if decide (a ∈ Ls) && decide (c ∈ Ls) then
        if opn == withWidthTag 64 "CMP" && d == a && js == [.cmp (π a) (.reg (π c))] then
          some Ls
        else if opOK π d opn a c js then some (liveW π Ls d (π d))
        else none
      else none
  | (.Lopn [.reg d] opn [.reg a, .imm k], .reg none) =>
      if decide (a ∈ Ls) then
        if opn == withWidthTag 64 "CMP" && d == a && js == [.cmp (π a) (.imm k)] then some Ls
        else if π d == π a && ((opn == "ADD:64" && js == [.add (π d) (.imm k)])
            || (opn == "SUB:64" && js == [.sub (π d) (.imm k)])) then
          some (liveW π Ls d (π d))
        else none
      else none
  | _ => none

variable {π : String → String}

theorem unary_sound {L : String → Prop} {d opn a : String} {js : List (JInstr 64)} (ha : L a)
    (h : unaryOK π d opn a js = true) {zl : Prop} :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d (π d)) Lay frame K False)
      [(.Lopn [.reg d] opn [.reg a], .reg none)] js := by
  have hS : Survives π L (liveAfter π L d (π d)) d := fun _ hr => hr
  simp only [unaryOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  have dz : ∀ {ls : List LinstrRM} {ms : List (JInstr 64)},
      DecSim (DecLsemCorr π L Lay frame K zl)
        (DecLsemCorr π (liveAfter π L d (π d)) Lay frame K zl) ls ms →
      DecSim (DecLsemCorr π L Lay frame K zl)
        (DecLsemCorr π (liveAfter π L d (π d)) Lay frame K False) ls ms :=
    fun h => h.weaken (fun _ _ _ h => h) (fun _ _ _ h => h.dropZf)
  rcases h with ⟨hopn, hjs⟩ | h
  · rcases hopn with rfl | rfl
    · rcases hjs with rfl | ⟨hda, hjs⟩
      · exact dz (decSim_movReg d a ha hS)
      · have : js = [] := by simpa using hjs
        subst this
        exact dz (decSim_movReg_elided d a ha hda hS)
    · rcases hjs with rfl | ⟨hda, hjs⟩
      · exact dz (decSim_shl0 d a ha hS)
      · have : js = [] := by simpa using hjs
        subst this
        exact dz (decSim_shl0_elided d a ha hda hS)
  · split at h
    · rename_i D k
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨rfl, hk0⟩, hk⟩, rfl⟩, hda⟩ := h
      exact decSim_shrImm (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a k hk0 hk ha
        hda hS
    · exact absurd h (by simp)

theorem op_sound {L : String → Prop} {d opn a c : String} {js : List (JInstr 64)} (ha : L a)
    (hc : L c) (h : opOK π d opn a c js = true) {zl : Prop} :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d (π d)) Lay frame K False)
      [(.Lopn [.reg d] opn [.reg a, .reg c], .reg none)] js := by
  simp only [opOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with ⟨hda, h⟩ | ⟨hcd, h⟩
  · rcases h with (((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩)
      | ⟨rfl, rfl⟩)
    · exact decSim_add_r d a c _ _ rfl hda.symm rfl ha hc
    · exact decSim_sub_r d a c _ _ rfl hda.symm rfl ha hc
    · exact decSim_and_r d a c _ _ rfl hda.symm rfl ha hc
    · exact decSim_xor_r d a c _ _ rfl hda.symm rfl ha hc
    · exact decSim_or_r d a c _ _ rfl hda.symm rfl ha hc
    · exact decSim_imul_r d a c _ _ rfl hda.symm rfl ha hc
  · rcases h with (((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩)
      | ⟨rfl, rfl⟩)
    · exact decSim_add_mov d a c _ _ _ rfl rfl rfl hcd ha hc
    · exact decSim_sub_mov d a c _ _ _ rfl rfl rfl hcd ha hc
    · exact decSim_and_mov d a c _ _ _ rfl rfl rfl hcd ha hc
    · exact decSim_xor_mov d a c _ _ _ rfl rfl rfl hcd ha hc
    · exact decSim_or_mov d a c _ _ _ rfl rfl rfl hcd ha hc
    · exact decSim_imul_mov_r d a c _ _ _ rfl rfl rfl hcd ha hc

/-- The correspondence on `liveAfter` is the correspondence on `liveW`. -/
theorem corr_liveW {Ls : List String} {d : String} {zl : Prop} {sa : AState} {b : LstateM}
    {zf : Bool} (h : DecLsemCorr π (liveAfter π (· ∈ Ls) d (π d)) Lay frame K zl sa b zf) :
    DecLsemCorr π (· ∈ liveW π Ls d (π d)) Lay frame K zl sa b zf :=
  h.mono (fun _ hr => mem_liveW.mp hr) id (fun _ _ h => h)

/-- **The register classes simulate their machine instructions.** -/
theorem regStep_sound {Ls Ls' : List String} {i : LinstrRM} {js : List (JInstr 64)}
    (h : regStep π Ls i js = some Ls') {zl : Prop} :
    DecSim (DecLsemCorr π (· ∈ Ls) Lay frame K zl) (DecLsemCorr π (· ∈ Ls') Lay frame K False)
      [i] js := by
  unfold regStep at h
  split at h
  · rename_i d opn a
    split at h
    · rename_i hc
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact (unary_sound hc.1 hc.2).weaken (fun _ _ _ h => h) (fun _ _ _ h => corr_liveW h)
    · exact absurd h (by simp)
  · rename_i d opn n
    split at h
    · rename_i hc
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact (decSim_movImm_r (Lay := Lay) (frame := frame) (K := K) (zl := zl)
        (L := (· ∈ Ls)) d (π d) n rfl).weaken (fun _ _ _ h => h)
        (fun _ _ _ h => corr_liveW h.dropZf)
    · exact absurd h (by simp)
  · rename_i d opn a c
    split at h
    · rename_i hac
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hac
      split at h
      · rename_i hc
        obtain rfl := Option.some.inj h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
        exact (decSim_cmpReg (Lay := Lay) (frame := frame) (K := K) (zl := zl) (π := π)
          (L := (· ∈ Ls)) d c hac.1 hac.2).weaken (fun _ _ _ h => h)
          (fun _ _ _ h => h.mono (fun _ hr => hr) (fun hf => hf.elim) (fun _ _ h => h))
      · split at h
        · rename_i hop
          obtain rfl := Option.some.inj h
          exact (op_sound hac.1 hac.2 hop).weaken (fun _ _ _ h => h)
            (fun _ _ _ h => corr_liveW h)
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  · rename_i d opn a k
    split at h
    · rename_i ha
      simp only [decide_eq_true_eq] at ha
      split at h
      · rename_i hc
        obtain rfl := Option.some.inj h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
        exact (decSim_cmpImm (Lay := Lay) (frame := frame) (K := K) (zl := zl) (π := π)
          (L := (· ∈ Ls)) d k ha).weaken (fun _ _ _ h => h)
          (fun _ _ _ h => h.mono (fun _ hr => hr) (fun hf => hf.elim) (fun _ _ h => h))
      · split at h
        · rename_i hc
          obtain rfl := Option.some.inj h
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
          obtain ⟨hda, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hc
          · exact (decSim_addImm_r (Lay := Lay) (frame := frame) (K := K) (zl := zl)
              (L := (· ∈ Ls)) d a (π d) k rfl hda.symm ha).weaken (fun _ _ _ h => h)
              (fun _ _ _ h => corr_liveW h)
          · exact (decSim_subImm_r (Lay := Lay) (frame := frame) (K := K) (zl := zl)
              (L := (· ∈ Ls)) d a (π d) k rfl hda.symm ha).weaken (fun _ _ _ h => h)
              (fun _ _ _ h => corr_liveW h)
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## 5. Memory classes -/

/-- **Indexed load through a register copy of the index.** `LOADIDX d, (A, idx, 8)` against
    `mov (%B, %X, 8), %d`, where `B` holds the base address of `A`, `X` holds the value of
    the register of `idx`, and that value selects a cell of `K`. -/
theorem decSim_loadX {L L' : String → Prop} {zl : Prop} (d A idx B X : String) (hidx : L idx)
    (hL : Survives π L L' d) :
    DecSim (fun sa b zf => DecLsemCorr π L Lay frame K zl sa b zf ∧ (sa.regs B = Lay.base A
        ∧ sa.regs X = sa.regs (π idx) ∧ K A (sa.regs (π idx)).toNat))
      (DecLsemCorr π L' Lay frame K zl) [loadN Lay d A idx] [.loadMemIdx (π d) B X 8] := by
  refine DecSim.single fun sa b zf ⟨h, hB, hX, hK⟩ => ?_
  obtain ⟨_, arr, harr, hcell⟩ := h.cells A _ hK
  refine ⟨(b.setReg d (stackGet arr (sa.regs (π idx)).toNat)).nextPc, zf, ?_, ?_⟩
  · rw [fstepF_loadN]
    simp only [lsemStepMem, loadN, loadStruct?, if_true, harr, h.regs idx hidx, Option.map_some]
  · refine h.write d _ _ (fun r => ?_) rfl hL (fun hz => h.zfEq hz)
    show (if r = π d then read64 sa.mem (sa.regs B
        + BitVec.ofInt 64 ((8 * (sa.regs X).toNat : Nat) : Int)) else sa.regs r) = _
    rw [hX, addr_idx8 Lay A _ _ hB, hcell]

/-- **Indexed in-place store through a register copy of the index.**
    `STOREIDX A, (A, idx, 8), val` against `mov %val, (%B, %X, 8)`, where `B` holds the
    base address of `A`, `X` holds the value of the register of `idx`, and that value is the
    cell `j` of `K`. The cells become `afterStore Lay K A A j`. -/
theorem decSim_storeX {L : String → Prop} {zl : Prop} (hsep : Lay.Sep frame)
    (A idx val B X : String) (hidx : L idx) (hval : L val) (j : Nat) :
    DecSim (fun sa b zf => DecLsemCorr π L Lay frame K zl sa b zf ∧ (sa.regs B = Lay.base A
        ∧ sa.regs X = sa.regs (π idx) ∧ (sa.regs (π idx)).toNat = j ∧ K A j))
      (DecLsemCorr π L Lay frame (afterStore Lay K A A j) zl)
      [storeN Lay A A idx val] [.storeMemIdx B X 8 (.reg (π val))] := by
  refine DecSim.single fun sa b zf ⟨h, hB, hX, hj, hK⟩ => ?_
  obtain ⟨hjl, arr, harr, _⟩ := h.cells A j hK
  refine ⟨(b.setArr A (stackSet arr j (sa.regs (π val)))).nextPc, zf, ?_, ?_⟩
  · rw [fstepF_storeN]
    simp only [lsemStepMem, storeN, storeStruct?, if_true, harr, h.regs idx hidx,
      h.regs val hval, hj, Option.map_some]
  · have hmem : (evalInstrA sa (.storeMemIdx B X 8 (.reg (π val)))).mem
        = write64 sa.mem (Lay.addr A j) (sa.regs (π val)) := by
      show write64 sa.mem (sa.regs B
        + BitVec.ofInt 64 ((8 * (sa.regs X).toNat : Nat) : Int)) (sa.regs (π val)) = _
      rw [hX, addr_idx8 Lay A _ _ hB, hj]
    have hdisj : ∀ C k, K C k → Lay.addr C k ≠ Lay.addr A j →
        Disjoint8 (Lay.addr A j) (Lay.addr C k) := fun C k hCk hne => by
      rcases hsep.cells A j C k hjl (h.cells C k hCk).1 with h' | h'
      · exact absurd h'.symm hne
      · exact h'
    refine ⟨fun r hr => ?_, fun hz => h.zfEq hz, fun A' j' hk => ?_, fun C q hq => ?_⟩
    · rw [LstateM.reg_nextPc, LstateM.reg_setArr, LstateN.getW_nextPc]
      exact h.regs r hr
    · rw [hmem]
      show j' < Lay.len A' ∧ ∃ arr' : Fin (Lay.len A') → BitVec 64,
        ((b.setArr A (stackSet arr j (sa.regs (π val)))).nextPc).getArr A' 64 (Lay.len A')
          = some arr'
        ∧ read64 (write64 sa.mem (Lay.addr A j) (sa.regs (π val))) (Lay.addr A' j')
          = stackGet arr' j'
      rcases hk with ⟨rfl, hk⟩ | ⟨hA, hk, hne⟩
      · rcases hk with rfl | ⟨hk, hne⟩
        · refine ⟨hjl, stackSet arr j' (sa.regs (π val)), by simp, ?_⟩
          rw [read64_write64_same, stackGet_stackSet_same _ _ _ hjl]
        · obtain ⟨hj', arr', ha', hr'⟩ := h.cells A' j' hk
          rw [harr] at ha'
          obtain rfl := Option.some.inj ha'
          refine ⟨hj', stackSet arr j (sa.regs (π val)), by simp, ?_⟩
          rw [read64_write64_of_disjoint _ _ _ _ (hdisj A' j' hk hne), hr',
            stackGet_stackSet_ne _ _ _ _ hjl hj']
          rintro rfl
          exact hne rfl
      · obtain ⟨hj', arr', ha', hr'⟩ := h.cells A' j' hk
        rw [read64_write64_of_disjoint _ _ _ _ (hdisj A' j' hk hne)]
        exact ⟨hj', arr', by simpa [hA] using ha', hr'⟩
    · rw [hmem]
      obtain ⟨aC, hqC, hpC⟩ := h.slots C q hq
      refine ⟨aC, hqC, ?_⟩
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.slots A j C q aC hjl hq hqC)]
      exact hpC

/-- The index register `X` of an access to the region `A` at the bound `nb`: `X` holds a
    valid index and the value of the register `I` of the index name. -/
def idxOK (E : MemEnv) (a : Abs) (A X I : String) : Bool :=
  decide (E.nb ≤ regLen E.rs A) && decide (X ∈ a.bnd) && (X == I || decide ((X, I) ∈ a.eqs))

/-- **The class check on one flag-machine instruction.** The memory classes and the register
    classes of `regStep`; no machine instruction writes the stack register. -/
def coreStep (E : MemEnv) (s : St) (i : LinstrRM) (js : List (JInstr 64)) : Option St :=
  if decide (E.sp ∈ js.flatMap dsts) then none else
  match i with
  | (.Lopn [.reg d] opn [.arrIdx A idx sc], .load w n) =>
      match js with
      | [.loadMemIdx D B X sc'] =>
          if opn == "LOADIDX" && sc == 8 && sc' == 8 && w == 64 && n == regLen E.rs A
              && decide (idx ∈ s.1) && D == E.pi d && decide ((B, A) ∈ s.2.ptr)
              && idxOK E s.2 A X (E.pi idx) then
            some (liveW E.pi s.1 d D, s.2.kill [D])
          else none
      | _ => none
  | (.Lopn [.reg dst] opn [.arrIdx A idx sc, .reg v], .store w n) =>
      match js with
      | [.storeMemIdx B X sc' (.reg V)] =>
          if opn == "STOREIDX" && dst == A && sc == 8 && sc' == 8 && w == 64
              && n == regLen E.rs A && decide (idx ∈ s.1) && decide (v ∈ s.1)
              && V == E.pi v && decide ((B, A) ∈ s.2.ptr) && idxOK E s.2 A X (E.pi idx) then
            some s
          else none
      | _ => none
  | _ => (regStep E.pi s.1 i js).map (fun Ls' => (Ls', s.2.kill (js.flatMap dsts)))

variable {E : MemEnv} {base : String → BitVec 64} {rsp : BitVec 64}

/-- The index facts of `idxOK` at a machine state. -/
theorem idxOK_holds {a : Abs} {A X I : String} (h : idxOK E a A X I = true) {sa : AState}
    (ha : a.Holds base E.nb sa) :
    sa.regs X = sa.regs I ∧ regK E.rs A (sa.regs I).toNat := by
  simp only [idxOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hnb, hX⟩, hXI⟩ := h
  have e : sa.regs X = sa.regs I := by
    rcases hXI with rfl | hXI
    · rfl
    · exact ha.1 _ hXI
  refine ⟨e, ?_⟩
  show (sa.regs I).toNat < regLen E.rs A
  rw [← e]
  exact lt_of_lt_of_le (ha.2.1 X hX) hnb

/-- The machine facts survive a block that does not write the stack register, with the
    facts on the registers it writes dropped. -/
theorem machOK_block {s : St} {js : List (JInstr 64)} {sa : AState}
    (hsp : E.sp ∉ js.flatMap dsts) (h : MachOK E base rsp s sa) :
    MachOK E base rsp (s.1, s.2.kill (js.flatMap dsts)) (aMachine.runBlock sa js) :=
  ⟨by rw [runBlock_regs_of_not_flat js sa _ hsp]; exact h.1,
    h.2.kill (fun R hR => runBlock_regs_of_not_flat js sa R hR)⟩

/-- **The class check is sound.** An accepted instruction simulates its machine
    instructions from `MCorr` at `s` to `MCorr` at the returned state. -/
theorem coreStep_sound (hsep : MemSep E.rs base rsp) {s s' : St} {i : LinstrRM}
    {js : List (JInstr 64)} (h : coreStep E s i js = some s') {zl : Prop} :
    DecSim (MCorr E base rsp s zl) (MCorr E base rsp s' False) [i] js := by
  unfold coreStep at h
  split at h
  · exact absurd h (by simp)
  rename_i hsp
  simp only [decide_eq_true_eq] at hsp
  split at h
  · -- the load
    rename_i d opn A idx sc w n
    split at h
    · rename_i D B X sc'
      split at h
      · rename_i hc
        obtain rfl := Option.some.inj h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hidx⟩, rfl⟩, hptr⟩, hix⟩ := hc
        have hs := decSim_loadX (π := E.pi) (Lay := regLay E.rs base)
          (frame := regFrame E.rs rsp) (K := regK E.rs) (zl := zl) (L := (· ∈ s.1))
          (L' := liveAfter E.pi (· ∈ s.1) d (E.pi d)) d A idx B X hidx (fun _ hr => hr)
        have hf := DecSim.frameWith _ (MachOK E base rsp s)
          (MachOK E base rsp (s.1, s.2.kill [E.pi d])) hs
          (fun sa hm => by
            obtain ⟨e, hk⟩ := idxOK_holds hix hm.2
            exact ⟨hm.2.2.2 _ hptr, e, hk⟩)
          (fun sa hm => machOK_block (js := [.loadMemIdx (E.pi d) B X 8]) hsp hm)
        exact hf.weaken (fun _ _ _ h => h) (fun _ _ _ h =>
          ⟨(corr_liveW h.1).mono (fun _ hr => hr) (fun hf => hf.elim) (fun _ _ h => h), h.2⟩)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- the store
    rename_i dst opn A idx sc v w n
    split at h
    · rename_i B X sc' V
      split at h
      · rename_i hc
        obtain rfl := Option.some.inj h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, hdA⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hidx⟩, hv⟩, rfl⟩, hptr⟩, hix⟩ := hc
        subst dst
        intro sa b zf ⟨hc, hm⟩
        obtain ⟨e, hk⟩ := idxOK_holds hix hm.2
        obtain ⟨b', z', hr, hJ⟩ := decSim_storeX (π := E.pi) (Lay := regLay E.rs base)
          (frame := regFrame E.rs rsp) (K := regK E.rs) (zl := zl) (L := (· ∈ s.1)) hsep.sep
          A idx v B X hidx hv _ sa b zf ⟨hc, hm.2.2.2 _ hptr, e, rfl, hk⟩
        refine ⟨b', z', hr, hJ.mono (fun _ hr => hr) (fun hf => hf.elim)
          (afterStore_regK hsep hk), ?_⟩
        have hregs : ∀ R, (aMachine.runBlock sa [.storeMemIdx B X 8 (.reg (E.pi v))]).regs R
            = sa.regs R := fun R => runBlock_regs_of_not_flat _ sa R (by simp [dsts])
        exact ⟨by rw [hregs]; exact hm.1, hm.2.of_regs hregs⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- the register classes
    obtain ⟨Ls', hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact DecSim.frame _ _ (regStep_sound (Lay := regLay E.rs base)
      (frame := regFrame E.rs rsp) (K := regK E.rs) (zl := zl) hr)
      (fun sa hm => machOK_block (s := s) hsp hm)

/-! ## 6. Machine-only instructions and groups -/

/-- **The machine-only classes.** A register copy into a register other than the stack
    register, and the reload of the pointer of a region from its frame slot. -/
def machStep (E : MemEnv) (s : St) (j : JInstr 64) : Option St :=
  match j with
  | .mov X (.reg Y) =>
      if X == E.sp then none else some (liveO E.pi s.1 X, s.2.movTo X Y)
  | .loadMem S B off =>
      if S == E.sp || B != E.sp then none else
      match E.rs.find? (fun r => r.off == off) with
      | some r =>
          if regFind E.rs r.name == some r then some (liveO E.pi s.1 S, s.2.reload S r.name)
          else none
      | none => none
  | _ => none

/-- **The machine-only classes are sound.** -/
theorem machStep_sound {s s' : St} {j : JInstr 64} (h : machStep E s j = some s') {zl : Prop} :
    DecSim (MCorr E base rsp s zl) (MCorr E base rsp s' zl) [] [j] := by
  unfold machStep at h
  split at h
  · rename_i X Y
    split at h
    · exact absurd h (by simp)
    rename_i hX
    obtain rfl := Option.some.inj h
    simp only [beq_iff_eq] at hX
    refine DecSim.machOnly fun sa b zf ⟨hc, hm⟩ => ?_
    have em : ∀ r, (evalInstrA sa (.mov X (.reg Y))).regs r
        = if r = X then sa.regs Y else sa.regs r := fun _ => rfl
    refine ⟨hc.machWrite X (sa.regs Y) _ em rfl (fun r hr => mem_liveO.mp hr)
      (fun hz => hc.zfEq hz), ?_, hm.2.movTo em⟩
    rw [em, if_neg (Ne.symm hX)]; exact hm.1
  · rename_i S B off
    split at h
    · exact absurd h (by simp)
    rename_i hSB
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_or, not_not] at hSB
    obtain ⟨hS, rfl⟩ := hSB
    split at h
    · rename_i r hr
      split at h
      · rename_i hf
        obtain rfl := Option.some.inj h
        simp only [beq_iff_eq] at hf
        have hoff : r.off = off := by
          have := List.find?_some hr
          simpa using this
        refine DecSim.machOnly fun sa b zf ⟨hc, hm⟩ => ?_
        have em : ∀ x, (evalInstrA sa (.loadMem S E.sp off)).regs x
            = if x = S then read64 sa.mem (sa.regs E.sp + BitVec.ofInt 64 off)
              else sa.regs x := fun _ => rfl
        have hq : (regLay E.rs base).slot r.name = some r.name := by
          simp [regLay, hf]
        have hfr : regFrame E.rs rsp r.name = some (sa.regs E.sp + BitVec.ofInt 64 off) := by
          simp [regFrame, hf, hm.1, hoff]
        obtain ⟨hS1, _⟩ := reload_regs hc r.name S E.sp r.name off hq hfr
        refine ⟨hc.machWrite S _ _ em rfl (fun r hr => mem_liveO.mp hr)
          (fun hz => hc.zfEq hz), ?_, ?_⟩
        · rw [em, if_neg (Ne.symm hS)]; exact hm.1
        · have hk : (s.2.kill [S]).Holds base E.nb (evalInstrA sa (.loadMem S E.sp off)) :=
            hm.2.kill (fun R hR => by rw [em, if_neg (by simpa using hR)])
          refine ⟨hk.1, hk.2.1, fun p hp => ?_⟩
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hS1
          · exact hk.2.2 p hp
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- One flag-machine instruction against a group of machine instructions: a prefix of
    machine-only instructions, then the instructions of one class. -/
def grpStep (E : MemEnv) (i : LinstrRM) : St → List (JInstr 64) → Option St
  | s, [] => coreStep E s i []
  | s, j :: js =>
      match coreStep E s i (j :: js) with
      | some s' => some s'
      | none => (machStep E s j).bind fun s1 => grpStep E i s1 js

theorem grpStep_sound (hsep : MemSep E.rs base rsp) (i : LinstrRM) :
    ∀ (js : List (JInstr 64)) (s s' : St) (zl : Prop), grpStep E i s js = some s' →
      DecSim (MCorr E base rsp s zl) (MCorr E base rsp s' False) [i] js := by
  intro js
  induction js with
  | nil => intro s s' zl h; exact coreStep_sound hsep h
  | cons j js ih =>
    intro s s' zl h
    simp only [grpStep] at h
    split at h
    · rename_i s'' hc
      obtain rfl := Option.some.inj h
      exact coreStep_sound hsep hc
    · obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      exact DecSim.mach_cons (machStep_sound h1) (ih s1 s' zl h2)

/-- A block of machine-only instructions. -/
def machRun (E : MemEnv) : St → List (JInstr 64) → Option St
  | s, [] => some s
  | s, j :: js => (machStep E s j).bind fun s1 => machRun E s1 js

theorem machRun_sound :
    ∀ (js : List (JInstr 64)) (s s' : St) (zl : Prop), machRun E s js = some s' →
      DecSim (MCorr E base rsp s zl) (MCorr E base rsp s' zl) [] js := by
  intro js
  induction js with
  | nil =>
    intro s s' zl h
    obtain rfl := Option.some.inj h
    exact DecSim.nil _
  | cons j js ih =>
    intro s s' zl h
    obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    exact DecSim.mach_cons (machStep_sound h1) (ih s1 s' zl h2)

/-! ## 7. A body -/

/-- **The check on a body.** Each flag-machine instruction against a group of the machine
    instructions, the groups found by search; the machine instructions after the last group
    are machine-only, and the final state satisfies `fin`. Returns the final live list and
    abstract state. -/
def mbodyOK (E : MemEnv) (fin : St → Bool) : St → List LinstrRM → List (JInstr 64) → Option St
  | s, [], js =>
      match machRun E s js with
      | some s' => if fin s' then some s' else none
      | none => none
  | s, i :: is, js => (List.range (js.length + 1)).findSome? fun k =>
      (grpStep E i s (js.take k)).bind fun s1 => mbodyOK E fin s1 is (js.drop k)

/-- **An accepted body simulates its machine instructions**, and its final state satisfies
    `fin`. -/
theorem mbodyOK_sound (hsep : MemSep E.rs base rsp) (fin : St → Bool) :
    ∀ (is : List LinstrRM) (s s' : St) (js : List (JInstr 64)) (zl : Prop),
      mbodyOK E fin s is js = some s' →
      fin s' = true ∧ DecSim (MCorr E base rsp s zl) (MCorr E base rsp s' False) is js := by
  intro is
  induction is with
  | nil =>
    intro s s' js zl h
    simp only [mbodyOK] at h
    split at h
    · rename_i s'' hm
      split at h
      · rename_i hf
        obtain rfl := Option.some.inj h
        exact ⟨hf, (machRun_sound js s s'' zl hm).weaken (fun _ _ _ h => h)
          (fun _ _ _ h => ⟨h.1.mono (fun _ hr => hr) (fun hf => hf.elim) (fun _ _ h => h),
            h.2⟩)⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  | cons i is ih =>
    intro s s' js zl h
    simp only [mbodyOK] at h
    obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
    obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp hk
    obtain ⟨hf, h2'⟩ := ih s1 s' (js.drop k) False h2
    have := (grpStep_sound hsep i (js.take k) s s1 zl h1).append h2'
    rw [List.take_append_drop] at this
    exact ⟨hf, this⟩

/-- The final check of a loop body: the live list contains `L0`. -/
def liveFin (L0 : List String) (s : St) : Bool := L0.all (fun r => decide (r ∈ s.1))

/-- **The check on a loop body.** The body is accepted from the live list `L0` and the
    abstract state `a0`, with a final live list containing `L0`. -/
def loopOK (E : MemEnv) (L0 : List String) (a0 : Abs) (is : List LinstrRM)
    (js : List (JInstr 64)) : Bool :=
  (mbodyOK E (liveFin L0) (L0, a0) is js).isSome

/-- **An accepted loop body simulates its machine instructions**, from the live list `L0`
    with the facts `a0` back to `L0` with no machine facts. -/
theorem decSim_of_loopOK (hsep : MemSep E.rs base rsp) {L0 : List String} {a0 : Abs}
    {is : List LinstrRM} {js : List (JInstr 64)} (h : loopOK E L0 a0 is js = true) (zl : Prop) :
    DecSim (MCorr E base rsp (L0, a0) zl) (MCorr E base rsp (L0, Abs.empty) False) is js := by
  unfold loopOK at h
  obtain ⟨s', hs⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hf, hd⟩ := mbodyOK_sound hsep (liveFin L0) is _ s' js zl hs
  have hL : ∀ r ∈ L0, r ∈ s'.1 := by simpa [liveFin] using hf
  exact hd.weaken (fun _ _ _ h => h)
    (fun sa _ _ h => ⟨h.1.mono (fun r hr => hL r hr) id (fun _ _ h => h),
      h.2.1, Abs.holds_empty base E.nb sa⟩)

/-- **A loop body from its head.** At a loop head related by `MCorr` with no machine facts,
    whose index register `R` holds a value below the bound, an accepted loop body from the
    fact `R ∈ bnd` simulates its machine instructions. -/
theorem decSim_of_loopOK_idx (hsep : MemSep E.rs base rsp) {L0 : List String} {R : String}
    {is : List LinstrRM} {js : List (JInstr 64)} (h : loopOK E L0 ⟨[], [R], []⟩ is js = true)
    (zl : Prop) :
    DecSim (fun sa b zf => MCorr E base rsp (L0, Abs.empty) zl sa b zf ∧ (sa.regs R).toNat < E.nb)
      (MCorr E base rsp (L0, Abs.empty) False) is js :=
  (decSim_of_loopOK hsep h zl).weaken (fun _ _ _ h => ⟨h.1.1, h.1.2.1,
    fun _ hp => by simp at hp, fun R' hR' => by
      rw [List.mem_singleton] at hR'; subst hR'; exact h.2, fun _ hp => by simp at hp⟩)
    (fun _ _ _ h => h)

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem
