/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeCarry

@[expose] public section

set_option autoImplicit false

/-!
# A decoded loop body read back as flag-machine instructions

The loop route compares a certified virtual loop body with the loop body the owned back end
prints and the encoder emits. The printed body is the virtual one after register allocation,
scheduling, the widening-multiply fusion, spilling and the two-address legalisation, so the
two are related by translation validation rather than by a fixed register map. This module
reads a decoded machine loop body back as flag-machine instructions over machine register
names (`liftBody`), the form the validator compares with the virtual body. The stack
register is `%rsp`; every other register an instruction names is one of `liftRegs`.

* a register `%rN` is the name `RN` (`liftReg`);
* the reload of the base of a word-array region from its frame slot is a machine-only
  instruction: it is read as nothing, and records that the register holds the region's base;
* an indexed load or store through a register holding the base of the region `A` is the
  indexed access to the array `A`, at the region's length, when the index register holds a
  value below that length;
* a store to a frame word at an offset of the list `S` is a copy to the name `slot.off`
  (`slotName`); a load of such a word, and a compare with it, read that name, when the
  reading state records that the name holds the word's value (`slive`);
* the register and immediate moves, the two-address operations `add`, `sub`, `and`, `xor`,
  `or`, `imul` on registers, `add` and `sub` of an immediate, the shifts by an immediate
  count in `[1, 63]` (in the count-in-name form `immShiftI`) and the compares are their
  flag-machine forms; a copy of a register whose name does not hold its value is
  machine-only, and the name of its destination then does not hold its value either;
* `mulx H, Lo` with its implicit source `%rdx` and the source `C` is the high word
  `H := MULXHI:64 [RDX, C]` and the low word `Lo := MUL:64 [RDX, C]`; when the reading
  state records that `Lo` already holds the low word of the product of `%rdx` and `C`, it is
  the high word alone.

The reading state (`LiftSt`) records syntactic facts on machine values: region bases,
constants, copies, low words of products (from `mov D, X; imul D, Y`, kept through
`and D, M` with `M` all-ones and through copies), index bounds `v < nb + δ` for the loop
bound `nb` (kept through copies and raised by the addition of a constant), whether the
machine zero flag is the flag machine's (after a compare and until the next flag-writing
operation), and the registers a pointer reload wrote (`dead`), whose names an instruction
read back may not read until it writes them. The reading is syntactic; its soundness, which checks these facts on the
machine state, is `DecodeLoopTVSound`.

## Main results

* `liftReg`, `slotName`, `liftRegs` — the names of a register and of a frame word, and the
  registers read.
* `LiftEnv`, `LiftSt`, `LiftSt.kill`, `LiftSt.copy`, `LiftSt.holdsLo`, `LiftSt.bndOf`,
  `LiftSt.immOf` — the reading environment and state.
* `liftInstr`, `liftRun`, `liftBody` — the reading of a loop body.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLoopTV

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (Region regLen)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (dsts)

/-- The flag-machine name of a machine register: `%rax` is `RAX`. -/
def liftReg (r : String) : String := String.ofList ((r.toList.drop 1).map Char.toUpper)

/-- The flag-machine name of the frame word at the offset `off` from the stack pointer. -/
def slotName (off : Int) : String := "slot." ++ toString off

/-- The machine registers a read instruction may name besides the stack register. -/
def liftRegs : List String :=
  ["%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%r8", "%r9", "%r10", "%r11",
    "%r12", "%r13", "%r14", "%r15"]

/-- The environment of the reading: the regions, the frame offsets read as names, and the
    loop bound `nb` of the index facts. -/
structure LiftEnv where
  /-- The word-array regions. -/
  rs : List Region
  /-- The offsets from `%rsp` of the frame words read as the names `slot.off`. -/
  S : List Int
  /-- The loop bound: an index fact `(R, δ)` states that `R` holds a value below `nb + δ`. -/
  nb : Nat

/-- The state of the reading: facts on the values of machine registers and on the zero
    flag. -/
structure LiftSt where
  /-- `(B, A)`: the register `B` holds the base of the region `A`. -/
  ptr : List (String × String) := []
  /-- `(R, n)`: the register `R` holds the word `n`. -/
  imm : List (String × Nat) := []
  /-- `(D, X)`: the register `D` holds the value of the register `X`. -/
  cp : List (String × String) := []
  /-- `(D, X, Y)`: the register `D` holds the low word of the product of the registers `X`
      and `Y`. -/
  lo : List (String × String × String) := []
  /-- `(R, δ)`: the register `R` holds a value below `nb + δ`. -/
  bnd : List (String × Nat) := []
  /-- The machine zero flag is the flag machine's zero flag. -/
  zl : Bool := false
  /-- The registers whose value differs from the flag machine's name for them: a register a
      machine-only instruction wrote, until an instruction read back writes it. -/
  dead : List String := []
  /-- The offsets of the frame words whose flag-machine name `slot.off` holds their value. -/
  slive : List Int := []

/-- The register `X` is read back and its flag-machine name holds its value. -/
def LiftSt.live (st : LiftSt) (X : String) : Bool := liftRegs.contains X && !st.dead.contains X

/-- The reading state after an instruction read back writes the registers `ws`: the facts
    that name none of them, and the registers `ws` live. -/
def LiftSt.kill (st : LiftSt) (ws : List String) : LiftSt :=
  { st with
    dead := st.dead.filter fun r => !ws.contains r
    ptr := st.ptr.filter fun p => !ws.contains p.1
    imm := st.imm.filter fun p => !ws.contains p.1
    cp := st.cp.filter fun p => !ws.contains p.1 && !ws.contains p.2
    lo := st.lo.filter fun p => !ws.contains p.1 && !ws.contains p.2.1 && !ws.contains p.2.2
    bnd := st.bnd.filter fun p => !ws.contains p.1 }

/-- The facts after the copy `D := X` from the state `st` with the facts on `D` removed: `D`
    holds the value of `X`, and every fact on the value of `X` holds for `D`. -/
def LiftSt.copy (st : LiftSt) (D X : String) : LiftSt :=
  { st with
    ptr := (st.ptr.filterMap fun p => if p.1 == X then some (D, p.2) else none) ++ st.ptr
    imm := (st.imm.filterMap fun p => if p.1 == X then some (D, p.2) else none) ++ st.imm
    cp := (D, X) :: st.cp
    lo := (st.lo.filterMap fun p => if p.1 == X then some (D, p.2) else none) ++ st.lo
    bnd := (st.bnd.filterMap fun p => if p.1 == X then some (D, p.2) else none) ++ st.bnd }

/-- The facts state that `D` holds the low word of the product of `X` and `Y`, in either
    order of the factors or through a copy of `X`. -/
def LiftSt.holdsLo (st : LiftSt) (D X Y : String) : Bool :=
  let has := fun (a : String) => st.lo.contains (D, a, Y) || st.lo.contains (D, Y, a)
  has X || st.cp.any fun p => p.1 == X && has p.2

/-- The first index fact on the register `R`. -/
def LiftSt.bndOf (st : LiftSt) (R : String) : Option Nat := st.bnd.lookup R

/-- The first constant fact on the register `R`. -/
def LiftSt.immOf (st : LiftSt) (R : String) : Option Nat := st.imm.lookup R

/-- The reading state after `D := D + n` for the constant `n`: the facts on `D` removed, and
    the index fact `(D, δ + n)` when `D` had the index fact `(D, δ)` and `nb + δ + n` is at
    most `2 ^ 64`. -/
def LiftSt.addConst (E : LiftEnv) (st : LiftSt) (D : String) (n : Nat) : LiftSt :=
  let st' := { st.kill [D] with zl := false }
  match st.bndOf D with
  | some δ => if E.nb + δ + n ≤ 2 ^ 64 then { st' with bnd := (D, δ + n) :: st'.bnd } else st'
  | none => st'

/-- The flag-machine instruction `op:64 d, srcs` on registers. -/
def opI (opn D : String) (srcs : List LOperand) : LinstrRM :=
  (.Lopn [.reg (liftReg D)] (withWidthTag 64 opn) srcs, .reg none)

/-- The two-address operations on registers read as `op:64 d, d, s`, with the facts after
    them. -/
def binRegLift (E : LiftEnv) (st : LiftSt) : JInstr 64 → Option (String × String × LiftSt)
  | .add D (.reg Y) => some ("ADD", Y,
      match st.immOf Y with
      | some n => if Y == D then { st.kill [D] with zl := false } else st.addConst E D n
      | none => { st.kill [D] with zl := false })
  | .sub D (.reg Y) => some ("SUB", Y, { st.kill [D] with zl := false })
  | .and_ D (.reg Y) => some ("AND", Y,
      if Y != D && st.immOf Y == some (2 ^ 64 - 1) then { st with zl := false }
      else { st.kill [D] with zl := false })
  | .xor_ D (.reg Y) => some ("XOR", Y, { st.kill [D] with zl := false })
  | .or_ D (.reg Y) => some ("OR", Y, { st.kill [D] with zl := false })
  | .imul D (.reg Y) =>
      let new := if Y == D then [] else (st.cp.filter (·.1 == D)).map fun p => (D, p.2, Y)
      let st' := { st.kill [D] with zl := false }
      some ("MUL", Y, { st' with lo := new ++ st'.lo })
  | _ => none

/-- **One machine instruction of a loop body read back** in the environment `E`: the
    reading state after the instruction and its flag-machine instructions, or `none` outside
    the read fragment. -/
def liftInstr (E : LiftEnv) (st : LiftSt) (j : JInstr 64) : Option (LiftSt × List LinstrRM) :=
  let ok := fun (X : String) => liftRegs.contains X
  let rd := st.live
  match j with
  | .loadMem S B off =>
      if B != "%rsp" || !ok S then none else
      match E.rs.find? (·.off == off) with
      | some g =>
          if DecodeGenMem.regFind E.rs g.name != some g then none else
          let st' := st.kill [S]
          some ({ st' with ptr := (S, g.name) :: st'.ptr, dead := S :: st'.dead }, [])
      | none =>
          if st.slive.contains off then
            some (st.kill [S], [opI "MOV" S [.reg (slotName off)]])
          else none
  | .storeMem B off (.reg X) =>
      if B != "%rsp" || !rd X || !E.S.contains off || E.rs.any (·.off == off) then none
      else some ({ st with slive := off :: st.slive },
        [(.Lopn [.reg (slotName off)] (withWidthTag 64 "MOV") [.reg (liftReg X)], .reg none)])
  | .loadMemIdx D B X sc =>
      if !ok D || !ok B || !rd X || sc != 8 then none else
      match st.ptr.lookup B, st.bndOf X with
      | some A, some δ =>
          if E.nb + δ ≤ regLen E.rs A then
            some (st.kill [D], [(.Lopn [.reg (liftReg D)] "LOADIDX" [.arrIdx A (liftReg X) 8],
              .load 64 (regLen E.rs A))])
          else none
      | _, _ => none
  | .storeMemIdx B X sc (.reg V) =>
      if !ok B || !rd X || !rd V || sc != 8 then none else
      match st.ptr.lookup B, st.bndOf X with
      | some A, some δ =>
          if E.nb + δ ≤ regLen E.rs A then
            some (st, [(.Lopn [.reg A] "STOREIDX" [.arrIdx A (liftReg X) 8,
              .reg (liftReg V)], .store 64 (regLen E.rs A))])
          else none
      | _, _ => none
  | .mov D (.reg X) =>
      if !ok D || !ok X then none
      else if !rd X then
        let st' := st.kill [D]
        some ({ st' with dead := D :: st'.dead }, [])
      else some (if X == D then st else (st.kill [D]).copy D X,
        [opI "MOV" D [.reg (liftReg X)]])
  | .mov D (.imm n) =>
      if !ok D || !decide (n < 2 ^ 64) then none
      else some ({ st.kill [D] with imm := (D, n) :: (st.kill [D]).imm }, [opI "MOV" D [.imm n]])
  | .add D (.imm k) =>
      if !rd D then none else some (st.addConst E D k, [opI "ADD" D [.reg (liftReg D), .imm k]])
  | .sub D (.imm k) =>
      if !rd D then none
      else some ({ st.kill [D] with zl := false }, [opI "SUB" D [.reg (liftReg D), .imm k]])
  | .shr D (.imm k) =>
      if !rd D || k == 0 || !decide (k < 64) then none
      else some ({ st.kill [D] with zl := false },
        [DecodedLsemStep.immShiftI "SHR" (liftReg D) (liftReg D) k])
  | .shl D (.imm k) =>
      if !rd D || k == 0 || !decide (k < 64) then none
      else some ({ st.kill [D] with zl := false },
        [DecodedLsemStep.immShiftI "SHL" (liftReg D) (liftReg D) k])
  | .mulx H Lo (.reg S) (.reg C) =>
      if S != "%rdx" || H == Lo || !ok H || !ok Lo || !rd "%rdx" || !rd C then none else
      let srcs := [.reg (liftReg "%rdx"), .reg (liftReg C)]
      let hi := opI "MULXHI" H srcs
      let mul := opI "MUL" Lo srcs
      if st.holdsLo Lo "%rdx" C then some (st.kill [H], [hi])
      else if H != "%rdx" && H != C then some (st.kill [H, Lo], [hi, mul])
      else if Lo != "%rdx" && Lo != C then some (st.kill [H, Lo], [mul, hi])
      else none
  | .cmp A (.reg X) =>
      if !rd A || !rd X then none
      else some ({ st with zl := true }, [opI "CMP" A [.reg (liftReg A), .reg (liftReg X)]])
  | .cmp A (.imm k) =>
      if !rd A then none
      else some ({ st with zl := true }, [opI "CMP" A [.reg (liftReg A), .imm k]])
  | .cmpMem A B off =>
      if B != "%rsp" || !rd A || !st.slive.contains off then none
      else some ({ st with zl := true },
        [opI "CMP" A [.reg (liftReg A), .reg (slotName off)]])
  | j =>
      match binRegLift E st j with
      | some (opn, Y, st') =>
          match j with
          | .add D _ | .sub D _ | .and_ D _ | .xor_ D _ | .or_ D _ | .imul D _ =>
              if !rd D || !rd Y then none
              else some (st', [opI opn D [.reg (liftReg D), .reg (liftReg Y)]])
          | _ => none
      | none => none

/-- **A decoded loop body read back** from the reading state `st`: the reading state at its
    end and the flag-machine instructions of every machine instruction, or `none` when one
    lies outside the read fragment. -/
def liftRun (E : LiftEnv) : LiftSt → List (JInstr 64) → Option (LiftSt × List LinstrRM)
  | st, [] => some (st, [])
  | st, j :: js => (liftInstr E st j).bind fun (st', is) =>
      (liftRun E st' js).map fun (st'', is') => (st'', is ++ is')

/-- The flag-machine instructions of a decoded loop body read back from `st`. -/
def liftBody (E : LiftEnv) (st : LiftSt) (js : List (JInstr 64)) : Option (List LinstrRM) :=
  (liftRun E st js).map (·.2)

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLoopTV
