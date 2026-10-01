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
names (`liftBody`), the form the validator compares with the virtual body:

* a register `%rN` is the name `RN` (`liftReg`);
* the reload of the base of a word-array region from its frame slot is a machine-only
  instruction: it is read as nothing, and records that the register holds the region's base;
* an indexed load or store through a register holding the base of the region `A` is the
  indexed access to the array `A`, at the region's length;
* a load or store of another frame word is a copy from or to the name `slot.off`
  (`slotName`);
* a compare with a frame word compares with the name `slot.off`;
* the two-address operations, the register and immediate moves, the immediate shifts and
  `mulx` are their flag-machine forms (`MULX:64` with its implicit source `RDX`).

The reading is syntactic; the decode check of the read body against the machine body is
its soundness.

## Main results

* `liftReg`, `slotName` — the names of a register and of a frame word.
* `LiftSt`, `liftInstr`, `liftBody` — the reading of a loop body.
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

/-- The flag-machine operand of a machine operand. -/
def liftOp : JOperand → LOperand
  | .reg r => .reg (liftReg r)
  | .imm n => .imm n

/-- The state of the reading: the machine registers holding the base of a region, with the
    region's name. -/
structure LiftSt where
  /-- `(B, A)`: the register `B` holds the base of the region `A`. -/
  ptr : List (String × String)

/-- The reading state after a machine instruction writes the registers `ws`. -/
def LiftSt.kill (st : LiftSt) (ws : List String) : LiftSt :=
  ⟨st.ptr.filter fun p => !ws.contains p.1⟩

/-- The two-address operations read as `op:64 d, d, s`. -/
def binOpName : JInstr 64 → Option (String × String × JOperand)
  | .add D s => some ("ADD:64", D, s)
  | .sub D s => some ("SUB:64", D, s)
  | .and_ D s => some ("AND:64", D, s)
  | .xor_ D s => some ("XOR:64", D, s)
  | .or_ D s => some ("OR:64", D, s)
  | .imul D s => some ("MUL:64", D, s)
  | _ => none

/-- **One machine instruction of a loop body read back.** `sp` is the stack register and `rs`
    the regions; the result is the reading state after the instruction and its flag-machine
    instructions, or `none` outside the read fragment. -/
def liftInstr (sp : String) (rs : List Region) (st : LiftSt) (j : JInstr 64) :
    Option (LiftSt × List LinstrRM) :=
  let st' := st.kill (dsts j)
  match j with
  | .loadMem S B off =>
      if B != sp || S == sp then none else
      match rs.find? (·.off == off) with
      | some g => some (⟨(S, g.name) :: st'.ptr⟩, [])
      | none => some (st',
          [(.Lopn [.reg (liftReg S)] (withWidthTag 64 "MOV") [.reg (slotName off)], .reg none)])
  | .storeMem B off (.reg X) =>
      if B != sp || (rs.any (·.off == off)) then none
      else some (st,
        [(.Lopn [.reg (slotName off)] (withWidthTag 64 "MOV") [.reg (liftReg X)], .reg none)])
  | .loadMemIdx D B X sc =>
      match st.ptr.lookup B with
      | some A => if sc != 8 then none else some (st',
          [(.Lopn [.reg (liftReg D)] "LOADIDX" [.arrIdx A (liftReg X) 8],
            .load 64 (regLen rs A))])
      | none => none
  | .storeMemIdx B X sc (.reg V) =>
      match st.ptr.lookup B with
      | some A => if sc != 8 then none else some (st,
          [(.Lopn [.reg A] "STOREIDX" [.arrIdx A (liftReg X) 8, .reg (liftReg V)],
            .store 64 (regLen rs A))])
      | none => none
  | .mov D s => if D == sp then none else
      some (st', [(.Lopn [.reg (liftReg D)] (withWidthTag 64 "MOV") [liftOp s], .reg none)])
  | .shr D (.imm k) => some (st',
      [(.Lopn [.reg (liftReg D)] (withWidthTag 64 "SHR") [.reg (liftReg D), .imm k], .reg none)])
  | .shl D (.imm k) => some (st',
      [(.Lopn [.reg (liftReg D)] (withWidthTag 64 "SHL") [.reg (liftReg D), .imm k], .reg none)])
  | .mulx H Lo (.reg S) (.reg C) =>
      if S != "%rdx" then none else some (st',
        [(.Lopn [.reg (liftReg Lo), .reg (liftReg H)] (withWidthTag 64 "MULX")
          [.reg (liftReg C)], .reg none)])
  | .cmp A s => some (st,
      [(.Lopn [.reg (liftReg A)] (withWidthTag 64 "CMP") [.reg (liftReg A), liftOp s],
        .reg none)])
  | .cmpMem A B off =>
      if B != sp then none else some (st,
        [(.Lopn [.reg (liftReg A)] (withWidthTag 64 "CMP") [.reg (liftReg A),
          .reg (slotName off)], .reg none)])
  | j =>
      match binOpName j with
      | some (opn, D, s) => if D == sp then none else some (st',
          [(.Lopn [.reg (liftReg D)] opn [.reg (liftReg D), liftOp s], .reg none)])
      | none => none

/-- **A decoded loop body read back** from the reading state `st`: the flag-machine
    instructions of every machine instruction, or `none` when one lies outside the read
    fragment. -/
def liftBody (sp : String) (rs : List Region) : LiftSt → List (JInstr 64) → Option (List LinstrRM)
  | _, [] => some []
  | st, j :: js => (liftInstr sp rs st j).bind fun (st', is) =>
      (liftBody sp rs st' js).map (is ++ ·)

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLoopTV
