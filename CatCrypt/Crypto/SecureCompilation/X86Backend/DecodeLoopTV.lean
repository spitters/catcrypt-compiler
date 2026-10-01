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
* the two-address operations, the register and immediate moves and the immediate shifts are
  their flag-machine forms;
* `mulx H, Lo` with its implicit source `%rdx` and the source `C` is the high word
  `H := MULXHI:64 [RDX, C]` and the low word `Lo := MUL:64 [RDX, C]`; when the reading
  state records that `Lo` already holds the low word of the product of `%rdx` and `C`, it is
  the high word alone.

The reading state (`LiftSt`) records syntactic facts on register values: region bases,
the all-ones word, copies, and low words of products (from `mov D, X; imul D, Y`, kept
through `and D, M` with `M` all-ones and through copies). The reading is syntactic; the
decode check of the read body against the machine body, which checks these facts on the
machine state, is its soundness.

## Main results

* `liftReg`, `slotName` — the names of a register and of a frame word.
* `LiftSt`, `LiftSt.kill`, `LiftSt.copy`, `LiftSt.holdsLo` — the facts of the reading.
* `liftInstr`, `liftBody` — the reading of a loop body.
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

/-- The state of the reading: facts on the values of machine registers. -/
structure LiftSt where
  /-- `(B, A)`: the register `B` holds the base of the region `A`. -/
  ptr : List (String × String) := []
  /-- The registers holding the all-ones word `2 ^ 64 - 1`. -/
  ones : List String := []
  /-- `(D, X)`: the register `D` holds the value of the register `X`. -/
  cp : List (String × String) := []
  /-- `(D, X, Y)`: the register `D` holds the low word of the product of the registers `X`
      and `Y`. -/
  lo : List (String × String × String) := []

/-- The reading state after a machine instruction writes the registers `ws`: the facts that
    name none of them. -/
def LiftSt.kill (st : LiftSt) (ws : List String) : LiftSt :=
  { ptr := st.ptr.filter fun p => !ws.contains p.1
    ones := st.ones.filter fun r => !ws.contains r
    cp := st.cp.filter fun p => !ws.contains p.1 && !ws.contains p.2
    lo := st.lo.filter fun p => !ws.contains p.1 && !ws.contains p.2.1 && !ws.contains p.2.2 }

/-- The facts after the copy `D := X` from the state `st` with the facts on `D` removed: `D`
    holds the value of `X`, and every fact on the value of `X` holds for `D`. -/
def LiftSt.copy (st : LiftSt) (D X : String) : LiftSt :=
  { st with
    ones := if st.ones.contains X then D :: st.ones else st.ones
    cp := (D, X) :: st.cp
    lo := (st.lo.filterMap fun p => if p.1 == X then some (D, p.2) else none) ++ st.lo }

/-- The facts state that `D` holds the low word of the product of `X` and `Y`, in either
    order of the factors or through a copy of `X`. -/
def LiftSt.holdsLo (st : LiftSt) (D X Y : String) : Bool :=
  let has := fun (a : String) => st.lo.contains (D, a, Y) || st.lo.contains (D, Y, a)
  has X || st.cp.any fun p => p.1 == X && has p.2

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
  let op (opn D : String) (srcs : List LOperand) : LinstrRM :=
    (.Lopn [.reg (liftReg D)] (withWidthTag 64 opn) srcs, .reg none)
  match j with
  | .loadMem S B off =>
      if B != sp || S == sp then none else
      match rs.find? (·.off == off) with
      | some g => some ({ st' with ptr := (S, g.name) :: st'.ptr }, [])
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
      let st'' := match s with
        | .reg X => if X == D then st else st'.copy D X
        | .imm n => if n == 2 ^ 64 - 1 then { st' with ones := D :: st'.ones } else st'
      some (st'', [op "MOV" D [liftOp s]])
  | .imul D (.reg Y) => if D == sp then none else
      let new := if Y == D then [] else
        (st.cp.filter (·.1 == D)).map fun p => (D, p.2, Y)
      some ({ st' with lo := new ++ st'.lo }, [op "MUL" D [.reg (liftReg D), .reg (liftReg Y)]])
  | .and_ D (.reg M) => if D == sp then none else
      some (if M != D && st.ones.contains M then st else st',
        [op "AND" D [.reg (liftReg D), .reg (liftReg M)]])
  | .shr D (.imm k) => some (st',
      [(.Lopn [.reg (liftReg D)] (withWidthTag 64 "SHR") [.reg (liftReg D), .imm k], .reg none)])
  | .shl D (.imm k) => some (st',
      [(.Lopn [.reg (liftReg D)] (withWidthTag 64 "SHL") [.reg (liftReg D), .imm k], .reg none)])
  | .mulx H Lo (.reg S) (.reg C) =>
      if S != "%rdx" || H == Lo then none else
      let srcs := [.reg (liftReg "%rdx"), .reg (liftReg C)]
      let hi := op "MULXHI" H srcs
      let mul := op "MUL" Lo srcs
      if st.holdsLo Lo "%rdx" C then some (st.kill [H], [hi])
      else if H != "%rdx" && H != C then some (st', [hi, mul])
      else if Lo != "%rdx" && Lo != C then some (st', [mul, hi])
      else none
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
