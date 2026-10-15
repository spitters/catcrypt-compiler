/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.KatGuard
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen

@[expose] public section

set_option autoImplicit false

/-!
# Encoder pins for operands in frame slots

`LprogBytes.encodeLopn` encodes an operand in a frame slot (`k.N`, `qsave.X`) as the
`%rsp`-relative memory form `LprogAsmPrinter.renderLopn` prints. This module pins four
families against their component encoders, in a frame of `128` bytes with `64`-bit
spill cells, where `k.0` is at offset `56` and `k.1` at offset `48`:

* a two-address `ALU` operation with a slot source or destination takes the operation's
  own opcode in the `r ← r/m` or `r/m ← r` direction (`ADC` `13`, `ADD` `01`), and a move
  the `MOV` load `8B`;
* `MULX` with a slot source is the memory form `mulx off(%rsp), lo, hi`, and a slot
  destination has no encoding;
* `ADCX` into a slot with a slot first source or a slot second source runs in the
  borrowed scratch saved at `-128(%rsp)`: `bt $0, cin`, the save, the reload of the slot
  source or the register copy, `adcx` with a register or `%rsp`-relative source, the
  store into the destination slot and the restore;
* `ADCX` with its carry-in in a slot saves a scratch at `-128(%rsp)`, reloads the carry-in
  word into it and tests it with `bt $0`; for a register destination the scratch is
  restored before the register `mov`/`adcx`, and for a slot destination it is the
  accumulator of the spilled-destination sequence;
* `CMOV:64` with its true value in a slot and register destination, condition and false
  value is the copy of the false value, `test` of the condition and `cmovne` from the
  slot (`REX.W 0F 45 /r` with the `%rsp` base);
* `CMOV:64` with its false value in a slot and register destination and condition is the
  load of the slot into the destination, `test` of the condition and `cmovne` from a
  register true value other than the destination or from a slot true value.

The `ADCX` pins also check that `DecodeGen.shapeOf` splits the bytes into pieces that
decode to the printed instructions.

## Main results

* `#kat` pins of the slot-operand encodings of `ADC`/`ADD`/`MOV`, `MULX` and `ADCX`, of the
  refused slot `MULX` destination, the refused three-source `ADOX`, the carry-out `ADCXHI`
  into a slot, and of the `shapeOf` decode of both spilled `ADCX` forms.
* `#kat` pins of `ADCX` with a slot carry-in: the bytes, the `shapeOf` decode and the printed
  lines for a register and a slot destination, and the refused 32-bit form.
* `#kat` pins of the slot-source `CMOV:64` select: the printed lines, the bytes against the
  component encoders, and the bytes the assembler writes.
* `#kat` pins of the slot-false-value and both-slot `CMOV:64` selects: the printed lines, the
  bytes, the `shapeOf` decode, and the refused form whose destination is the true value.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeSlotOperandKats

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LinstrR LOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
  (encMulxMem encAdxCarry)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (DShape)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen (shapeOf)

/-- The body parameters of the pins: a `128`-byte frame, `64`-bit spill cells, the
    eight-cell save block. -/
def pinP : Params := { frame := 128, spillW := 64, qsaveB := 64, tbl := [] }

/-- The bytes of an instruction under `pinP`. -/
def enc (i : LinstrR) : List (BitVec 8) :=
  encodeLopn pinP.frame pinP.spillW i pinP.qsaveB

/-- The printed form of the instructions the computed shape of `i` decodes to; empty
    when the shape is not a run of pieces. -/
def shapeJs (i : LinstrR) : String :=
  match shapeOf pinP i with
  | some (.ops pcs) => reprStr (pcs.map Prod.snd)
  | _ => ""

-- the frame offsets of the two spill cells
#kat spillQsaveOff 128 64 "k.0" 64 == some 56 && spillQsaveOff 128 64 "k.1" 64 == some 48

-- `ADC:64` from a slot: `adc 56(%rsp), %rax`, opcode `13`
#kat enc (.Lopn [.reg "RAX"] "ADC:64" [.reg "RAX", .reg "k.0"]) == encRspMem 1 0x13 0 56

-- `ADD:64` into a slot: `add %rbx, 56(%rsp)`, opcode `01`
#kat enc (.Lopn [.reg "k.0"] "ADD:64" [.reg "k.0", .reg "RBX"]) == encRspMem 1 0x01 3 56

-- a move from a slot keeps the `MOV` load
#kat enc (.Lopn [.reg "RAX"] "MOV:64" [.reg "k.0"]) == encRspMem 1 0x8b 0 56

-- `MULX` from a slot: `mulx 56(%rsp), %r8, %r9`
#kat enc (.Lopn [.reg "R8", .reg "R9"] "MULX" [.reg "k.0"]) == encMulxMem 9 8 4 56

-- `MULX` into a slot has no encoding
#kat enc (.Lopn [.reg "k.0", .reg "R9"] "MULX" [.reg "R10"]) == []

/-- `ADCX:64 k.0 := k.1 + R10 + R11`: the scratch is `%rax`, the first of `%rax`, `%rbx`,
    `%rcx`, `%rdx` that no operand names. -/
def adcxSlotA : LinstrR := .Lopn [.reg "k.0"] "ADCX:64" [.reg "k.1", .reg "R10", .reg "R11"]

/-- `ADCX:64 k.0 := R10 + k.1 + RAX`: the scratch is `%rbx`. -/
def adcxSlotS : LinstrR := .Lopn [.reg "k.0"] "ADCX:64" [.reg "R10", .reg "k.1", .reg "RAX"]

#kat enc adcxSlotA
  == encBtImm 1 11 0 ++ encRspMem 1 0x89 0 (-128) ++ encRspMem 1 0x8b 0 48
    ++ encAdxCarry 0x66 0 10 ++ encRspMem 1 0x89 0 56 ++ encRspMem 1 0x8b 0 (-128)

#kat enc adcxSlotS
  == encBtImm 1 0 0 ++ encRspMem 1 0x89 3 (-128) ++ encAluRRw 1 0x89 3 10
    ++ encAdxRspMem 0x66 3 48 ++ encRspMem 1 0x89 3 56 ++ encRspMem 1 0x8b 3 (-128)

#kat shapeJs adcxSlotA == reprStr ([.bt "%r11" (.imm 0),
    .storeMem "%rsp" (-128) (.reg "%rax"), .loadMem "%rax" "%rsp" 48,
    .adcx "%rax" (.reg "%r10"), .storeMem "%rsp" 56 (.reg "%rax"),
    .loadMem "%rax" "%rsp" (-128)] : List (JInstr 64))

#kat shapeJs adcxSlotS == reprStr ([.bt "%rax" (.imm 0),
    .storeMem "%rsp" (-128) (.reg "%rbx"), .mov "%rbx" (.reg "%r10"),
    .adcxMem "%rbx" "%rsp" 48, .storeMem "%rsp" 56 (.reg "%rbx"),
    .loadMem "%rbx" "%rsp" (-128)] : List (JInstr 64))

/-- `ADCX:64 RBX := R10 + R11 + k.1`: a register destination with its carry-in in a slot;
    the scratch is `%rax`. -/
def adcxSlotCR : LinstrR := .Lopn [.reg "RBX"] "ADCX:64" [.reg "R10", .reg "R11", .reg "k.1"]

/-- `ADCX:64 k.0 := R10 + R11 + k.1`: a slot destination with its carry-in in a slot. -/
def adcxSlotCD : LinstrR := .Lopn [.reg "k.0"] "ADCX:64" [.reg "R10", .reg "R11", .reg "k.1"]

/-- `ADCX:64 RCX := RAX + R11 + k.1`: the scratch is `%rbx`, the first candidate no source
    names. -/
def adcxSlotCX : LinstrR := .Lopn [.reg "RCX"] "ADCX:64" [.reg "RAX", .reg "R11", .reg "k.1"]

-- save, reload of the carry-in word, `bt $0`, restore, then `mov %r10, %rbx; adcx %r11, %rbx`
#kat enc adcxSlotCR
  == encRspMem 1 0x89 0 (-128) ++ encRspMem 1 0x8b 0 48 ++ encBtImm 1 0 0
    ++ encRspMem 1 0x8b 0 (-128) ++ encAluRRw 1 0x89 3 10 ++ encAdxCarry 0x66 3 11

-- save, reload, `bt $0`, then the spilled-destination sequence in the scratch
#kat enc adcxSlotCD
  == encRspMem 1 0x89 0 (-128) ++ encRspMem 1 0x8b 0 48 ++ encBtImm 1 0 0
    ++ encAluRRw 1 0x89 0 10 ++ encAdxCarry 0x66 0 11 ++ encRspMem 1 0x89 0 56
    ++ encRspMem 1 0x8b 0 (-128)

#kat enc adcxSlotCX
  == encRspMem 1 0x89 3 (-128) ++ encRspMem 1 0x8b 3 48 ++ encBtImm 1 3 0
    ++ encRspMem 1 0x8b 3 (-128) ++ encAluRRw 1 0x89 1 0 ++ encAdxCarry 0x66 1 11

#kat shapeJs adcxSlotCR == reprStr ([.storeMem "%rsp" (-128) (.reg "%rax"),
    .loadMem "%rax" "%rsp" 48, .bt "%rax" (.imm 0), .loadMem "%rax" "%rsp" (-128),
    .mov "%rbx" (.reg "%r10"), .adcx "%rbx" (.reg "%r11")] : List (JInstr 64))

#kat shapeJs adcxSlotCD == reprStr ([.storeMem "%rsp" (-128) (.reg "%rax"),
    .loadMem "%rax" "%rsp" 48, .bt "%rax" (.imm 0), .mov "%rax" (.reg "%r10"),
    .adcx "%rax" (.reg "%r11"), .storeMem "%rsp" 56 (.reg "%rax"),
    .loadMem "%rax" "%rsp" (-128)] : List (JInstr 64))

-- the printer prints the same instructions
#kat LprogAsmPrinter.renderLopn pinP.frame pinP.spillW false [.reg "RBX"] "ADCX:64"
    [.reg "R10", .reg "R11", .reg "k.1"] pinP.qsaveB
  == ["\tmovq %rax, -128(%rsp)", "\tmovq 48(%rsp), %rax", "\tbtq $0, %rax",
      "\tmovq -128(%rsp), %rax", "\tmovq %r10, %rbx", "\tadcxq %r11, %rbx"]

#kat LprogAsmPrinter.renderLopn pinP.frame pinP.spillW false [.reg "k.0"] "ADCX:64"
    [.reg "R10", .reg "R11", .reg "k.1"] pinP.qsaveB
  == ["\tmovq %rax, -128(%rsp)", "\tmovq 48(%rsp), %rax", "\tbtq $0, %rax",
      "\tmovq %r10, %rax", "\tadcxq %r11, %rax", "\tmovq %rax, 56(%rsp)",
      "\tmovq -128(%rsp), %rax"]

#kat LprogAsmPrinter.renderLopn pinP.frame pinP.spillW false [.reg "RCX"] "ADCX:64"
    [.reg "RAX", .reg "R11", .reg "k.1"] pinP.qsaveB
  == ["\tmovq %rbx, -128(%rsp)", "\tmovq 48(%rsp), %rbx", "\tbtq $0, %rbx",
      "\tmovq -128(%rsp), %rbx", "\tmovq %rax, %rcx", "\tadcxq %r11, %rcx"]

-- a slot carry-in at the 32-bit width has no encoding
#kat enc (.Lopn [.reg "RBX"] "ADCX" [.reg "R10", .reg "R11", .reg "k.1"]) == []

-- `ADOX` with a value carry-in has no encoding: `bt` leaves `OF` undefined
#kat enc (.Lopn [.reg "RAX"] "ADOX:64" [.reg "RAX", .reg "RBX", .reg "RCX"]) == []

-- the printer refuses the same instruction
#kat (LprogAsmPrinter.renderLopn 0 0 false [.reg "RAX"] "ADOX:64"
    [.reg "RAX", .reg "RBX", .reg "RCX"]).all (fun l => "\t# UNHANDLED".isPrefixOf l)

-- a carry-out into a frame slot is `movq $0` and `setc` into the slot, as the printer prints it
#kat enc (.Lopn [.reg "k.0"] "ADCXHI:64" [.reg "R10", .reg "R11", .reg "RCX"])
  == encCarryOutRspMem 0x92 56

-- a carry-out into a register is `setc` and `movzbq`
#kat enc (.Lopn [.reg "RBX"] "ADCXHI:64" [.reg "R10", .reg "R11", .reg "RCX"])
  == encSetccMovzx 0x92 3

-- `ADCX` at 32-bit width with a slot source has no encoding
#kat enc (.Lopn [.reg "k.0"] "ADCX" [.reg "k.1", .reg "R10", .reg "R11"]) == []

/-- `CMOV:64 RBX := R10 ? k.1 : RAX`: the select with its true value in a slot. -/
def cmovSlotT : LinstrR := .Lopn [.reg "RBX"] "CMOV:64" [.reg "R10", .reg "k.1", .reg "RAX"]

-- the printer: `mov %rax, %rbx`, `test %r10, %r10`, `cmovne 48(%rsp), %rbx`
#kat LprogAsmPrinter.renderLopn pinP.frame pinP.spillW false [.reg "RBX"] "CMOV:64"
    [.reg "R10", .reg "k.1", .reg "RAX"] pinP.qsaveB
  == ["\tmovq %rax, %rbx", "\ttestq %r10, %r10", "\tcmovneq 48(%rsp), %rbx"]

-- the bytes of those three lines, against their component encoders
#kat enc cmovSlotT
  == encAluRRw 1 0x89 3 0 ++ encAluRRw 1 0x85 10 10 ++ encCmovRspMem 1 0x45 3 48

-- the same bytes as the assembler writes them: `48 89 c3`, `4d 85 d2`, `48 0f 45 5c 24 30`
#kat enc cmovSlotT
  == ([0x48, 0x89, 0xc3, 0x4d, 0x85, 0xd2, 0x48, 0x0f, 0x45, 0x5c, 0x24, 0x30] : List Nat).map
      (BitVec.ofNat 8)

/-- `CMOV:64 RBX := R10 ? RAX : k.1`: the select with its false value in a slot. -/
def cmovSlotF : LinstrR := .Lopn [.reg "RBX"] "CMOV:64" [.reg "R10", .reg "RAX", .reg "k.1"]

/-- `CMOV:64 RBX := R10 ? k.0 : k.1`: the select with both values in slots. -/
def cmovSlotTF : LinstrR := .Lopn [.reg "RBX"] "CMOV:64" [.reg "R10", .reg "k.0", .reg "k.1"]

-- the printer: `mov 48(%rsp), %rbx`, `test %r10, %r10`, `cmovne %rax, %rbx`
#kat LprogAsmPrinter.renderLopn pinP.frame pinP.spillW false [.reg "RBX"] "CMOV:64"
    [.reg "R10", .reg "RAX", .reg "k.1"] pinP.qsaveB
  == ["\tmovq 48(%rsp), %rbx", "\ttestq %r10, %r10", "\tcmovneq %rax, %rbx"]

-- the bytes of those three lines, against their component encoders
#kat enc cmovSlotF
  == encRspMem 1 0x8b 3 48 ++ encAluRRw 1 0x85 10 10 ++ enc0FRRw 1 0x45 3 0

-- the same bytes as the assembler writes them: `48 8b 5c 24 30`, `4d 85 d2`, `48 0f 45 d8`
#kat enc cmovSlotF
  == ([0x48, 0x8b, 0x5c, 0x24, 0x30, 0x4d, 0x85, 0xd2, 0x48, 0x0f, 0x45, 0xd8] : List Nat).map
      (BitVec.ofNat 8)

#kat shapeJs cmovSlotF == reprStr ([.loadMem "%rbx" "%rsp" 48, .test "%r10" (.reg "%r10"),
    .cmovne "%rbx" (.reg "%rax")] : List (JInstr 64))

-- the printer: `mov 48(%rsp), %rbx`, `test %r10, %r10`, `cmovne 56(%rsp), %rbx`
#kat LprogAsmPrinter.renderLopn pinP.frame pinP.spillW false [.reg "RBX"] "CMOV:64"
    [.reg "R10", .reg "k.0", .reg "k.1"] pinP.qsaveB
  == ["\tmovq 48(%rsp), %rbx", "\ttestq %r10, %r10", "\tcmovneq 56(%rsp), %rbx"]

#kat enc cmovSlotTF
  == encRspMem 1 0x8b 3 48 ++ encAluRRw 1 0x85 10 10 ++ encCmovRspMem 1 0x45 3 56

#kat shapeJs cmovSlotTF == reprStr ([.loadMem "%rbx" "%rsp" 48, .test "%r10" (.reg "%r10"),
    .cmovccMem .ne "%rbx" "%rsp" 56] : List (JInstr 64))

-- a slot false value with the destination equal to the true value is printed as `test` and
-- `cmove` from the slot, and encoded as the same two instructions
#kat enc (.Lopn [.reg "RAX"] "CMOV:64" [.reg "R10", .reg "RAX", .reg "k.1"])
  == encAluRRw 1 0x85 10 10 ++ encCmovRspMem 1 0x44 0 48

end CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeSlotOperandKats
