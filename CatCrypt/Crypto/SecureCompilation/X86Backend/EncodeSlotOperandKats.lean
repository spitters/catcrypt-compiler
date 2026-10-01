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
`%rsp`-relative memory form `LprogAsmPrinter.renderLopn` prints. This module pins three
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
  store into the destination slot and the restore.

The `ADCX` pins also check that `DecodeGen.shapeOf` splits the bytes into pieces that
decode to the printed instructions.

## Main results

* `#kat` pins of the slot-operand encodings of `ADC`/`ADD`/`MOV`, `MULX` and `ADCX`, of the
  refused slot `MULX` destination, the refused three-source `ADOX`, and of the `shapeOf`
  decode of both spilled `ADCX` forms.
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

-- `ADOX` with a value carry-in has no encoding: `bt` leaves `OF` undefined
#kat enc (.Lopn [.reg "RAX"] "ADOX:64" [.reg "RAX", .reg "RBX", .reg "RCX"]) == []

-- the printer refuses the same instruction
#kat (LprogAsmPrinter.renderLopn 0 0 false [.reg "RAX"] "ADOX:64"
    [.reg "RAX", .reg "RBX", .reg "RCX"]).all (fun l => "\t# UNHANDLED".isPrefixOf l)

-- `ADCX` at 32-bit width with a slot source has no encoding
#kat enc (.Lopn [.reg "k.0"] "ADCX" [.reg "k.1", .reg "R10", .reg "R11"]) == []

end CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeSlotOperandKats
