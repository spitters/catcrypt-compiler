/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime

@[expose] public section

set_option autoImplicit false

/-!
# The load-op forms of the printed body

A two-address `SUB:64`, `AND:64`, `OR:64` or `XOR:64` whose second source is a frame word
`q` (a spill slot `k.N` or an ABI save `qsave.X`), and an and-not `ANDN:64 D, A, q` whose
second source is a frame word, are encoded by `LprogBytes.encodeLopn` as one instruction
with a memory operand `off(%rsp)`: `REX.W 2B`/`23`/`0B`/`33 /r` (`ScalarEncoder.memAluOpcode`)
and `VEX.LZ.0F38.W1 F2 /r` (`ScalarEncoder.encVex3Mem`). This module states, for each form,
the bytes, the decoded machine instruction (`JInstr.aluMem`, `JInstr.andnMem`), its effect on
the address machine `Ascent.AddrMem.evalInstrA`, and its leakage: the memory access at the
base register `%rsp` and the compile-time displacement, the event a load of the frame word
leaks (`MachineConstantTime.instrLeak`).

## Main definitions

* `memAluOfMnem?`: the memory-source operation of a 64-bit two-address mnemonic.

## Main results

* `encodeLopn_aluSlot`, `pieceDec_aluSlot`: the bytes of `op:64 D, D, q` and their decoding
  to `aluMem op (phys D) "%rsp" off`.
* `encodeLopn_andnSlot`, `pieceDec_andnSlot`: the bytes of `ANDN:64 D, A, q` and their
  decoding to `andnMem (phys D) (phys A) "%rsp" off`.
* `evalInstrA_aluMem`, `evalInstrA_andnMem`: the registers after the machine step, which
  writes no memory.
* `instrLeak_aluMem`, `instrLeak_andnMem`: the leakage, the frame word's address only, as for
  the load `loadMem`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LoadOpForms

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen (PieceDec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- The memory-source operation of a 64-bit two-address mnemonic: `SUB:64`, `AND:64`,
    `OR:64`, `XOR:64`; `none` for every other mnemonic. -/
def memAluOfMnem? : String → Option MemAluOp
  | "SUB:64" => some .sub
  | "AND:64" => some .and_
  | "OR:64" => some .or_
  | "XOR:64" => some .xor_
  | _ => none

/-- `encRspMem` at `REX.W = 1` is the general memory form at base `%rsp` (number `4`). -/
theorem encRspMem_eq_encMemMovw4 (op r : Nat) (off : Int) :
    encRspMem 1 op r off = encMemMovw 1 op r 4 off := by
  rw [encRspMem_eq_memTail]
  simp [encMemMovw, rexOpt, bit]

/-- **The bytes of a load-op on a frame word.** `op:64 D, D, q` with `D` a general-purpose
    name and `q` a frame word at offset `off` is the one instruction
    `REX.W (memAluOpcode op) /r` against `off(%rsp)`. -/
theorem encodeLopn_aluSlot (F W : Nat) {m : String} {o : MemAluOp}
    (hm : memAluOfMnem? m = some o) (D q : String) (qB : Nat) (off : Int)
    (hD : gpOk D = true) (hoff : spillQsaveOff F W q qB = some off) :
    encodeLopn F W (.Lopn [.reg D] m [.reg D, .reg q]) qB
      = encRspMem 1 (memAluOpcode o) (gpNumU D) off := by
  have fD := gpFacts hD
  unfold memAluOfMnem? at hm
  split at hm <;> simp only [Option.some.injEq, reduceCtorEq] at hm <;> subst hm <;>
    simp (config := { decide := true }) [encodeLopn, fD.isGp, fD.off, hoff, tagShiftExt,
      aluOpcode, stripWidthTag, adxPrefix, LprogBytes.rexW, encTwoAddr, memSrcOp, memAluOpcode]

/-- The bytes of a load-op on a frame word decode, in front of every continuation, to the
    memory-source operation on the machine register of `D` at `off(%rsp)`. -/
theorem pieceDec_aluSlot (o : MemAluOp) (D : String) (off : Int) (h : dispOk32 off = true) :
    PieceDec (encRspMem 1 (memAluOpcode o) (gpNumU D) off, .aluMem o (phys D) "%rsp" off) :=
  fun rest => by
    rw [encRspMem_eq_encMemMovw4]
    exact decodeLinstr_aluMem o _ 4 off rest (gpNumU_lt_16 D) (by decide) h

/-- **The bytes of an and-not on a frame word.** `ANDN:64 D, A, q` with `D`, `A`
    general-purpose names and `q` a frame word at offset `off` is the one instruction
    `VEX.LZ.0F38.W1 F2 /r` against `off(%rsp)`. -/
theorem encodeLopn_andnSlot (F W : Nat) (D A q : String) (qB : Nat) (off : Int)
    (hD : gpOk D = true) (hA : gpOk A = true) (hg : isGpName q = false)
    (hoff : spillQsaveOff F W q qB = some off) :
    encodeLopn F W (.Lopn [.reg D] "ANDN:64" [.reg A, .reg q]) qB
      = encVex3Mem 0b00010 0b00 0xf2 (gpNumU D) (gpNumU A) 4 off := by
  have fD := gpFacts hD
  have fA := gpFacts hA
  simp only [encodeLopn,
    show (isCarryOutBinding "ANDN:64" || isMulHiBinding "ANDN:64") = false from by decide +kernel,
    show stripWidthTag "ANDN:64" = "ANDN" from by decide +kernel,
    show mnemWidth "ANDN:64" = 64 from by decide +kernel,
    show ("ANDN" == "MULX") = false from by decide +kernel,
    show ("ANDN" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "ANDN" = none from by decide +kernel,
    show tagShiftExt "ANDN" = none from by decide +kernel,
    show aluOpcode "ANDN" = none from by decide +kernel,
    show twoByteOpcode "ANDN" = none from by decide +kernel,
    show ("ANDN" == "STOREIDX") = false from by decide +kernel,
    show ("ANDN" == "CMP") = false from by decide +kernel,
    show ("ANDN" == "SHL" || "ANDN" == "SHR" || "ANDN" == "SAR") = false from by decide +kernel,
    show setccCmpOp "ANDN" = none from by decide +kernel,
    show ("ANDN" == "ANDN") = true from by decide +kernel,
    LprogBytes.rexW, fD.isGp, fA.isGp, hg, Bool.false_eq_true, ite_false, ite_true]
  simp [encAndnMemOp, hoff]

/-- The bytes of an and-not on a frame word decode, in front of every continuation, to the
    memory-source and-not on the machine registers of `D` and `A` at `off(%rsp)`. -/
theorem pieceDec_andnSlot (D A : String) (off : Int) (h : dispOk32 off = true) :
    PieceDec (encVex3Mem 0b00010 0b00 0xf2 (gpNumU D) (gpNumU A) 4 off,
      .andnMem (phys D) (phys A) "%rsp" off) :=
  fun rest => decodeLinstr_andnMem _ _ 4 off rest (gpNumU_lt_16 D) (gpNumU_lt_16 A) (by decide) h

/-- **The machine step of a load-op.** `aluMem op D b off` writes `D` with the word of the
    operation on `D` and the eight bytes at `regs b + off`, writes no memory, and keeps every
    other register. -/
theorem evalInstrA_aluMem (sa : AState) (o : MemAluOp) (D b : String) (off : Int) :
    (∀ r, (evalInstrA sa (.aluMem o D b off)).regs r = if r = D then
        (o.sem (sa.regs D) (read64 sa.mem (sa.regs b + BitVec.ofInt 64 off))).word
      else sa.regs r)
      ∧ (evalInstrA sa (.aluMem o D b off)).mem = sa.mem := by
  refine ⟨fun r => ?_, rfl⟩
  by_cases hr : r = D <;>
    simp [evalInstrA, evalInstr, JState.writeB5W, AState.view, JState.load, JState.get, hr]

/-- **The machine step of a memory-source and-not.** `andnMem D A b off` writes `D` with
    `~A & [regs b + off]`, writes no memory, and keeps every other register. -/
theorem evalInstrA_andnMem (sa : AState) (D A b : String) (off : Int) :
    (∀ r, (evalInstrA sa (.andnMem D A b off)).regs r = if r = D then
        (x86_ANDN (sa.regs A) (read64 sa.mem (sa.regs b + BitVec.ofInt 64 off))).word
      else sa.regs r)
      ∧ (evalInstrA sa (.andnMem D A b off)).mem = sa.mem := by
  refine ⟨fun r => ?_, rfl⟩
  by_cases hr : r = D <;>
    simp [evalInstrA, evalInstr, JState.writeB5W, AState.view, JState.load, JState.get, hr]

/-- **The leakage of a load-op**: the access at the base register and the compile-time
    displacement, the event of the load `loadMem` of the same cell. -/
theorem instrLeak_aluMem {w : Nat} (s : JState w) (o : MemAluOp) (D b : String) (off : Int) :
    instrLeak s (.aluMem o D b off) = instrLeak s (.loadMem D b off) := rfl

/-- **The leakage of a memory-source and-not**: the access at the base register and the
    compile-time displacement, the event of the load `loadMem` of the same cell. -/
theorem instrLeak_andnMem {w : Nat} (s : JState w) (D A b : String) (off : Int) :
    instrLeak s (.andnMem D A b off) = instrLeak s (.loadMem D b off) := rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoadOpForms
