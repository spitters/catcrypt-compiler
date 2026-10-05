/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Export
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Export
public meta import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaData
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaData

@[expose] public section

set_option autoImplicit false

/-!
# The x86 values of the instruction-set data record

The x86-64 constants the loop exporter, the allocator, the printer and the two-address
legaliser share, and the two records built from them: the register file and calling
convention `x86Abi : IsaAbi` and the instruction-set data `x86Data : IsaData`. The module
imports the mnemonic helpers of `JasminLprogExport.Export` and the record types of
`LprogIsaData` only, so the loop exporter `JasminLprogExport.ExportLoops` reads its loop
guards from `x86Data`. Each constant keeps the namespace of the module that uses it.

## Main definitions

* `JasminLprogExport.sysvArgRegs`, `sysvRetReg`, `sysvCallerSaved`, `sysvSseArgRegs`,
  `sysvSseRetReg`: the System V AMD64 argument, return and caller-saved registers.
* `JasminLprogExport.gpRegNames`, `numGPRegs`, `reloadScratch`, `reloadScratch2`: the
  allocatable general-purpose registers and the two reserved reload scratches.
* `X86Backend.LprogAsmPrinter.qsaveSlot`, `calleeSavedRegs`, `x86Abi`: the save slots, the
  callee-saved registers and the x86 register file and calling convention.
* `X86Backend.TwoAddrLegalize.tieBase`, `tiedBases`, `needsTie`, `commBases`, `movFor`,
  `x86Data`: the mnemonic data of the two-address legaliser and the x86 instruction-set
  data, with the flag loop guard, the flag zero-trip guard and the compare invariant touch.
* `X86Backend.TwoAddrLegalize.x86Data_loopGuard`, `x86Data_zeroTripGuard`,
  `x86Data_invTouch`: the two guards as instruction lists and the invariant touch.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## The System V AMD64 calling convention -/

/-- The System V AMD64 integer/pointer argument registers, in order. The first
    `min n 6` call arguments are passed here; further args would spill to the
    stack (not needed by the leaf kernels MSM/GGM call, which are ≤ 6 args). -/
def sysvArgRegs : List String := ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]

/-- The System V AMD64 integer return register (where a leaf's scalar/pointer
    result is found after the call returns). -/
def sysvRetReg : String := "RAX"

/-- The SysV AMD64 caller-saved (volatile) registers: a real `call` may clobber
    any of these, so a value live across the call must be callee-saved or spilled.
    Exposed so the RA / a liveness pass can treat a `loopBodyCallLcmd` site as a
    clobber barrier for this register class. -/
def sysvCallerSaved : List String :=
  ["RAX", "RCX", "RDX", "RSI", "RDI", "R8", "R9", "R10", "R11"]

/-- The System V AMD64 SSE argument registers, in order. A 128/256-bit
    (`reg 128`) call argument is passed in the first free one of these, a
    *separate* sequence from the GP `sysvArgRegs` (a mixed arg list draws each
    argument from its own class). Further SSE args would spill to the stack (not
    needed by the leaves this path targets, which are ≤ 8 SSE args). -/
def sysvSseArgRegs : List String :=
  ["XMM0", "XMM1", "XMM2", "XMM3", "XMM4", "XMM5", "XMM6", "XMM7"]

/-- The System V AMD64 SSE return register (`xmm0`): a 128-bit leaf result is
    found here after the call returns. -/
def sysvSseRetReg : String := "XMM0"

/-! ## The 13 allocatable x86-64 GP registers and the 2 reserved reload scratches

`register_to_string` (jasmin `x86_decl.v`) lists the 16 GP registers
`RAX RCX RDX RBX RSP RBP RSI RDI R8 … R15`. `RSP` is the stack pointer and is
not a general allocation target, leaving 15 usable registers. **Two** of those
are **reserved as reload scratches**:

* `R15` (`reloadScratch`) — the primary scratch, always available;
* `R14` (`reloadScratch2`) — the secondary scratch, used when both operands of a
  binop are memory (spill) slots so the encoding must thread *two* values
  through scratches simultaneously.

Reserving the second scratch is what closes the link 4/7 asmgen failure
(`asmgen: can not map variable to a register`): jasmin's asmgen pass refuses to
admit a memory `lexpr` as the destination of a non-MOV `Lopn`. Routing through
R15/R14 keeps every spill name (`k.N`) inside a MOV-context source/dest, never
as a binop operand.

That leaves **13** allocatable registers. The physical index `0 … 12` names an
allocatable register; `13 …` spills to the stack array `k`. -/

/-- The 13 allocatable x86-64 GP register names (`RSP` excluded as the stack
    pointer, `R15`/`R14` reserved as reload scratches), indexed by physical slot
    `0 … 12`. -/
def gpRegNames : List String :=
  ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP",
   "R8", "R9", "R10", "R11", "R12", "R13"]

/-- Number of allocatable physical GP registers. -/
def numGPRegs : Nat := gpRegNames.length

/-- The primary reserved reload scratch register (`R15`): never an allocation
    target, so it is always free to legalize a two-memory-operand x86
    instruction. -/
def reloadScratch : String := "R15"

/-- The secondary reserved reload scratch register (`R14`): used together with
    `reloadScratch` when **both** operands of a binop are memory (spill) slots,
    so the binop is routed `mov R15, dst; mov R14, src; op R15, R14;
    mov dst, R15`. Reserving this second scratch lets the reload pass keep
    every `k.N` spill name inside a MOV-context, never as a binop operand. -/
def reloadScratch2 : String := "R14"

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## The x86 register file and calling convention -/

/-- The zero-based qsave slot index of a save register (`RDI`=0 … `R15`=7, plus
    the 2nd+ SysV input pointer regs `RDX`=8 … `R9`=11 for multi-input array
    loops), used to place its 8-byte cell in the frame's top block. -/
def qsaveSlot : String → Option Nat
  | "RDI" => some 0 | "RSI" => some 1
  | "RBX" => some 2 | "RBP" => some 3
  | "R12" => some 4 | "R13" => some 5
  | "R14" => some 6 | "R15" => some 7
  | "RDX" => some 8 | "RCX" => some 9
  | "R8"  => some 10 | "R9" => some 11
  | _ => none

/-- The SysV x86-64 ABI callee-saved GP registers (the caller relies on these
    surviving a call). `RSP` is the stack pointer (handled by the frame), not in
    this set. -/
def calleeSavedRegs : List String := ["RBX", "RBP", "R12", "R13", "R14", "R15"]

/-- **The x86 register file and calling convention**: the allocation pool `gpRegNames`, the
    reload scratches `R15`, `R14`, the SysV argument registers, the callee-saved registers and
    their save slots, the stack pointer `RSP`, the return registers `RAX`, `RDX`, the SysV
    caller-saved registers and the 128-byte red zone. The export reads the allocation pool and
    the argument registers from it, the printer the save slots and the callee-saved set. -/
@[reducible] def x86Abi : VIR.LprogIsa.IsaAbi where
  allocPool := gpRegNames
  scratch := [reloadScratch, reloadScratch2]
  argRegs := sysvArgRegs
  calleeSaved := calleeSavedRegs
  saveSlot := qsaveSlot
  sp := "RSP"
  retRegs := [sysvRetReg, "RDX"]
  callerSaved := sysvCallerSaved
  redZone := 128

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## The x86 instruction-set data -/

/-- The base of a mnemonic: the characters before its first `:`. -/
def tieBase (opn : String) : String := String.ofList (opn.toList.takeWhile (· != ':'))

/-- The bases of the two-source mnemonics `LprogAsmPrinter.renderLopn` prints in the
    x86 two-address form `op b, d`. -/
def tiedBases : List String :=
  ["ADD", "SUB", "MUL", "AND", "OR", "XOR", "ADC", "SBB", "CMP", "TEST", "ADCX", "ADOX",
   "CMOVE", "CMOVNE", "CMOVB", "CMOVAE", "CMOVL", "CMOVGE"]

/-- Whether `Lopn [d] opn [a, b]` is printed in the two-address form `op b, d`: its
    base is in `tiedBases`, or it is a shift whose count `b` is an immediate. -/
def needsTie (opn : String) (b : LOperand) : Bool :=
  tiedBases.contains (tieBase opn) ||
    ((tieBase opn == "SHL" || tieBase opn == "SHR" || tieBase opn == "SAR") &&
      match b with | .imm _ => true | _ => false)

/-- The bases whose two-source operation is commutative in value and in the flags
    it sets. -/
def commBases : List String := ["ADD", "MUL", "AND", "OR", "XOR"]

/-- The copy at the width of `opn`: `MOV` for an untagged mnemonic, `MOV:64` for a
    `:64`-tagged one, `none` for any other tag. -/
def movFor (opn : String) : Option String :=
  if opn == tieBase opn then some "MOV"
  else if opn == tieBase opn ++ ":64" then some "MOV:64"
  else none

/-- **The x86 instruction-set data**: the register file and calling convention
    `LprogAsmPrinter.x86Abi`, the tied mnemonics `needsTie`, the commutative bases
    `commBases`, the scratch register `reloadScratch`, the copies `movFor`, the implicit read
    of `RDX` by the `MULX` family, the flag loop guard `CMP ctr, 0; jne top`, the flag
    zero-trip guard `CMP ctr, 0; je endL` and the invariant touch `CMP ctr, r`. The legaliser
    reads its mnemonic data and scratch register from it, the loop exporter its two guards
    and its invariant touch. -/
@[reducible] def x86Data : VIR.LprogIsa.IsaData :=
  { LprogAsmPrinter.x86Abi with
    tied := needsTie
    commutes := fun base => commBases.contains base
    tieScratch := reloadScratch
    copyMnemonic := movFor
    implicitReads := fun opn =>
      if "MULX".toList.isPrefixOf ((stripWidthTag opn).toList.map Char.toUpper) then ["RDX"]
      else []
    loopGuard := fun ctr top =>
      [.Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0], .Lcond (.reg "NZ") top]
    zeroTripGuard := fun ctr _ endL =>
      [.Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0], .Lcond (.reg "Z") endL]
    invTouch := fun ctr r => .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r] }

/-- The x86 loop guard is the flag guard `CMP ctr, 0; jne top`. -/
theorem x86Data_loopGuard (ctr : String) (top : LLabel) :
    x86Data.loopGuard ctr top =
      [.Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0], .Lcond (.reg "NZ") top] :=
  rfl

/-- The x86 zero-trip guard is the flag guard `CMP ctr, 0; je endL`. -/
theorem x86Data_zeroTripGuard (ctr : String) (top endL : LLabel) :
    x86Data.zeroTripGuard ctr top endL =
      [.Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0], .Lcond (.reg "Z") endL] :=
  rfl

/-- The x86 invariant touch is the compare `CMP ctr, r`. -/
theorem x86Data_invTouch (ctr r : String) :
    x86Data.invTouch ctr r = .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r] :=
  rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize
