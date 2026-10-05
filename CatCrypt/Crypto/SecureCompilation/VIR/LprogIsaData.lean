/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Types

@[expose] public section

set_option autoImplicit false

/-!
# The instruction-set record of the `Lprog` back end: data fields

The data an instruction set supplies to the back half of the `Lprog` pipeline, in two
records.

* `IsaAbi`, the register file and calling convention: the allocatable registers and the
  reserved scratch registers the exporter reads, the argument registers of the entry, the
  callee-saved registers with their save slots the printer reads, the stack pointer `sp`, the
  return registers `retRegs`, the caller-saved registers `callerSaved` and the red-zone size
  `redZone`.
* `IsaData`, which extends `IsaAbi` by the mnemonic data of the two-address legaliser: which
  instructions the printer emits in tied form, which operations commute, the scratch register
  of the legaliser, the copy mnemonic at the width of an operation, the leakage regime
  `leaksOperands` (which mnemonic bases make their data operands observable), the accepted
  mnemonic bases `supports`, the implicit register reads `implicitReads`, the loop back
  edge `loopGuard`, and the guard `zeroTripGuard` that skips a loop whose runtime count is
  zero.

`LprogIsa.Isa` extends `IsaData` by the step semantics. The x86 values are
`X86Backend.LprogAsmPrinter.x86Abi` and `X86Backend.TwoAddrLegalize.x86Data`, defined in
`VIR.X86IsaData`; `X86Backend.X86Isa.x86Isa` carries them.

## Main definitions

* `IsaAbi`: register file and calling convention.
* `IsaData`: `IsaAbi` with the legaliser's mnemonic data.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- **The register file and calling convention of an instruction set**: the registers the
    allocator assigns, the reserved scratch registers, the argument registers, the
    callee-saved registers and the index of the frame save slot of a register. -/
structure IsaAbi : Type where
  /-- The registers the allocator assigns, in slot order. -/
  allocPool : List String
  /-- The scratch registers reserved from allocation, primary first. -/
  scratch : List String
  /-- The integer argument registers, in argument order. -/
  argRegs : List String
  /-- The callee-saved registers. -/
  calleeSaved : List String
  /-- The index of the frame save slot of a register, `none` for a register without one. -/
  saveSlot : String → Option Nat
  /-- The stack pointer. -/
  sp : String
  /-- The integer return registers, in order; the head holds a scalar result. -/
  retRegs : List String
  /-- The caller-saved registers, which a call may clobber. -/
  callerSaved : List String
  /-- The size in bytes of the red zone below the stack pointer that a leaf function may use
      without adjusting it. -/
  redZone : Nat := 0

/-- **The data of an instruction set**: `IsaAbi` with the mnemonic data of the two-address
    legaliser, the accepted mnemonic bases, the implicit register reads, the loop guard and
    the zero-trip guard. -/
structure IsaData extends IsaAbi where
  /-- Whether `Lopn [d] opn [a, b]` is printed in tied form, which requires `a = d`. -/
  tied : String → LOperand → Bool
  /-- Whether the operation with this mnemonic base commutes in value and in the flags it
      sets. -/
  commutes : String → Bool
  /-- The scratch register through which the legaliser routes an untied operation. -/
  tieScratch : String
  /-- The copy mnemonic at the width of an operation, `none` when there is none. -/
  copyMnemonic : String → Option String
  /-- The leakage regime: whether an instruction with this mnemonic base makes its data
      operands observable through its execution time. The default `true` for every base is
      the regime without a vendor timing guarantee. -/
  leaksOperands : String → Bool := fun _ => true
  /-- Whether the instruction set accepts the mnemonic base. The default `true` for every
      base imposes no restriction. -/
  supports : String → Bool := fun _ => true
  /-- The registers an instruction with this mnemonic reads without naming them as
      operands. -/
  implicitReads : String → List String := fun _ => []
  /-- The instructions of the loop back edge on counter register `ctr` to label `top`: branch
      to `top` when `ctr` is non-zero, fall through otherwise. -/
  loopGuard : String → LLabel → List LinstrR
  /-- The instructions of the zero-trip guard on counter register `ctr`, placed immediately
      before the loop label `top`, with exit label `endL`: branch to `endL` when `ctr` is
      zero, reach `top` otherwise, by falling through or by a branch to it. -/
  zeroTripGuard : String → LLabel → LLabel → List LinstrR

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
