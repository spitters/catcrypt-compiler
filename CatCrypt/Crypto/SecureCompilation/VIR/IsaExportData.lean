/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.X86IsaData
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhysAbi
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

@[expose] public section

set_option autoImplicit false

/-!
# The x86 export data and the constants of the export, the printer and the encoder

The record `LprogIsa.IsaExportData` and the quantities derived from an `LprogIsa.IsaAbi` are
defined in `VIR.LprogIsaData`, and the x86 value `x86ExportData` in `VIR.X86IsaData`. Each
x86 value is stated equal to the constant the physical export, the printer or the encoder of
the `Lprog` back end uses.

## Main results

* `x86ExportData_vecPool`, `x86ExportData_vecArgRegs`, `x86ExportData_vecRetRegs`,
  `x86ExportData_vecCopy`, `x86ExportData_ip`: the register file fields at x86.
* `x86ExportData_saveBytes`, `x86ExportData_saveBytesCall`, `x86ExportData_spillCell`,
  `x86ExportData_vecSpillBytes`, `x86ExportData_frameSize`: the frame fields at x86.
* `x86Abi_reload`, `x86Abi_reloadSnd`, `x86Abi_retReg`, `x86Abi_hwRegNames`,
  `x86Abi_calleeFirstOrder`, `x86Abi_callerSavedPool`, `x86Abi_calleeSavedPoolIdx`,
  `x86Abi_callScratchPoolIdx`, `x86Abi_redZone`: the derived quantities at x86.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend

/-! ## The register file fields at x86 -/

/-- The x86 vector pool is the vector register list of the allocator. -/
theorem x86ExportData_vecPool : x86ExportData.vecPool = vectorRegNames := rfl

/-- The x86 vector argument registers are the System V ones of the call marshalling. -/
theorem x86ExportData_vecArgRegs : x86ExportData.vecArgRegs = sysvSseArgRegs := rfl

/-- The x86 vector return registers are the System V one of the call marshalling. -/
theorem x86ExportData_vecRetRegs : x86ExportData.vecRetRegs = [sysvSseRetReg] := rfl

/-- The x86 vector copy is the mnemonic of the classed call marshalling. -/
theorem x86ExportData_vecCopy : x86ExportData.vecCopy = vecMovMnem := rfl

/-- The x86 instruction pointer and stack pointer are the `lp_rip` and `lp_rsp` of an
    exported loop program. -/
theorem x86ExportData_ip {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (fname outArg : String) (inArgs : List String) :
    (ComL.toLprogPhysAbi c fname outArg inArgs).lp_rip = x86ExportData.ip
      ∧ (ComL.toLprogPhysAbi c fname outArg inArgs).lp_rsp = x86Abi.sp :=
  ⟨rfl, rfl⟩

/-! ## The frame fields at x86 -/

/-- The save block of a body without a call. -/
theorem x86ExportData_saveBytes :
    x86ExportData.wordBytes * x86ExportData.saveCells = qsaveBytes := rfl

/-- The save block of a body with a call. -/
theorem x86ExportData_saveBytesCall :
    x86ExportData.wordBytes * x86ExportData.saveCellsCall = qsaveBytesCall := rfl

/-- The 64-bit spill cell is a word. -/
theorem x86ExportData_spillCell : spillCellBytes 64 = x86ExportData.wordBytes := rfl

/-- The vector spill region in vector spill cells. -/
theorem x86ExportData_vecSpillBytes (body : Lcmd) :
    vecSpillBytes body =
      match maxVecSpillIdx body with
      | some m => x86ExportData.vecCellBytes * (m + 2)
      | none => 0 := rfl

/-- **The frame size in the fields of the record**: the layout rounded up to the stack
    alignment, plus one word when the pushed return address, the pushed callee-saved
    registers and the layout leave the stack pointer of a calling body unaligned. -/
theorem x86ExportData_frameSize (body : Lcmd) :
    frameSize body =
      (let E := x86ExportData
       let frameAdd := frameAddDirective body
       let f16 :=
         match frameDirective body with
         | some f =>
             (f + frameAdd + (qsaveBytesFor body - E.wordBytes * E.saveCells) + (E.stackAlign - 1))
               / E.stackAlign * E.stackAlign
         | none =>
           let cell := if bodyIsU64 body then E.wordBytes else 4
           let spillBytes := match maxSpillIdx body with
                             | some m => cell * (m + 1)
                             | none => 0
           let raw := qsaveBytesFor body + spillBytes + vecSpillBytes body + frameAdd
           (raw + (E.stackAlign - 1)) / E.stackAlign * E.stackAlign
       if bodyHasCall body
           && (E.callPushBytes + E.wordBytes * (calleeSavedToSave body).length + f16)
             % E.stackAlign != 0 then f16 + E.wordBytes
       else f16) := rfl

/-- The red-zone cell of the encoder's select and wide-multiply forms is the lowest word
    of the red zone. -/
theorem x86Abi_redZone : LprogBytes.cmovRedZone = -(Int.ofNat x86Abi.redZone) := rfl

/-! ## The derived quantities at x86 -/

/-- The x86 primary reload scratch. -/
theorem x86Abi_reload : x86Abi.reload = reloadScratch := rfl

/-- The x86 secondary reload scratch. -/
theorem x86Abi_reloadSnd : x86Abi.reloadSnd = reloadScratch2 := rfl

/-- The x86 scalar return register. -/
theorem x86Abi_retReg : x86Abi.retReg = sysvRetReg := rfl

/-- The hardware register names the allocator pins are the allocation pool, the scratch
    registers, the stack pointer and the vector argument registers. -/
theorem x86Abi_hwRegNames :
    hwRegNames = x86Abi.allocPool ++ x86Abi.scratch.reverse ++ [x86Abi.sp]
      ++ x86ExportData.vecArgRegs := rfl

/-- The callee-saved first order of the x86 pool. -/
theorem x86Abi_calleeFirstOrder : x86Abi.calleeFirstOrder = calleeSavedFirstOrder := by decide

/-- The allocatable caller-saved registers of x86. -/
theorem x86Abi_callerSavedPool : x86Abi.callerSavedPool = callerSavedAllocGPRs := by decide

/-- The callee-saved pool of the straight-line call barrier at x86. -/
theorem x86Abi_calleeSavedPoolIdx :
    x86Abi.calleeSavedPoolIdx = straightCallCalleeSavedPool := by decide

/-- The scratch pool of the straight-line call barrier at x86. -/
theorem x86Abi_callScratchPoolIdx :
    x86Abi.callScratchPoolIdx = straightCallScratchPool := by decide

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
