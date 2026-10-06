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
# Export data of an instruction set: vector register file, frame layout, save templates

The data the physical export, the printer and the encoder of the `Lprog` back end read
beside `LprogIsa.IsaAbi` and `LprogIsa.IsaData`, as a record `IsaExportData`, with its x86
value `x86ExportData`. The record holds the instruction pointer, the vector register file
with its calling convention and copy mnemonic, and the sizes of the frame layout: the word,
the stack alignment, the bytes a call pushes, the save cells of a leaf and of a calling body,
and the vector spill cell.

The module also defines the quantities the export derives from an `IsaAbi`: the two reload
scratches, the scalar return register, the save slot name of a register, the callee-saved
first order of the allocation pool, the allocatable caller-saved registers, the two pools of
the straight-line call barrier, and the entry save and exit restore sequences.

Each x86 value is stated equal to the constant the export, the printer or the encoder uses.

## Main definitions

* `IsaExportData`, `x86ExportData`: the record and its x86 value.
* `IsaAbi.reload`, `IsaAbi.reloadSnd`, `IsaAbi.retReg`, `IsaAbi.saveName`: derived registers and
  the save slot name.
* `IsaAbi.calleeFirstOrder`, `IsaAbi.callerSavedPool`, `IsaAbi.calleeSavedPoolIdx`,
  `IsaAbi.callScratchPoolIdx`: derived orders and pools of the allocation pool.
* `IsaAbi.entrySaves`, `IsaAbi.calleeRestores`: the entry save and exit restore sequences.

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

/-- **The export data of an instruction set** beside `IsaAbi` and `IsaData`: the instruction
    pointer, the vector register file with its calling convention and copy mnemonic, and the
    sizes of the frame layout. -/
structure IsaExportData : Type where
  /-- The instruction pointer, the `lp_rip` of an exported program. -/
  ip : String
  /-- The vector registers the allocator assigns, in slot order. -/
  vecPool : List String
  /-- The vector argument registers, in argument order. -/
  vecArgRegs : List String
  /-- The vector return registers, in order; the head holds a vector result. -/
  vecRetRegs : List String
  /-- The copy mnemonic between a vector register and a vector register or memory cell. -/
  vecCopy : String
  /-- The size in bytes of a register word, of a save cell and of a 64-bit spill cell. -/
  wordBytes : Nat
  /-- The alignment in bytes of the stack pointer at a call instruction. -/
  stackAlign : Nat
  /-- The bytes a call instruction pushes on the stack: the return address, `0` for an
      instruction set with a link register. -/
  callPushBytes : Nat
  /-- The number of save cells at the top of the frame of a body without a call. -/
  saveCells : Nat
  /-- The number of save cells at the top of the frame of a body with a call. -/
  saveCellsCall : Nat
  /-- The size in bytes of a vector spill cell. -/
  vecCellBytes : Nat

namespace IsaAbi

variable (abi : IsaAbi)

/-- The primary reload scratch: the head of `scratch`. -/
def reload : String := abi.scratch.headD ""

/-- The secondary reload scratch: the second entry of `scratch`. -/
def reloadSnd : String := abi.scratch.getD 1 ""

/-- The scalar return register: the head of `retRegs`. -/
def retReg : String := abi.retRegs.headD ""

/-- The name of the frame save slot of a register. -/
def saveName (r : String) : String := "qsave." ++ r

/-- The indices of the allocation pool, those of the callee-saved registers first, each
    group in pool order. -/
def calleeFirstOrder : List Nat :=
  (List.range abi.allocPool.length).filter
      (fun i => abi.calleeSaved.contains (abi.allocPool.getD i ""))
    ++ (List.range abi.allocPool.length).filter
        (fun i => !abi.calleeSaved.contains (abi.allocPool.getD i ""))

/-- The caller-saved registers of the allocation pool, in pool order. -/
def callerSavedPool : List String := abi.allocPool.filter abi.callerSaved.contains

/-- The pool indices of the callee-saved registers of the allocation pool. -/
def calleeSavedPoolIdx : List Nat :=
  (List.range abi.allocPool.length).filter
    (fun i => abi.calleeSaved.contains (abi.allocPool.getD i ""))

/-- The pool indices of the caller-saved registers that are neither an argument register nor
    a return register: no call marshalling and no result capture writes them. -/
def callScratchPoolIdx : List Nat :=
  (List.range abi.allocPool.length).filter (fun i =>
    let r := abi.allocPool.getD i ""
    abi.callerSaved.contains r && !abi.argRegs.contains r && !abi.retRegs.contains r)

/-- The entry save sequence for the pointer argument registers `args`: each of `args` and
    each callee-saved register copied to its save slot, then the second of `args` copied to
    the secondary reload scratch. -/
def entrySaves (args : List String) : Lcmd :=
  (args ++ abi.calleeSaved).map (fun r => ⟨0, .Lopn [.reg (saveName r)] "MOVQ" [.reg r]⟩)
    ++ [⟨0, .Lopn [.reg abi.reloadSnd] "MOVQ" [.reg (args.getD 1 "")]⟩]

/-- The exit restore sequence: each callee-saved register copied back from its save slot. -/
def calleeRestores : Lcmd :=
  abi.calleeSaved.map (fun r => ⟨0, .Lopn [.reg r] "MOVQ" [.reg (saveName r)]⟩)

end IsaAbi

/-- **The x86 export data**: the instruction pointer `RIP`, the vector registers
    `XMM0`–`XMM15` with the System V vector arguments `XMM0`–`XMM7` and result `XMM0`, the
    copy `VMOVDQU`, 8-byte words, 16-byte stack alignment at a call, the 8-byte return
    address a call pushes, eight save cells for a leaf and twelve for a calling body, and
    32-byte vector spill cells. -/
@[reducible] def x86ExportData : IsaExportData where
  ip := "RIP"
  vecPool := ["XMM0", "XMM1", "XMM2", "XMM3", "XMM4", "XMM5", "XMM6", "XMM7",
    "XMM8", "XMM9", "XMM10", "XMM11", "XMM12", "XMM13", "XMM14", "XMM15"]
  vecArgRegs := sysvSseArgRegs
  vecRetRegs := [sysvSseRetReg]
  vecCopy := "VMOVDQU"
  wordBytes := 8
  stackAlign := 16
  callPushBytes := 8
  saveCells := 8
  saveCellsCall := 12
  vecCellBytes := 32

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
