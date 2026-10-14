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
records, and the export data in a third.

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
  edge `loopGuard`, the guard `zeroTripGuard` that skips a loop whose runtime count is
  zero, the instruction `invTouch` that reads a loop-invariant register at the foot of a
  loop, and the operand forms: the operand positions that may be memory `memOperand`, the
  accepted immediates `immFits`, the operands bound to one register `fixedOperand`, the
  scales of an indexed address `indexScales` and the fused high multiply `mulHiFuse`.
* `keepTouch`, the keep marker: an `Lopn` with the reserved mnemonic `KEEP` and the operand
  footprint of a compare, which an instruction set steps as a no-op; `isKeep` recognises
  it.
* `IsaExportData`, the data the physical export, the printer and the encoder read beside the
  two records: the instruction pointer, the vector register file with its calling convention
  and copy mnemonic, and the sizes of the frame layout (the word, the stack alignment, the
  bytes a call pushes, the save cells of a leaf and of a calling body, the vector spill cell),
  and the reach of a relative call.

The module also defines the quantities the export derives from an `IsaAbi`: the two reload
scratches, the scalar return register, the save slot name of a register, the callee-saved
first order of the allocation pool, the allocatable caller-saved registers, the two pools of
the straight-line call barrier, and the entry save and exit restore sequences.

`LprogIsa.Isa` extends `IsaData` by the step semantics. The x86 values are
`X86Backend.LprogAsmPrinter.x86Abi`, `X86Backend.TwoAddrLegalize.x86Data` and
`LprogIsa.x86ExportData`, defined in `VIR.X86IsaData`; `X86Backend.X86Isa.x86Isa` carries the
first two.

## Main definitions

* `IsaAbi`: register file and calling convention.
* `IsaData`: `IsaAbi` with the legaliser's mnemonic data.
* `keepTouch`, `isKeep`: the keep marker and its recogniser.
* `IsaExportData`: the export data.
* `IsaAbi.reload`, `IsaAbi.reloadSnd`, `IsaAbi.retReg`, `IsaAbi.saveName`: derived registers and
  the save slot name.
* `IsaAbi.calleeFirstOrder`, `IsaAbi.callerSavedPool`, `IsaAbi.calleeSavedPoolIdx`,
  `IsaAbi.callScratchPoolIdx`: derived orders and pools of the allocation pool.
* `IsaAbi.entrySaves`, `IsaAbi.calleeRestores`: the entry save and exit restore sequences.
* `IsaAbi.WF`, `IsaData.WF`, `IsaData.TieWF`: the well-formedness of the register file, of
  the implicit reads and of the tied form.
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

/-- **The keep marker** on the registers `ctr` and `r`: the instruction
    `Lopn [ctr] "KEEP" [ctr, r]`. It has the operand footprint of the compare `CMP ctr, r`
    (destination `ctr`, reads `ctr` and `r`), so the liveness analysis of the allocator
    records the same write and the same reads for both. An instruction set steps it as a
    no-op that advances the program counter, and it is printed and encoded to nothing. -/
def keepTouch (ctr r : String) : LinstrR := .Lopn [.reg ctr] "KEEP" [.reg ctr, .reg r]

/-- Whether an instruction is a keep marker: an `Lopn` with the mnemonic `KEEP`, on any
    operands. -/
def isKeep : LinstrR → Bool
  | .Lopn _ opn _ => opn == "KEEP"
  | _ => false

@[simp] theorem isKeep_keepTouch (ctr r : String) : isKeep (keepTouch ctr r) = true := rfl

/-- An `Lopn` is a keep marker exactly when its mnemonic is `KEEP`. -/
theorem isKeep_Lopn (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    isKeep (.Lopn dsts opn srcs) = (opn == "KEEP") := rfl

/-- **The data of an instruction set**: `IsaAbi` with the mnemonic data of the two-address
    legaliser, the accepted mnemonic bases, the implicit register reads, the loop guard,
    the zero-trip guard and the invariant touch. -/
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
  /-- Whether the instruction with this mnemonic base sets flags and writes no destination
      register. -/
  flagOnly : String → Bool
  /-- The mnemonic base of the select `Lopn [r] m [f, r, z]` that widens the one-bit flag
      register `f` to a word in `r`, `none` when the instruction set has no such select. -/
  selectMnemonic : Option String
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
  /-- The invariant touch on counter register `ctr` and loop-invariant register `r`: one
      instruction at the foot of a loop that reads `r`, so the allocator keeps `r` in its
      register across the back edge. It names `ctr` as destination and first source and does
      not change a register. An instruction set with a compare uses `CMP ctr, r`; one
      without uses the keep marker `keepTouch ctr r`. -/
  invTouch : String → String → LinstrR
  /-- Whether the operand at position `k` of an instruction with this mnemonic base may be a
      frame slot or a `mem.*` cell. The positions number the operands of
      `Lopn dsts opn srcs` in the order `dsts ++ srcs`, from `0`. The default `false` at
      every position is a load-store instruction set. -/
  memOperand : String → Nat → Bool := fun _ _ => false
  /-- Whether the immediate `v`, read as a signed integer, is accepted at operand position
      `k` of an instruction with this mnemonic base, the positions as in `memOperand`. The
      default accepts no immediate. -/
  immFits : String → Nat → Int → Bool := fun _ _ _ => false
  /-- The register that a register operand at position `k` of an instruction with this
      mnemonic base must be, the positions as in `memOperand`; `none` at a position without
      such a register. -/
  fixedOperand : String → Nat → Option String := fun _ _ => none
  /-- The scales a register-indexed address `arrIdx b i scale` may carry. -/
  indexScales : List Nat := []
  /-- The mnemonic base of the fused high multiply, `none` when the instruction set has
      none. -/
  mulHiFuse : Option String := none

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
  /-- The reach in bytes of a relative call: a call reaches a target whose displacement
      from the call has absolute value below `callRange`. -/
  callRange : Nat

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

/-- **The well-formedness of a register file and calling convention**: the allocation pool,
    the scratch registers and the stack pointer are pairwise distinct; the argument registers
    are in the allocation pool; distinct callee-saved registers have distinct save slots; the
    return registers are caller-saved. -/
structure WF : Prop where
  /-- The allocation pool, the scratch registers and the stack pointer are pairwise
      distinct. -/
  nodup : (abi.allocPool ++ abi.scratch ++ [abi.sp]).Nodup
  /-- The argument registers are in the allocation pool. -/
  args_sub : ∀ r ∈ abi.argRegs, r ∈ abi.allocPool
  /-- The save slot is injective on the callee-saved registers. -/
  saveSlot_inj : ∀ r ∈ abi.calleeSaved, ∀ r' ∈ abi.calleeSaved,
    abi.saveSlot r = abi.saveSlot r' → r = r'
  /-- The return registers are caller-saved. -/
  ret_sub : ∀ r ∈ abi.retRegs, r ∈ abi.callerSaved

end IsaAbi

namespace IsaData

variable (I : IsaData)

/-- **The well-formedness of an instruction set's register data**: its register file is
    well-formed (`IsaAbi.WF`), and the registers an instruction reads without naming them
    are allocatable or scratch registers. -/
structure WF : Prop extends I.toIsaAbi.WF where
  /-- The implicit reads of every mnemonic are in the allocation pool or the scratch
      registers. -/
  implicit_sub : ∀ (opn r : String), r ∈ I.implicitReads opn → r ∈ I.allocPool ++ I.scratch

/-- **The well-formedness of the tied form**: the scratch register of the legaliser is not
    allocatable, and every mnemonic printed in tied form has a copy mnemonic. Both hold
    when `tied` is constantly `false` and `tieScratch` is a scratch register. -/
structure TieWF : Prop where
  /-- The scratch register of the legaliser is not in the allocation pool. -/
  tieScratch_not_mem : I.tieScratch ∉ I.allocPool
  /-- A mnemonic printed in tied form has a copy mnemonic. -/
  copy_of_tied : ∀ (opn : String) (b : LOperand), I.tied opn b = true →
    (I.copyMnemonic opn).isSome

end IsaData

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
