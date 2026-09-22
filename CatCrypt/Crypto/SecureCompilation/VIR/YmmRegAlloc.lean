/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
public import CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-!
# The 256-bit YMM instruction set as a `MachineModel`

`Optimizer.GenericRegAlloc` states a spilling register allocator once, over any
instruction type `I` carrying a `MachineModel I`: its written and read register
names, an allocatable physical file, and a spill store and reload load. It has
instances for the A64 `AInst` and the RV64 `RInst` general-purpose files. This
module gives it one for the x86 vector file, at `YmmAsmPrint.YmmInstr`.

`YmmInstr` is the carrier because it has memory moves: `yload` and `ystore` over
a `YmmMem` (base register plus displacement) are what a spill and a reload are.
The register-only `Sha2MultiBufAvx2Emit.YInst` has neither, and its `YState` has
no memory, so a spiller would have nowhere to spill to.

A vector value is 32 bytes, so frame cells are allocated at `ymmStride = 32`,
passed as the `stride` of `GenericRegAlloc.spillAlloc`; the allocator itself is
unchanged.

## Main definitions

* `ymmFile`: the sixteen AVX2 vector registers `%ymm0 .. %ymm15`.
* `ymmFrameBase`, `ymmStride`: the base register and cell width of vector spills.
* `instMachineModelYmmInstr`: `MachineModel YmmInstr`.
* `ymmSpillAlloc`: `GenericRegAlloc.spillAlloc` at the vector file and stride.

## The frame base is not a name to allocate

`readNames` reports the vector registers an instruction reads and leaves out the
general-purpose base of a memory operand. The allocator collects every written
and read name as a value to place, and the base (`%rsp`) is a pinned
general-purpose register outside `ymmFile`; counting it would make the allocator
try to assign a vector register to the stack pointer.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAlloc

open CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
open CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-- The sixteen AVX2 vector registers, in the `%ymmN` spelling `YmmInstr` and
    its printer use. -/
def ymmFile : List String :=
  (List.range 16).map (fun i => "%ymm" ++ toString i)

/-- The base register of a vector spill slot. `renderYmmMem` prints the base
    verbatim, so it carries the `%`. -/
def ymmFrameBase : String := "%rsp"

/-- The width in bytes of one vector frame cell: a 256-bit value. -/
def ymmStride : Int := 32

/-- The vector registers an instruction writes. A store writes memory and no
    register. -/
def ymmWrittenNames : YmmInstr → List String
  | .alu _ dst _  => [dst]
  | .ymov dst _   => [dst]
  | .yload dst _  => [dst]
  | .ystore _ _   => []
  | .ternlog _ d _ _ => [d]

/-- The vector registers an instruction reads. The general-purpose base of a
    memory operand is excluded; see the module docstring. -/
def ymmReadNames : YmmInstr → List String
  | .alu _ _ srcs => srcs
  | .ymov _ src   => [src]
  | .yload _ _    => []
  | .ystore _ src => [src]
  | .ternlog _ d b c => [d, b, c]

/-- **`MachineModel YmmInstr`**: the x86 vector file for the generic allocator.
    A spill is a `ystore` of the register to its frame cell and a reload is a
    `yload` from it, both relative to `ymmFrameBase`. -/
instance instMachineModelYmmInstr : MachineModel YmmInstr where
  writtenNames := ymmWrittenNames
  readNames := ymmReadNames
  physRegs := ymmFile
  mkSpill r off := .ystore ⟨ymmFrameBase, off⟩ r
  mkReload r off := .yload r ⟨ymmFrameBase, off⟩

/-- The spill decisions for a vector block: `GenericRegAlloc.spillAlloc` over
    `ymmFile` with 32-byte cells. `pinned` are names fixed to a register by the
    caller's ABI and `scratch` are registers withheld from allocation. -/
def ymmSpillAlloc (pinned scratch : List String) (frameBase : Int)
    (block : List YmmInstr) : List (String × Slot) :=
  spillAlloc (I := YmmInstr) pinned scratch frameBase block ymmStride

/-! ## Materializing the decisions

`GenericRegAlloc.rewriteBlock` surrounds each instruction with its spill traffic
and leaves renaming to the printer, which for the x86 GP file knows the
decisions. `renderYmmInstr` prints register names verbatim, so a vector block
must be renamed before it is printed: a resident name becomes its `%ymmN`, and
a spilled name becomes a scratch register for the one instruction that touches
it, loaded before and stored after.

Scratch registers are assigned per instruction by the position of the name in
that instruction's list of distinct spilled names, so two spilled operands of one
instruction get distinct scratch registers while a name that is both read and
written — the two-address form `vpxor x, x, y` — keeps one. The scratch
registers are withheld from allocation by passing them as `scratch` to
`ymmSpillAlloc`, so no resident value is ever assigned one. -/

/-- Rename every vector register an instruction names. The base of a memory
    operand is a general-purpose register and is left alone. -/
def renameYmm (f : String → String) : YmmInstr → YmmInstr
  | .alu op d srcs => .alu op (f d) (srcs.map f)
  | .ymov d s      => .ymov (f d) (f s)
  | .yload d m     => .yload (f d) m
  | .ystore m s    => .ystore m (f s)
  | .ternlog k d b c => .ternlog k (f d) (f b) (f c)

/-- The distinct spilled names one instruction touches, in first-occurrence
    order; a name's index here is its scratch register. -/
def spilledNamesOf (decisions : List (String × Slot)) (i : YmmInstr) : List String :=
  ((ymmReadNames i) ++ (ymmWrittenNames i)).eraseDups.filter
    (fun n => (spillSlotOf decisions n).isSome)

/-- One instruction with its reloads before and its stores after, every name
    mapped onto a physical register. -/
def ymmMaterializeInstr (decisions : List (String × Slot)) (scratch : List String)
    (i : YmmInstr) : List YmmInstr :=
  let spilled := spilledNamesOf decisions i
  let scr : String → Option String := fun n =>
    (spilled.findIdx? (· == n)).bind (fun k => scratch[k]?)
  let phys : String → String := fun n =>
    match residentReg decisions n with
    | some r => r
    | none   => (scr n).getD n
  let reloads := (ymmReadNames i).eraseDups.filterMap (fun n =>
    (spillSlotOf decisions n).bind (fun off =>
      (scr n).map (fun s => YmmInstr.yload s ⟨ymmFrameBase, off⟩)))
  let stores := (ymmWrittenNames i).eraseDups.filterMap (fun n =>
    (spillSlotOf decisions n).bind (fun off =>
      (scr n).map (fun s => YmmInstr.ystore ⟨ymmFrameBase, off⟩ s)))
  reloads ++ renameYmm phys i :: stores

/-- The materialized block: every instruction renamed and surrounded by its
    spill traffic. -/
def ymmMaterialize (decisions : List (String × Slot)) (scratch : List String)
    (block : List YmmInstr) : List YmmInstr :=
  block.flatMap (ymmMaterializeInstr decisions scratch)

/-- The vector names an instruction mentions, read or written. -/
def ymmNamesOf (i : YmmInstr) : List String := ymmReadNames i ++ ymmWrittenNames i

/-- Every vector name in a block is one of the sixteen physical registers — the
    property a materialized block must have before it is printed. -/
def ymmAllPhysical (block : List YmmInstr) : Bool :=
  block.all (fun i => (ymmNamesOf i).all (fun n => ymmFile.contains n))

/-- The largest number of distinct spilled names any one instruction touches —
    the number of scratch registers `ymmMaterialize` needs. -/
def ymmScratchNeeded (decisions : List (String × Slot)) (block : List YmmInstr) : Nat :=
  block.foldl (fun m i => max m (spilledNamesOf decisions i).length) 0

/-! ## Static pins

Each guard fixes a property the instance must keep, and each finishes in a few
milliseconds: they are static checks on the definitions, not measurements. -/

/-- The allocatable file is the sixteen AVX2 registers. -/
theorem ymmFile_length : ymmFile.length = 16 := by decide

/-- A spill and its reload address the same cell and move the same register. -/
theorem ymm_spill_reload_same_cell (r : String) (off : Int) :
    (MachineModel.mkSpill (I := YmmInstr) r off, MachineModel.mkReload (I := YmmInstr) r off)
      = (.ystore ⟨ymmFrameBase, off⟩ r, .yload r ⟨ymmFrameBase, off⟩) := rfl

/-- A spill writes no register, so it cannot clobber a live vector value. -/
theorem ymm_spill_writes_nothing (r : String) (off : Int) :
    MachineModel.writtenNames (MachineModel.mkSpill (I := YmmInstr) r off) = [] := rfl

/-- The stack pointer is never a name the allocator places: no instruction
    reports it as read. -/
theorem ymm_base_not_read (m : YmmMem) (d : String) :
    MachineModel.readNames (I := YmmInstr) (.yload d m) = [] := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAlloc
