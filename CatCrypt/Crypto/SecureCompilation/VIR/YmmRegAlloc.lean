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
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect

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

/-! ## Allocation over an explicit register file

`ymmSpillAlloc` allocates over `MachineModel.physRegs`, the sixteen AVX2
registers. Under AVX-512VL the file holds thirty-two 256-bit registers,
`%ymm16 .. %ymm31` being reachable only through the EVEX encoding.
`ymmSpillAllocIn` is the same linear scan over a register list the caller
supplies; at `ymmFile` it is `ymmSpillAlloc` (`ymmSpillAllocIn_ymmFile`). -/

/-- The thirty-two AVX-512VL vector registers at 256-bit width. -/
def evexYmmFile : List String :=
  (List.range 32).map (fun i => "%ymm" ++ toString i)

/-- The registers of `evexYmmFile` that only the EVEX encoding reaches. -/
def evexOnlyYmm : List String :=
  (List.range 16).map (fun i => "%ymm" ++ toString (i + 16))

/-- The live ranges of a vector block, as the allocator computes them. -/
def ymmLiveRanges (block : List YmmInstr) : List LiveRange :=
  liveRanges (I := YmmInstr) block

/-- The linear-scan spill decisions over the register list `file`, from live
    ranges `lrs` already computed for the block. -/
def ymmSpillAllocRanges (file pinned scratch : List String) (frameBase : Int)
    (lrs : List LiveRange) : List (String × Slot) :=
  linearScan (file.filter (fun r => ¬ pinned.contains r ∧ ¬ scratch.contains r))
    frameBase lrs ymmStride

/-- The linear-scan spill decisions for a vector block over the register list
    `file`, with 32-byte frame cells. -/
def ymmSpillAllocIn (file pinned scratch : List String) (frameBase : Int)
    (block : List YmmInstr) : List (String × Slot) :=
  ymmSpillAllocRanges file pinned scratch frameBase (ymmLiveRanges block)

/-- Over the sixteen AVX2 registers the explicit-file allocator is
    `ymmSpillAlloc`. -/
theorem ymmSpillAllocIn_ymmFile (pinned scratch : List String) (frameBase : Int)
    (block : List YmmInstr) :
    ymmSpillAllocIn ymmFile pinned scratch frameBase block
      = ymmSpillAlloc pinned scratch frameBase block := rfl

/-! ## Frame-cell reuse

`linearScan` gives every spilled name a fresh cell, so the frame grows with the
number of spilled names rather than with the number spilled at once.
`compactSlots` reassigns the cells first-fit in order of definition: a spilled
name takes the lowest cell whose previous occupant's live range ended strictly
before this name's first write. Every access `ymmMaterialize` makes to a
spilled name's cell (the store after a write, the reload before a read) lies
inside the name's live range, so two names with disjoint live ranges never
observe each other's cell contents. `slotsReuseDisjoint` is the checkable form
of that condition. -/

/-- The first-fit cell assignment: `cells` holds `(offset, lastUse)` of each
    cell's current occupant, in offset order; `acc` the `(name, offset)` pairs
    assigned so far. -/
def compactSlotsGo (frameBase : Int) :
    List (Int × Nat) → List (String × Int) → List LiveRange → List (String × Int)
  | _, acc, [] => acc
  | cells, acc, lr :: rest =>
    match cells.find? (fun c => c.2 < lr.defIdx) with
    | some c =>
      compactSlotsGo frameBase
        (cells.map (fun d => if d.1 == c.1 then (c.1, lr.lastUse) else d))
        ((lr.name, c.1) :: acc) rest
    | none =>
      let off := frameBase + ymmStride * (cells.length : Int)
      compactSlotsGo frameBase (cells ++ [(off, lr.lastUse)]) ((lr.name, off) :: acc) rest

/-- The spilled live ranges of `decisions`, in order of definition. -/
def spilledRanges (lrs : List LiveRange) (decisions : List (String × Slot)) :
    List LiveRange :=
  (lrs.filter (fun lr => (spillSlotOf decisions lr.name).isSome)).mergeSort
    (fun a b => a.defIdx ≤ b.defIdx)

/-- `decisions` with every spilled name moved to its first-fit reused cell.
    Resident decisions are unchanged. -/
def compactSlots (lrs : List LiveRange) (frameBase : Int)
    (decisions : List (String × Slot)) : List (String × Slot) :=
  let assign := compactSlotsGo frameBase [] [] (spilledRanges lrs decisions)
  decisions.map (fun d => match d.2 with
    | .spilled off => (d.1, .spilled ((assign.lookup d.1).getD off))
    | .resident r => (d.1, .resident r))

/-- Every two spilled names that share a frame cell have disjoint live ranges. -/
def slotsReuseDisjoint (lrs : List LiveRange) (decisions : List (String × Slot)) :
    Bool :=
  let sp := (spilledRanges lrs decisions).filterMap (fun lr =>
    (spillSlotOf decisions lr.name).map (fun off => (lr, off)))
  sp.zipIdx.all (fun (p, i) => sp.zipIdx.all (fun (q, j) =>
    i == j || p.2 != q.2 || p.1.lastUse < q.1.defIdx || q.1.lastUse < p.1.defIdx))

/-- The bytes of frame the spilled cells of `decisions` occupy above
    `frameBase`: one cell past the highest spill offset. -/
def frameExtent (frameBase : Int) (decisions : List (String × Slot)) : Nat :=
  decisions.foldl (fun m d => match d.2 with
    | .spilled off => max m (off - frameBase + ymmStride).toNat
    | .resident _ => m) 0

/-! ## Withholding only the scratch registers the spills need

`ymmMaterialize` needs as many scratch registers as the largest number of
spilled names one instruction touches (`ymmScratchNeeded`), which depends on
the decisions, which depend on how many registers are withheld.
`ymmAllocFewestScratch` tries `k = 0, 1, ...` withheld registers, taken from
the front of `scratch`, and keeps the first allocation whose spills need at
most `k`; every register not withheld is allocatable. -/

/-- The allocation, with frame cells reused, that withholds the first `k`
    registers of `scratch`. -/
def ymmAllocWithScratch (file pinned scratch : List String) (frameBase : Int)
    (lrs : List LiveRange) (k : Nat) : List String × List (String × Slot) :=
  let sc := scratch.take k
  (sc, compactSlots lrs frameBase (ymmSpillAllocRanges file pinned sc frameBase lrs))

/-- The allocation withholding the fewest scratch registers that its own spills
    need; all of `scratch` when no smaller prefix suffices. Returns the withheld
    registers and the decisions. -/
def ymmAllocFewestScratch (file pinned scratch : List String) (frameBase : Int)
    (block : List YmmInstr) (lrs : List LiveRange) :
    List String × List (String × Slot) :=
  let fits := (List.range (scratch.length + 1)).find? (fun k =>
    ymmScratchNeeded (ymmAllocWithScratch file pinned scratch frameBase lrs k).2 block ≤ k)
  ymmAllocWithScratch file pinned scratch frameBase lrs (fits.getD scratch.length)

/-! ## EVEX spelling

An instruction that names a register of `evexOnlyYmm` must be spelled with an
EVEX mnemonic: the VEX forms `vpxor`, `vpor`, `vpand`, `vpandn` and `vmovdqu`
have no EVEX encoding, and their AVX-512VL counterparts are the quadword forms
`vpxorq`, `vporq`, `vpandq`, `vpandnq` and `vmovdqu64`, which compute the same
256-bit result with the same operand order. Shifts, `vprolq` and `vpternlogq`
keep their mnemonic, which the assembler encodes as EVEX when an operand
requires it. An instruction naming only `%ymm0 .. %ymm15` is printed by
`renderYmmInstr` unchanged. -/

/-- Whether an instruction names a register only EVEX reaches. -/
def namesEvexOnly (i : YmmInstr) : Bool :=
  (ymmNamesOf i).any (fun n => evexOnlyYmm.contains n)

/-- The AVX-512VL mnemonic of an ALU op, for the ops whose EVEX form this
    printer covers; `none` for the rest. -/
def evexMnemonic : YmmOp → Option String
  | .vpxor => some "vpxorq"
  | .vpor => some "vporq"
  | .vpand => some "vpandq"
  | .vpandn => some "vpandnq"
  | .vpaddq => some "vpaddq"
  | .vpsubq => some "vpsubq"
  | .vpsllq _ => some "vpsllq"
  | .vpsrlq _ => some "vpsrlq"
  | .vprolq _ => some "vprolq"
  | _ => none

/-- Whether `renderYmmInstrEvex` has a spelling for the instruction. -/
def evexSpellable : YmmInstr → Bool
  | i@(.alu op _ _) => !namesEvexOnly i || (evexMnemonic op).isSome
  | _ => true

/-- The AT&T line of an instruction over `evexYmmFile`: `renderYmmInstr` with
    the mnemonic replaced by its EVEX form when an operand is one of
    `evexOnlyYmm`. -/
def renderYmmInstrEvex (i : YmmInstr) : String :=
  let line := renderYmmInstr i
  if !namesEvexOnly i then line
  else match i with
    | .alu op _ _ =>
      match evexMnemonic op with
      | some mn => line.replace ("\t" ++ op.attMnemonic ++ "\t") ("\t" ++ mn ++ "\t")
      | none => line
    | .ymov _ _ | .yload _ _ | .ystore _ _ => line.replace "\tvmovdqu\t" "\tvmovdqu64\t"
    | .ternlog _ _ _ _ => line

/-- Every vector name in a block is a register of `file`. -/
def ymmAllPhysicalIn (file : List String) (block : List YmmInstr) : Bool :=
  block.all (fun i => (ymmNamesOf i).all (fun n => file.contains n))

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
