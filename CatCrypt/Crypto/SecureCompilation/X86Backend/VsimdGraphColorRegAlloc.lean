/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.ByteMemMachine
public import CatCrypt.Crypto.Optimizer.GraphColoringGeneric
public import CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint

/-!
# Graph-coloring (Chaitin–Briggs) register allocation with spilling for the `vsimd`
  fragment of `Com jasminDialect`

`VIR.VsimdAsmPrint.allocXmm` / `allocXmmSeeded` allocate the `vsimd` fragment by
**linear scan with last-use recycling**: no interference graph, no coloring, and no
spilling — an over-budget block simply leaves later temps unmapped, which the printer
renders as the `<UNALLOCATED:…>` sentinel. A kernel whose values are
whole-program-live across a long body (a register-resident block cipher or hash core)
needs the stronger discipline: an interference graph, a use-density spill metric, and
spill/reload traffic that is proved denotation-transparent.

This module supplies that over the same block representation the surviving printer
already consumes.

## The representation mapping

The allocation input of the surviving path is the `(dst, srcs)` block that
`VsimdAsmPrint.collectVsimdDefs` produces and `VsimdAsmPrint.allocXmm` consumes:

```
Com jasminDialect (vsimd) ──collectVsimdDefs──▶ List (String × List String)
                          ──allocXmm reserved─▶ XAlloc = List (String × String)
                          ──renderVsimdCom────▶ AT&T .s lines
```

* `VsimdEntry` is that `(dst, srcs)` pair (`VsimdEntry.ofPair` / `toPair` are the
  bijection with the surviving element type). It carries the def/use interface a
  register allocator reads and nothing else, so it is what the coloring pipeline runs
  on: `MachineModel.writtenNames ⟨d, ss⟩ = [d]`, `readNames ⟨d, ss⟩ = ss`.
* `VsimdSemInst w` is the same pair together with an operator interpretation
  `eval : List (BitVec w) → BitVec w`, and `VsimdSemInst.erase` forgets it back to a
  `VsimdEntry`. The interpretation is per instruction and arbitrary, so the soundness
  results below hold for every operator reading of a `vsimd` body.
* `VecFrameState w` is the machine state: a `String`-named vector register file of
  `BitVec w` values plus an `Int`-offset frame. `RegMachine.runBlock` at
  `VsimdSemInst w` is its straight-line semantics, and `RegMachine.runBlock_append` is
  a class field, so the interpreter-append law needs no separate proof.
* A spill slot is a **pseudo-register name** (`spillSlotName off`) that no program
  value writes, so a spill store and its reload are moves in the same instruction
  type — `mkSpill` / `mkReload` of the `MachineModel` instance.

## What is built

1. **The seam** (§1): the `MachineModel VsimdEntry` instance. Everything the
   Chaitin–Briggs pipeline needs is this instance; the pipeline itself —
   `GraphColoringGeneric.{rangesOverlap, interfere, neighbours, useCount, rangeLen,
   spillCostFrac, cheaperSpill, degreeIn, pickNode, simplifyStack, firstFreeColor,
   valueRanges}` and `GenericRegAlloc.{LiveRange, liveRanges, Slot, spillCount,
   residentCount, rewriteBlock, rewriteBlock_length}` — is inherited unchanged.
2. **The pool- and stride-explicit top level** (§2): `vsimdGraphColorAllocIn` over any
   vector register file, passing `GraphColoringGeneric.selectColors` the file's value
   width as its frame-cell stride, so a 32-byte `%ymm` or 64-byte `%zmm` slot does not
   overlap its successor.
3. **The bridge to the printer** (§3): `xallocOfDecisions` projects the resident half
   of a decision list to the `XAlloc` that `VsimdAsmPrint.renderVsimdCom` consumes,
   with `spilledNames` naming the remainder.
4. **The machine** (§4): `VecFrameState w` with `RegMachine (VsimdSemInst w)` and
   `MemMachine` instances, and `erase`-agreement (§5) showing the live ranges and the
   allocation computed on the erased block are the ones the semantic block has.
5. **Spill soundness** (§6): `SlotHolds`, `spillStore_establishes`, `reload_noop`,
   `reloadBeforeUse_runBlock`, and `spillReload_sandwich` — a spilled
   value's store/body/reload sandwich denotes the same as the sandwich without the
   reload, for every operator interpretation of the body.
6. **The resident case** (§7): a spill-free allocation inserts no traffic, so the
   emitted block is the original under a register renaming, whose soundness is the
   generic `GenericRegAlloc.renameBlock_runBlock`.
7. **The frame route** (§9): the vector frame as an `Optimizer.ByteMemMachine` of
   `w/8`-byte accesses, the byte-addressed spill sandwich at it, and the frame-layout
   obligation `GenericRegAlloc.SlotsSeparated` discharged for each entry point from its
   stride. §6's sandwich is over the slot pseudo-registers, where two offsets give two
   names whatever their byte distance; §9 is where the byte distance is the hypothesis.
8. **The frame-touching instruction** (§10): `VsimdFrameInst`, whose spill store and
   reload write and read a byte-granular frame, as an
   `Optimizer.ByteMemMachine.FrameStepMachine`; the store/body/reload sandwich over a body
   of such instructions, with byte separation of the slots as its hypothesis and the
   allocator's `SlotsSeparated` discharging it; and a body refuting the conclusion when
   the separation is dropped.

The allocator itself is untrusted; the verified artifact is the spill/reload checker
of §6 and the renaming soundness of §7, both allocation-agnostic.

## Main definitions

* `VsimdEntry`, `VsimdSemInst`: the erased and semantic vector instruction, with
  `erase` between them
* `VecFrameState`: register file plus spill frame, the state the soundness is over
* `instMachineModelVsimdEntry`, `instRegMachineVsimdSemInst`: the two instances that
  bring `Optimizer.GraphColoringGeneric` and `Optimizer.GenericRegAlloc` to bear
* `vsimdGraphColorAllocIn`, `vsimdGraphColorAllocYmm`, `vsimdGraphColorAllocXmm`,
  `vsimdGraphColorAllocZmm`: the pool- and stride-explicit entry points, one per
  vector register file, each pairing its file with that file's value width
* `VsimdFrameInst`, `evalVsimdFrameInst`: the instruction whose spill store and reload
  write and read a byte-granular frame, and its step

## Main results

* `spillReload_sandwich`: a value spilled to a slot pseudo-register, used across a body
  that preserves the slot, then reloaded, equals the original
* `vsimdFrameSpillReload_sandwich`: the same sandwich with the slot a byte range of the
  frame, under byte separation of the slots the body writes
* `vsimdFrameSandwich_fails_without_separation`: a body refuting that conclusion once the
  separation hypothesis is dropped
* `vsimdFrameSandwich_of_ymmAlloc` and its `%xmm`/`%zmm` siblings: the separation
  hypothesis discharged from the allocation's own frame layout
* `reload_noop`, `spillStore_establishes`, `reloadBeforeUse_runBlock`: the
  slot-validity steps the sandwich is built from
* `renameBlock_runVsimdBlock`: an injective register renaming preserves the run
* `liveRanges_map_erase`: erasing the operator preserves live ranges, so the
  allocation computed on erased entries is the one the soundness speaks about
* `runVsimdBlock_append`: the interpreter-append law, inherited as a `RegMachine`
  class field rather than proved
* `vsimdGraphColorAllocYmm_slotsSeparated` and its `%xmm`/`%zmm` siblings: the frame slots
  each entry point assigns cover pairwise-disjoint byte ranges at that file's value width
* `pressureBlock_ymm_slots_overlap_at_stride_eight`: the same allocation run at the
  general-purpose stride `8` does not
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VsimdGraphColorRegAlloc

open CatCrypt.Crypto.Optimizer.GenericRegAlloc
open CatCrypt.Crypto.Optimizer.GraphColoringGeneric
open CatCrypt.Crypto.Optimizer.ByteMemMachine

/-! ## 1. The seam: the def/use interface of one `vsimd` block entry -/

/-- The frame-cell pseudo-register name of the spill slot at byte offset `off`. A
    spill slot is a name no program value writes, so the spill store and its reload
    are moves between a value name and this name. -/
def spillSlotName (off : Int) : String := "#slot" ++ toString off

/-- One entry of the straight-line `vsimd` block: the destination name and the source
    names of a single binding. This is the element type of the block
    `VsimdAsmPrint.collectVsimdDefs` produces and `VsimdAsmPrint.allocXmm` consumes,
    as a named structure. -/
structure VsimdEntry where
  /-- The name the binding writes. -/
  dst : String
  /-- The names the binding reads. -/
  srcs : List String
  deriving Repr, DecidableEq

/-- The `(dst, srcs)` pair of an entry — the surviving block element type. -/
def VsimdEntry.toPair (e : VsimdEntry) : String × List String := (e.dst, e.srcs)

/-- An entry from a `(dst, srcs)` pair. -/
def VsimdEntry.ofPair (p : String × List String) : VsimdEntry := ⟨p.1, p.2⟩

/-- `ofPair` and `toPair` are mutually inverse: `VsimdEntry` is the surviving
    `String × List String` block element under a different name. -/
@[simp] theorem VsimdEntry.ofPair_toPair (e : VsimdEntry) :
    VsimdEntry.ofPair e.toPair = e := rfl

/-- `toPair` after `ofPair` is the identity. -/
@[simp] theorem VsimdEntry.toPair_ofPair (p : String × List String) :
    (VsimdEntry.ofPair p).toPair = p := rfl

/-- A block of `VsimdAsmPrint.collectVsimdDefs` output as `VsimdEntry`s. -/
def ofVsimdBlock (block : List (String × List String)) : List VsimdEntry :=
  block.map VsimdEntry.ofPair

/-- The 16 `%ymm` registers — the 256-bit vector file the 8-way kernels allocate
    from. (`VsimdAsmPrint.xmmPool` is the 128-bit file.) -/
def ymmPool : List String := (List.range 16).map (fun i => "%ymm" ++ toString i)

/-- The 32 `%zmm` registers — the 512-bit vector file. -/
def zmmPool : List String := (List.range 32).map (fun i => "%zmm" ++ toString i)

/-- **The def/use interface of a `vsimd` block entry.** A binding writes its single
    destination and reads its sources; the register file defaults to the 128-bit
    `VsimdAsmPrint.xmmPool` that `allocXmm` allocates from (the wider files are
    reached with the pool-explicit entry point `vsimdGraphColorAllocIn`); a spill
    store writes the slot pseudo-name from the value name, and a reload writes the
    value name from the slot pseudo-name. This instance is the whole adapter the
    Chaitin–Briggs pipeline needs. -/
instance instMachineModelVsimdEntry : MachineModel VsimdEntry where
  writtenNames e := [e.dst]
  readNames e := e.srcs
  physRegs := CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint.xmmPool
  mkSpill r off := ⟨spillSlotName off, [r]⟩
  mkReload r off := ⟨r, [spillSlotName off]⟩

/-! ## 2. Coloring over an explicit vector file and frame stride

The spill offsets of `GraphColoringGeneric.selectColors` advance by its `stride`
argument, the byte width of one allocated value: a 256-bit spill takes 32 and a
512-bit spill 64, and the default 8 is the general-purpose word. One `VsimdEntry`
serves three vector files of three widths, so both the pool and the stride are
arguments of the entry points below rather than data of the `MachineModel` instance. -/

/-- **Graph-coloring allocation over an explicit vector register file.** Value live
    ranges (`GraphColoringGeneric.valueRanges`) → interference graph → Briggs
    simplify/potential-spill stack (`simplifyStack`, `|pool|` colors, spill choice by
    use density) → LIFO select with a `stride`-byte frame cell per spill. The pool is
    explicit so the same allocator serves the `%xmm`, `%ymm` and `%zmm` files;
    `pinned` names are held out of it. -/
def vsimdGraphColorAllocIn (pool pinned : List String) (frameBase stride : Int)
    (block : List VsimdEntry) : List (String × Slot) :=
  let avail := pool.filter (fun r => ¬ pinned.contains r)
  let lrs := valueRanges block
  let stack := simplifyStack block lrs avail.length
  selectColors avail lrs frameBase stack stride

/-- Graph-coloring allocation over the 16 `%ymm` registers with 32-byte spill cells —
    the file the 8-way (256-bit) kernels use. -/
def vsimdGraphColorAllocYmm (pinned : List String) (frameBase : Int)
    (block : List VsimdEntry) : List (String × Slot) :=
  vsimdGraphColorAllocIn ymmPool pinned frameBase 32 block

/-- Graph-coloring allocation over the 16 `%xmm` registers with 16-byte spill cells —
    the file `VsimdAsmPrint.allocXmm` allocates from, so this is the drop-in
    replacement for it on a block that needs spilling. -/
def vsimdGraphColorAllocXmm (pinned : List String) (frameBase : Int)
    (block : List VsimdEntry) : List (String × Slot) :=
  vsimdGraphColorAllocIn CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint.xmmPool
    pinned frameBase 16 block

/-- Graph-coloring allocation over the 32 `%zmm` registers with 64-byte spill cells. -/
def vsimdGraphColorAllocZmm (pinned : List String) (frameBase : Int)
    (block : List VsimdEntry) : List (String × Slot) :=
  vsimdGraphColorAllocIn zmmPool pinned frameBase 64 block

/-! ## 3. The bridge to the surviving printer

`VsimdAsmPrint.renderVsimdCom` consumes an `XAlloc = List (String × String)` mapping
each SSA name to its physical register. The resident half of a decision list is
exactly such a map; the spilled half is the traffic `GenericRegAlloc.rewriteBlock`
inserts. -/

/-- The `XAlloc` of a decision list: every `resident` name paired with its physical
    register, in decision order. Feeding this to `VsimdAsmPrint.renderVsimdCom` renders
    the block against the coloring; a spilled name is absent, so a body that was not
    first rewritten by `GenericRegAlloc.rewriteBlock` renders it as the printer's
    `<UNALLOCATED:…>` sentinel rather than silently aliasing. -/
def xallocOfDecisions (decisions : List (String × Slot)) :
    CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint.XAlloc :=
  decisions.filterMap (fun d => match d.2 with
    | .resident r => some (d.1, r)
    | .spilled _ => none)

/-- The names a decision list spills, with their frame offsets. -/
def spilledNames (decisions : List (String × Slot)) : List (String × Int) :=
  decisions.filterMap (fun d => match d.2 with
    | .resident _ => none
    | .spilled off => some (d.1, off))

/-- A decision list is **spill-free** when every name is register-resident. -/
def allResident (decisions : List (String × Slot)) : Bool :=
  decisions.all (fun d => match d.2 with | .resident _ => true | .spilled _ => false)

/-! ## 4. The vector machine: a named `BitVec w` register file and a frame

The state a spill/reload argument needs. `VsimdSemInst w` is a block entry together
with an operator interpretation, so a block of them is a `vsimd` body under an
arbitrary reading of its ops; `VecFrameState w` is a `String`-named vector register
file plus an `Int`-offset frame. The `RegMachine` instance gives the straight-line
semantics and, as class fields, the append and nil laws. -/

/-- One `vsimd` block entry together with an interpretation of its operator: the
    binding writes `dst` the value `eval` computes from the values of `srcs`. The
    interpretation is per instruction and unconstrained, so a statement quantified
    over `List (VsimdSemInst w)` covers every operator reading of a `vsimd` body. -/
structure VsimdSemInst (w : Nat) where
  /-- The name the binding writes. -/
  dst : String
  /-- The names the binding reads. -/
  srcs : List String
  /-- The operator: the written value as a function of the source values. -/
  eval : List (BitVec w) → BitVec w

/-- The def/use interface of a semantic instruction — the `VsimdEntry` it erases to. -/
def VsimdSemInst.erase {w : Nat} (i : VsimdSemInst w) : VsimdEntry := ⟨i.dst, i.srcs⟩

/-- A **register-to-register move** `dst ← src` as a semantic instruction: the
    identity operator on the single source. Spill stores and reloads are moves to and
    from a slot pseudo-name. -/
def vmovInst (w : Nat) (dst src : String) : VsimdSemInst w :=
  ⟨dst, [src], fun vs => vs.headD 0⟩

/-- The machine state: a `String`-named vector register file of `BitVec w` values and
    an `Int`-offset frame memory. -/
structure VecFrameState (w : Nat) where
  /-- The vector register file. -/
  regs : String → BitVec w
  /-- The frame memory, by byte offset. -/
  frame : Int → BitVec w

/-- Write a vector register. -/
def VecFrameState.setReg {w : Nat} (s : VecFrameState w) (r : String) (v : BitVec w) :
    VecFrameState w :=
  { s with regs := fun x => if x = r then v else s.regs x }

/-- Write a frame cell. -/
def VecFrameState.setCell {w : Nat} (s : VecFrameState w) (off : Int) (v : BitVec w) :
    VecFrameState w :=
  { s with frame := fun o => if o = off then v else s.frame o }

/-- One instruction's effect: write the destination the value the operator computes
    from the current source values. -/
def evalVsimdSemInst {w : Nat} (s : VecFrameState w) (i : VsimdSemInst w) :
    VecFrameState w :=
  s.setReg i.dst (i.eval (i.srcs.map s.regs))

/-- Straight-line block semantics: the left fold of `evalVsimdSemInst`. -/
def runVsimdBlock {w : Nat} (s : VecFrameState w) (block : List (VsimdSemInst w)) :
    VecFrameState w :=
  block.foldl evalVsimdSemInst s

/-- Reading back a just-written register returns the written value. -/
@[simp] theorem VecFrameState.regs_setReg_same {w : Nat} (s : VecFrameState w)
    (r : String) (v : BitVec w) : (s.setReg r v).regs r = v := by
  simp [VecFrameState.setReg]

/-- Writing one register leaves the others unchanged. -/
theorem VecFrameState.regs_setReg_other {w : Nat} (s : VecFrameState w)
    (r r' : String) (v : BitVec w) (h : r ≠ r') : (s.setReg r' v).regs r = s.regs r := by
  simp [VecFrameState.setReg, h]

/-- Writing a register a value it already holds is a no-op. -/
theorem VecFrameState.setReg_regs_self {w : Nat} (s : VecFrameState w) (r : String) :
    s.setReg r (s.regs r) = s := by
  cases s with
  | mk regs frame =>
    simp only [VecFrameState.setReg, VecFrameState.mk.injEq, and_true]
    funext x
    by_cases h : x = r <;> simp [h]

/-- Applying a renaming to a semantic instruction: rename the destination and every
    source, keeping the operator. -/
def renameVsimdSemInst {w : Nat} (ρ : String → String) (i : VsimdSemInst w) :
    VsimdSemInst w :=
  ⟨ρ i.dst, i.srcs.map ρ, i.eval⟩

/-- **The `vsimd` vector machine as a `RegMachine`.** The instruction's def/use
    interface, the register file with its two laws, the single-write step, and the
    `runBlock` nil/append laws. With this instance the generic resident-path result
    `GenericRegAlloc.renameBlock_runBlock` applies to `vsimd` bodies. -/
instance instRegMachineVsimdSemInst (w : Nat) :
    RegMachine (VsimdSemInst w) (VecFrameState w) where
  writtenNames i := [i.dst]
  readNames i := i.srcs
  physRegs := CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint.xmmPool
  mkSpill r off := vmovInst w (spillSlotName off) r
  mkReload r off := vmovInst w r (spillSlotName off)
  runBlock := runVsimdBlock
  Val := BitVec w
  get s r := s.regs r
  set s r v := s.setReg r v
  writes s i := [(i.dst, i.eval (i.srcs.map s.regs))]
  renameInst := renameVsimdSemInst
  isDiscard _ := false
  get_discard := by intro _ _ _ _ h; simp at h
  get_set_same := by intro s r v _; exact VecFrameState.regs_setReg_same s r v
  get_set_other := by
    intro s r r' v h; exact VecFrameState.regs_setReg_other s r r' v (Ne.symm h)
  evalInst_eq_set := by intro s i r; rfl
  runBlock_nil := by intro s; rfl
  runBlock_append := by
    intro s xs ys; simp [runVsimdBlock, List.foldl_append]
  writes_names := by intro s i; rfl
  writes_rename := by
    intro ρ s t i h
    have hmap : (i.srcs.map ρ).map t.regs = i.srcs.map s.regs := by
      rw [List.map_map]
      exact List.map_congr_left (fun a ha => h a ha)
    simp only [renameVsimdSemInst, List.map_cons, List.map_nil]
    rw [hmap]

/-- **The vector machine as a `MemMachine`.** The frame route for spill traffic: the
    register file, the frame, and the four cell/register laws. With this instance the
    generic `GenericRegAlloc.{spillStore_establishes, evalReload_noop, reload_sandwich}`
    apply to a `vsimd` spill against a real frame cell. -/
instance instMemMachineVecFrameState (w : Nat) : MemMachine (VecFrameState w) where
  Val := BitVec w
  get s r := s.regs r
  load s off := s.frame off
  setReg s r v := s.setReg r v
  store s off v := s.setCell off v
  load_store_same := by intro m off v; simp [VecFrameState.setCell]
  load_store_other := by intro m off o v h; simp [VecFrameState.setCell, h]
  get_store := by intro m off v r; rfl
  setReg_get_self := by intro m r; exact VecFrameState.setReg_regs_self m r

/-! ## 5. Erasure agreement: the allocation is computed on the block it is about

The coloring pipeline of §2 runs on `List VsimdEntry`; the soundness of §6–§7 is about
`List (VsimdSemInst w)`. The two are connected by `erase`: it preserves the def/use
interface pointwise, hence the block's names, live ranges, value ranges and therefore
the allocation itself. So the decisions the allocator computes from the erased block
are the decisions the semantic block's soundness statements are about. -/

/-- `erase` preserves the written names. -/
@[simp] theorem writtenNames_erase {w : Nat} (i : VsimdSemInst w) :
    writtenNames i.erase = writtenNames (I := VsimdSemInst w) i := rfl

/-- `erase` preserves the read names. -/
@[simp] theorem readNames_erase {w : Nat} (i : VsimdSemInst w) :
    readNames i.erase = readNames (I := VsimdSemInst w) i := rfl

/-- `erase` preserves the block's distinct names in order. -/
theorem blockNames_map_erase {w : Nat} (block : List (VsimdSemInst w)) :
    blockNames (block.map VsimdSemInst.erase) = blockNames block := by
  simp only [blockNames, List.flatMap_map, writtenNames_erase, readNames_erase]

/-- `erase` preserves each name's first defining index. -/
theorem defIdxOf_map_erase {w : Nat} (block : List (VsimdSemInst w)) (n : String) :
    defIdxOf (block.map VsimdSemInst.erase) n = defIdxOf block n := by
  simp only [defIdxOf, List.zipIdx_map, List.find?_map, Function.comp_def,
    Prod.map_fst, writtenNames_erase]
  cases List.find? (fun x : VsimdSemInst w × Nat => (writtenNames x.1).contains n)
    block.zipIdx <;> rfl

/-- `erase` preserves each name's last use index. -/
theorem lastUseIdx_map_erase {w : Nat} (block : List (VsimdSemInst w)) (n : String) :
    lastUseIdx (block.map VsimdSemInst.erase) n = lastUseIdx block n := by
  simp [lastUseIdx, List.zipIdx_map, List.foldl_map, Prod.map_fst, Prod.map_snd]; rfl

/-- **`erase` preserves the live ranges.** The interference graph, the use-density
    spill cost and hence every coloring decision are functions of the live ranges and
    the def/use interface alone, so running the allocator on the erased block computes
    the allocation of the semantic block. -/
theorem liveRanges_map_erase {w : Nat} (block : List (VsimdSemInst w)) :
    liveRanges (block.map VsimdSemInst.erase) = liveRanges block := by
  simp only [liveRanges, blockNames_map_erase, defIdxOf_map_erase, lastUseIdx_map_erase]

/-! ## 6. Spill soundness

A spilled value is materialized by a store `slot ← r` at its definition and a reload
`r ← slot` before each later use, where `slot` is the pseudo-name of its frame cell —
a name no program value writes. The store makes the slot hold the value; the reload is
then a no-op, because it writes `r` a value `r` already holds. So the inserted traffic
is denotation-transparent, for every operator interpretation of the body between them.
The heuristic that chose *which* names to spill is untrusted; this checker is
allocation-agnostic. -/

/-- `SlotHolds slot r s`: the spill slot `slot` holds `r`'s value in state `s`. -/
def SlotHolds {w : Nat} (slot r : String) (s : VecFrameState w) : Prop :=
  s.regs slot = s.regs r

/-- One instruction of a block runs as `evalVsimdSemInst`. -/
theorem runVsimdBlock_cons {w : Nat} (s : VecFrameState w) (i : VsimdSemInst w)
    (rest : List (VsimdSemInst w)) :
    runVsimdBlock s (i :: rest) = runVsimdBlock (evalVsimdSemInst s i) rest := rfl

/-- `runVsimdBlock` distributes over `++`. -/
theorem runVsimdBlock_append {w : Nat} (s : VecFrameState w)
    (xs ys : List (VsimdSemInst w)) :
    runVsimdBlock s (xs ++ ys) = runVsimdBlock (runVsimdBlock s xs) ys :=
  RegMachine.runBlock_append (I := VsimdSemInst w) s xs ys

/-- A move writes its destination the source's value. -/
theorem evalVsimdSemInst_vmov {w : Nat} (s : VecFrameState w) (d src : String) :
    evalVsimdSemInst s (vmovInst w d src) = s.setReg d (s.regs src) := rfl

/-- **The reload is a no-op when the slot holds the register's value.** Under
    `SlotHolds slot r`, the reload `r ← slot` writes `r` a value it already holds. -/
theorem reload_noop {w : Nat} {slot r : String} {s : VecFrameState w}
    (hv : SlotHolds slot r s) :
    evalVsimdSemInst s (vmovInst w r slot) = s := by
  rw [evalVsimdSemInst_vmov, show s.regs slot = s.regs r from hv,
    VecFrameState.setReg_regs_self]

/-- **The spill store establishes `SlotHolds`.** After the store `slot ← r`, the slot
    holds `r`'s value. The hypothesis `slot ≠ r` is the freshness of the slot
    pseudo-name: a spill slot is distinct from every value register. -/
theorem spillStore_establishes {w : Nat} {slot r : String} {s : VecFrameState w}
    (h : slot ≠ r) :
    SlotHolds slot r (evalVsimdSemInst s (vmovInst w slot r)) := by
  rw [evalVsimdSemInst_vmov]
  show (s.setReg slot (s.regs r)).regs slot = (s.setReg slot (s.regs r)).regs r
  rw [VecFrameState.regs_setReg_same,
    VecFrameState.regs_setReg_other s r slot (s.regs r) (Ne.symm h)]

/-- **A reload before a use preserves the run.** Prefixing the reload `r ← slot` to a
    block leaves its final state unchanged, provided the slot holds `r`'s value. -/
theorem reloadBeforeUse_runBlock {w : Nat} {slot r : String} {s : VecFrameState w}
    (hv : SlotHolds slot r s) (rest : List (VsimdSemInst w)) :
    runVsimdBlock s (vmovInst w r slot :: rest) = runVsimdBlock s rest := by
  rw [runVsimdBlock_cons, reload_noop hv]

/-- **The store/body/reload sandwich over the slot pseudo-registers.** For a spilled
    value whose store `slot ← r` precedes a body `mid` that leaves the slot holding
    `r`, the reload `r ← slot` inserted before `r`'s later use does not change the
    block's final state. Quantified over every `mid` and every operator interpretation of
    its instructions. The store's target is the pseudo-register `slot`, so the statement is
    about the register file and the byte distance between two slots does not enter it; the
    form in which it does is §10's `vsimdFrameSpillReload_sandwich`, over an instruction
    whose store writes the frame. -/
theorem spillReload_sandwich {w : Nat} {slot r : String} {s : VecFrameState w}
    (mid rest : List (VsimdSemInst w))
    (hmid : SlotHolds slot r
      (runVsimdBlock (evalVsimdSemInst s (vmovInst w slot r)) mid)) :
    runVsimdBlock s (vmovInst w slot r :: (mid ++ vmovInst w r slot :: rest))
      = runVsimdBlock s (vmovInst w slot r :: (mid ++ rest)) := by
  rw [runVsimdBlock_cons, runVsimdBlock_cons, runVsimdBlock_append,
    runVsimdBlock_append, runVsimdBlock_cons, reload_noop hmid]

/-! ## 7. The resident case

A spill-free allocation inserts no traffic: the emitted block is the original under
the renaming `name ↦ physical register`, whose denotation preservation is the generic
resident-path result `GenericRegAlloc.renameBlock_runBlock`, which the `RegMachine`
instance of §4 makes available at `vsimd` bodies. -/

/-- **A spill-free allocation spills nothing**, so `GenericRegAlloc.rewriteBlock`
    inserts no store/reload traffic and the emitted block is the original under a
    register renaming. -/
theorem spillCount_eq_zero_of_allResident (decisions : List (String × Slot))
    (h : allResident decisions = true) : spillCount decisions = 0 := by
  simp only [spillCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro d hd
  have hall := (List.all_eq_true.mp h) d hd
  revert hall
  cases d.2 <;> simp

/-- **A spill-free allocation names every decision's register**, so `xallocOfDecisions`
    loses nothing: the resident projection has one entry per decision. -/
theorem xallocOfDecisions_length_of_allResident (decisions : List (String × Slot))
    (h : allResident decisions = true) :
    (xallocOfDecisions decisions).length = decisions.length := by
  induction decisions with
  | nil => rfl
  | cons d ds ih =>
    have hd : (match d.2 with | .resident _ => true | .spilled _ => false) = true := by
      have := List.all_eq_true.mp h d (List.mem_cons_self ..)
      simpa [allResident] using this
    have hds : allResident ds = true := by
      simp only [allResident, List.all_eq_true] at h ⊢
      exact fun x hx => h x (List.mem_cons_of_mem _ hx)
    cases hslot : d.2 with
    | resident rg =>
      simp only [xallocOfDecisions, List.filterMap_cons, hslot, List.length_cons]
      rw [show (List.filterMap _ ds).length = ds.length from ih hds]
    | spilled off => rw [hslot] at hd; simp at hd

/-- **The resident path is denotation-preserving**, at `vsimd` bodies: an injective
    renaming `ρ` of value names to physical registers carries the reindex relation
    through the block, so the register-allocated body computes at `ρ n` exactly what
    the original computed at `n`. This is `GenericRegAlloc.renameBlock_runBlock`
    instantiated at the `RegMachine (VsimdSemInst w) (VecFrameState w)` instance; the
    `vsimd` machine has no discard register, so the two discard side-conditions are
    discharged here. -/
theorem renameBlock_runVsimdBlock {w : Nat} (ρ : String → String)
    (hinj : Function.Injective ρ) (block : List (VsimdSemInst w))
    (s t : VecFrameState w)
    (h : Reindexed (VsimdSemInst w) ρ s t) :
    Reindexed (VsimdSemInst w) ρ (runVsimdBlock s block)
      (runVsimdBlock t (renameBlock (S := VecFrameState w) ρ block)) :=
  renameBlock_runBlock (VsimdSemInst w) ρ hinj (by intro r hr; simp at hr)
    (fun _ _ => rfl) block (fun _ _ _ _ => rfl) s t h

/-! ## 8. A pressure witness

A three-binding block whose two temps are simultaneously live, allocated over a
one-register pool: the coloring must spill one of them. This exhibits the pipeline
running end-to-end at `VsimdEntry` — live ranges, interference, simplify/spill stack,
select — and the spill arm of the select phase taking effect, which the linear-scan
`VsimdAsmPrint.allocXmm` cannot do (it leaves the name unmapped). The two offsets it
receives are the stride apart, one whole vector value per frame cell. -/

/-- Two temps live at once, both consumed by a third binding. -/
def pressureBlock : List VsimdEntry :=
  [⟨"t0", ["p0"]⟩, ⟨"t1", ["p0"]⟩, ⟨"t2", ["t0", "t1"]⟩]

/-- The three destinations are the block's value names. -/
theorem pressureBlock_valueRanges_length :
    (valueRanges pressureBlock).length = 3 := by decide

/-- **Over a one-register pool the coloring spills, rather than leaving a name
    unmapped.** `t0` and `t1` are simultaneously live and `t2` overlaps both, so a
    single-color pool cannot color all three: the select phase assigns frame cells to
    the two it cannot color. -/
theorem pressureBlock_spills_over_one_register :
    spillCount (vsimdGraphColorAllocIn ["%ymm0"] [] 0 32 pressureBlock) = 2 := by decide

/-- **Over the full `%ymm` file the same block is spill-free** — the pressure is a
    property of the pool size, not of the allocator. -/
theorem pressureBlock_resident_over_ymm :
    spillCount (vsimdGraphColorAllocYmm [] 0 pressureBlock) = 0 := by decide

/-- **Two live `%ymm` spills take frame cells 32 bytes apart.** At the 256-bit stride
    the two names the one-register pool cannot color get the offsets `0` and `32`, so
    the cell of each holds one whole 256-bit value and neither runs into the other. -/
theorem pressureBlock_ymm_slots_32_apart :
    spilledNames (vsimdGraphColorAllocIn ["%ymm0"] [] 0 32 pressureBlock)
      = [("t0", 32), ("t2", 0)] := by decide

/-- **Two live `%zmm` spills take frame cells 64 bytes apart** — the same block at the
    512-bit stride, one whole 512-bit value per cell. -/
theorem pressureBlock_zmm_slots_64_apart :
    spilledNames (vsimdGraphColorAllocIn ["%zmm0"] [] 0 64 pressureBlock)
      = [("t0", 64), ("t2", 0)] := by decide

/-! ## 9. The frame route: the slot offsets as byte ranges

§6 spills to a slot **pseudo-register** `spillSlotName off`, so two offsets give two names
whatever their byte distance and the sandwich there holds of any stride. The frame of
`VecFrameState w` is the other route, and one access on it spans `w / 8` bytes: two slots
are independent when their byte ranges are disjoint, which is stronger than their offsets
differing.
`Optimizer.ByteMemMachine` is that interface, `instByteMemMachineVecFrameState` reads the
vector frame as one, and the obligation its non-interference law asks for —
`GenericRegAlloc.SlotsSeparated` on the allocation — is discharged from each entry point's
stride. At the general-purpose stride `8` a `%ymm` allocation does not discharge it
(`pressureBlock_ymm_slots_overlap_at_stride_eight`). -/

/-- **The vector frame as a byte-addressed spill memory.** One access spans the byte width
    of one value of the file, `max 1 (w / 8)`, and the non-interference law is conditioned
    on byte-range disjointness. Via `ByteMemMachine.ofMemMachine` from the cell-indexed
    `instMemMachineVecFrameState`, whose law is the same one with the separation hypothesis
    dropped. -/
instance instByteMemMachineVecFrameState (w : Nat) : ByteMemMachine (VecFrameState w) :=
  ofMemMachine (VecFrameState w) (max 1 (w / 8)) (Nat.le_max_left 1 (w / 8))

/-- A `%xmm` frame access spans 16 bytes. -/
theorem byteWidth_vecFrameState_xmm : byteWidth (VecFrameState 128) = 16 := by decide

/-- A `%ymm` frame access spans 32 bytes. -/
theorem byteWidth_vecFrameState_ymm : byteWidth (VecFrameState 256) = 32 := by decide

/-- A `%zmm` frame access spans 64 bytes. -/
theorem byteWidth_vecFrameState_zmm : byteWidth (VecFrameState 512) = 64 := by decide

/-- **The byte-addressed spill sandwich at the vector frame.** A value stored to its slot,
    a body of spill stores to other slots, then the reload before the value's use: the
    reload is a no-op provided every slot the body writes is byte-separated from this one.
    `ByteMemMachine.byteReload_after_storeSeq` at `VecFrameState w`. -/
theorem vsimdFrame_reload_after_storeSeq {w : Nat} (m : VecFrameState w) (off : Int)
    (r : String) (ss : List (Int × String))
    (hsep : ∀ p ∈ ss, SepAt (byteWidth (VecFrameState w)) p.1 off) :
    byteReload (byteStoreSeq (byteSpillStore m off r) ss) r off
      = byteStoreSeq (byteSpillStore m off r) ss :=
  byteReload_after_storeSeq m off r ss hsep

/-- **Every allocation this entry point produces has separated slots at any value width its
    stride covers.** The frame-layout obligation of the byte-addressed route, discharged
    from the `stride` argument alone — `GraphColoringGeneric.selectColors_slotsSeparated`
    through `vsimdGraphColorAllocIn`. -/
theorem vsimdGraphColorAllocIn_slotsSeparated (width : Nat) (pool pinned : List String)
    (frameBase stride : Int) (block : List VsimdEntry) (hw : (width : Int) ≤ stride) :
    SlotsSeparated width (vsimdGraphColorAllocIn pool pinned frameBase stride block) :=
  selectColors_slotsSeparated width _ _ frameBase _ stride hw

/-- **The `%xmm` entry point's slots hold one whole 128-bit value each**: its 16-byte
    stride separates them at the `%xmm` frame's access width. -/
theorem vsimdGraphColorAllocXmm_slotsSeparated (pinned : List String) (frameBase : Int)
    (block : List VsimdEntry) :
    SlotsSeparated (byteWidth (VecFrameState 128))
      (vsimdGraphColorAllocXmm pinned frameBase block) := by
  rw [byteWidth_vecFrameState_xmm]
  exact vsimdGraphColorAllocIn_slotsSeparated 16 _ pinned frameBase 16 block (by decide)

/-- **The `%ymm` entry point's slots hold one whole 256-bit value each**: its 32-byte
    stride separates them at the `%ymm` frame's access width. -/
theorem vsimdGraphColorAllocYmm_slotsSeparated (pinned : List String) (frameBase : Int)
    (block : List VsimdEntry) :
    SlotsSeparated (byteWidth (VecFrameState 256))
      (vsimdGraphColorAllocYmm pinned frameBase block) := by
  rw [byteWidth_vecFrameState_ymm]
  exact vsimdGraphColorAllocIn_slotsSeparated 32 ymmPool pinned frameBase 32 block (by decide)

/-- **The `%zmm` entry point's slots hold one whole 512-bit value each**: its 64-byte
    stride separates them at the `%zmm` frame's access width. -/
theorem vsimdGraphColorAllocZmm_slotsSeparated (pinned : List String) (frameBase : Int)
    (block : List VsimdEntry) :
    SlotsSeparated (byteWidth (VecFrameState 512))
      (vsimdGraphColorAllocZmm pinned frameBase block) := by
  rw [byteWidth_vecFrameState_zmm]
  exact vsimdGraphColorAllocIn_slotsSeparated 64 zmmPool pinned frameBase 64 block (by decide)

/-- **A `%ymm` allocation at the general-purpose stride `8` has overlapping slots.** The
    two spills of the pressure block land 8 bytes apart while each holds 32 bytes, so the
    frame-layout obligation of the byte-addressed route fails: the byte range of one slot
    covers the first bytes of the other. The stride argument of
    `GraphColoringGeneric.selectColors` is what stands between the two allocations, and
    this is the statement that distinguishes them. -/
theorem pressureBlock_ymm_slots_overlap_at_stride_eight :
    ¬ SlotsSeparated (byteWidth (VecFrameState 256))
        (vsimdGraphColorAllocIn ["%ymm0"] [] 0 8 pressureBlock) := by
  rw [byteWidth_vecFrameState_ymm]
  decide

/-! ## 10. The frame-touching instruction

§6 spills to the slot pseudo-register `spillSlotName off`, so its target is a name and two
offsets are two names whatever their byte distance. §9 is over the frame, but the bodies its
sandwich quantifies over are sequences of spill stores rather than blocks that also compute,
and `VecFrameState w` holds one whole `BitVec w` per frame offset, so no store on it can
partially overwrite another slot.

`VsimdFrameInst n` is the instruction type where both are joined: an operator arm over
`n`-byte lane vectors together with a frame store and a frame load, stepped on the
byte-granular `Optimizer.ByteMemMachine.ByteFrame n`, where an access at `off` covers the
bytes `off, …, off + n - 1` and overlapping accesses alias. `evalVsimdFrameInst` writes the
frame at a byte offset for a store and reads it for a reload, `frameWritesOf` and
`regWritesOf` are the two write lists the
`Optimizer.ByteMemMachine.FrameStepMachine` laws bound a step by, and
`vsimdFrameSpillReload_sandwich` is the store/body/reload transparency with byte separation
of the slots as its hypothesis. `vsimdFrameSandwich_fails_without_separation` exhibits a
four-byte frame, a slot at `0` and a body writing the slot at `2` on which the conclusion
fails, so the hypothesis carries the statement. `vsimdFrameSandwich_of_slotsSeparated` reads
that hypothesis off `GenericRegAlloc.SlotsSeparated`, which each entry point's
`_slotsSeparated` theorem supplies.

`VsimdFrameInst.erase` is the def/use interface the allocator reads, and it sends a frame
store and a frame load to the `MachineModel VsimdEntry` spill and reload entries
(`erase_frameStore`, `erase_frameLoad`) — the traffic `GenericRegAlloc.rewriteBlock`
inserts, under the pseudo-register reading of the same instruction. -/

/-- One entry of a `vsimd` block over a byte-addressed frame: a vector operation, a spill
    store of a register to the frame slot at a byte offset, or a reload of that slot into a
    register. A register holds `n` bytes, the width of one frame access; the operator is per
    instruction and unconstrained, so a block of these covers every operator reading of a
    `vsimd` body carrying spill traffic. -/
inductive VsimdFrameInst (n : Nat) where
  /-- The binding `dst ← eval srcs`. -/
  | op (dst : String) (srcs : List String) (eval : List (Fin n → BitVec 8) → Fin n → BitVec 8)
  /-- The spill store: the `n` bytes at `off` take register `r`'s value. -/
  | frameStore (off : Int) (r : String)
  /-- The reload: register `r` takes the `n` bytes at `off`. -/
  | frameLoad (r : String) (off : Int)

/-- One instruction's effect on the byte frame: an operation writes its destination
    register, a spill store writes the `n` bytes at its offset, and a reload writes its
    register from those bytes. -/
def evalVsimdFrameInst {n : Nat} (m : ByteFrame n) : VsimdFrameInst n → ByteFrame n
  | .op d ss f => ByteFrame.setRegB m d (f (ss.map m.regs))
  | .frameStore off r => ByteFrame.storeB m off (m.regs r)
  | .frameLoad r off => ByteFrame.setRegB m r (ByteFrame.loadB m off)

/-- The `(byte offset, source register)` frame writes of an instruction: a spill store's
    slot, and nothing for the arms that write only a register. -/
def frameWritesOf {n : Nat} : VsimdFrameInst n → List (Int × String)
  | .op _ _ _ => []
  | .frameStore off r => [(off, r)]
  | .frameLoad _ _ => []

/-- The register names an instruction writes: an operation's destination, a reload's
    target, and nothing for a spill store, whose write goes to the frame. -/
def regWritesOf {n : Nat} : VsimdFrameInst n → List String
  | .op d _ _ => [d]
  | .frameStore _ _ => []
  | .frameLoad r _ => [r]

/-- The def/use interface of a frame instruction, as the `VsimdEntry` the allocator reads:
    an operation gives its destination and sources, and the spill store and reload give the
    slot pseudo-register entries. -/
def VsimdFrameInst.erase {n : Nat} : VsimdFrameInst n → VsimdEntry
  | .op d ss _ => ⟨d, ss⟩
  | .frameStore off r => ⟨spillSlotName off, [r]⟩
  | .frameLoad r off => ⟨r, [spillSlotName off]⟩

/-- A frame store erases to the spill-store entry of the `MachineModel VsimdEntry`
    instance — the instruction `GenericRegAlloc.rewriteBlock` inserts after a spilled
    definition. -/
theorem erase_frameStore {n : Nat} (off : Int) (r : String) :
    (VsimdFrameInst.frameStore off r : VsimdFrameInst n).erase
      = mkSpill (I := VsimdEntry) r off := rfl

/-- A frame load erases to the reload entry of the `MachineModel VsimdEntry` instance — the
    instruction `GenericRegAlloc.rewriteBlock` inserts before a spilled use. -/
theorem erase_frameLoad {n : Nat} (off : Int) (r : String) :
    (VsimdFrameInst.frameLoad r off : VsimdFrameInst n).erase
      = mkReload (I := VsimdEntry) r off := rfl

/-- **The frame-touching `vsimd` instruction set over the byte-granular frame.** The step,
    the two spill instructions, the frame and register write lists, and the two
    non-interference laws: a step changes no access separated from its frame writes (for a
    spill store this is `ByteFrame.loadB_storeB_sep`, for the other arms the frame is
    untouched) and no register outside its register writes. -/
instance instFrameStepMachineVsimdFrameInst (n : Nat) :
    FrameStepMachine (VsimdFrameInst (n + 1)) (ByteFrame (n + 1)) where
  toByteMemMachine := instByteMemMachineByteFrame n
  step := evalVsimdFrameInst
  mkFrameStore off r := .frameStore off r
  mkFrameLoad r off := .frameLoad r off
  frameWrites := frameWritesOf
  regWrites := regWritesOf
  step_mkFrameStore := by intro m off r; rfl
  step_mkFrameLoad := by intro m r off; rfl
  load_step_sep := by
    intro m i o h
    cases i with
    | op d ss f => exact ByteFrame.loadB_setRegB m d _ o
    | frameStore off r =>
      exact ByteFrame.loadB_storeB_sep m off o (m.regs r) (h (off, r) (List.mem_singleton_self _))
    | frameLoad r off => exact ByteFrame.loadB_setRegB m r _ o
  get_step_other := by
    intro m i r h
    cases i with
    | op d ss f =>
      exact ByteFrame.regs_setRegB_other m d r _ (fun hc => h (hc ▸ List.mem_singleton_self _))
    | frameStore off r' => rfl
    | frameLoad r' off =>
      exact ByteFrame.regs_setRegB_other m r' r _ (fun hc => h (hc ▸ List.mem_singleton_self _))

/-- The class step of the instance is `evalVsimdFrameInst`. -/
theorem step_eq_evalVsimdFrameInst {n : Nat} (m : ByteFrame (n + 1))
    (i : VsimdFrameInst (n + 1)) : FrameStepMachine.step m i = evalVsimdFrameInst m i := rfl

/-- The block semantics of the instance is the left fold of `evalVsimdFrameInst`. -/
theorem runFrameBlock_eq_foldl {n : Nat} (m : ByteFrame (n + 1))
    (block : List (VsimdFrameInst (n + 1))) :
    runFrameBlock m block = block.foldl evalVsimdFrameInst m := rfl

/-- **The spill/reload sandwich with the slot a byte range of the frame.** A value stored
    to the slot at byte offset `off`, a body whose every frame write is separated from that
    slot and which never writes `r`, then the reload before `r`'s use: the reload leaves the
    block's final state unchanged. Both hypotheses are needed and the separation one is what
    `VecFrameState w`'s cell-indexed frame cannot ask for; dropping it makes the conclusion
    false (`vsimdFrameSandwich_fails_without_separation`). -/
theorem vsimdFrameSpillReload_sandwich {n : Nat} (m : ByteFrame (n + 1)) (off : Int)
    (r : String) (mid rest : List (VsimdFrameInst (n + 1)))
    (hsep : ∀ i ∈ mid, ∀ p ∈ frameWritesOf i, SepAt (n + 1) p.1 off)
    (hreg : ∀ i ∈ mid, r ∉ regWritesOf i) :
    runFrameBlock m (.frameStore off r :: (mid ++ .frameLoad r off :: rest))
      = runFrameBlock m (.frameStore off r :: (mid ++ rest)) :=
  frameReload_sandwich m off r mid rest (fun i hi => ⟨hsep i hi, hreg i hi⟩)

/-- A four-byte frame whose register `"v"` holds `1` in every lane and whose other
    registers and every frame byte hold `0`. -/
def overlapFrame : ByteFrame 4 :=
  ⟨fun x => if x = "v" then (fun _ => 1) else (fun _ => 0), fun _ => 0⟩

/-- **The separation hypothesis carries the sandwich.** On a frame of 4-byte accesses, a
    value spilled to the slot at `0` and a body storing to the slot at `2` — offsets whose
    byte ranges overlap — the reload reads two bytes the body wrote, and the block with the
    reload reaches a different state from the block without it. So the conclusion of
    `vsimdFrameSpillReload_sandwich` does not hold of every body whose frame writes miss the
    slot's offset: it holds of the bodies whose writes miss the slot's bytes. -/
theorem vsimdFrameSandwich_fails_without_separation :
    ∃ (m : ByteFrame 4) (off : Int) (r : String) (mid rest : List (VsimdFrameInst 4)),
      (¬ ∀ i ∈ mid, ∀ p ∈ frameWritesOf i, SepAt 4 p.1 off) ∧
      runFrameBlock m (.frameStore off r :: (mid ++ .frameLoad r off :: rest))
        ≠ runFrameBlock m (.frameStore off r :: (mid ++ rest)) := by
  refine ⟨overlapFrame, 0, "r", [.frameStore 2 "v"], [], by decide, fun hEq => ?_⟩
  exact absurd (congrFun (congrArg (fun s => ByteFrame.regs s "r") hEq) 2) (by decide)

/-- **The sandwich's separation hypothesis read off a separated allocation.** When the
    body's frame writes go to slots of an allocation whose slots are pairwise separated at
    the access width, and none of them is the value's own slot, the byte separation the
    sandwich asks for follows. This is the join between the allocator's frame-layout
    obligation and the frame-level spill transparency. -/
theorem vsimdFrameSandwich_of_slotsSeparated {n : Nat} (decisions : List (String × Slot))
    (hsep : SlotsSeparated (n + 1) decisions) (m : ByteFrame (n + 1)) (off : Int) (r : String)
    (mid rest : List (VsimdFrameInst (n + 1))) (hoff : off ∈ slotOffsets decisions)
    (hmid : ∀ i ∈ mid, (∀ p ∈ frameWritesOf i, p.1 ∈ slotOffsets decisions ∧ p.1 ≠ off)
      ∧ r ∉ regWritesOf i) :
    runFrameBlock m (.frameStore off r :: (mid ++ .frameLoad r off :: rest))
      = runFrameBlock m (.frameStore off r :: (mid ++ rest)) :=
  vsimdFrameSpillReload_sandwich m off r mid rest
    (fun i hi p hp =>
      sepAt_of_slotsSeparated hsep hoff ((hmid i hi).1 p hp).1 ((hmid i hi).1 p hp).2)
    (fun i hi => (hmid i hi).2)

/-- **The `%ymm` allocation discharges the frame-level sandwich's hypothesis.** At the
    32-byte frame of the 256-bit file, a body whose spill stores go to other slots of a
    `vsimdGraphColorAllocYmm` allocation is separated from this one by
    `vsimdGraphColorAllocYmm_slotsSeparated`, so the reload before the value's use is a
    no-op. -/
theorem vsimdFrameSandwich_of_ymmAlloc (pinned : List String) (frameBase : Int)
    (block : List VsimdEntry) (m : ByteFrame 32) (off : Int) (r : String)
    (mid rest : List (VsimdFrameInst 32))
    (hoff : off ∈ slotOffsets (vsimdGraphColorAllocYmm pinned frameBase block))
    (hmid : ∀ i ∈ mid,
      (∀ p ∈ frameWritesOf i,
        p.1 ∈ slotOffsets (vsimdGraphColorAllocYmm pinned frameBase block) ∧ p.1 ≠ off)
      ∧ r ∉ regWritesOf i) :
    runFrameBlock m (.frameStore off r :: (mid ++ .frameLoad r off :: rest))
      = runFrameBlock m (.frameStore off r :: (mid ++ rest)) := by
  have hsep : SlotsSeparated 32 (vsimdGraphColorAllocYmm pinned frameBase block) := by
    have h := vsimdGraphColorAllocYmm_slotsSeparated pinned frameBase block
    rwa [byteWidth_vecFrameState_ymm] at h
  exact vsimdFrameSandwich_of_slotsSeparated (n := 31) _ hsep m off r mid rest hoff hmid

/-- **The `%xmm` allocation discharges the frame-level sandwich's hypothesis**, at the
    16-byte frame of the 128-bit file. -/
theorem vsimdFrameSandwich_of_xmmAlloc (pinned : List String) (frameBase : Int)
    (block : List VsimdEntry) (m : ByteFrame 16) (off : Int) (r : String)
    (mid rest : List (VsimdFrameInst 16))
    (hoff : off ∈ slotOffsets (vsimdGraphColorAllocXmm pinned frameBase block))
    (hmid : ∀ i ∈ mid,
      (∀ p ∈ frameWritesOf i,
        p.1 ∈ slotOffsets (vsimdGraphColorAllocXmm pinned frameBase block) ∧ p.1 ≠ off)
      ∧ r ∉ regWritesOf i) :
    runFrameBlock m (.frameStore off r :: (mid ++ .frameLoad r off :: rest))
      = runFrameBlock m (.frameStore off r :: (mid ++ rest)) := by
  have hsep : SlotsSeparated 16 (vsimdGraphColorAllocXmm pinned frameBase block) := by
    have h := vsimdGraphColorAllocXmm_slotsSeparated pinned frameBase block
    rwa [byteWidth_vecFrameState_xmm] at h
  exact vsimdFrameSandwich_of_slotsSeparated (n := 15) _ hsep m off r mid rest hoff hmid

/-- **The `%zmm` allocation discharges the frame-level sandwich's hypothesis**, at the
    64-byte frame of the 512-bit file. -/
theorem vsimdFrameSandwich_of_zmmAlloc (pinned : List String) (frameBase : Int)
    (block : List VsimdEntry) (m : ByteFrame 64) (off : Int) (r : String)
    (mid rest : List (VsimdFrameInst 64))
    (hoff : off ∈ slotOffsets (vsimdGraphColorAllocZmm pinned frameBase block))
    (hmid : ∀ i ∈ mid,
      (∀ p ∈ frameWritesOf i,
        p.1 ∈ slotOffsets (vsimdGraphColorAllocZmm pinned frameBase block) ∧ p.1 ≠ off)
      ∧ r ∉ regWritesOf i) :
    runFrameBlock m (.frameStore off r :: (mid ++ .frameLoad r off :: rest))
      = runFrameBlock m (.frameStore off r :: (mid ++ rest)) := by
  have hsep : SlotsSeparated 64 (vsimdGraphColorAllocZmm pinned frameBase block) := by
    have h := vsimdGraphColorAllocZmm_slotsSeparated pinned frameBase block
    rwa [byteWidth_vecFrameState_zmm] at h
  exact vsimdFrameSandwich_of_slotsSeparated (n := 63) _ hsep m off r mid rest hoff hmid

end CatCrypt.Crypto.SecureCompilation.X86Backend.VsimdGraphColorRegAlloc
