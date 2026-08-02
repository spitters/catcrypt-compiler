/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.GenericRegAlloc
import CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-!
# Whole-block spill/reload well-formedness and the memory footprint of `spillReloadBlock`

`SpillingRegAlloc.spillReload_sandwich_runBlock` is the proved per-spill core: a
single spilled value's `store / mid / reload` sandwich around `use :: rest`
denotes the same as `store :: mid ++ rest` when the spill cell still holds the
register at the reload (`hmid`). `SpillingRegAlloc.lean` §6 lists the two
structural facts a whole-block lifting would carry — distinct live cells and no
intervening write to a spilled cell — and this module states them as a decidable
`SpillWellFormed` predicate.

The section also records the exact memory footprint of the materialization. Each
spilled name `n` has, appended after its defining instruction, a
`storeMem spillBase off (.reg n)` (`SpillingRegAlloc.spillRewriteInstr`). Under
`evalInstr` a `storeMem` writes the memory cell `(spillBase, off)`
(`JasminModel.evalInstr` / `JState.store`), and `runBlock` returns the full
`JState`, memory included. The original block never uses `spillBase` as a memory
base, so it leaves those cells at their input value. Hence the materialized block
and the original block differ, on the final state, exactly at the spill cells:
`spillReloadBlock` is `runBlock`-equal to the original block only when it inserts
no spill stores at all (the no-spill case, where it is literally the identity).
`spillReloadBlock_store_residue` witnesses this on a well-formed single-spill
block.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SpillReloadBlockSound

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-! ## 1. The whole-block well-formedness predicate (`SpillingRegAlloc.lean` §6)

`SpillWellFormed` gathers the two structural conditions §6 names as sufficient for
the per-spill sandwich's `hmid` to hold at every reload:

1. **Distinct live cells** — the spilled byte offsets are pairwise distinct, so no
   two spilled names share a frame cell and a reload of one cell never reads a
   value a different spilled name's store wrote. `SpillWellFormedSep` is the byte-level
   refinement: the offsets' `width`-byte ranges are pairwise disjoint, which distinctness
   implies only for values no wider than the offset spacing.
2. **Cell disjointness and single def** — `spillBase` is not a register/base name
   used anywhere in the block (so the original block never reads or writes any
   spill cell), and every spilled name is written exactly once (straight-line SSA),
   so between a spilled name's def-store and each of its reloads the cell is written
   only by that one store. -/

/-- The spilled byte offsets recorded in `decisions`. -/
def spilledOffsets (decisions : List (String × Slot)) : List Int :=
  decisions.filterMap (fun d => match d.2 with | .spilled off => some off | _ => none)

/-- The names `decisions` marks as spilled. -/
def spilledNames (decisions : List (String × Slot)) : List String :=
  decisions.filterMap (fun d => match d.2 with | .spilled _ => some d.1 | _ => none)

/-- The number of instructions in `block` that write register name `n`. -/
def defCount (block : List (JInstr 64)) (n : String) : Nat :=
  (block.filter (fun i => (writtenNames i).contains n)).length

/-- **Whole-block spill well-formedness (`SpillingRegAlloc.lean` §6).** Decidable
    conjunction of: the spilled offsets are distinct; `spillBase` is disjoint from
    the block's register/base names; and each spilled name is written exactly once.

    The first conjunct is offset distinctness, which is the condition the cell-indexed
    frame of `SpillingRegAlloc`/`GenericRegAlloc.MemMachine` needs. Its byte-level
    refinement is `SpillWellFormedSep`. -/
def SpillWellFormed (decisions : List (String × Slot)) (spillBase : String)
    (block : List (JInstr 64)) : Bool :=
  decide ((spilledOffsets decisions).Nodup)
    && (! (blockNames block).contains spillBase)
    && (spilledNames decisions).all (fun n => defCount block n == 1)

/-- **Byte separation of the spilled offsets**: the `width`-byte ranges of any two spill
    slots are disjoint (`GenericRegAlloc.SepAt`). At `width = 8` on 8-byte-aligned offsets
    this coincides with distinctness; at a wider value it is strictly stronger, since two
    distinct offsets closer together than `width` overlap. -/
def SpillSeparated (width : Nat) (decisions : List (String × Slot)) : Bool :=
  decide ((spilledOffsets decisions).Pairwise (GenericRegAlloc.SepAt width))

/-- **Whole-block well-formedness with byte-separated slots.** `SpillWellFormed` with its
    offset-distinctness conjunct replaced by byte separation at the width of one spilled
    value. This is the form a spill/reload argument over a byte-addressed frame
    (`Optimizer.ByteMemMachine`) needs, and `GraphColoringGeneric.selectColors_slotsSeparated`
    /`GenericRegAlloc.linearScan_slotsSeparated` discharge its first conjunct from the
    allocator's frame stride. -/
def SpillWellFormedSep (width : Nat) (decisions : List (String × Slot)) (spillBase : String)
    (block : List (JInstr 64)) : Bool :=
  SpillSeparated width decisions
    && (! (blockNames block).contains spillBase)
    && (spilledNames decisions).all (fun n => defCount block n == 1)

/-- **The separated form refines the distinct form.** At a positive value width, byte
    separation implies offset distinctness, so `SpillWellFormedSep` implies
    `SpillWellFormed` and every result stated under the latter applies. The converse fails:
    the offsets `0` and `8` are distinct and their 32-byte ranges overlap. -/
theorem spillWellFormed_of_spillWellFormedSep {width : Nat} (hw : 0 < width)
    {decisions : List (String × Slot)} {spillBase : String} {block : List (JInstr 64)}
    (h : SpillWellFormedSep width decisions spillBase block = true) :
    SpillWellFormed decisions spillBase block = true := by
  simp only [SpillWellFormedSep, SpillSeparated, SpillWellFormed, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  exact ⟨⟨h.1.1.imp (GenericRegAlloc.SepAt.ne hw), h.1.2⟩, h.2⟩

/-! ## 2. The memory footprint of the materialization

For a spilled name, `spillReloadBlock` appends a `storeMem spillBase off (.reg n)`
after its def; this store writes cell `(spillBase, off)`. The original block does
not use `spillBase` as a base, so it leaves that cell untouched. The two blocks
therefore reach different final memories at the spill cells — the reloads are
removable under the well-formedness invariant, but the stores write memory and
those writes persist in the `runBlock` result. -/

/-- A single-instruction block defining `"a"`, allocated to a spill cell. -/
def wfBlock : List (JInstr 64) := [JInstr.mov "a" (.imm 1)]

/-- `"a"` spilled to frame offset `0`. -/
def wfDecisions : List (String × Slot) := [("a", .spilled 0)]

/-- The witness block is well-formed: one spilled offset, `spillBase` `"%rbp"`
    disjoint from the block's names, `"a"` written exactly once. -/
theorem wf_holds : SpillWellFormed wfDecisions "%rbp" wfBlock = true := by decide

/-- The witness block is well-formed in the separated form too, at every value width: its
    single slot has no other slot to overlap. -/
theorem wf_sep_holds (width : Nat) :
    SpillWellFormedSep width wfDecisions "%rbp" wfBlock = true := by
  have hsep : SpillSeparated width wfDecisions = true := by
    simp [SpillSeparated, wfDecisions, spilledOffsets]
  have hbase : (! (blockNames wfBlock).contains "%rbp") = true := by decide
  have hdef : (spilledNames wfDecisions).all (fun n => defCount wfBlock n == 1) = true := by
    decide
  simp only [SpillWellFormedSep, hsep, hbase, hdef, Bool.and_true]

/-- **The frame layout that is well-formed for a word-sized spill is not well-formed for a
    256-bit one.** Two slots 8 bytes apart are separated at the general-purpose width and
    overlap at a `%ymm` value's width, so the predicate distinguishes the two allocations
    that offset distinctness cannot. -/
theorem wordStride_separated_iff_width :
    SpillSeparated 8 [("a", .spilled 0), ("b", .spilled 8)] = true
      ∧ SpillSeparated 32 [("a", .spilled 0), ("b", .spilled 8)] = false := by decide

/-- The materialization appends the def-store: `spillReloadBlock` of the witness is
    the original `mov` followed by `storeMem "%rbp" 0 (.reg "a")`. -/
theorem wf_spillReloadBlock :
    spillReloadBlock wfDecisions "%rbp" wfBlock
      = [JInstr.mov "a" (.imm 1), JInstr.storeMem "%rbp" 0 (.reg "a")] := by
  rfl

/-- **The spill store persists in the final memory.** On a well-formed single-spill
    block the materialized block and the original block reach different final
    states: the materialized block's def-store leaves `1` in the spill cell
    `("%rbp", 0)`, while the original block leaves it at its input value `0`. This is
    the exact obstruction to `runBlock s (spillReloadBlock …) = runBlock s block`:
    the inserted spill stores are real memory writes, observable in the full
    `runBlock` state, so the equality holds only in the no-spill (identity) case. -/
theorem spillReloadBlock_store_residue :
    let s : JState 64 := { regs := fun _ => 0 }
    (runBlock s (spillReloadBlock wfDecisions "%rbp" wfBlock)).mem "%rbp" 0
      ≠ (runBlock s wfBlock).mem "%rbp" 0 := by
  intro s
  rw [wf_spillReloadBlock]
  simp only [wfBlock, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval,
    x86_MOV, JState.setReg, JState.get, JState.store]
  decide

end CatCrypt.Crypto.Optimizer.SpillReloadBlockSound
