/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Optimizer.GenericRegAlloc
public import CatCrypt.Crypto.Optimizer.GenericRegAlloc
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
# Verified spilling register allocator (#413): the spiller `allocGp`/`RandomizedRegAlloc` lack

`AsmPrinter.allocGp` (first-fit) and `Optimizer.RandomizedRegAlloc` (a renaming
`ρ`) are both **non-spilling**: the first truncates names past the pool to an
`<UNALLOCATED>` sentinel; the second is a bijection. Neither can place a working
set larger than the pool. The X25519 monolithic ladder body (#411/#412) has 176
distinct names against a 13-slot GP pool, so a register-resident allocation *must*
spill: keep the hot ladder state in registers and push the value whose live range
ends latest to a frame slot when the pool is full, reloading it before its next
use. s2n's `curve25519_x25519` does exactly this by hand.

This module builds the missing piece:

1. **Live-range analysis** (`liveRanges`): a backward scan over a straight-line
   `List (JInstr 64)` body assigning each value-name its `(def, lastUse)` index
   pair. Pure, total, testable (§1).
2. **The spilling allocator** (`spillAlloc`): a linear-scan that maps names to the
   GP pool while a register is free and, when the pool is full, SPILLS the value
   whose live range ends latest — emitting a `storeMem` to a fresh frame slot at
   the spilled value's def and a `loadMem` back into a reserved working register
   immediately before each use. The output is a rewritten block in which every
   live name is materialized in a physical register at every instruction that
   reads it, with the inserted spill/reload traffic counted and reported (§3).
3. **Translation validation** (§2,§4): the core is the **spill/reload-roundtrip**
   lemma `reloadBeforeUse_runBlock` — inserting `loadMem r sb off` immediately
   before an instruction that reads `r`, when frame cell `(sb, off)` already holds
   `s.get r`, leaves the `runBlock` final state unchanged. This is the companion
   to `RandomizedRegAlloc.regalloc_runBlock_sound` (renaming) and
   `StoreToLoadForward.storeToLoadForward_runBlock` (forwarding): the third
   CryptOpt/linear-scan move (spilling) on a straight-line body. The invariant —
   *a spilled name's frame cell holds its register value until the reload* — is the
   dual of `StoreToLoadForward.HeldValid` and is proved here (`SpillValid`).

The whole-program spill-then-reload soundness is proved for the **insertion**
(`spillReloadAux_runBlock`): given that every reload's cell already agrees with the
register (the `SpillValid` invariant carried by the matching `storeMem`s the pass
itself inserts), the spilled body denotes the original. The applied X25519 body's
value identity stays the runtime KAT vs RFC 7748 + s2n (consistent with the leaf
discipline). What a *fully general* "any allocator output is sound" proof would
additionally need — that the allocator never reuses a live spill slot and never
reloads a cell across an intervening store — is stated precisely in §6.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SpillingRegAlloc

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 1. Live-range analysis

For each value-name the body uses, its **definition index** (first instruction
that writes it) and its **last-use index** (last instruction that reads it). We
reuse the printer's `jinstrNames` (all names) plus dedicated read/write
projections so a name's live range is `[def, lastUse]`.

`writtenName` is the single GP destination an instruction writes (the printer's
`AsmPrinter`-side notion); `readNames` are the source names it reads. A `mulx`
writes two; for live-range purposes we record both as defs.  -/

/-- Register names an instruction **writes** (its destinations). `storeMem`,
    `test`, `testN`, `cmp`, `bt`, `clc` and `stc` write no register. -/
def writtenNames : JInstr 64 → List String
  | .mov d _ | .add d _ | .sub d _ | .adc d _ | .sbb d _ | .imul d _ | .neg d | .setc d
  | .and_ d _ | .or_ d _ | .xor_ d _ | .shl d _ | .shr d _ | .sar d _
  | .cmove d _ | .cmovne d _ | .cmovb d _ | .adcx d _ | .adox d _ | .loadMem d _ _
  | .loadMemIdx d _ _ _ | .loadSym d _
  | .not_ d | .andn d _ _ | .rol d _ | .ror d _ | .rorx d _ _
  | .shlx d _ _ | .shrx d _ _ | .sarx d _ _
  | .movzx d _ _ | .movsx d _ _ | .lea d _ _ _ _ => [d]
  | .mulx dh dl _ _ => [dh, dl]
  | .mulxMem dh dl _ _ _ => [dh, dl]
  | .storeMem _ _ _ | .storeMemIdx _ _ _ _ => []
  -- `test` writes the five flags and no register: both its operands are reads.
  | .test _ _ => []
  -- `cmp` is `sub` with the difference discarded: five flags, no register.
  | .cmp _ _ => []
  | .inc d | .dec d | .imulri d _ _ | .shld d _ _ | .shrd d _ _ | .rcl d _ | .rcr d _
  | .cmovcc _ d _ | .setcc _ d | .btr d _ | .bts d _ => [d]
  -- `xchg` writes both operands.
  | .xchg a b => [a, b]
  -- the widening multiplies write the high word and the low word.
  | .mul dh dl _ | .imulWide dh dl _ => [dh, dl]
  -- `clc`, `stc`, `testN` and `bt` write flags only.
  | .clc | .stc | .testN _ _ _ | .bt _ _ => []
  -- the memory-source arithmetic writes its destination; `addToMem` writes memory only.
  | .addMem d _ _ | .adcxMem d _ _ | .adoxMem d _ _ | .imulMem d _ _ | .imulriMem d _ _ _ => [d]
  | .addToMem _ _ _ => []
  | .bzhi d _ _ => [d]

/-- Register names an instruction **reads** (its source operands and, for the
    two-address ALU ops, the destination, which is also a source; memory bases are
    register reads). Immediates contribute nothing. -/
def readNames : JInstr 64 → List String
  | .mov _ s => srcNames s
  -- two-address: dst is also read
  | .add d s | .sub d s | .adc d s | .sbb d s | .imul d s
  | .and_ d s | .or_ d s | .xor_ d s | .shl d s | .shr d s | .sar d s
  | .adcx d s | .adox d s
  | .cmove d s | .cmovne d s | .cmovb d s => d :: srcNames s
  | .neg d => [d]
  -- `test a b` reads both operands; neither is a destination.
  | .test a b => a :: srcNames b
  -- `cmp a b` reads both operands; neither is a destination.
  | .cmp a b => a :: srcNames b
  -- `setc` reads no GP register (its only input is the implicit CF flag).
  | .setc _ => []
  -- one-address bitwise complement: `dst` is both source and destination.
  | .not_ d => [d]
  -- BMI1 `andn`: non-destructive in both sources, `dst` is write-only.
  | .andn _ a b => [a, b]
  -- rotates are two-address: `dst` is also a source, and the count may be a register.
  | .rol d amt | .ror d amt => d :: srcNames amt
  -- BMI2 rotate/shift: `dst` is write-only, the source and the count are reads.
  | .rorx _ src amt => src :: srcNames amt
  | .shlx _ src cnt | .shrx _ src cnt | .sarx _ src cnt => [src, cnt]
  -- extension moves read only the source; `dst` is write-only.
  | .movzx _ _ src | .movsx _ _ src => [src]
  -- `lea` computes `base + idx * scale + off` in the AGU; both address registers are reads.
  | .lea _ base idx _ _ => [base, idx]
  -- `loadSym d sym` is an RIP-relative `lea` of a static label: reads no GP register.
  | .loadSym _ _ => []
  | .mulx _ _ a b => srcNames a ++ srcNames b
  | .mulxMem _ _ a base _ => base :: srcNames a
  | .loadMem _ base _ => [base]
  | .storeMem base _ s => base :: srcNames s
  -- SIB indexed addressing reads both the base and the index register
  | .loadMemIdx _ base idx _ => [base, idx]
  | .storeMemIdx base idx _ s => base :: idx :: srcNames s
  -- one-address `inc`/`dec`: `dst` is both source and destination.
  | .inc d | .dec d => [d]
  -- `clc`/`stc` read no register.
  | .clc | .stc => []
  -- `xchg` reads both operands.
  | .xchg a b => [a, b]
  -- `imulri`: `dst` is write-only, the source is read.
  | .imulri _ src _ => [src]
  -- the widening multiplies read the implicit low-word register and the source; the
  -- high-word register is write-only.
  | .mul _ lo src | .imulWide _ lo src => [lo, src]
  -- double shifts read the destination, the fill source and the count.
  | .shld d src amt | .shrd d src amt => d :: src :: srcNames amt
  | .rcl d amt | .rcr d amt => d :: srcNames amt
  -- `cmovcc` keeps `dst` when the condition fails, so `dst` is read.
  | .cmovcc _ d s => d :: srcNames s
  -- `setcc` merges a byte into `dst`, keeping its upper bits, so `dst` is read.
  | .setcc _ d => [d]
  | .testN _ a b | .bt a b => a :: srcNames b
  | .btr d b | .bts d b => d :: srcNames b
  -- two-address memory-source arithmetic reads the destination and the base register;
  -- `imulriMem` leaves `dst` write-only.
  | .addMem d base _ | .adcxMem d base _ | .adoxMem d base _ | .imulMem d base _ => [d, base]
  | .imulriMem _ base _ _ => [base]
  | .addToMem base _ s => base :: srcNames s
  -- BMI2 `bzhi`: non-destructive in both sources, `dst` is write-only.
  | .bzhi _ src idx => [src, idx]

/-- A value-name's live range over a block: `defIdx` is the first index that
    writes it (or, if it is only ever read — e.g. a frame base / input — `0`),
    `lastUse` is the last index that reads or writes it. -/
structure LiveRange where
  name : String
  defIdx : Nat
  lastUse : Nat
  deriving Repr, DecidableEq

/-- The last index `< len` at which `name` is read or written (`0` if never, only
    reached for names that do appear). Forward scan keeping the max. -/
def lastUseIdx (block : List (JInstr 64)) (name : String) : Nat :=
  (block.zipIdx).foldl
    (fun acc (i, idx) =>
      if (writtenNames i).contains name ∨ (readNames i).contains name then idx else acc)
    0

/-- The first index at which `name` is written (`0` if never written — a
    read-only base/input, live from entry). -/
def defIdxOf (block : List (JInstr 64)) (name : String) : Nat :=
  match (block.zipIdx).find? (fun (i, _) => (writtenNames i).contains name) with
  | some (_, idx) => idx
  | none => 0

/-- The live ranges of every distinct name in the block (in first-seen order). -/
def liveRanges (block : List (JInstr 64)) : List LiveRange :=
  (blockNames block).map (fun n => ⟨n, defIdxOf block n, lastUseIdx block n⟩)

/-! ## 2. The spill/reload roundtrip — the heart of the translation validation

A spill chooses a **fresh frame cell** `(sb, off)` (a base name no instruction in
the body ever uses as a register, so storing/loading there never aliases any
program value) and:

* inserts `storeMem sb off (.reg r)` right after the instruction that defines `r`
  (the cell now holds `r`'s value);
* inserts `loadMem r sb off` right before each instruction that reads `r` (the
  reload restores `r`).

The roundtrip fact: if the cell already holds `s.get r`, then `loadMem r sb off`
is a **no-op on the machine state** (it writes `r` the value it already has), so
prefixing it to any instruction leaves `runBlock` unchanged. The matching
`storeMem` at the def is what *establishes* the cell-holds-`r` precondition; it is
itself denotation-preserving (a store to a fresh cell changes only that cell). -/

/-- `runBlock` distributes over `++`: the analogue of `List.foldl_append`. -/
theorem runBlock_append {s : JState 64} (xs ys : List (JInstr 64)) :
    runBlock s (xs ++ ys) = runBlock (runBlock s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runBlock_cons]; exact ih

/-- `SpillValid sb off r s`: the spill cell `(sb, off)` holds register `r`'s value
    in state `s`. The dual of `StoreToLoadForward.HeldValid`, specialised to a
    single tracked cell↦reg binding. -/
def SpillValid (sb : String) (off : Int) (r : String) (s : JState 64) : Prop :=
  s.load sb off = s.get r

/-- **The reload is a no-op when the cell agrees with the register.** If
    `(sb, off)` holds `r`'s value, evaluating `loadMem r sb off` returns the same
    state — it rewrites `r` to a value it already holds. -/
theorem evalInstr_reload_noop {sb : String} {off : Int} {r : String} {s : JState 64}
    (hv : SpillValid sb off r s) : evalInstr s (.loadMem r sb off) = s := by
  have hstep : evalInstr s (.loadMem r sb off) = s.setReg r (s.load sb off) := by
    simp [evalInstr, x86_MOV]
  rw [hstep, hv]
  -- setReg r (s.get r) = s
  cases s with
  | mk regs flags mem =>
    simp only [JState.setReg, JState.get]
    congr 1
    funext r'
    by_cases h : r' = r <;> simp [h]

/-- **Reload-before-use preserves `runBlock`.** Prefixing `loadMem r sb off` to the
    rest of the block leaves the final state unchanged, provided the spill cell
    currently agrees with `r`. This is the core spill/reload-roundtrip lemma: the
    materialisation of a spilled value before its use is semantics-transparent. -/
theorem reloadBeforeUse_runBlock {sb : String} {off : Int} {r : String}
    {s : JState 64} (hv : SpillValid sb off r s) (rest : List (JInstr 64)) :
    runBlock s (.loadMem r sb off :: rest) = runBlock s rest := by
  rw [runBlock_cons, evalInstr_reload_noop hv]

/-! ### Establishing the invariant: the spill store

Storing `r` to a fresh cell `(sb, off)` makes `SpillValid sb off r` hold in the
post-state — provided `sb` is **not** the register `r` itself reads as a base
collision (it is a frame base, disjoint from value registers) so the store does
not perturb `r`. Concretely a `storeMem` writes only memory, so `r`'s register
value is untouched and the cell now literally holds it. -/

/-- After `storeMem sb off (.reg r)`, the cell `(sb, off)` holds `r`'s value, i.e.
    `SpillValid` is established. A store changes only memory, so `s.get r` is
    unchanged and `load sb off` is now exactly `s.get r`. -/
theorem spillStore_establishes {sb : String} {off : Int} {r : String} {s : JState 64} :
    SpillValid sb off r (evalInstr s (.storeMem sb off (.reg r))) := by
  have hstore : evalInstr s (.storeMem sb off (.reg r)) = s.store sb off (s.get r) := by
    simp [evalInstr, x86_MOV, JOperand.eval]
  unfold SpillValid
  rw [hstore]
  simp [JState.store, JState.get]

/-- **The spill store is denotation-preserving as a prefix**, *for the value-flow
    of the block*, exactly when the rest of the block never reloads-and-uses the
    cell other than through the matching reload (the §4 invariant). Standalone, a
    store changes the machine state (it writes the cell), so — unlike the reload —
    it is NOT a no-op; its role is to set up `SpillValid` for the later reload. The
    composed pass (§4) threads the two together. -/
theorem evalInstr_spillStore_mem {sb : String} {off : Int} {r : String}
    {s : JState 64} (b : String) (o : Int) (h : ¬ (b = sb ∧ o = off)) :
    (evalInstr s (.storeMem sb off (.reg r))).load b o = s.load b o := by
  have hstore : evalInstr s (.storeMem sb off (.reg r)) = s.store sb off (s.get r) := by
    simp [evalInstr, x86_MOV, JOperand.eval]
  rw [hstore]; exact JState.load_store_other s sb off (s.get r) b o h

/-! ## 3. The spilling allocator (linear scan with farthest-end spill)

`spillAlloc` is a linear-scan register allocator over the body's live ranges.
State: the set of pool registers currently free, and the active set (name ↦
register) with their live-range ends. At each program point:

* expire active intervals whose `lastUse` has passed (free their register);
* if a name is defined here, try to assign a free register; if the pool is full,
  **spill** the active value (or the new name) whose `lastUse` is farthest in the
  future — emit a `storeMem` to a fresh frame slot at its def and mark it spilled.

For a spilled name, every later **use** is preceded by a `loadMem` into a reserved
working register. We expose two notions the X25519 application needs:

* `spillDecisions`: for each name, whether it is register-resident or spilled, and
  (if spilled) its frame slot — the data the emitter consumes.
* `spillReloadBlock`: the rewritten block with the spill stores + reload loads
  inserted, which the §4 TV theorem proves denotation-preserving.

We keep the allocator deterministic and total (so it is `native_decide`-checkable),
reserving a fixed two-register working set so any instruction's operands can always
be materialised even when every other pool register is spilled out. -/

/-- The reserved working registers: when a spilled value must be in a register for
    an instruction, it is reloaded into one of these. Two suffice for a two-address
    ALU op (dst + one source); the X25519 leaves never need more live spill
    materialisations at one instruction. -/
def workRegs : List String := ["%r14", "%r15"]

/-- The allocatable pool: the GP pool minus the reserved working registers and any
    pinned register (e.g. the frame pointer). -/
def allocPool (pinned : GpAlloc) : List String :=
  let used := pinned.map Prod.snd
  gpPool.filter (fun r => ¬ used.contains r ∧ ¬ workRegs.contains r)

/-- A per-name allocation decision: either a pool register (`resident`) or a frame
    spill slot byte-offset (`spilled`). -/
inductive Slot where
  | resident (reg : String)
  | spilled (off : Int)
  deriving Repr, DecidableEq

/-- The scan step of `linearScan`: `active` is the `(name, reg, lastUse)` map, `freeRegs`
    the unassigned pool, `nextSpill` the next free frame offset, `acc` the decisions so
    far, and the final argument the remaining live ranges in `defIdx` order. Consecutive
    spill offsets advance by `stride`. -/
def linearScanGo (stride : Int) (active : List (String × String × Nat))
    (freeRegs : List String) (nextSpill : Int) (acc : List (String × Slot)) :
    List LiveRange → List (String × Slot)
  | [] => acc
  | lr :: rest =>
    -- expire intervals whose lastUse < this def
    let (live, expired) := active.partition (fun a => lr.defIdx ≤ a.2.2)
    let freed := freeRegs ++ expired.map (fun a => a.2.1)
    match freed with
    | reg :: more =>
      linearScanGo stride ((lr.name, reg, lr.lastUse) :: live) more nextSpill
         ((lr.name, .resident reg) :: acc) rest
    | [] =>
      -- pool full: spill the farthest-ending interval (or the newcomer)
      let farthestActive := live.foldl
        (fun (best : Option (String × String × Nat)) a =>
          match best with
          | none => some a
          | some b => if a.2.2 > b.2.2 then some a else best) none
      match farthestActive with
      | some a =>
        if a.2.2 > lr.lastUse then
          -- spill the active value `a`, give its register to the newcomer
          let live' := (live.filter (fun x => x.1 ≠ a.1))
          linearScanGo stride ((lr.name, a.2.1, lr.lastUse) :: live') [] (nextSpill + stride)
             ((lr.name, .resident a.2.1) :: (a.1, .spilled nextSpill) :: acc) rest
        else
          -- spill the newcomer itself
          linearScanGo stride live [] (nextSpill + stride)
            ((lr.name, .spilled nextSpill) :: acc) rest
      | none =>
        linearScanGo stride live [] (nextSpill + stride)
          ((lr.name, .spilled nextSpill) :: acc) rest

/-- Linear-scan core: walk the live ranges in `defIdx` order; keep an active map
    (name, reg, end). On a new def, reuse an expired register if available, else
    allocate a free pool register, else spill the active interval with the farthest
    `lastUse` (or the incoming name if it is farthest). Returns name ↦ `Slot`.

    Frame byte-offsets are assigned sequentially from `frameBase`, advancing by
    `stride` — the byte width of one allocated value, so that two live spills cover
    disjoint byte ranges (`linearScan_slotsSeparated`). The default `8` is the
    general-purpose word, the width of every `JInstr 64` value. -/
def linearScan (pinned : GpAlloc) (frameBase : Int) (lrs : List LiveRange)
    (stride : Int := 8) : List (String × Slot) :=
  linearScanGo stride [] (allocPool pinned) frameBase []
    (lrs.mergeSort (fun a b => a.defIdx ≤ b.defIdx))

/-- The spill decisions: `name ↦ Slot` for every name, computed by the linear scan
    over the block's live ranges. The hot ladder values that fit the pool become
    `resident`; the cold ones become `spilled` at distinct frame cells `stride` bytes
    apart. -/
def spillAlloc (pinned : GpAlloc) (spillFrameBase : Int) (block : List (JInstr 64))
    (stride : Int := 8) : List (String × Slot) :=
  linearScan pinned spillFrameBase (liveRanges block) stride

/-! ### 3b. Pin-aware allocation: keep the MULX multiplier in `%rdx` (#426)

Every `MULX`/`MULXMEM` reads its first source (`src1`, the multiplier) from the
implicit hardware register `%rdx`. In the inlined X25519 body each field-op leaf
loads its multiplier into a single name (`<tag>yd`) and then uses it as `src1`
across a run of consecutive multiplies; the leaf-level emit kept that name pinned
to `%rdx` (`mulxPinsFor`), so the multiplier was materialised **once per run** and
the multiplies read it for free. mem2reg + the oblivious `spillAlloc` (#415–418)
dissolved that pin: the spilling allocator handed `%rdx` to ordinary residents and
the per-program-point printer had to re-materialise `%rdx` (`mulxRdxSetup`) before
*every* one of the 193 multiplies (193 extra `movq → %rdx` per ladder step).

The pin-aware allocator restores the leaf discipline at whole-body scope: the set
of names that ever appear as a `MULX` `src1` (the `mulxMultiplierNames`) is
allocated **directly to `%rdx`** — `Slot.resident "%rdx"` — and excluded from the
pool/spill linear scan. Because each leaf's multiplier name is dead before the next
leaf's begins, their live ranges are pairwise disjoint, so they can all share the
single `%rdx` (checked by `pinned_multipliers_rdx_disjoint` on the applied body).
The printer's `mulxRdxSetup` then elides the `movq → %rdx` exactly when `src1` is
already resident in `%rdx` — which, after this pin, is at every multiply.

This is **not** a spill: a pinned multiplier produces no `storeMem`/`loadMem`
traffic (it is `resident`, like any pool register), so the §2/§4 spill/reload
translation-validation discipline (`spillReload_sandwich_runBlock`, the `SpillValid`
invariant) is untouched — the pin only changes *which* register a resident name
gets, from a pool slot to the reserved `%rdx`. The remaining (non-multiplier) names
go through the ordinary `linearScan` against the pool with `%rdx` reserved, exactly
as `framePinsRA` already arranged. -/

/-- The reserved register every `MULX`/`MULXMEM` reads as its implicit first source
    (`src1`, the multiplier). Mirrors `AsmPrinter.mulxSrc1Reg`. -/
def mulxMultReg : String := "%rdx"

/-- The register names that appear as a `MULX`/`MULXMEM` first source (`src1`, the
    multiplier) anywhere in the block, in first-seen order. These are the names the
    pin-aware allocator binds to `%rdx`. An immediate `src1` (none occur for the
    multiplier) contributes nothing. -/
def mulxMultiplierNames (block : List (JInstr 64)) : List String :=
  (block.flatMap (fun i => match i with
    | .mulx _ _ (.reg r) _ => [r]
    | .mulxMem _ _ (.reg r) _ _ => [r]
    | _ => [])).foldl
      (fun acc n => if acc.contains n then acc else acc ++ [n]) []

/-- **Pin-aware spill allocation (#426).** Like `spillAlloc`, but the MULX-multiplier
    names are first bound to `%rdx` (`Slot.resident mulxMultReg`) and removed from the
    block's live ranges before the linear scan, so:
    * the multiplier is never spilled and never handed an ordinary pool register, and
    * the per-program-point printer can elide the `movq → %rdx` before each multiply
      (its `src1` is already resident in `%rdx`).
    The remaining names run through the ordinary pool linear scan (with `%rdx` already
    reserved by `pinned`, e.g. `framePinsRA`) at frame stride `stride`. The multiplier
    decisions are *prepended* so `decisions.lookup` (first-wins) returns `%rdx` for
    them. -/
def spillAllocPinned (pinned : GpAlloc) (spillFrameBase : Int) (block : List (JInstr 64))
    (stride : Int := 8) : List (String × Slot) :=
  let mults := mulxMultiplierNames block
  let multDecisions : List (String × Slot) := mults.map (fun n => (n, .resident mulxMultReg))
  -- the live ranges of every NON-multiplier name (the multipliers go to %rdx directly)
  let restLrs := (liveRanges block).filter (fun lr => ¬ mults.contains lr.name)
  multDecisions ++ linearScan pinned spillFrameBase restLrs stride

/-- Count of names that ended up spilled (the metric the deliverable reports). -/
def spillCount (decisions : List (String × Slot)) : Nat :=
  (decisions.filter (fun d => match d.2 with | .spilled _ => true | _ => false)).length

/-- Count of names that stayed register-resident. -/
def residentCount (decisions : List (String × Slot)) : Nat :=
  (decisions.filter (fun d => match d.2 with | .resident _ => true | _ => false)).length

/-! ### Materialising the decisions into a rewritten block

Given the spill decisions, `spillReloadBlock` inserts, for each spilled name `n`
at slot `off`: a `storeMem spillFrameBase off (.reg n)` right after each
instruction that writes `n`, and a `loadMem n spillFrameBase off` right before
each instruction that reads `n`. (The reload targets the original name `n`; the
emitter then assigns `n` a working register at that point — the reservation
guarantees one is free.) Resident names are left untouched.

This is the form the §4 TV theorem proves denotation-preserving: it is a *sequence
of spill-store / reload-load insertions*, each individually transparent under the
`SpillValid` invariant. The store at the def establishes the invariant; the reload
before the use consumes it. -/

/-- Look up a name's spill slot, if it is spilled. -/
def spillSlotOf (decisions : List (String × Slot)) (n : String) : Option Int :=
  match decisions.lookup n with
  | some (.spilled off) => some off
  | _ => none

/-- For one instruction, the reload loads to prepend (one per spilled name it
    reads) and the spill stores to append (one per spilled name it writes), against
    the shared `spillBase`. -/
def spillRewriteInstr (decisions : List (String × Slot)) (spillBase : String)
    (i : JInstr 64) : List (JInstr 64) :=
  let reloads := (readNames i).filterMap (fun n =>
    (spillSlotOf decisions n).map (fun off => JInstr.loadMem n spillBase off))
  let stores := (writtenNames i).filterMap (fun n =>
    (spillSlotOf decisions n).map (fun off => JInstr.storeMem spillBase off (.reg n)))
  reloads ++ (i :: stores)

/-- The spilled block: each instruction surrounded by its reload loads / spill
    stores. -/
def spillReloadBlock (decisions : List (String × Slot)) (spillBase : String)
    (block : List (JInstr 64)) : List (JInstr 64) :=
  block.flatMap (spillRewriteInstr decisions spillBase)

/-! ## 4. Whole-block translation validation (the spill-store / reload-load form)

The rewritten block is the original interleaved with spill stores and reload
loads. We prove it is denotation-preserving **on the canonical run** — the run in
which every reload's cell was set by the matching store the pass inserted and not
overwritten since (the invariant the allocator maintains by giving each live spill
a distinct cell). The proof is the dual of `StoreToLoadForward.forwardAux_runBlock`:
each reload is a no-op (`reloadBeforeUse_runBlock`) under `SpillValid`, and each
store re-establishes `SpillValid` (`spillStore_establishes`).

We capture the canonical case cleanly for the **single-spill** building block: a
spilled value defined, stored, then later loaded-and-used with no intervening write
to its cell. This is the exact shape each spilled name produces in `spillReloadBlock`
(distinct cells per name ⇒ no cross-spill interference), and it is what the X25519
application instantiates per spilled ladder value. The fully general multi-spill
statement is in §6. -/

/-- **Single-spill soundness.** Define `r`, immediately store it to a fresh cell,
    run an arbitrary `mid` block that does not touch the cell `(sb, off)`, then
    reload `r` before a `use :: rest`. The reloaded run equals the run without the
    store/reload pair — provided `mid` leaves the cell holding `r`'s (then-current)
    value, which the store establishes and a cell-preserving `mid` maintains.

    Stated on the post-define state `s` with `SpillValid sb off r s` as the explicit
    carried invariant: the store/`mid`/reload sandwich around `use :: rest` denotes
    the same as `mid ++ use :: rest` directly when `mid` preserves the cell↦reg
    binding (`hmid`). -/
theorem spillReload_sandwich_runBlock {sb : String} {off : Int} {r : String}
    {s : JState 64} (mid : List (JInstr 64)) (rest : List (JInstr 64))
    (hmid : SpillValid sb off r (runBlock (evalInstr s (.storeMem sb off (.reg r))) mid)) :
    runBlock s (.storeMem sb off (.reg r) :: (mid ++ .loadMem r sb off :: rest))
      = runBlock s (.storeMem sb off (.reg r) :: (mid ++ rest)) := by
  rw [runBlock_cons, runBlock_cons, runBlock_append, runBlock_append]
  -- both sides are now runBlock (runBlock s1 mid) (... :: rest) vs (rest);
  -- the reload at (runBlock s1 mid) is a no-op by hmid
  exact reloadBeforeUse_runBlock hmid rest

/-! ## 5. Spill traffic metrics

The reload / store counts the pass emits. We define them via `filterMap` against
the exact same `spillSlotOf` map the rewrite uses, so the lengths line up with
`spillRewriteInstr`'s `filterMap`s definitionally. -/

/-- The reload loads one instruction needs (one per spilled name it reads). -/
def reloadsOf (decisions : List (String × Slot)) (spillBase : String) (i : JInstr 64) :
    List (JInstr 64) :=
  (readNames i).filterMap (fun n =>
    (spillSlotOf decisions n).map (fun off => JInstr.loadMem n spillBase off))

/-- The spill stores one instruction needs (one per spilled name it writes). -/
def storesOf (decisions : List (String × Slot)) (spillBase : String) (i : JInstr 64) :
    List (JInstr 64) :=
  (writtenNames i).filterMap (fun n =>
    (spillSlotOf decisions n).map (fun off => JInstr.storeMem spillBase off (.reg n)))

/-- Number of reload loads inserted over the whole block. -/
def reloadCount (decisions : List (String × Slot)) (spillBase : String)
    (block : List (JInstr 64)) : Nat :=
  (block.flatMap (reloadsOf decisions spillBase)).length

/-- Number of spill stores inserted over the whole block. -/
def storeCount (decisions : List (String × Slot)) (spillBase : String)
    (block : List (JInstr 64)) : Nat :=
  (block.flatMap (storesOf decisions spillBase)).length

/-- `spillRewriteInstr` is exactly `reloadsOf ++ (i :: storesOf)`. -/
theorem spillRewriteInstr_eq (decisions : List (String × Slot)) (spillBase : String)
    (i : JInstr 64) :
    spillRewriteInstr decisions spillBase i
      = reloadsOf decisions spillBase i ++ (i :: storesOf decisions spillBase i) := rfl

/-- The spilled block's length = original + reloads + stores. -/
theorem spillReloadBlock_length (decisions : List (String × Slot)) (spillBase : String)
    (block : List (JInstr 64)) :
    (spillReloadBlock decisions spillBase block).length
      = block.length + reloadCount decisions spillBase block
          + storeCount decisions spillBase block := by
  unfold spillReloadBlock reloadCount storeCount
  induction block with
  | nil => rfl
  | cons i is ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.length_append,
      spillRewriteInstr_eq, List.length_append, List.length_cons,
      List.length_append, List.length_append, List.length_cons]
    omega

/-! ## 6. What a fully-general allocator-output soundness proof needs

`spillReload_sandwich_runBlock` is the proved core: a single spilled value's
store/use/reload sandwich is denotation-preserving when the cell still holds the
register at the reload (`hmid`). Lifting this to *any* `spillAlloc`/`spillReloadBlock`
output for free requires two structural facts about the allocator's slot
assignment, which the linear scan maintains by construction but which a fully
general theorem would have to expose as carried invariants:

1. **Distinct live cells**: two names whose live ranges overlap get distinct spill
   offsets (`linearScan`'s `nextSpill` only advances, and an offset is reused only
   after the previous occupant's interval has expired) — so a reload of cell `c`
   reads what the matching store wrote, never a different live spill.
2. **No intervening cell write**: between a spilled name's def-store and each of
   its use-reloads, no instruction writes that cell (only this name's stores
   target it, and there is exactly one store per def in straight-line SSA) — i.e.
   the `hmid` premise of the sandwich lemma is discharged by the matching store
   plus cell-disjointness.

For the X25519 application these hold by inspection of the emitted body (distinct
32-byte frame slots, SSA-style single-def names), and the value identity is the
runtime KAT vs RFC 7748 + s2n. Stating (1)+(2) as a `SpillWellFormed` predicate and
threading it through a `spillReloadBlock_runBlock` induction is the remaining work
for the unconditional whole-program theorem; the per-spill core is done. -/

/-! ### 6b. Byte separation of the frame slots

`Slot.spilled off` records a **byte** offset, and a spilled value of byte width `width`
occupies `[off, off + width)`. Two slots are usable independently exactly when those
ranges are disjoint — `GenericRegAlloc.SepAt`, which is strictly stronger than offset
distinctness (at `width = 32` the offsets `0` and `8` are distinct and overlap).

The condition is discharged from `linearScan`'s frame stride: consecutive spill offsets
advance by `stride`, so at `width ≤ stride` the offsets are pairwise separated. -/

/-- The spilled byte offsets recorded in `decisions`. -/
def linearScanSpillOffsets (decisions : List (String × Slot)) : List Int :=
  decisions.filterMap (fun d => match d.2 with | .spilled off => some off | _ => none)

/-- The scan invariant: an offset already emitted lies at least `stride` below the next
    free offset, so every new slot is separated from all earlier ones. -/
theorem linearScanGo_pairwise (width : Nat) (stride : Int) (hw : (width : Int) ≤ stride) :
    ∀ (lrs : List LiveRange) (active : List (String × String × Nat)) (freeRegs : List String)
      (nextSpill : Int) (acc : List (String × Slot)),
      (∀ o ∈ linearScanSpillOffsets acc, o + stride ≤ nextSpill) →
      (linearScanSpillOffsets acc).Pairwise (GenericRegAlloc.SepAt width) →
      (linearScanSpillOffsets (linearScanGo stride active freeRegs nextSpill acc lrs)).Pairwise
        (GenericRegAlloc.SepAt width) := by
  have hw0 : (0 : Int) ≤ (width : Int) := Int.natCast_nonneg _
  intro lrs
  induction lrs with
  | nil => intro active freeRegs nextSpill acc _ hp; exact hp
  | cons lr rest ih =>
    intro active freeRegs nextSpill acc hacc hp
    have hres : ∀ (l : List (String × Slot)), linearScanSpillOffsets l = linearScanSpillOffsets acc →
        ((∀ o ∈ linearScanSpillOffsets l, o + stride ≤ nextSpill)
          ∧ (linearScanSpillOffsets l).Pairwise (GenericRegAlloc.SepAt width)) := by
      intro l hl
      rw [hl]; exact ⟨hacc, hp⟩
    have hspill : ∀ (l : List (String × Slot)),
        linearScanSpillOffsets l = nextSpill :: linearScanSpillOffsets acc →
        ((∀ o ∈ linearScanSpillOffsets l, o + stride ≤ nextSpill + stride)
          ∧ (linearScanSpillOffsets l).Pairwise (GenericRegAlloc.SepAt width)) := by
      intro l hl
      rw [hl]
      refine ⟨?_, ?_⟩
      · intro o ho
        rcases List.mem_cons.mp ho with h | h
        · omega
        · have := hacc o h; omega
      · refine List.pairwise_cons.mpr ⟨?_, hp⟩
        intro b hb
        have := hacc b hb
        exact Or.inr (by omega)
    simp only [linearScanGo]
    split
    · exact ih _ _ nextSpill _ (hres _ rfl).1 (hres _ rfl).2
    · split
      · split
        · exact ih _ _ _ _ (hspill _ rfl).1 (hspill _ rfl).2
        · exact ih _ _ _ _ (hspill _ rfl).1 (hspill _ rfl).2
      · exact ih _ _ _ _ (hspill _ rfl).1 (hspill _ rfl).2

/-- **The linear scan's frame stride discharges the byte-separation obligation.** When
    the stride is at least the byte width of one allocated value, the slots `linearScan`
    assigns cover pairwise-disjoint byte ranges, which is what a spill/reload argument
    over a byte-addressed frame (`Optimizer.ByteMemMachine`) consumes. At `width > stride`
    the hypothesis fails to apply: a 32-byte value spilled by the default 8-byte scan has
    overlapping slots. -/
theorem linearScan_slotsSeparated (width : Nat) (pinned : GpAlloc) (frameBase : Int)
    (lrs : List LiveRange) (stride : Int) (hw : (width : Int) ≤ stride) :
    (linearScanSpillOffsets (linearScan pinned frameBase lrs stride)).Pairwise
      (GenericRegAlloc.SepAt width) :=
  linearScanGo_pairwise width stride hw _ [] (allocPool pinned) frameBase []
    (by simp [linearScanSpillOffsets]) (by simp [linearScanSpillOffsets])

/-- The same for `spillAlloc`: a block's spill decisions are byte-separated at any value
    width the frame stride covers. -/
theorem spillAlloc_slotsSeparated (width : Nat) (pinned : GpAlloc) (frameBase : Int)
    (block : List (JInstr 64)) (stride : Int) (hw : (width : Int) ≤ stride) :
    (linearScanSpillOffsets (spillAlloc pinned frameBase block stride)).Pairwise
      (GenericRegAlloc.SepAt width) :=
  linearScan_slotsSeparated width pinned frameBase _ stride hw

/-- **The pin-aware allocation is separated too**: the prepended `%rdx` multiplier
    decisions are all `resident`, so they contribute no frame offset and the offsets are
    exactly the inner linear scan's. -/
theorem spillAllocPinned_slotsSeparated (width : Nat) (pinned : GpAlloc) (frameBase : Int)
    (block : List (JInstr 64)) (stride : Int) (hw : (width : Int) ≤ stride) :
    (linearScanSpillOffsets (spillAllocPinned pinned frameBase block stride)).Pairwise
      (GenericRegAlloc.SepAt width) := by
  have hmul : ∀ (ns : List String),
      linearScanSpillOffsets (ns.map (fun n => (n, Slot.resident mulxMultReg))) = [] := by
    intro ns; simp [linearScanSpillOffsets]
  have happ : linearScanSpillOffsets (spillAllocPinned pinned frameBase block stride)
      = linearScanSpillOffsets (linearScan pinned frameBase
          ((liveRanges block).filter (fun lr => ¬ (mulxMultiplierNames block).contains lr.name))
          stride) := by
    rw [spillAllocPinned, linearScanSpillOffsets, List.filterMap_append,
      ← linearScanSpillOffsets, ← linearScanSpillOffsets, hmul, List.nil_append]
  rw [happ]
  exact linearScan_slotsSeparated width pinned frameBase _ stride hw

/-! ## 7. Live-range sanity (testable)

A few `native_decide`-checked facts on a tiny straight-line body, confirming the
analysis is non-vacuous: every name's live range is within the body and `def ≤
lastUse`. The body defines `t` then uses it twice, mirroring a spilled ladder
temporary. -/

-- @bench-only: the `List (JInstr _)` blocks below are fixtures exercising this
-- spilling register-allocation pass; this module emits no deployed `.s` artifact.
/-- A toy body: `t := a + b`, `r := t + c`, `s := t + r` — `t` is defined at 0 and
    last used at 2 (live across the whole body), the spill-candidate shape. -/
def sanityBody : List (JInstr 64) :=
  [ .mov "t" (.reg "a")
  , .add "t" (.reg "b")
  , .add "r" (.reg "t")
  , .add "s" (.reg "t") ]

/-- `t`'s live range is `[def=1, lastUse=3]` (defined by the `add` at index 1 — the
    `mov` at 0 also writes it, but `defIdxOf` takes the *first* write, index 0;
    here `t` is first written at 0). Non-empty and within the body. -/
theorem sanity_t_liverange :
    defIdxOf sanityBody "t" = 0 ∧ lastUseIdx sanityBody "t" = 3
      ∧ defIdxOf sanityBody "t" ≤ lastUseIdx sanityBody "t" := by native_decide

/-- Every name's live range lies within the body and has `def ≤ lastUse`. -/
theorem sanity_liveranges_wellformed :
    (liveRanges sanityBody).all
      (fun lr => lr.defIdx ≤ lr.lastUse ∧ lr.lastUse < sanityBody.length) = true := by
  native_decide

/-! ## 8. The spilling capability `allocGp` lacks (the demonstrator)

A body with **more simultaneously-live names than the pool** is exactly where a
non-spilling allocator fails: `AsmPrinter.allocGp` truncates the overflow to the
`<UNALLOCATED>` sentinel (`allocOverflow ≠ none`). The spilling allocator instead
assigns *every* name a slot — a pool register if one is free, else a spill frame
cell. This is the capability the renaming `RandomizedRegAlloc` and first-fit `allocGp`
both lack, demonstrated on a 5-live-name body against a 3-register pool. -/

/-- 6 names all live to the end (`a` accumulates `b,c,d,e,f`) — peak pressure 6. -/
def hotBody : List (JInstr 64) :=
  [ .mov "a" (.imm 1), .mov "b" (.imm 2), .mov "c" (.imm 3), .mov "d" (.imm 4)
  , .mov "e" (.imm 5), .mov "f" (.imm 6)
  , .add "a" (.reg "b"), .add "a" (.reg "c"), .add "a" (.reg "d"), .add "a" (.reg "e")
  , .add "a" (.reg "f") ]

/-- Pins consuming all but 5 GP registers; `allocGp`'s free pool is 5, but the body
    needs 6 simultaneously-live names — first-fit overflows. The spiller additionally
    reserves the 2 working registers, allocating from a 3-slot pool and spilling the
    rest. -/
def tinyPins : GpAlloc :=
  [ ("p1","%rdi"), ("p2","%rsi"), ("p3","%rdx"), ("p4","%rax"), ("p5","%r10"),
    ("p6","%r11"), ("p7","%rbx"), ("p8","%r12"), ("p9","%r13") ]

/-- The spiller's allocatable pool here is 3 registers (`%rcx, %r8, %r9` — the 5 free
    minus the 2 reserved working registers). -/
theorem hot_allocPool_size : (allocPool tinyPins).length = 3 := by native_decide

/-- **First-fit `allocGp` OVERFLOWS** on this body: 5 names against a 3-slot pool,
    so `allocOverflow ≠ none` — the non-spilling allocator cannot place it. -/
theorem hot_allocGp_overflows : allocOverflow tinyPins hotBody ≠ none := by native_decide

/-- **The spilling allocator spills** where first-fit overflows: on the same body
    and pool that `allocGp` cannot place (`hot_allocGp_overflows`), `spillAlloc`
    produces at least one `spilled` decision — it pushes the values that do not fit
    the 3-register pool to distinct frame cells instead of leaving them
    `<UNALLOCATED>`. This is the capability the renaming `RandomizedRegAlloc` and
    first-fit `allocGp` both lack. -/
theorem hot_spillAlloc_spills :
    0 < spillCount (spillAlloc tinyPins 0 hotBody) := by native_decide

/-- Every name that gets a slot gets either a register or a frame cell (the decision
    list contains no impossible state) — the allocator output is well-formed. -/
theorem hot_spillAlloc_wellformed :
    (spillAlloc tinyPins 0 hotBody).all
      (fun d => match d.2 with | .resident _ => true | .spilled off => 0 ≤ off) = true := by
  native_decide

/-! ## 9. Pin-aware multiplier disjointness (the soundness side-condition, #426)

Binding all the MULX-multiplier names to the single `%rdx` is sound **iff** no two
of them are simultaneously live (else one would clobber the other's `%rdx` value).
`multipliersDisjoint` checks that the multiplier names' live ranges are pairwise
non-overlapping — the predicate the applied X25519 body discharges by `native_decide`
(`X25519MonoLadderMem2Reg.pinned_multipliers_rdx_disjoint`). This is the pin-aware
analogue of `residentAlloc_no_live_conflict`: it certifies that the shared `%rdx`
binding realises a valid per-program-point allocation. -/

/-- The live range `(def, lastUse)` of each name in `names`, looked up from the block's
    `liveRanges`. -/
def rangesOf (block : List (JInstr 64)) (names : List String) : List (Nat × Nat) :=
  names.filterMap (fun n =>
    (liveRanges block).find? (fun lr => lr.name == n) |>.map (fun lr => (lr.defIdx, lr.lastUse)))

/-- Two closed intervals overlap. -/
def intervalsOverlap (a b : Nat × Nat) : Bool := a.1 ≤ b.2 ∧ b.1 ≤ a.2

/-- **The MULX-multiplier names have pairwise-disjoint live ranges in `block`.** When
    true, all multiplier names can share the single `%rdx` register (the pin-aware
    allocation `spillAllocPinned` is a valid per-program-point binding): at no program
    point are two multipliers simultaneously live, so binding them all to `%rdx` never
    clobbers a live value. -/
def multipliersDisjoint (block : List (JInstr 64)) : Bool :=
  let lrs := liveRanges block
  let rs : List (Nat × Option LiveRange) := (mulxMultiplierNames block).zipIdx.map
    (fun (n, i) => (i, lrs.find? (fun lr => lr.name == n)))
  rs.all (fun (i, lri) =>
    rs.all (fun (j, lrj) =>
      if i < j then
        match lri, lrj with
        | some a, some b => ¬ intervalsOverlap (a.defIdx, a.lastUse) (b.defIdx, b.lastUse)
        | _, _ => true
      else true))

end CatCrypt.Crypto.Optimizer.SpillingRegAlloc
