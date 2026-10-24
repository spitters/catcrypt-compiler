/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# A generic `MachineModel`-parameterized validated register allocator

`Optimizer.SpillingRegAlloc` (x86, monomorphized to `JInstr 64`/`JState 64`)
and `ARMBackend.ArmRegAlloc` (A64, the `AInst`/`AState` analogue) are *the
same allocator written twice*. Both work over a straight-line block of string-named
SSA values with a read/write interface (`writtenName(s)`/`readNames`), a fixed pool
of physical registers, and a spill/reload rendering against a frame memory; only
the physical-register file and the concrete spill/reload instruction shapes differ.
The soundness story is identical in both: a linear-scan allocator (untrusted) plus
a verified checker — an injective-renaming-commutes lemma for the register-resident
half, and a spill-store/reload-roundtrip sandwich for the spilled half.

This module is the CompCert/Jasmin/LLVM-style **generalization**: a `MachineModel`
typeclass over `(I S : Type)` (the instruction and register-state types) abstracting
exactly the differences, and the ~6 core register-allocation lemmas stated **once**
over `[MachineModel I S]`. The allocator is untrusted (a pure linear scan, totally
reusable); the **checker** — the renaming/spill soundness — is the verified artifact,
in the translation-validation discipline of `TranslationValidationEgraph`.

## The abstraction (what x86/ARM/RISC-V have in common)

| field | x86 (`JInstr 64`/`JState 64`) | A64 (`AInst`/`AState`) | RV64 (`RInst`/`RState`) |
|---|---|---|---|
| `writtenName` | the GP dest | `(ainstDstSrcs i).1` | `(rinstDstSrcs i).1` |
| `readNames`   | source names | `(ainstDstSrcs i).2` | `(rinstDstSrcs i).2` |
| `physRegs`    | `gpPool` | `w0..w30` | `a0..a7,t0..t6,s0..s11` |
| `mkSpill`     | `storeMem fb off (.reg r)` | `str r → [fb,off]` | `sw r → off(fb)` |
| `mkReload`    | `loadMem r fb off` | `ldr r ← [fb,off]` | `lw r ← off(fb)` |
| `runBlock`    | `runBlock` | `runABlock` | `runRBlock` |

## What is built and proved (generically, fully proved, no new custom axioms)

1. **Live-range analysis + the linear-scan allocator** (`liveRanges`, `linearScan`,
   `spillAlloc`) — pure, total, parametric over `[MachineModel I S]`; the untrusted
   half (any allocator output is *checked*, never trusted).
2. **The resident-path checker** (`renameBlock_runBlock`): applying an **injective
   renaming** `ρ : name → physreg` to a block commutes with `runBlock` — the renamed
   block computes, at each `ρ n`, exactly what the original computed at `n`. Proved
   once over an abstract `RegMachine` interface (`get`/`set` + their two laws), by
   induction with no new custom axioms. The soundness of the register-resident path.
3. **The spill-path checker** (`spillStore_establishes`, `evalReload_noop`,
   `reload_sandwich`): on a memory-extended state (`MemMachine`: `get`/`load`/`setReg`
   /`store` + four laws), the spill store establishes the cell↦reg invariant
   (`SpillValid`) and the matching reload is a no-op under it — so the spill/reload
   roundtrip is denotation-preserving.
4. **The rewrite-length decomposition** (`rewriteBlock_length`): the RA-rewritten
   block is one machine instruction per op plus exactly the inserted spill traffic.
5. **Byte separation of frame slots** (`SepAt`, `SlotsSeparated`,
   `linearScan_slotsSeparated`): a spilled value of byte width `width` occupies
   `[off, off + width)`, two slots are usable independently when those ranges are
   disjoint, and the linear scan's frame stride discharges that obligation when it is at
   least the value width. `Optimizer.ByteMemMachine` is the memory interface whose
   non-interference law consumes it.
6. **Straight-line allocation with split live ranges** (`nextUseAlloc`): a value stays
   in its register until it dies or is evicted, the victim being the resident value whose
   next read is furthest; an evicted value is stored to a spill slot unless it has a home
   location or a slot already holds it, and is loaded back before its next read. Untrusted,
   like `linearScan`.

§5–§6 exhibit that the x86 / A64 instances **fit** the typeclass (the generic lemmas,
instantiated, give back what `SpillingRegAlloc`/`ArmRegAlloc` proved), and §7 is the
sanity demonstrator. The fresh RISC-V instantiation is `RISCVBackend.RiscvRegAlloc`.

This file uses `set_option autoImplicit false` (the `Optimizer/` convention); the
abstract interfaces are bundled typeclasses, so no auto-implicits are needed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-! ## 1. The `MachineModel` typeclass: the read/write/phys/spill interface

The *data* every backend supplies: how to read an instruction's written/read names,
the physical register file, how to render a spill store / reload load, and the
straight-line block semantics. Instruction `I` and register-state `S` are the two
abstracted types. -/

/-- The *syntactic* data interface a backend exposes to the generic register
    allocator: the written/read names of one instruction, the physical register pool,
    and the spill / reload instruction constructors. This is over the instruction type
    `I` alone (the register-state type `S` enters only with the semantics, in
    `RegMachine`/`MemMachine`). The common shape of `SpillingRegAlloc` (x86),
    `ArmRegAlloc` (A64), and `RiscvRegAlloc` (RV64). The `Lprog` back half does not
    allocate through this class: it allocates in the `Lprog` export
    (`ExportPhys.physScanSpill`). -/
class MachineModel (I : Type) where
  /-- The register names an instruction writes (its destinations). Usually a singleton,
      but multi-output ops (x86 `mulx` writes hi+lo, `adcx`/`adox` write data+flag) give
      a longer list. -/
  writtenNames : I → List String
  /-- The register names an instruction reads (its source operands). -/
  readNames : I → List String
  /-- The allocatable physical-register file (the GP pool the RA assigns from). -/
  physRegs : List String
  /-- Render a spill store: write register `r`'s value to frame cell `off`. -/
  mkSpill : String → Int → I
  /-- Render a reload load: read frame cell `off` back into register `r`. -/
  mkReload : String → Int → I

export MachineModel (writtenNames readNames physRegs mkSpill mkReload)

/-! ## 2. Live-range analysis + the linear-scan allocator (the untrusted half)

Both backends compute the per-name `(def, lastUse)` interval over the block and feed
it to a linear scan that assigns each name a pool register (`resident`) or a distinct
frame cell (`spilled`). This is the *untrusted* allocator: its output is checked by
§3–§4, never trusted. Stated parametrically over `[MachineModel I S]`. -/

variable {I : Type}

/-- A value-name's live range over a block: `defIdx` is the first index that writes
    it (`0` if only read — a read-only input, live from entry), `lastUse` is the last
    index that reads or writes it. -/
structure LiveRange where
  /-- The register name. -/
  name : String
  /-- First index that writes the name (`0` if never written). -/
  defIdx : Nat
  /-- Last index that reads or writes the name. -/
  lastUse : Nat
  deriving Repr, DecidableEq

/-- The last index at which `name` is read or written (`0` if never). -/
def lastUseIdx [MachineModel I] (block : List I) (name : String) : Nat :=
  block.zipIdx.foldl
    (fun acc (i, idx) =>
      if (writtenNames i).contains name ∨ (readNames i).contains name then idx
      else acc) 0

/-- The first index at which `name` is written (`0` if never: a read-only input). -/
def defIdxOf [MachineModel I] (block : List I) (name : String) : Nat :=
  match block.zipIdx.find? (fun (i, _) => (writtenNames i).contains name) with
  | some (_, idx) => idx
  | none => 0

/-- Every distinct name in the block, in first-seen order. -/
def blockNames [MachineModel I] (block : List I) : List String :=
  (block.flatMap (fun i => writtenNames i ++ readNames i)).foldl
    (fun acc n => if acc.contains n then acc else acc ++ [n]) []

/-- The live ranges of every distinct name in the block (first-seen order). -/
def liveRanges [MachineModel I] (block : List I) : List LiveRange :=
  (blockNames block).map
    (fun n => ⟨n, defIdxOf block n, lastUseIdx block n⟩)

/-- Register pressure (count of simultaneously-live names) at index `i`. -/
def pressureAt [MachineModel I] (block : List I) (i : Nat) : Nat :=
  ((liveRanges block).filter (fun l => l.defIdx ≤ i ∧ i ≤ l.lastUse)).length

/-- Peak register pressure over the block — the count the pool must hold to be
    spill-free. -/
def peakPressure [MachineModel I] (block : List I) : Nat :=
  ((List.range block.length).map (pressureAt block)).foldl max 0

/-- A per-name allocation decision: a pool register (`resident`) or a frame spill
    slot byte-offset (`spilled`). -/
inductive Slot where
  /-- The name stays in physical register `reg` for its whole live range. -/
  | resident (reg : String)
  /-- The name is spilled to the frame at byte offset `off`. -/
  | spilled (off : Int)
  deriving Repr, DecidableEq

/-- The allocatable pool: `physRegs` minus the reserved scratch / pinned registers. -/
def allocPool [MachineModel I] (pinned scratch : List String) : List String :=
  (physRegs (I := I)).filter (fun r => ¬ pinned.contains r ∧ ¬ scratch.contains r)

/-- The scan step of `linearScan`: `active` is the `(name, reg, lastUse)` map, `freeRegs`
    the unassigned pool, `nextSpill` the next free frame offset, `acc` the decisions so
    far, and the final argument the remaining live ranges in `defIdx` order. Consecutive
    spill offsets advance by `stride`. -/
def linearScanGo (stride : Int) (active : List (String × String × Nat))
    (freeRegs : List String) (nextSpill : Int) (acc : List (String × Slot)) :
    List LiveRange → List (String × Slot)
  | [] => acc
  | lr :: rest =>
    let (live, expired) := active.partition (fun a => lr.defIdx ≤ a.2.2)
    let freed := freeRegs ++ expired.map (fun a => a.2.1)
    match freed with
    | reg :: more =>
      linearScanGo stride ((lr.name, reg, lr.lastUse) :: live) more nextSpill
         ((lr.name, .resident reg) :: acc) rest
    | [] =>
      let farthestActive := live.foldl
        (fun (best : Option (String × String × Nat)) a =>
          match best with
          | none => some a
          | some b => if a.2.2 > b.2.2 then some a else best) none
      match farthestActive with
      | some a =>
        if a.2.2 > lr.lastUse then
          let live' := live.filter (fun x => x.1 ≠ a.1)
          linearScanGo stride ((lr.name, a.2.1, lr.lastUse) :: live') [] (nextSpill + stride)
             ((lr.name, .resident a.2.1) :: (a.1, .spilled nextSpill) :: acc) rest
        else
          linearScanGo stride live [] (nextSpill + stride)
            ((lr.name, .spilled nextSpill) :: acc) rest
      | none =>
        linearScanGo stride live [] (nextSpill + stride)
          ((lr.name, .spilled nextSpill) :: acc) rest

/-- **The generic linear-scan allocator** (farthest-end eviction). Walk the live
    ranges in `defIdx` order keeping an active map `(name, reg, lastUse)` and the free
    pool; on a new def, reuse a free / expired register if one is available, else spill
    the farthest-ending active interval (or the newcomer) to a fresh frame cell.
    Consecutive spill offsets advance from `frameBase` by `stride`, the byte width of one
    allocated value; the default `8` is the general-purpose word. This is the *single*
    source for `SpillingRegAlloc.linearScan` and `ArmRegAlloc.linearScan` — they differ
    only in the pool the `MachineModel` supplies. -/
def linearScan (pool : List String) (frameBase : Int) (lrs : List LiveRange)
    (stride : Int := 8) : List (String × Slot) :=
  linearScanGo stride [] pool frameBase []
    (lrs.mergeSort (fun a b => a.defIdx ≤ b.defIdx))

/-- The spill decisions for a block: `name ↦ Slot` by linear scan over its live
    ranges, with `stride`-byte frame cells. -/
def spillAlloc [MachineModel I] (pinned scratch : List String) (frameBase : Int)
    (block : List I) (stride : Int := 8) : List (String × Slot) :=
  linearScan (allocPool (I := I) pinned scratch) frameBase (liveRanges block) stride

/-- Count of spilled names. -/
def spillCount (decisions : List (String × Slot)) : Nat :=
  (decisions.filter (fun d => match d.2 with | .spilled _ => true | _ => false)).length

/-- Count of register-resident names. -/
def residentCount (decisions : List (String × Slot)) : Nat :=
  (decisions.filter (fun d => match d.2 with | .resident _ => true | _ => false)).length

/-- The frame offset a `spilled` name is bound to, if spilled. -/
def spillSlotOf (decisions : List (String × Slot)) (n : String) : Option Int :=
  match decisions.lookup n with
  | some (.spilled off) => some off
  | _ => none

/-- The physical register a `resident` name is bound to, if resident. -/
def residentReg (decisions : List (String × Slot)) (n : String) : Option String :=
  match decisions.lookup n with
  | some (.resident r) => some r
  | _ => none

/-! ### 2a. First-fit allocation as the linear scan over simultaneously live names

When every name is live at every point, the linear scan never frees a register: the
`k`-th name receives the `k`-th pool register and the names past the pool are spilled.
Restricted to its resident decisions this is first-fit allocation, `names.zip pool`
(`firstFitScan_eq_zip`). The x86 printer's `AsmPrinter.allocGp` is this scan. -/

/-- The register-resident decisions of a decision list as `(name, register)` pairs, in
    list order. -/
def residentPairs (decisions : List (String × Slot)) : List (String × String) :=
  decisions.filterMap (fun d => match d.2 with
    | .resident r => some (d.1, r)
    | .spilled _ => none)

/-- The live ranges in which all `names` are live together: the interval `[0, 0]` for
    each name, so every pair of ranges overlaps. -/
def allLiveRanges (names : List String) : List LiveRange :=
  names.map (fun n => ⟨n, 0, 0⟩)

/-- **First-fit allocation by linear scan.** The resident decisions of the linear scan of
    `allLiveRanges names` against `pool`, in name order. The ranges are already in `defIdx`
    order, so the scan step `linearScanGo` runs on them directly
    (`firstFitScan_eq_linearScan`). -/
def firstFitScan (pool names : List String) : List (String × String) :=
  (residentPairs (linearScanGo 8 [] pool 0 [] (allLiveRanges names))).reverse

/-- A left fold whose step returns either its element or its accumulator ends at an
    element of the list or at the initial value. -/
theorem foldl_some_mem {α : Type} (f : Option α → α → Option α)
    (hf : ∀ o a, f o a = some a ∨ f o a = o) :
    ∀ (l : List α) (init : Option α) (b : α), l.foldl f init = some b → b ∈ l ∨ init = some b
  | [], _, _, h => Or.inr h
  | x :: xs, init, b, h => by
      rcases foldl_some_mem f hf xs (f init x) b h with hm | hi
      · exact Or.inl (List.mem_cons_of_mem _ hm)
      · rcases hf init x with hx | hx
        · rw [hx] at hi; cases hi; exact Or.inl List.mem_cons_self
        · rw [hx] at hi; exact Or.inr hi

/-- The scan invariant for simultaneously live names: with every active interval ending
    at `0`, no register is freed and none is evicted, so the scan pairs the remaining names
    with the free registers in order and spills the rest. -/
theorem linearScanGo_allLive_residentPairs (stride : Int) :
    ∀ (names : List String) (active : List (String × String × Nat)) (free : List String)
      (next : Int) (acc : List (String × Slot)),
      (∀ a ∈ active, a.2.2 = 0) →
      residentPairs (linearScanGo stride active free next acc (allLiveRanges names))
        = (names.zip free).reverse ++ residentPairs acc
  | [], _, _, _, _, _ => by simp [allLiveRanges, linearScanGo]
  | n :: ns, active, free, next, acc, h => by
      have hpart : List.partition (fun a => decide (0 ≤ a.snd.snd)) active = (active, []) := by
        simp [List.partition_eq_filter_filter]
      simp only [allLiveRanges, List.map_cons, linearScanGo, hpart, List.map_nil,
        List.append_nil]
      cases free with
      | cons r more =>
          simp only
          rw [← allLiveRanges, linearScanGo_allLive_residentPairs stride ns _ more next _ (by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · rfl
            · exact h a ha)]
          simp [residentPairs]
      | nil =>
          simp only
          split
          · rename_i a hfa
            have ha0 : a.snd.snd = 0 := by
              rcases foldl_some_mem _ (fun o x => by
                cases o with
                | none => exact Or.inl rfl
                | some b =>
                    by_cases hx : x.snd.snd > b.snd.snd
                    · exact Or.inl (ite_eq_left hx)
                    · exact Or.inr (ite_eq_right hx)) active none a hfa with hm | hn
              · exact h a hm
              · cases hn
            rw [ite_eq_right (by omega), ← allLiveRanges,
              linearScanGo_allLive_residentPairs stride ns _ [] _ _ h]
            simp [residentPairs]
          · rw [← allLiveRanges, linearScanGo_allLive_residentPairs stride ns _ [] _ _ h]
            simp [residentPairs]

/-- **The linear scan over simultaneously live names is first-fit.** -/
theorem firstFitScan_eq_zip (pool names : List String) :
    firstFitScan pool names = names.zip pool := by
  rw [firstFitScan, linearScanGo_allLive_residentPairs 8 names [] pool 0 [] (by simp)]
  simp [residentPairs]

/-- `firstFitScan` is the resident part of `linearScan`: sorting ranges that share one
    `defIdx` leaves them in place. -/
theorem firstFitScan_eq_linearScan (pool names : List String) :
    firstFitScan pool names
      = (residentPairs (linearScan pool 0 (allLiveRanges names))).reverse := by
  rw [firstFitScan, linearScan, List.mergeSort_of_pairwise]
  simp [allLiveRanges, List.pairwise_map, List.pairwise_of_forall]

/-! ### 2b. The printer scan: instruction-order allocation with last-read recycling

The non-spilling allocator the A64, RV32 and RV64 printers run (`ARMBackend.allocGp`,
`RISCVBackend.allocGp`, `RISCVBackend.allocGp64`). It walks the block in instruction
order over single-destination instructions, described by `dstSrcs i = (dst, srcs)`.
A destination not yet bound takes the head of the free list; when the free list is
empty the name stays unbound. A source that is not reserved, is not the instruction's
destination, and is read for the last time at this index returns its register to the
end of the free list. The scan has no live ranges over writes, no sorting and no
spill; it differs from `linearScan` in each of these respects, so the two produce
different allocations on the same block. -/

/-- The index of the last instruction of `block` that reads `n` (`0` if none), where
    `dstSrcs i` is the destination and the source names of instruction `i`. -/
def lastReadIdx (dstSrcs : I → String × List String) (block : List I) (n : String) : Nat :=
  (block.zipIdx.foldl (fun acc (i, idx) =>
    if (dstSrcs i).2.contains n then idx else acc) 0)

/-- **The printer scan.** Starting from the bindings `pinned` and the free list `pool`,
    bind each instruction's unbound destination to the next free register and return
    the register of every non-`reserved` source to the free list after its last read.
    The result is the final binding list, newest binding first, then `pinned`. -/
def lastReadScan (dstSrcs : I → String × List String) (pinned : List (String × String))
    (pool reserved : List String) (block : List I) : List (String × String) :=
  let step : (List (String × String) × List String) → (I × Nat) →
      (List (String × String) × List String) :=
    fun (alloc, free) (instr, idx) =>
      let (dst, _) := dstSrcs instr
      let (alloc1, free1) :=
        if (alloc.lookup dst).isSome then (alloc, free)
        else match free with
          | [] => (alloc, free)
          | r :: rest => ((dst, r) :: alloc, rest)
      let toFree := (dstSrcs instr).2.filter (fun s =>
        ¬ reserved.contains s ∧ lastReadIdx dstSrcs block s = idx ∧ s ≠ dst)
      let freedRegs := toFree.filterMap (fun s => alloc1.lookup s)
      (alloc1, free1 ++ freedRegs)
  let (alloc, _) := block.zipIdx.foldl step (pinned, pool)
  alloc

/-! ## 3. The resident-path checker: an injective renaming commutes with `runBlock`

The register-resident half of any allocation output is a **renaming** `ρ : name →
physreg`. We prove — once, over an abstract `RegMachine` interface (read/write of a
register file with their two algebraic laws) — that an injective `ρ` whose image
avoids the zero register commutes with `runBlock`: the renamed block computes at
`ρ n` exactly what the original computed at `n`.

To stay generic we factor out the *per-instruction effect* every backend's step has:
`evalInst s i = s.set (writtenName i) (instVal s i)`, where `instVal` reads only the
read-names. This is the shared shape of `evalInstr`/`evalAInst`/`evalRInst` (each is
a single write of a value computed from the sources). We package it as a class. -/

/-- An abstract register machine: a named register file with read (`get`) / write
    (`set`), a designated zero register (writes ignored, reads `0`), and a
    single-step semantics `evalInst` of the shape `set (writtenName i) (instVal s i)`
    — every op writes its destination a value `instVal` computed from its sources.
    The two register-file laws (`get_set_same`/`get_set_other`) and the
    source-locality of `instVal` (it only reads the read-names, so it is stable under
    a value-preserving rename of the state) are the class obligations. This is the
    common shape of the x86 `JState`, A64 `AState`, RV64 `RState` step semantics. -/
class RegMachine (I : Type) (S : Type) extends MachineModel I where
  /-- The straight-line block semantics (left fold of the per-instruction step). -/
  runBlock : S → List I → S
  /-- The register/cell value type (`BitVec 32`, `BitVec 64`, …). -/
  Val : Type
  /-- Read a register. -/
  get : S → String → Val
  /-- Write a register (writes to a discard register are ignored). -/
  set : S → String → Val → S
  /-- The `(name, value)` pairs an instruction writes, as a function of the register
      state. Single-output ops give a singleton `[(dst, v)]`; multi-output ops (x86
      `mulx` → `[(hi, vhi), (lo, vlo)]`) give one pair per destination, applied
      left-to-right. The names are exactly `writtenNames i` (see `writes_names`). -/
  writes : S → I → List (String × Val)
  /-- Apply a renaming `ρ` to an instruction (rename dsts + all sources). -/
  renameInst : (String → String) → I → I
  /-- The discard-register predicate (`= wzr` for A64, `∈ {zero, x0}` for RV64, always
      `false` for x86). Writes to a discard register are ignored; the set is a single
      conceptual zero register that may have several spellings. -/
  isDiscard : String → Bool
  /-- Reading any discard register gives a single fixed value (independent of which
      discard register and of the state). -/
  get_discard : ∀ (s s' : S) (r r' : String),
    isDiscard r = true → isDiscard r' = true → get s r = get s' r'
  /-- Reading back a just-written non-discard register returns the written value. -/
  get_set_same : ∀ (s : S) (r : String) (v : Val), isDiscard r = false → get (set s r v) r = v
  /-- Writing one register leaves the others unchanged. -/
  get_set_other : ∀ (s : S) (r r' : String) (v : Val), r' ≠ r → get (set s r' v) r = get s r
  /-- A single step applies every `(name, value)` pair of `writes s i`, left-to-right
      (a left fold of `set`), **as observed on the register file**: reading any register
      after the step equals reading it after the fold. This register-observable form (not
      whole-state equality) is what register-allocation soundness needs — the resident-path
      result only ever inspects `get` — and it admits ops with *non-register* side effects, like
      x86 `adcx`/`adox` writing a flag alongside their destination. For a single-output
      op the fold is one `set`; for `mulx` it is two. -/
  evalInst_eq_set : ∀ (s : S) (i : I) (r : String),
    get (runBlock s [i]) r = get ((writes s i).foldl (fun st p => set st p.1 p.2) s) r
  /-- `runBlock s [] = s` — the empty block is a no-op. -/
  runBlock_nil : ∀ (s : S), runBlock s [] = s
  /-- `runBlock` is the left fold: running `xs ++ ys` runs `xs` then `ys`. -/
  runBlock_append : ∀ (s : S) (xs ys : List I),
    runBlock s (xs ++ ys) = runBlock (runBlock s xs) ys
  /-- The written names are exactly `writtenNames i`, independent of the state (the
      values may depend on `s`, the destinations do not). -/
  writes_names : ∀ (s : S) (i : I),
    (writes s i).map Prod.fst = MachineModel.writtenNames i
  /-- Source-locality + destination-renaming, bundled: under a value-preserving rename
      of the read-names, the renamed instruction writes the SAME values to the
      `ρ`-renamed destinations. (Generalizes `ArmRegAlloc.instVal_rename` +
      `writtenName_rename`; proved per-backend by `cases i`.) -/
  writes_rename : ∀ (ρ : String → String) (s t : S) (i : I),
    (∀ a ∈ MachineModel.readNames i, get t (ρ a) = get s a) →
    writes t (renameInst ρ i) = (writes s i).map (fun p => (ρ p.1, p.2))

variable {S : Type}

/-! The `RegMachine` projections take the carrier types `(I S)` as explicit
arguments (class structure params); we wrap them in implicit-argument abbreviations
so the soundness proofs read cleanly. -/

/-- The straight-line block semantics, `I` explicit (`RegMachine.runBlock`). -/
abbrev rmRun (I : Type) [RegMachine I S] (s : S) (block : List I) : S :=
  RegMachine.runBlock s block
/-- Read a register, `I` explicit (`RegMachine.get`). -/
abbrev rmGet (I : Type) [RegMachine I S] (s : S) (r : String) : RegMachine.Val I S :=
  RegMachine.get (I := I) s r
/-- The discard-register predicate (`RegMachine.isDiscard`). -/
abbrev rmDisc (I S : Type) [RegMachine I S] (r : String) : Bool := RegMachine.isDiscard I S r
/-- Apply a renaming to an instruction, `S` explicit (`RegMachine.renameInst`). -/
abbrev rmRename (S : Type) [RegMachine I S] (ρ : String → String) (i : I) : I :=
  RegMachine.renameInst (S := S) ρ i

/-- Apply a renaming to a whole block. -/
def renameBlock [RegMachine I S] (ρ : String → String) (block : List I) : List I :=
  block.map (rmRename S ρ)

/-- The `Reindexed` relation between an original state `s` and a renamed state `t`:
    `get t (ρ n) = get s n` for every name `n` whose image is not a discard register. -/
def Reindexed (I : Type) [RegMachine I S] (ρ : String → String) (s t : S) : Prop :=
  ∀ n, rmDisc I S (ρ n) = false → rmGet I t (ρ n) = rmGet I s n

/-- **The renamed read of a source equals the original read.** For an injective `ρ`
    that maps discard registers to discard registers, reading source `a` in the renamed
    state `t` at `ρ a` equals reading `a` in the original `s`. (If `a` is a discard
    register both read the fixed discard value; else `ρ a` is non-discard by injectivity
    of the discard-preserving `ρ`, so `Reindexed` applies.) -/
theorem reindexed_src (I : Type) [RegMachine I S] (ρ : String → String)
    (hρd : ∀ r, rmDisc I S r = true → rmDisc I S (ρ r) = true)
    (hρnd : ∀ r, rmDisc I S r = false → rmDisc I S (ρ r) = false)
    (s t : S) (h : Reindexed I ρ s t) (a : String) :
    rmGet I t (ρ a) = rmGet I s a := by
  by_cases ha : rmDisc I S a = true
  · -- `a` is a discard register: so is `ρ a`; both read the single fixed discard value
    have hρa : rmDisc I S (ρ a) = true := hρd a ha
    exact RegMachine.get_discard t s (ρ a) a hρa ha
  · exact h a (hρnd a (by simpa using ha))

/-- Fold the register-file `set` over a list of `(name, value)` writes — the
    multi-output single-step shape (`mulx` writes two pairs, a scalar op one). -/
def setMany (I : Type) [RegMachine I S] (s : S)
    (pairs : List (String × RegMachine.Val I S)) : S :=
  pairs.foldl (fun st p => RegMachine.set (I := I) st p.1 p.2) s

@[simp] theorem setMany_nil (I : Type) [RegMachine I S] (s : S) :
    setMany I s ([] : List (String × RegMachine.Val I S)) = s := rfl

@[simp] theorem setMany_cons (I : Type) [RegMachine I S] (s : S)
    (p : String × RegMachine.Val I S) (ps : List (String × RegMachine.Val I S)) :
    setMany I s (p :: ps) = setMany I (RegMachine.set (I := I) s p.1 p.2) ps := rfl

/-- **A single `set` preserves `Reindexed`.** Writing the same value `v` to `n`
    (original) and `ρ n` (renamed) keeps the reindex relation, when `n` is non-discard
    and `ρ` is injective and non-discard-preserving. This is the per-write atom the
    multi-output step iterates. -/
theorem set_step_reindexed (I : Type) [RegMachine I S] (ρ : String → String)
    (hinj : Function.Injective ρ)
    (hρnd : ∀ r, rmDisc I S r = false → rmDisc I S (ρ r) = false)
    (s t : S) (n : String) (v : RegMachine.Val I S)
    (hz : rmDisc I S n = false) (h : Reindexed I ρ s t) :
    Reindexed I ρ (RegMachine.set (I := I) s n v) (RegMachine.set (I := I) t (ρ n) v) := by
  intro m hm
  show RegMachine.get _ _ = RegMachine.get _ _
  have hzρ : rmDisc I S (ρ n) = false := hρnd _ hz
  by_cases hd : m = n
  · subst hd
    rw [RegMachine.get_set_same _ _ _ hzρ, RegMachine.get_set_same _ _ _ hz]
  · have hne : ρ n ≠ ρ m := fun hc => hd (hinj hc.symm)
    rw [RegMachine.get_set_other _ _ _ _ hne, RegMachine.get_set_other _ _ _ _ (Ne.symm hd)]
    exact h m hm

/-- **A whole list of writes preserves `Reindexed`** — iterate `set_step_reindexed`. The
    original writes `pairs`; the renamed writes the `ρ`-image pairs `(ρ n, v)`. -/
theorem setMany_reindexed (I : Type) [RegMachine I S] (ρ : String → String)
    (hinj : Function.Injective ρ)
    (hρnd : ∀ r, rmDisc I S r = false → rmDisc I S (ρ r) = false) :
    ∀ (pairs : List (String × RegMachine.Val I S)),
      (∀ p ∈ pairs, rmDisc I S p.1 = false) →
      ∀ (s t : S), Reindexed I ρ s t →
        Reindexed I ρ (setMany I s pairs)
          (setMany I t (pairs.map (fun p => (ρ p.1, p.2)))) := by
  intro pairs
  induction pairs with
  | nil => intro _ s t h; exact h
  | cons p ps ih =>
    intro hz s t h
    have hstep := set_step_reindexed I ρ hinj hρnd s t p.1 p.2 (hz p (List.mem_cons_self ..)) h
    have hrest := ih (fun q hq => hz q (List.mem_cons_of_mem _ hq))
      (RegMachine.set (I := I) s p.1 p.2) (RegMachine.set (I := I) t (ρ p.1) p.2) hstep
    simpa [setMany_cons, List.map_cons] using hrest

/-- One step preserves `Reindexed` when `ρ` is injective, discard-preserving, and every
    written name is non-discard. Over the multi-output write-list, this is
    `setMany_reindexed` applied to `writes s i` (whose names are `writtenNames i`). -/
theorem evalInst_rename_preserves (I : Type) [RegMachine I S] (ρ : String → String)
    (hinj : Function.Injective ρ) (hρd : ∀ r, rmDisc I S r = true → rmDisc I S (ρ r) = true)
    (hρnd : ∀ r, rmDisc I S r = false → rmDisc I S (ρ r) = false)
    (s t : S) (i : I) (hz : ∀ n ∈ writtenNames i, rmDisc I S n = false)
    (h : Reindexed I ρ s t) :
    Reindexed I ρ (rmRun I s [i]) (rmRun I t [rmRename S ρ i]) := by
  intro n hn
  show RegMachine.get (RegMachine.runBlock t [rmRename S ρ i]) (ρ n)
     = RegMachine.get (RegMachine.runBlock s [i]) n
  rw [RegMachine.evalInst_eq_set t (rmRename S ρ i) (ρ n),
      RegMachine.evalInst_eq_set s i n,
      RegMachine.writes_rename ρ s t i (fun a _ => reindexed_src I ρ hρd hρnd s t h a)]
  have hsub : ∀ p ∈ RegMachine.writes s i, rmDisc I S p.1 = false := by
    intro p hp
    apply hz
    have hpn : p.1 ∈ (RegMachine.writes s i).map Prod.fst := List.mem_map_of_mem hp
    rwa [RegMachine.writes_names s i] at hpn
  exact setMany_reindexed I ρ hinj hρnd (RegMachine.writes s i) hsub s t h n hn

/-- `runBlock s [] = s` — the empty block is a no-op. -/
theorem rmRun_nil (I : Type) [RegMachine I S] (s : S) : rmRun I s [] = s :=
  RegMachine.runBlock_nil s

/-- `runBlock` distributes over a cons (one step then the rest), from the class's
    left-fold law (`i :: is = [i] ++ is`). -/
theorem rmRun_cons (I : Type) [RegMachine I S] (s : S) (i : I) (is : List I) :
    rmRun I s (i :: is) = rmRun I (rmRun I s [i]) is := by
  have := RegMachine.runBlock_append (I := I) s [i] is
  simpa [rmRun] using this

/-- `renameBlock` distributes over a cons. -/
theorem renameBlock_cons [RegMachine I S] (ρ : String → String) (i : I) (is : List I) :
    renameBlock (S := S) ρ (i :: is) = rmRename S ρ i :: renameBlock (S := S) ρ is := rfl

/-- **Resident-path soundness, generically.** For an injective renaming `ρ`
    that maps discard registers to discard registers and whose image avoids the discard
    set on every written name, running the renamed block preserves `Reindexed`: the
    renamed block computes at `ρ n` exactly what the original computes at `n`. The single
    source for the x86 `regalloc_runBlock_sound` and A64 `renameABlock_runABlock`, by
    induction, no new custom axioms. -/
theorem renameBlock_runBlock (I : Type) [RegMachine I S] (ρ : String → String)
    (hinj : Function.Injective ρ) (hρd : ∀ r, rmDisc I S r = true → rmDisc I S (ρ r) = true)
    (hρnd : ∀ r, rmDisc I S r = false → rmDisc I S (ρ r) = false)
    (block : List I) (hz : ∀ i ∈ block, ∀ n ∈ writtenNames i, rmDisc I S n = false)
    (s t : S) (h : Reindexed I ρ s t) :
    Reindexed I ρ (rmRun I s block) (rmRun I t (renameBlock (S := S) ρ block)) := by
  induction block generalizing s t with
  | nil =>
    rw [show renameBlock (S := S) ρ [] = [] from rfl, rmRun_nil, rmRun_nil]; exact h
  | cons i is ih =>
    rw [renameBlock_cons, rmRun_cons I s i is,
      rmRun_cons I t (rmRename S ρ i) (renameBlock (S := S) ρ is)]
    apply ih (s := rmRun I s [i]) (t := rmRun I t [rmRename S ρ i])
    · intro j hj; exact hz j (List.mem_cons_of_mem _ hj)
    · exact evalInst_rename_preserves I ρ hinj hρd hρnd s t i (hz i (List.mem_cons_self ..)) h

/-! ## 4. The spill-path checker: the spill-store / reload-roundtrip sandwich

For spilled names the allocator inserts a store after the def and a reload before
each use. We model the spill store / reload load over an abstract **memory-extended**
state (`MemMachine`: register `get`, frame `load`, register `setReg`, frame `store`,
with their four laws), and prove — once — that the store establishes the cell↦reg
invariant and the matching reload is a no-op under it. The shared core of the x86
`spillReload_sandwich_runBlock` and A64 `reload_sandwich`. -/

/-- An abstract memory-extended machine for the spill path: a register file
    (`get`/`setReg`) plus a frame memory (`load`/`store`), with the four cell/register
    laws. `M` is the memory-extended state type. The common shape of the x86 `JState`
    (regs+mem) and the A64 `AMemState`. -/
class MemMachine (M : Type) where
  /-- The register/cell value type. -/
  Val : Type
  /-- Read a register. -/
  get : M → String → Val
  /-- Read a frame cell. -/
  load : M → Int → Val
  /-- Write a register. -/
  setReg : M → String → Val → M
  /-- Write a frame cell. -/
  store : M → Int → Val → M
  /-- Reading back a just-written cell returns the stored value. -/
  load_store_same : ∀ (m : M) (off : Int) (v : Val), load (store m off v) off = v
  /-- A store leaves every other cell unchanged. -/
  load_store_other : ∀ (m : M) (off o : Int) (v : Val), o ≠ off → load (store m off v) o = load m o
  /-- A store leaves every register unchanged. -/
  get_store : ∀ (m : M) (off : Int) (v : Val) (r : String), get (store m off v) r = get m r
  /-- Writing register `r` a value it already holds is a no-op (idempotent reload). -/
  setReg_get_self : ∀ (m : M) (r : String), setReg m r (get m r) = m

variable {M : Type}

/-- The spill store: write `r`'s value to cell `off`. -/
def evalSpillStore [MemMachine M] (m : M) (off : Int) (r : String) : M :=
  MemMachine.store m off (MemMachine.get m r)

/-- The reload load: write cell `off`'s value back into register `r`. -/
def evalReload [MemMachine M] (m : M) (r : String) (off : Int) : M :=
  MemMachine.setReg m r (MemMachine.load m off)

/-- `SpillValid off r m`: cell `off` holds register `r`'s value in `m`. -/
def SpillValid [MemMachine M] (off : Int) (r : String) (m : M) : Prop :=
  MemMachine.load m off = MemMachine.get m r

/-- **The spill store establishes `SpillValid`.** After storing `r` to `off`, the cell
    holds `r`'s value. The generic source for the x86/A64 `spillStore_establishes`. -/
theorem spillStore_establishes [MemMachine M] (m : M) (off : Int) (r : String) :
    SpillValid off r (evalSpillStore m off r) := by
  unfold SpillValid evalSpillStore
  rw [MemMachine.load_store_same, MemMachine.get_store]

/-- **The reload is a no-op when the cell agrees with the register.** Under
    `SpillValid`, the reload rewrites `r` to a value it already holds. The generic
    source for the x86 `evalInstr_reload_noop` and A64 `evalReload_noop`. -/
theorem evalReload_noop [MemMachine M] (m : M) (off : Int) (r : String)
    (hv : SpillValid off r m) : evalReload m r off = m := by
  unfold SpillValid at hv
  unfold evalReload
  rw [hv, MemMachine.setReg_get_self]

/-- The spill store changes only its own cell (the disjointness a later reload of a
    different cell relies on). -/
theorem evalSpillStore_other_cell [MemMachine M] (m : M) (off o : Int) (r : String)
    (h : o ≠ off) : MemMachine.load (evalSpillStore m off r) o = MemMachine.load m o := by
  unfold evalSpillStore
  rw [MemMachine.load_store_other _ _ _ _ h]

/-- **Single-spill roundtrip soundness (the generic sandwich).** Starting from a state
    `m'` with the spill cell still holding `r` (`SpillValid`, established by the matching
    store and maintained by a cell-preserving body), the reload before `r`'s use is a
    no-op. The generic source for the x86 `spillReload_sandwich_runBlock` and A64
    `reload_sandwich`. -/
theorem reload_sandwich [MemMachine M] (m' : M) (off : Int) (r : String)
    (hv : SpillValid off r m') : evalReload m' r off = m' :=
  evalReload_noop m' off r hv

/-! ## 5. The rewrite-length decomposition (the checker's accounting)

`rewriteInstr` surrounds each instruction with the reload loads (one per spilled
source) and spill stores (one per spilled destination) the decisions dictate; the
resident names are renamed by the printer. The length decomposition is proved
generically over `[MachineModel I S]` (the generic `spillReloadBlock_length`). -/

/-- The reload instructions one instruction needs (one per spilled source). -/
def reloadsOf [MachineModel I] (decisions : List (String × Slot)) (i : I) : List I :=
  (readNames i).filterMap (fun n =>
    (spillSlotOf decisions n).map (fun off => mkReload n off))

/-- The store instructions one instruction needs (one per spilled destination). -/
def storesOf [MachineModel I] (decisions : List (String × Slot)) (i : I) : List I :=
  (writtenNames i).filterMap (fun n =>
    (spillSlotOf decisions n).map (fun off => mkSpill n off))

/-- One instruction surrounded by its reloads (before) and stores (after). -/
def rewriteInstr [MachineModel I] (decisions : List (String × Slot)) (i : I) : List I :=
  reloadsOf decisions i ++ (i :: storesOf decisions i)

/-- The rewritten block: every instruction surrounded by its spill traffic. -/
def rewriteBlock [MachineModel I] (decisions : List (String × Slot)) (block : List I) :
    List I :=
  block.flatMap (rewriteInstr decisions)

/-- Number of reload loads inserted over the whole block. -/
def reloadCount [MachineModel I] (decisions : List (String × Slot)) (block : List I) : Nat :=
  (block.flatMap (reloadsOf decisions)).length

/-- Number of spill stores inserted over the whole block. -/
def storeCount [MachineModel I] (decisions : List (String × Slot)) (block : List I) : Nat :=
  (block.flatMap (storesOf decisions)).length

/-- `rewriteInstr` is exactly `reloadsOf ++ (i :: storesOf)`. -/
theorem rewriteInstr_eq [MachineModel I] (decisions : List (String × Slot)) (i : I) :
    rewriteInstr decisions i
      = reloadsOf decisions i ++ (i :: storesOf decisions i) := rfl

/-- **The rewritten block's length = original + reloads + stores** (the generic
    `spillReloadBlock_length`): the emitted body is one machine instruction per
    verified op plus exactly the spill traffic the allocator inserted — not a
    load/store per op. -/
theorem rewriteBlock_length [MachineModel I] (decisions : List (String × Slot))
    (block : List I) :
    (rewriteBlock decisions block).length
      = block.length + reloadCount decisions block + storeCount decisions block := by
  unfold rewriteBlock reloadCount storeCount
  induction block with
  | nil => rfl
  | cons i is ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.length_append,
      rewriteInstr_eq, List.length_append, List.length_cons,
      List.length_append, List.length_append, List.length_cons]
    omega

/-! ## 6. Byte separation of frame slots

`Slot.spilled off` records a **byte** offset, and one spilled value occupies the bytes
`[off, off + width)` where `width` is the byte width of the allocated value. Two spill
slots are usable independently exactly when those byte ranges are disjoint — `SepAt`.
Distinctness of the offsets is strictly weaker: at `width = 32` the offsets `0` and `8`
are distinct and their ranges overlap.

`SlotsSeparated width decisions` is the whole-allocation form of the condition, and
`linearScan_slotsSeparated` discharges it from the allocator's own frame stride: at
`width ≤ stride` the offsets `linearScan` assigns are pairwise separated. -/

/-- `SepAt width a b`: the `width`-byte accesses at byte offsets `a` and `b` cover
    disjoint byte ranges — `[a, a + width)` ends at or before `b`, or the other way
    round. -/
def SepAt (width : Nat) (a b : Int) : Prop := a + width ≤ b ∨ b + width ≤ a

instance instDecidableSepAt (width : Nat) (a b : Int) : Decidable (SepAt width a b) := by
  unfold SepAt; infer_instance

/-- Separation is symmetric. -/
theorem SepAt.symm {width : Nat} {a b : Int} (h : SepAt width a b) : SepAt width b a := Or.symm h

/-- Separated offsets are distinct, at a positive width. The converse fails: distinct
    offsets closer together than `width` overlap. -/
theorem SepAt.ne {width : Nat} {a b : Int} (hw : 0 < width) (h : SepAt width a b) : a ≠ b := by
  rcases h with h | h <;> omega

/-- **Distinct offsets on a `width`-aligned grid are separated.** The cell-indexed frame
    of `MemMachine` — one cell per value, distinct cells disjoint by construction — is the
    byte-addressed frame restricted to the multiples of `width`, and this is why: on that
    grid, offset distinctness already gives byte-range disjointness. -/
theorem sepAt_of_aligned (width : Nat) (i j : Int) (h : i ≠ j) :
    SepAt width (width * i) (width * j) := by
  have hw : (0 : Int) ≤ width := Int.natCast_nonneg width
  rcases Int.lt_or_lt_of_ne h with hlt | hgt
  · exact Or.inl (by simpa [Int.mul_add] using Int.mul_le_mul_of_nonneg_left (a := i + 1) hlt hw)
  · exact Or.inr (by simpa [Int.mul_add] using Int.mul_le_mul_of_nonneg_left (a := j + 1) hgt hw)

/-- Any two members of a pairwise-separated offset list are separated (separation is
    symmetric, so the list order carries no information). -/
theorem sepAt_of_pairwise_mem {width : Nat} {l : List Int} (hl : l.Pairwise (SepAt width))
    {a b : Int} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) : SepAt width a b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rcases List.pairwise_cons.mp hl with ⟨hx, hxs⟩
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hab
      · exact hx b hb'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact (hx a ha').symm
      · exact ih hxs ha' hb'

/-- The byte offsets a decision list spills to. -/
def slotOffsets (decisions : List (String × Slot)) : List Int :=
  decisions.filterMap (fun d => match d.2 with | .spilled off => some off | _ => none)

/-- **The whole-allocation separation obligation.** Every two frame slots of `decisions`
    cover disjoint byte ranges at value width `width`. This is the condition a spill/reload
    argument over a byte-addressed frame needs, and the condition
    `(slotOffsets decisions).Nodup` is the weaker distinctness form of. -/
def SlotsSeparated (width : Nat) (decisions : List (String × Slot)) : Prop :=
  (slotOffsets decisions).Pairwise (SepAt width)

instance instDecidableSlotsSeparated (width : Nat) (decisions : List (String × Slot)) :
    Decidable (SlotsSeparated width decisions) := by
  unfold SlotsSeparated; infer_instance

/-- **Separation refines distinctness**: separated slots have distinct offsets, so
    `SlotsSeparated width` implies the `Nodup` condition, at a positive width. -/
theorem slotOffsets_nodup_of_slotsSeparated {width : Nat} {decisions : List (String × Slot)}
    (hw : 0 < width) (h : SlotsSeparated width decisions) : (slotOffsets decisions).Nodup :=
  h.imp (SepAt.ne hw)

/-- The scan invariant: an offset already emitted lies at least `stride` below the next
    free offset, so every new slot is separated from all earlier ones. -/
theorem linearScanGo_pairwise (width : Nat) (stride : Int) (hw : (width : Int) ≤ stride) :
    ∀ (lrs : List LiveRange) (active : List (String × String × Nat)) (freeRegs : List String)
      (nextSpill : Int) (acc : List (String × Slot)),
      (∀ o ∈ slotOffsets acc, o + stride ≤ nextSpill) →
      (slotOffsets acc).Pairwise (SepAt width) →
      (slotOffsets (linearScanGo stride active freeRegs nextSpill acc lrs)).Pairwise
        (SepAt width) := by
  have hw0 : (0 : Int) ≤ (width : Int) := Int.natCast_nonneg _
  intro lrs
  induction lrs with
  | nil => intro active freeRegs nextSpill acc _ hp; exact hp
  | cons lr rest ih =>
    intro active freeRegs nextSpill acc hacc hp
    have hres : ∀ (l : List (String × Slot)), slotOffsets l = slotOffsets acc →
        ((∀ o ∈ slotOffsets l, o + stride ≤ nextSpill)
          ∧ (slotOffsets l).Pairwise (SepAt width)) := by
      intro l hl
      rw [hl]; exact ⟨hacc, hp⟩
    have hspill : ∀ (l : List (String × Slot)),
        slotOffsets l = nextSpill :: slotOffsets acc →
        ((∀ o ∈ slotOffsets l, o + stride ≤ nextSpill + stride)
          ∧ (slotOffsets l).Pairwise (SepAt width)) := by
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

/-- **The linear scan's frame stride discharges the separation obligation.** When the
    frame stride is at least the byte width of an allocated value, the slots `linearScan`
    assigns cover pairwise-disjoint byte ranges. At `width > stride` the conclusion is not
    available — a `%ymm` value (`width = 32`) spilled by the default 8-byte scan has
    overlapping slots, and this is the theorem that says so by failing to apply. -/
theorem linearScan_slotsSeparated (width : Nat) (pool : List String) (frameBase : Int)
    (lrs : List LiveRange) (stride : Int) (hw : (width : Int) ≤ stride) :
    SlotsSeparated width (linearScan pool frameBase lrs stride) :=
  linearScanGo_pairwise width stride hw _ [] pool frameBase [] (by simp [slotOffsets])
    (by simp [slotOffsets])

/-- The same for `spillAlloc`: a block's spill decisions are separated at any value width
    the frame stride covers. -/
theorem spillAlloc_slotsSeparated [MachineModel I] (width : Nat) (pinned scratch : List String)
    (frameBase : Int) (block : List I) (stride : Int) (hw : (width : Int) ≤ stride) :
    SlotsSeparated width (spillAlloc (I := I) pinned scratch frameBase block stride) :=
  linearScan_slotsSeparated width _ frameBase _ stride hw

/-! ## 8. Straight-line allocation with eviction by furthest next read

`linearScan` gives each value one decision for its whole live range. `nextUseAlloc`
splits live ranges instead: a value stays in its register until it dies or is evicted,
and an evicted value is loaded back into a free register before its next read. The victim
is the resident value, not read by the current step, whose next read is furthest (Belady's
rule), preferring among equals one that needs no store. A value needs no store when it has
a home location (an input region it can be loaded from again) or a spill slot already
holds it; values are single-assignment, so a stored copy stays valid. Values and registers
are numbers; the caller maps them to its names. The allocator is untrusted: its output is
checked by a translation validator. -/

/-- A step of a straight-line program as `nextUseAlloc` reads it. -/
structure NUStep where
  /-- The values the step reads. -/
  reads : List Nat
  /-- The values the step writes, after its reads. -/
  writes : List Nat

/-- A move `nextUseAlloc` places before a step. -/
inductive NUMove where
  /-- Store register `reg`, which holds value `v`, to spill slot `slot`. -/
  | store (v reg slot : Nat)
  /-- Load value `v` into register `reg` from spill slot `slot`, or from the home location
      of `v` when `slot = none`. -/
  | load (v reg : Nat) (slot : Option Nat)
  deriving Repr, DecidableEq

/-- The allocation of one step: the moves before it and the register of each value it
    reads or writes. -/
structure NUStepAlloc where
  /-- The moves, in order. -/
  moves : List NUMove
  /-- The register of each value the step reads or writes. -/
  regs : List (Nat × Nat)
  deriving Repr

/-- The state of `nextUseAlloc`. -/
structure NUState where
  /-- The register holding each value. -/
  regOf : Array (Option Nat)
  /-- The value each register holds. -/
  holder : Array (Option Nat)
  /-- The spill slot holding a copy of each value. -/
  slotOf : Array (Option Nat)
  /-- For each value, the position of its next read in its list of reading steps. -/
  ptr : Array Nat
  /-- The free registers. -/
  free : List Nat
  /-- The released spill slots. -/
  freeSlots : List Nat
  /-- The number of spill slots used. -/
  nSlots : Nat

/-- The next step reading `v`, from its reading steps `uses`. -/
def nuNextRead (uses : Array (Array Nat)) (st : NUState) (v : Nat) : Option Nat :=
  (uses.getD v #[])[st.ptr.getD v 0]?

/-- Whether an evicted `v` needs no store: it has a home location or a slot holds it. -/
def nuClean (home : Nat → Bool) (st : NUState) (v : Nat) : Bool :=
  home v || (st.slotOf.getD v none).isSome

/-- The register and value to evict: among the registers of `pool` holding a value
    outside `protect`, the one whose next read is furthest (`big` when there is none),
    a value needing no store preferred among equals. -/
def nuVictim (uses : Array (Array Nat)) (home : Nat → Bool) (big : Nat) (pool : List Nat)
    (st : NUState) (protect : List Nat) : Option (Nat × Nat) :=
  let best := pool.foldl (fun (best : Option (Nat × Nat × Nat)) r =>
    match st.holder.getD r none with
    | none => best
    | some v =>
      if protect.contains v then best else
      let key := 2 * (nuNextRead uses st v).getD big + (if nuClean home st v then 1 else 0)
      match best with
      | some (_, _, k) => if key > k then some (r, v, key) else best
      | none => some (r, v, key)) none
  best.map (fun (r, v, _) => (r, v))

/-- A register for a new occupant: the head of the free list, or else the register of the
    victim `nuVictim` picks, with the store of the victim when it needs one. The returned
    register holds no value in the returned state. -/
def nuGrab (uses : Array (Array Nat)) (home : Nat → Bool) (big : Nat) (pool : List Nat)
    (st : NUState) (protect : List Nat) : Except String (Nat × List NUMove × NUState) :=
  match st.free with
  | r :: rest => .ok (r, [], { st with free := rest })
  | [] =>
    match nuVictim uses home big pool st protect with
    | none => .error "nextUseAlloc: no register to evict"
    | some (r, v) =>
      let clean := nuClean home st v
      let st := { st with regOf := st.regOf.setIfInBounds v none,
                          holder := st.holder.setIfInBounds r none }
      if clean then .ok (r, [], st)
      else
        let (s, st) := match st.freeSlots with
          | s :: rest => (s, { st with freeSlots := rest })
          | [] => (st.nSlots, { st with nSlots := st.nSlots + 1 })
        .ok (r, [.store v r s], { st with slotOf := st.slotOf.setIfInBounds v (some s) })

/-- The state with value `v` in register `r`. -/
def nuPlace (st : NUState) (v r : Nat) : NUState :=
  { st with regOf := st.regOf.setIfInBounds v (some r),
            holder := st.holder.setIfInBounds r (some v) }

/-- The state after value `v` dies: its register returns to the tail of the free list and
    its spill slot to the released slots. -/
def nuRelease (st : NUState) (v : Nat) : NUState :=
  let st := match st.regOf.getD v none with
    | some r => { st with regOf := st.regOf.setIfInBounds v none,
                          holder := st.holder.setIfInBounds r none, free := st.free ++ [r] }
    | none => st
  match st.slotOf.getD v none with
  | some s => { st with slotOf := st.slotOf.setIfInBounds v none,
                        freeSlots := s :: st.freeSlots }
  | none => st

/-- One step of `nextUseAlloc` at index `i`: every value read is made resident (loaded
    from its slot or its home), the values read for the last time die, and each value
    written takes a register, evicting when none is free; a value written and never read
    dies at once. -/
def nuStep (uses : Array (Array Nat)) (home : Nat → Bool) (big : Nat) (pool : List Nat)
    (st0 : NUState) (i : Nat) (s : NUStep) : Except String (NUStepAlloc × NUState) := do
  let reads := s.reads.eraseDups
  let mut st := st0
  let mut moves : Array NUMove := #[]
  for v in reads do
    if (st.regOf.getD v none).isNone then
      let src := st.slotOf.getD v none
      if src.isNone && !home v then
        throw s!"nextUseAlloc: value {v} read at step {i} before it is written"
      let (r, mv, st') ← nuGrab uses home big pool st reads
      st := nuPlace st' v r
      moves := (moves ++ mv.toArray).push (.load v r src)
  let readRegs := reads.map (fun v => (v, (st.regOf.getD v none).getD 0))
  for v in reads do
    st := { st with ptr := st.ptr.modify v (· + 1) }
    if (nuNextRead uses st v).isNone then
      st := nuRelease st v
  let mut writeRegs : Array (Nat × Nat) := #[]
  for w in s.writes do
    let (r, mv, st') ← nuGrab uses home big pool st s.writes
    st := nuPlace st' w r
    moves := moves ++ mv.toArray
    writeRegs := writeRegs.push (w, r)
  for w in s.writes do
    if (nuNextRead uses st w).isNone then
      st := nuRelease st w
  pure ({ moves := moves.toList, regs := readRegs ++ writeRegs.toList }, st)

/-- **Straight-line allocation with split live ranges.** Allocates the values
    `0..nValues-1` of `steps` to the registers `pool` (free list in that order), a value
    `v` with `home v` loadable from its home location. Returns, per step, the moves before
    it and the registers of the values it reads and writes, and the number of spill slots
    used. Fails when a value without a home is read before it is written, or when a step
    needs more registers than the pool has. -/
def nextUseAlloc (nValues : Nat) (pool : List Nat) (home : Nat → Bool)
    (steps : Array NUStep) : Except String (Array NUStepAlloc × Nat) := do
  let uses : Array (Array Nat) := steps.zipIdx.foldl
    (fun u (s, i) => s.reads.eraseDups.foldl (fun u v => u.modify v (·.push i)) u)
    (Array.replicate nValues #[])
  let st0 : NUState :=
    { regOf := .replicate nValues none, holder := .replicate (pool.foldl max 0 + 1) none,
      slotOf := .replicate nValues none, ptr := .replicate nValues 0, free := pool,
      freeSlots := [], nSlots := 0 }
  let (out, st) ← steps.zipIdx.foldlM
    (fun (acc : Array NUStepAlloc × NUState) (s, i) => do
      let (a, st) ← nuStep uses home (steps.size + 1) pool acc.2 i s
      pure (acc.1.push a, st)) (#[], st0)
  pure (out, st.nSlots)

end CatCrypt.Crypto.Optimizer.GenericRegAlloc
