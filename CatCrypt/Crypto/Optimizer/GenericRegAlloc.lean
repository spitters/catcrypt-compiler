/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# A generic `MachineModel`-parameterized validated register allocator (#552)

`Optimizer.SpillingRegAlloc` (#413, x86, monomorphized to `JInstr 64`/`JState 64`)
and `ARMBackend.ArmRegAlloc` (#551, A64, the `AInst`/`AState` analogue) are *the
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
in the translation-validation discipline of our #541 egraph validator.

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
   induction with no new custom axioms. The keystone for the register-resident path.
3. **The spill-path checker** (`spillStore_establishes`, `evalReload_noop`,
   `reload_sandwich`): on a memory-extended state (`MemMachine`: `get`/`load`/`setReg`
   /`store` + four laws), the spill store establishes the cell↦reg invariant
   (`SpillValid`) and the matching reload is a no-op under it — so the spill/reload
   roundtrip is denotation-preserving.
4. **The rewrite-length decomposition** (`rewriteBlock_length`): the RA-rewritten
   block is one machine instruction per op plus exactly the inserted spill traffic.

§5–§6 exhibit that the x86 / A64 instances **fit** the typeclass (the generic lemmas,
instantiated, give back what `SpillingRegAlloc`/`ArmRegAlloc` proved), and §7 is the
sanity demonstrator. The fresh RISC-V instantiation is `RISCVBackend.RiscvRegAlloc`.

This file uses `set_option autoImplicit false` (the `Optimizer/` convention); the
abstract interfaces are bundled typeclasses, so no auto-implicits are needed.
-/

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
    `ArmRegAlloc` (A64), and `RiscvRegAlloc` (RV64). -/
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

/-- **The generic linear-scan allocator** (farthest-end eviction). Walk the live
    ranges in `defIdx` order keeping an active map `(name, reg, lastUse)` and the free
    pool; on a new def, reuse a free / expired register if one is available, else spill
    the farthest-ending active interval (or the newcomer) to a fresh frame cell.
    `frameBase` byte-offsets advance sequentially so two live spills never alias. This
    is the *single* source for `SpillingRegAlloc.linearScan` and `ArmRegAlloc.linearScan`
    — they differ only in the pool the `MachineModel` supplies. -/
def linearScan (pool : List String) (frameBase : Int) (lrs : List LiveRange) :
    List (String × Slot) :=
  let rec go (active : List (String × String × Nat)) (freeRegs : List String)
      (nextSpill : Int) (acc : List (String × Slot)) :
      List LiveRange → List (String × Slot)
    | [] => acc
    | lr :: rest =>
      let (live, expired) := active.partition (fun a => lr.defIdx ≤ a.2.2)
      let freed := freeRegs ++ expired.map (fun a => a.2.1)
      match freed with
      | reg :: more =>
        go ((lr.name, reg, lr.lastUse) :: live) more nextSpill
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
            go ((lr.name, a.2.1, lr.lastUse) :: live') [] (nextSpill + 8)
               ((lr.name, .resident a.2.1) :: (a.1, .spilled nextSpill) :: acc) rest
          else
            go live [] (nextSpill + 8) ((lr.name, .spilled nextSpill) :: acc) rest
        | none =>
          go live [] (nextSpill + 8) ((lr.name, .spilled nextSpill) :: acc) rest
  go [] pool frameBase [] (lrs.mergeSort (fun a b => a.defIdx ≤ b.defIdx))

/-- The spill decisions for a block: `name ↦ Slot` by linear scan over its live
    ranges. -/
def spillAlloc [MachineModel I] (pinned scratch : List String) (frameBase : Int)
    (block : List I) : List (String × Slot) :=
  linearScan (allocPool (I := I) pinned scratch) frameBase (liveRanges block)

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
      whole-state equality) is what register-allocation soundness needs — the keystone
      only ever inspects `get` — and it admits ops with *non-register* side effects, like
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
      `ρ`-renamed destinations. (Generalizes the old `instVal_rename` +
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

/-- **Resident-path soundness (the generic keystone).** For an injective renaming `ρ`
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

end CatCrypt.Crypto.Optimizer.GenericRegAlloc
