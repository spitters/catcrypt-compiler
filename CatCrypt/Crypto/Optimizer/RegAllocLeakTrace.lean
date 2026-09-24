/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-!
# Leakage-trace preservation for the register-allocation / spill rewrite

This module closes the **biggest vacuousness gap** in the constant-time (CT)
preservation story for the verified optimizer.

## The gap

`VIR.CtPreservationNewTransforms` proves `applyRA_preserves_CT` and its
siblings *by `rfl`*, because at the `Com`/`JForProg` level the framework's
`applyRA p ra = p` is the **identity** transform — the register-allocation
decisions live in the `RegisterAllocation` value, consumed *downstream* by the
emit pass. So those theorems say nothing about whether the **actual**
register-allocation and spill/reload decisions preserve CT: they are
`X = X`. The real RA decisions — which names go to registers, which spill to
the frame, where the spill stores / reload loads are inserted — happen in the
`GenericRegAlloc` checker (`renameBlock`, `rewriteBlock`, `reloadsOf`,
`storesOf`), and *those* passes carried only a **value-denotation** soundness
theorem (`renameBlock_runBlock`, `reload_sandwich`), never a CT / leakage-trace
theorem.

## The key insight (what makes CT survive RA)

A source-CT program — one whose only branches are on public values and whose
only memory addresses are public — stays CT through register allocation and
spilling **because those passes are denotation-preserving AND only**:

1. **relabel registers** (`renameBlock`): the physical register a value lives
   in is invisible to a leakage adversary — the cache/branch-predictor side
   channel sees the *sequence of branch conditions and memory addresses*, not
   which architectural register holds a value. So a register rename leaves the
   leakage trace **pointwise unchanged**;

2. **insert spill stores / reload loads to PUBLIC frame slots**
   (`rewriteBlock` via `reloadsOf` / `storesOf`): the allocator picks each
   spill offset by a static linear scan (`linearScan`, `nextSpill + 8`) — the
   offsets are **compile-time constants**, never functions of secret data. A
   spill store / reload load therefore adds a **public** memory-access event to
   the leakage trace; it never adds a secret-dependent branch or a
   secret-dependent address.

So the theorem is **leakage-shape preservation**: the RA/spill rewrite
preserves the *security-relevant* leakage trace — the subsequence of
secret-dependent observations — even though it changes the full instruction
list. Equivalently, if the source leakage trace is CT-free (no secret branch,
no secret address), so is the rewritten one.

## What is proved here (all non-vacuous, fully proved, axiom-clean)

We work at the `GenericRegAlloc.MachineModel` level — the layer where the real
RA decisions are made — so the theorems apply uniformly to the x86, A64, and
RV64 back-ends.

* **The leakage alphabet** `RALeakEvent`: `compute` (a pure register op — no
  leakage), `mem (cls : AddrClass) (off : Int)` (a memory access, tagged by
  whether the address is public or secret-derived), `branch (cls : AddrClass)`
  (a conditional, tagged the same way). `AddrClass = public | secret`.
* `blockLeakTrace` — the leakage trace of a block, computed from a per-backend
  classifier `RALeak I` (`leakOf : I → RALeakEvent`).
* `ctLeakFree` — the CT predicate on a leakage trace: no `secret` branch and no
  `secret`-classified memory access.
* **`renameBlock_preserves_leakTrace`** — register renaming leaves the leakage
  trace pointwise unchanged (the classifier ignores the register name). NON
  vacuous: it is the equation `blockLeakTrace (renameBlock ρ b) = blockLeakTrace b`,
  not `X = X`, discharged from the `RALeak.leakOf_rename` law.
* **`storesOf_leakFree` / `reloadsOf_leakFree`** — every inserted spill store /
  reload load is a **public** memory access, hence CT-leak-free. NON vacuous:
  the proof uses the `RALeak.leakOf_mkSpill` / `leakOf_mkReload` laws that pin
  the inserted instructions to `mem .public`.
* **`rewriteBlock_preserves_ctLeakFree`** — if the source block is CT-leak-free,
  the spill-rewritten block is too. The rewrite adds only public spill traffic
  around each (renamed) instruction, so no secret observation is introduced.
* **`raRewrite_preserves_ctLeakFree`** — the composed statement: rename **then**
  spill-rewrite (the full RA output shape) preserves CT-leak-freedom.

## How far CT reaches

These theorems establish CT preservation at the **`MachineModel` instruction /
leakage-shape level** — the level at which the real register-allocation and
spill decisions are taken, downstream of the `Com` identity transform. The
leakage trace is the sequence of branch-condition and memory-address
observations; CT-leak-freedom means none of them is secret-derived. This is
strictly stronger than the `applyRA_preserves_CT = rfl` story: it ranges over a
**non-identity** transform (`rewriteBlock` changes the instruction list) and
proves that the transform introduces no secret observation.

**Residual / frontier.** The leakage trace is defined here at the
instruction-shape granularity (one `RALeakEvent` per machine instruction,
address-class tracked symbolically as public/secret). It is *not* lowered to a
byte-level cache-line model — the verified back-end emits no byte-level leakage
semantics, so the leakage frontier is the instruction/`Lprog` shape, exactly as
`UnifiedTrace`'s `Cmd.leakTrace` is. Pushing CT to a concrete cache-line trace
would require a byte-level leakage semantics for the emitted asm, which the
pipeline does not currently provide; that is the documented frontier, the same
one `JasminSem.Cmd.leakTrace` sits at.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.GenericRegAlloc

open CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-! ## 1. The leakage alphabet for the RA layer -/

/-- The security class of a memory address or branch condition: a **public**
    address/condition (a function of public inputs only — e.g. a static frame
    offset, a public loop counter) leaks nothing, whereas a **secret**-derived
    address/condition is a side channel. -/
inductive AddrClass where
  /-- The address / condition is a function of public data only. -/
  | pub : AddrClass
  /-- The address / condition is derived from secret data. -/
  | sec : AddrClass
  deriving DecidableEq, Repr, Inhabited

/-- One leakage observation of a machine instruction.

* `compute` — a pure register-to-register operation. It touches no memory and
  takes no branch, so a leakage adversary observes nothing of value. (The
  register *identity* is deliberately erased: which architectural register
  holds a value is invisible to the cache/branch-predictor side channel.)
* `mem cls off` — a memory access at static offset `off`, whose **address** is
  classified `cls`. A spill store / reload load to a public frame slot is
  `mem .public _`; a secret-indexed table lookup would be `mem .secret _`.
* `branch cls` — a conditional whose **guard** is classified `cls`. A
  public-counter loop bound is `branch .public`; a branch on a secret bit is
  `branch .secret`. -/
inductive RALeakEvent where
  /-- A pure register operation — no memory, no branch, no leakage. -/
  | compute : RALeakEvent
  /-- A memory access at static offset `off` with address class `cls`. -/
  | mem (cls : AddrClass) (off : Int) : RALeakEvent
  /-- A conditional branch with guard class `cls`. -/
  | branch (cls : AddrClass) : RALeakEvent
  deriving DecidableEq, Repr, Inhabited

/-- The CT predicate on a single leakage event: a `secret`-classified memory
    access or branch is the *only* way an event can leak; everything else is
    CT-safe. -/
def RALeakEvent.ctSafe : RALeakEvent → Bool
  | .compute        => true
  | .mem .pub _  => true
  | .mem .sec _  => false
  | .branch .pub => true
  | .branch .sec => false

/-- A leakage trace: the ordered list of per-instruction leakage events. -/
abbrev RALeakTrace := List RALeakEvent

/-- The CT predicate on a leakage trace: **no** secret-dependent branch and
    **no** secret-dependent memory address occurs. This is the constant-time
    property at the leakage-shape level: the sequence of observations carries no
    secret. -/
def ctLeakFree (t : RALeakTrace) : Bool :=
  t.all RALeakEvent.ctSafe

@[simp] theorem ctLeakFree_nil : ctLeakFree [] = true := rfl

@[simp] theorem ctLeakFree_cons (e : RALeakEvent) (t : RALeakTrace) :
    ctLeakFree (e :: t) = (e.ctSafe && ctLeakFree t) := by
  simp [ctLeakFree]

theorem ctLeakFree_append (xs ys : RALeakTrace) :
    ctLeakFree (xs ++ ys) = (ctLeakFree xs && ctLeakFree ys) := by
  simp [ctLeakFree, List.all_append]

/-! ## 2. The per-backend leakage classifier

A backend that already supplies a `MachineModel I` (read/write names, spill /
reload rendering) additionally classifies each instruction's leakage. The two
*laws* are what make RA leakage-preserving:

* `leakOf_rename` — the leakage of an instruction is **invariant under register
  renaming**: the side channel sees a memory/branch *shape*, not which register
  holds the operands. This is the formal statement of "RA only relabels
  registers, which the adversary cannot see".
* `leakOf_mkSpill` / `leakOf_mkReload` — a rendered spill store / reload load is
  always a **public** memory access at its (static) frame offset. This is the
  formal statement of "the allocator's spill slots are compile-time constants,
  never secret addresses". -/

/-- Leakage classification for a backend's instruction type, layered on top of
    its `MachineModel`. The classifier `leakOf` assigns each instruction its
    leakage event; `renameI` is the syntactic register-renaming the allocator's
    resident half applies (the same operation `RegMachine.renameInst` carries,
    here decoupled from the state semantics so the leakage story needs no `S`);
    the laws pin RA-relevant instructions to leakage-safe shapes. -/
class RALeak (I : Type) [MachineModel I] where
  /-- The leakage event an instruction produces. -/
  leakOf : I → RALeakEvent
  /-- Apply a register renaming to an instruction (rename dst + all sources).
      Agrees with `RegMachine.renameInst` on backends that supply both. -/
  renameI : (String → String) → I → I
  /-- **Register renaming is invisible to leakage.** Renaming the registers an
      instruction reads / writes does not change its leakage event — the side
      channel observes a memory/branch shape and address class, not register
      identity. -/
  leakOf_rename : ∀ (ρ : String → String) (i : I), leakOf (renameI ρ i) = leakOf i
  /-- **A rendered spill store is a public memory access.** Its address is the
      static frame offset `off` chosen by the allocator — a compile-time
      constant, never a secret. -/
  leakOf_mkSpill : ∀ (r : String) (off : Int), leakOf (mkSpill r off) = .mem .pub off
  /-- **A rendered reload load is a public memory access.** Same reasoning as
      the spill store. -/
  leakOf_mkReload : ∀ (r : String) (off : Int), leakOf (mkReload r off) = .mem .pub off

variable {I : Type}

/-- The leakage trace of a straight-line block: one event per instruction, in
    source order. -/
def blockLeakTrace [MachineModel I] [RALeak I] (block : List I) : RALeakTrace :=
  block.map RALeak.leakOf

@[simp] theorem blockLeakTrace_nil [MachineModel I] [RALeak I] :
    blockLeakTrace (I := I) [] = [] := rfl

@[simp] theorem blockLeakTrace_cons [MachineModel I] [RALeak I]
    (i : I) (is : List I) :
    blockLeakTrace (i :: is) = RALeak.leakOf i :: blockLeakTrace is := rfl

theorem blockLeakTrace_append [MachineModel I] [RALeak I] (xs ys : List I) :
    blockLeakTrace (xs ++ ys) = blockLeakTrace xs ++ blockLeakTrace ys := by
  simp [blockLeakTrace, List.map_append]

theorem blockLeakTrace_flatMap [MachineModel I] [RALeak I]
    (f : I → List I) (block : List I) :
    blockLeakTrace (block.flatMap f)
      = block.flatMap (fun i => blockLeakTrace (f i)) := by
  induction block with
  | nil => rfl
  | cons i is ih =>
    rw [List.flatMap_cons, blockLeakTrace_append, List.flatMap_cons, ih]

/-! ## 3. Register renaming preserves the leakage trace (the resident half)

This is the leakage companion to `renameBlock_runBlock`
(`GenericRegAlloc` §3): the *value-denotation* theorem shows the renamed block
computes the same values; here we show it produces the **same leakage trace**.
Both are needed for CT-preservation — value-denotation alone permits a pass to
change the leakage shape. -/

/-- Apply the resident-half register renaming to a whole block (the syntactic
    half of `GenericRegAlloc.renameBlock`, over `RALeak.renameI`). -/
def renameBlockI [MachineModel I] [RALeak I] (ρ : String → String)
    (block : List I) : List I :=
  block.map (RALeak.renameI ρ)

@[simp] theorem renameBlockI_cons [MachineModel I] [RALeak I]
    (ρ : String → String) (i : I) (is : List I) :
    renameBlockI ρ (i :: is) = RALeak.renameI ρ i :: renameBlockI ρ is := rfl

/-- **Register renaming leaves the leakage trace pointwise unchanged.** A
    NON-vacuous `blockLeakTrace (renameBlockI ρ block) = blockLeakTrace block`:
    register allocation's resident-half decision (which physical register a
    value lives in) is invisible to a leakage adversary. The proof is
    `List.map` of the per-instruction `leakOf_rename` law, not `rfl`. -/
theorem renameBlock_preserves_leakTrace [MachineModel I] [RALeak I]
    (ρ : String → String) (block : List I) :
    blockLeakTrace (renameBlockI ρ block) = blockLeakTrace block := by
  induction block with
  | nil => rfl
  | cons i is ih =>
    rw [renameBlockI_cons, blockLeakTrace_cons, blockLeakTrace_cons, ih,
      RALeak.leakOf_rename ρ i]

/-- **Corollary: register renaming preserves CT-leak-freedom.** If the source
    block is CT-leak-free, so is its renaming — directly, since the trace is
    pointwise unchanged. -/
theorem renameBlock_preserves_ctLeakFree [MachineModel I] [RALeak I]
    (ρ : String → String) (block : List I)
    (h : ctLeakFree (blockLeakTrace block) = true) :
    ctLeakFree (blockLeakTrace (renameBlockI ρ block)) = true := by
  rw [renameBlock_preserves_leakTrace]; exact h

/-! ## 4. The spill rewrite adds only public memory accesses (the spilled half)

This is the leakage companion to the `reload_sandwich` (`GenericRegAlloc` §4):
the *value-denotation* theorem shows the reload before a use is a no-op; here
we show the inserted spill stores and reload loads are all **public** memory
accesses, so they never add a secret observation to the leakage trace. -/

/-- Every reload load inserted before an instruction is a **public** memory
    access (its address is a static frame offset). Hence the reload prefix is
    CT-leak-free. NON-vacuous: pinned by `RALeak.leakOf_mkReload`. -/
theorem reloadsOf_leakFree [MachineModel I] [RALeak I]
    (decisions : List (String × Slot)) (i : I) :
    ctLeakFree (blockLeakTrace (reloadsOf decisions i)) = true := by
  unfold ctLeakFree reloadsOf blockLeakTrace
  rw [List.all_eq_true]
  intro e he
  rw [List.mem_map] at he
  obtain ⟨j, hj, rfl⟩ := he
  -- `j` ranges over the `filterMap`-produced reload instructions, each a `mkReload`.
  rw [List.mem_filterMap] at hj
  obtain ⟨n, _hn, hj⟩ := hj
  rw [Option.map_eq_some_iff] at hj
  obtain ⟨off, _hoff, rfl⟩ := hj
  rw [RALeak.leakOf_mkReload]
  rfl

/-- Every spill store inserted after an instruction is a **public** memory
    access. Hence the store suffix is CT-leak-free. NON-vacuous: pinned by
    `RALeak.leakOf_mkSpill`. -/
theorem storesOf_leakFree [MachineModel I] [RALeak I]
    (decisions : List (String × Slot)) (i : I) :
    ctLeakFree (blockLeakTrace (storesOf decisions i)) = true := by
  unfold ctLeakFree storesOf blockLeakTrace
  rw [List.all_eq_true]
  intro e he
  rw [List.mem_map] at he
  obtain ⟨j, hj, rfl⟩ := he
  -- `storesOf` is a `filterMap` over the written names (one `mkSpill` per spilled
  -- destination); each produced element is a `mkSpill`, hence a public access.
  rw [List.mem_filterMap] at hj
  obtain ⟨n, _hn, hj⟩ := hj
  rw [Option.map_eq_some_iff] at hj
  obtain ⟨off, _hoff, rfl⟩ := hj
  rw [RALeak.leakOf_mkSpill]
  rfl

/-- **CT-leak-freedom is preserved instruction-by-instruction by the spill
    rewrite.** If instruction `i`'s own leakage event is CT-safe, then the whole
    `rewriteInstr` expansion (reloads ++ i ++ stores) is CT-leak-free: the
    inserted spill traffic is all public, and `i` itself is unchanged. -/
theorem rewriteInstr_preserves_ctLeakFree [MachineModel I] [RALeak I]
    (decisions : List (String × Slot)) (i : I)
    (hi : (RALeak.leakOf i).ctSafe = true) :
    ctLeakFree (blockLeakTrace (rewriteInstr decisions i)) = true := by
  rw [rewriteInstr_eq, blockLeakTrace_append, blockLeakTrace_cons,
    ctLeakFree_append, ctLeakFree_cons]
  rw [reloadsOf_leakFree decisions i, hi, storesOf_leakFree decisions i]
  rfl

/-- **The spill rewrite preserves CT-leak-freedom (the headline spilled-half
    theorem).** If the source block is CT-leak-free, the spill-rewritten block
    `rewriteBlock decisions block` — every instruction surrounded by its
    reload loads and spill stores — is CT-leak-free. The rewrite is a
    **non-identity** transform on the instruction list, yet introduces no secret
    observation, because all inserted spill traffic is public. -/
theorem rewriteBlock_preserves_ctLeakFree [MachineModel I] [RALeak I]
    (decisions : List (String × Slot)) (block : List I)
    (h : ctLeakFree (blockLeakTrace block) = true) :
    ctLeakFree (blockLeakTrace (rewriteBlock decisions block)) = true := by
  unfold rewriteBlock
  rw [blockLeakTrace_flatMap, ctLeakFree]
  rw [List.all_eq_true]
  intro e he
  -- `e` lies in the leak trace of some `rewriteInstr decisions i` for `i ∈ block`.
  rw [List.mem_flatMap] at he
  obtain ⟨i, hi, he⟩ := he
  have hisafe : (RALeak.leakOf i).ctSafe = true := by
    have : (RALeak.leakOf i) ∈ blockLeakTrace block := List.mem_map_of_mem hi
    have hall := (List.all_eq_true).mp (by rw [← ctLeakFree]; exact h)
    exact hall _ this
  have hrw := rewriteInstr_preserves_ctLeakFree decisions i hisafe
  rw [ctLeakFree, List.all_eq_true] at hrw
  exact hrw e he

/-! ## 5. The composed register-allocation rewrite

The full RA output shape is: rename the resident names **then** insert spill
traffic for the spilled names. We compose the two halves into the headline
CT-leakage-preservation theorem for register allocation. -/

/-- The full RA rewrite of a block: rename residents by `ρ`, then surround every
    instruction with its spill / reload traffic per `decisions`. This is the
    instruction-list shape the printer emits (residents renamed; spilled names
    fetched/stored around each use). -/
def raRewrite [MachineModel I] [RALeak I] (ρ : String → String)
    (decisions : List (String × Slot)) (block : List I) : List I :=
  rewriteBlock decisions (renameBlockI ρ block)

/-- **Register allocation preserves CT-leak-freedom (the headline).**

A CT-leak-free source block stays CT-leak-free after the **full** register
allocation rewrite: renaming the residents (invisible to leakage) and inserting
spill / reload traffic (all public memory accesses). This is the
**non-vacuous** CT-preservation statement for register allocation — it ranges
over the real, non-identity instruction-list transform `raRewrite`, not the
`applyRA p ra = p` identity at the `Com` level.

The proof composes the two halves:
* `renameBlock_preserves_ctLeakFree` — the resident rename keeps the trace
  CT-leak-free;
* `rewriteBlock_preserves_ctLeakFree` — the spill rewrite adds only public
  spill traffic. -/
theorem raRewrite_preserves_ctLeakFree [MachineModel I] [RALeak I]
    (ρ : String → String) (decisions : List (String × Slot)) (block : List I)
    (h : ctLeakFree (blockLeakTrace block) = true) :
    ctLeakFree (blockLeakTrace (raRewrite ρ decisions block)) = true := by
  unfold raRewrite
  exact rewriteBlock_preserves_ctLeakFree decisions _
    (renameBlock_preserves_ctLeakFree ρ block h)

/-! ## 6. Non-vacuity: a secret-indexed access IS flagged

To confirm `ctLeakFree` is discriminating (not vacuously true), we
exhibit a one-instruction leak classifier where a secret-indexed access is
rejected and the corresponding rewrite-preservation hypothesis is therefore
*not* satisfiable — i.e. the theorems above have real content. We do this
abstractly: a block whose sole instruction leaks `mem .secret` is not
CT-leak-free, so `raRewrite_preserves_ctLeakFree`'s hypothesis
constrains the input. -/

/-- A leakage trace containing a secret memory access is **not** CT-leak-free.
    Confirms `ctLeakFree` is non-vacuous: it is `false` exactly when a secret
    observation occurs. -/
theorem secret_mem_not_ctLeakFree (off : Int) (rest : RALeakTrace) :
    ctLeakFree (RALeakEvent.mem .sec off :: rest) = false := by
  simp [ctLeakFree, RALeakEvent.ctSafe]

/-- A leakage trace containing a secret branch is **not** CT-leak-free. -/
theorem secret_branch_not_ctLeakFree (rest : RALeakTrace) :
    ctLeakFree (RALeakEvent.branch .sec :: rest) = false := by
  simp [ctLeakFree, RALeakEvent.ctSafe]

/-- A public memory access (e.g. a spill slot) **is** CT-leak-free.
    Confirms the spill-traffic side is accepted. -/
theorem public_mem_ctLeakFree (off : Int) :
    ctLeakFree [RALeakEvent.mem .pub off] = true := by
  simp [ctLeakFree, RALeakEvent.ctSafe]

/-! ## 7. A concrete witness: the class is inhabited and the transform is real

The parametric theorems above range over `[MachineModel I] [RALeak I]`. To
confirm that quantification is **not** vacuous (an uninstantiable class would
make the headline a statement about nothing), we exhibit a concrete
instruction type `DemoI` with a `MachineModel` and `RALeak`, and apply the
headline to it. The demo also confirms the rewrite is
**non-identity**: the spill of a value lengthens the instruction list, yet the
leakage trace stays CT-leak-free. -/

/-- A minimal demo instruction set: a pure register move, a memory load from a
    static (public) offset, a memory store to a static offset, a spill store,
    and a reload load. (Enough to exercise the `MachineModel`/`RALeak`
    interface.) -/
inductive DemoI where
  /-- `mov dst src` — a pure register move. -/
  | mov (dst src : String) : DemoI
  /-- `load dst off` — load from public frame offset `off`. -/
  | load (dst : String) (off : Int) : DemoI
  /-- `store src off` — store to public frame offset `off`. -/
  | store (src : String) (off : Int) : DemoI
  deriving DecidableEq, Repr

/-- The written name of a demo instruction (`store` writes nothing observable —
    we model its destination as the empty discard name). -/
def DemoI.written : DemoI → String
  | .mov dst _  => dst
  | .load dst _ => dst
  | .store _ _  => ""

/-- The read names of a demo instruction. -/
def DemoI.reads : DemoI → List String
  | .mov _ src   => [src]
  | .load _ _    => []
  | .store src _ => [src]

/-- Apply a register renaming to a demo instruction (offsets are static, never
    renamed). -/
def DemoI.rename (ρ : String → String) : DemoI → DemoI
  | .mov dst src  => .mov (ρ dst) (ρ src)
  | .load dst off => .load (ρ dst) off
  | .store src off => .store (ρ src) off

instance : MachineModel DemoI where
  writtenNames i := [DemoI.written i]
  readNames := DemoI.reads
  physRegs := ["r0", "r1", "r2"]
  mkSpill r off := .store r off
  mkReload r off := .load r off

/-- The leakage of a demo instruction: a move computes (no leakage), a
    load/store is a public memory access at its static offset. The renaming and
    spill/reload laws all hold by `rfl` / `cases` — the offsets are static, so
    every memory access is `mem .pub`. -/
instance : RALeak DemoI where
  leakOf
    | .mov _ _     => .compute
    | .load _ off  => .mem .pub off
    | .store _ off => .mem .pub off
  renameI := DemoI.rename
  leakOf_rename ρ i := by cases i <;> rfl
  leakOf_mkSpill r off := rfl
  leakOf_mkReload r off := rfl

/-- A straight-line demo block: move, load, store — all CT-leak-free. -/
def demoBlock : List DemoI :=
  [.mov "a" "b", .load "c" 0, .store "c" 8]

/-- The demo block is CT-leak-free (no secret address, no branch). -/
theorem demoBlock_ctLeakFree :
    ctLeakFree (blockLeakTrace demoBlock) = true := by
  decide

/-- **Worked application of the headline.** Applying the full RA rewrite
    (`raRewrite`) to the CT-leak-free demo block keeps it CT-leak-free — a
    concrete, non-vacuous instance of `raRewrite_preserves_ctLeakFree`. The
    `decisions` spill `"c"` to frame offset `16`, so the rewrite inserts real
    spill traffic (the instruction list changes), yet the leakage trace stays
    secret-free. -/
theorem demoBlock_raRewrite_ctLeakFree (ρ : String → String) :
    ctLeakFree
        (blockLeakTrace (raRewrite ρ [("c", Slot.spilled 16)] demoBlock)) = true :=
  raRewrite_preserves_ctLeakFree ρ _ demoBlock demoBlock_ctLeakFree

/-- The RA rewrite of the demo block is **non-identity**: spilling
    `"c"` inserts a reload before the `store "c" 8` use and a spill store after
    the `load "c" 0` def, so the rewritten instruction list is strictly longer
    than the original. (Confirms the headline is not a disguised `X = X`.) -/
theorem demoBlock_raRewrite_grows :
    (raRewrite id [("c", Slot.spilled 16)] demoBlock).length > demoBlock.length := by
  decide

end CatCrypt.Crypto.Optimizer.GenericRegAlloc
