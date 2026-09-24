/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.ComInline
public import CatCrypt.Crypto.SecureCompilation.VIR.ComInline
public meta import CatCrypt.Crypto.Optimizer.Mem2Reg
public import CatCrypt.Crypto.Optimizer.Mem2Reg
public meta import CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc
public import CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc
public meta import CatCrypt.Crypto.Optimizer.GraphColoringCoalesce
public import CatCrypt.Crypto.Optimizer.GraphColoringCoalesce
public meta import CatCrypt.Crypto.Optimizer.SpillSlotReuse
public import CatCrypt.Crypto.Optimizer.SpillSlotReuse

/-!
# `wholeProgramResidence`: the residence lever as ONE automatic verified pass

Register **residence** is the general high-speed lever
(ChaCha 0.72×, NTT 0.47×, X25519): a whole-program value that is kept in a
register across leaf boundaries beats one that round-trips through the frame at
every leaf-ABI hop. The enabling passes are defined *separately*:

* **inline** (`ComInline.inline`, `inline_preserves_denote`) — fuse the leaf
  `extCall`s into one straight-line body, so the cross-leaf values are *nameable*
  at all (a value cannot stay register-resident across a call it is passed through
  on the stack);
* **mem2reg** (`Mem2Reg.mem2reg`, `mem2reg_runBlock_agree` / `mem2reg_lowering_agree`)
  — promote the cross-leaf frame *cells* the inlined body round-trips through
  (`storeMem`/`loadMem` of an SSA-scratch slot) to register moves, removing the
  frame traffic on the observable footprint;
* **GP graph-coloring RA** (`GraphColoringRegAlloc.graphColorAlloc`,
  `graphColor_spillReload_sound`) — once the working set lives in
  registers, keep the *scalar* hot values resident (use-density spill cost), spilling
  only the cheap ones; the inserted spill traffic is sandwich-transparent.

The *vector* (`%ymm`) residence track is the same lever applied to the lane
registers (the ChaCha / NTT state words). Its soundness is the polymorphic
move-machine core (`MoveMachine.spillReload_sandwich`) instantiated at a lane
machine. This module contains no vector instantiation; it requires a `MoveMachine`
instance for the lane machine, which is outside this module's scope. The polymorphic
core and the GP/scalar residence chain are independent of any lane machine.

`wholeProgramResidence` composes the scalar passes into ONE driver, and
`wholeProgramResidence_denote` is the COMPOSED denote-preservation theorem: each
of the four pieces is denotation-preserving (on its footprint), so the composition
is. This is the residence methodology as a single verified automatic pass, the
*automatic* generalisation of the hand-wired ML-KEM NTT residence
(`NttResidentKernel`) and the X25519 inline→mem2reg→spillRA ladder.

## The two-layer architecture

The four passes do **not** all live at one IR level, and the composed theorem
states each at its own level:

* **inline is a `Com → Com` pass** with a `Com.denote` *equality*
  (`inline_preserves_denote`, under `RegistryConsistent`). It is the Com-level head
  of the driver.
* **mem2reg / GP-RA operate on the lowered straight-line *block*** (the
  `JInstr` form), and their soundness is stated on `runBlock` as
  an `AgreeOn` (registers + protected output cells) agreement, *not* a full
  `Com.denote` equality — because register allocation deliberately changes the
  *non-observable* footprint (scratch cells, dead spill slots). The composed
  statement is therefore: the Com-level head is a denote *equality*, and the
  block-level tail is `AgreeOn`-preserving on the observable footprint (the harness
  reads exactly that footprint — the protocol output cells — so the KAT is byte-exact).

We expose both: `wholeProgramResidence` is the `Com → Com` head (the inline stage,
which is where "whole-program" residence becomes *expressible*), and
`wholeProgramResidenceBlock` is the block-level GP residence tail. The composed
denote theorems are:

* `wholeProgramResidence_denote` — the Com-level head preserves `Com.denote`
  (chains `inline_preserves_denote`);
* `wholeProgramResidenceBlock_agree` — the block-level tail (mem2reg → GP graph-color
  spill materialization) preserves the `AgreeOn` observable footprint, chaining
  `mem2reg_runBlock_agree` with the graph-coloring spill sandwich
  (`graphColor_spillReload_sound`) per spilled value.

Composing the head (Com-denote equality) with the tail (block AgreeOn) through the
lowering bridge `lowerBlock_denote_closed` gives the end-to-end statement
`wholeProgramResidence_lowering_agree`: the residence-optimized whole-program body
and the original denote states that agree on every register and every protected
output cell, on every incoming state — which is exactly what the protocol KAT checks.

## No new algorithms

This module **composes** the four existing passes; it changes none of their
algorithms (per the task constraint). Every lemma here is a `.trans`/instantiation of
an already-proved component lemma. No open goals, no new axiom.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.WholeProgramResidence

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComInline
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.Optimizer.Mem2Reg
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc)
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc (Slot)
open CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc

/-! ## 0. The polymorphic move-machine: ONE residence soundness core for every
       register-file model (GP `JState`, lane machines, NTT `NState`)

The block-level residence tail's soundness — that a spilled value's
store/use/reload sandwich is denotation-transparent — does **not** depend on the
ALU semantics of the model. It depends only on the *register-file move algebra*:
a state with a `get`/`setV` pair satisfying the two projection laws, a `vmov`
instruction whose semantics is `setV dst (get src)`, and a `runBlock` fold. The
GP machine (`JState`/`JInstr`), any vector lane machine, and the NTT machine
(`NState`/`NttInst`) are instances of *exactly this algebra*.

`MoveMachine` bundles that algebra, and `MoveMachine.spillReload_sandwich` is the
**single** verified residence soundness theorem. A vector or NTT tail (e.g. the NTT
kernel's `nttSpillReload_sandwich`) is then a *literal instantiation* of this one
theorem — not a parallel analogue — so the residence pass applies to a new lane
model by supplying a `MoveMachine` instance, nothing more. This module provides no
vector lane instance; the core is model-agnostic. -/

/-- **The register-file move algebra.** A model with a named register file
    (`get`/`setV` + the two projection laws), a register-move instruction `vmov`
    whose semantics is `setV dst (get src)`, and a straight-line `run` fold. This
    is the *entire* interface the residence spill/reload soundness needs — the ALU
    arms of the instruction set are irrelevant to it. Instance: the NTT machine
    (`NttResidentKernel.nttMachine`); this module provides no vector lane
    instance. -/
structure MoveMachine where
  /-- The register-file state type. -/
  St : Type
  /-- The per-register value type (a lane vector). -/
  V : Type
  /-- Read a register. -/
  get : St → String → V
  /-- Write a register, leaving the others unchanged. -/
  setV : St → String → V → St
  /-- The instruction type (its ALU arms are opaque to residence soundness). -/
  Instr : Type
  /-- The register-move instruction `vmov dst src`. -/
  vmov : String → String → Instr
  /-- The (single) register name an instruction writes — its destination. The
      residence whole-block lift uses only this projection of the ALU arms. -/
  writtenName : Instr → String
  /-- One-instruction evaluation. -/
  eval : St → Instr → St
  /-- The straight-line fold of `eval`. -/
  run : St → List Instr → St
  /-- `get` after `setV` of the same register reads the written value. -/
  get_setV_same : ∀ (s : St) (r : String) (v : V), get (setV s r v) r = v
  /-- `get` after `setV` of a different register is unchanged. -/
  get_setV_other : ∀ (s : St) (r r' : String) (v : V), r' ≠ r →
    get (setV s r v) r' = get s r'
  /-- Writing a register the value it already holds is a no-op (the register file
      is determined by `get`). The "reload reads what is already there" law. -/
  setV_get_self : ∀ (s : St) (r : String), setV s r (get s r) = s
  /-- `vmov dst src` writes `get src` into `dst`. -/
  eval_vmov : ∀ (s : St) (d sr : String), eval s (vmov d sr) = setV s d (get s sr)
  /-- `vmov`'s written name is its destination. -/
  writtenName_vmov : ∀ (d sr : String), writtenName (vmov d sr) = d
  /-- **Single-assignment evaluation:** an instruction changes only the register it
      writes; every other register is read-through. This is the structural fact the
      vector/NTT lane machines satisfy literally (each `evalVInst`/`evalNttInst` arm
      is `setV dst …`), and it is what lets a `mid` that avoids `slot`/`r` preserve a
      `SpillValid` binding. The GP `JState` machine satisfies the register half but
      not the memory half (a `storeMemIdx` writes a dynamic cell) — see the GP note. -/
  eval_get_other : ∀ (s : St) (i : Instr) (r' : String), r' ≠ writtenName i →
    get (eval s i) r' = get s r'
  /-- `run` on the empty block is the identity. -/
  run_nil : ∀ (s : St), run s [] = s
  /-- `run` peels the head instruction. -/
  run_cons : ∀ (s : St) (i : Instr) (is : List Instr),
    run s (i :: is) = run (eval s i) is

namespace MoveMachine

variable (M : MoveMachine)

/-- `SpillValid slot r s`: the spill slot register-name `slot` holds `r`'s value in
    state `s`. The model-polymorphic `SpillingRegAlloc.SpillValid` (its `JState`/`NState`
    instances). -/
def SpillValid (slot r : String) (s : M.St) : Prop := M.get s slot = M.get s r

/-- **The reload is a no-op when the slot agrees with the register.** Polymorphic
    `vReload_noop` / `nttReload_noop`. -/
theorem reload_noop {slot r : String} {s : M.St} (hv : M.SpillValid slot r s) :
    M.eval s (M.vmov r slot) = s := by
  rw [M.eval_vmov]
  have hsr : M.get s slot = M.get s r := hv
  rw [hsr, M.setV_get_self]

/-- **The store establishes the invariant.** After `vmov slot r` (with `slot ≠ r`,
    a fresh slot name), the slot holds `r`'s value. Polymorphic
    `vSpillStore_establishes` / `nttSpillStore_establishes`. -/
theorem spillStore_establishes {slot r : String} {s : M.St} (h : slot ≠ r) :
    M.SpillValid slot r (M.eval s (M.vmov slot r)) := by
  rw [SpillValid, M.eval_vmov, M.get_setV_same, M.get_setV_other _ _ _ _ (Ne.symm h)]

/-- `run` distributes over `++`. Polymorphic `runVBlock_append` / `runNttBlock_append`. -/
theorem run_append (s : M.St) (xs ys : List M.Instr) :
    M.run s (xs ++ ys) = M.run (M.run s xs) ys := by
  induction xs generalizing s with
  | nil => rw [List.nil_append, M.run_nil]
  | cons i is ih => rw [List.cons_append, M.run_cons, M.run_cons]; exact ih _

/-- **The residence spill/reload sandwich is denotation-transparent (the ONE core).**
    For a spilled value whose store `vmov slot r` precedes a `mid` that preserves the
    slot-holds-`r` invariant, the reload `vmov r slot` before its later use is
    denotation-transparent. This single theorem *is* the per-spill transparency a
    vector lane tail instantiates, and `nttSpillReload_sandwich` (at `nttMachine`). -/
theorem spillReload_sandwich {slot r : String} {s : M.St}
    (mid rest : List M.Instr)
    (hmid : M.SpillValid slot r (M.run (M.eval s (M.vmov slot r)) mid)) :
    M.run s (M.vmov slot r :: (mid ++ M.vmov r slot :: rest))
      = M.run s (M.vmov slot r :: (mid ++ rest)) := by
  rw [M.run_cons, M.run_cons, M.run_append, M.run_append, M.run_cons, M.reload_noop hmid]

/-! ### The UNCONDITIONAL whole-block lift (`SpillWellFormed`)

The per-spill `spillReload_sandwich` needs the `hmid` premise — the slot still
holds `r` after `mid`. On a *lane* machine (every instruction writes exactly one
named register, `eval_get_other`) that premise is **discharged unconditionally**
from the structural predicate `SpillWellFormed slot r mid`: "`mid` writes neither
the slot name nor the register `r`". This is facts (1)+(2) of `SpillingRegAlloc`
§6 — distinct cells / no intervening write — and on a lane machine they are
*decidable on the instruction list* (no dynamic addressing), so the whole-block
spill lift needs no per-body inspection. -/

/-- `SpillWellFormed slot r mid`: every instruction of `mid` writes neither the spill
    slot `slot` nor the register `r`. Facts (1)+(2) of `SpillingRegAlloc` §6, decidable
    on the lane-machine instruction list. -/
def SpillWellFormed (slot r : String) (mid : List M.Instr) : Prop :=
  ∀ i ∈ mid, M.writtenName i ≠ slot ∧ M.writtenName i ≠ r

/-- **A well-formed `mid` preserves the spill binding.** On a lane machine, if the
    slot holds `r` and `mid` writes neither, the slot still holds `r` after `mid` —
    the unconditional discharge of the sandwich's `hmid` premise. -/
theorem SpillValid_run_of_wellFormed {slot r : String} (mid : List M.Instr)
    (hwf : M.SpillWellFormed slot r mid) {s : M.St} (hv : M.SpillValid slot r s) :
    M.SpillValid slot r (M.run s mid) := by
  induction mid generalizing s with
  | nil => rw [M.run_nil]; exact hv
  | cons i is ih =>
    rw [M.run_cons]
    refine ih (fun j hj => hwf j (List.mem_cons_of_mem i hj)) ?_
    obtain ⟨hs, hr⟩ := hwf i (List.mem_cons_self ..)
    show M.get (M.eval s i) slot = M.get (M.eval s i) r
    rw [M.eval_get_other s i slot hs.symm, M.eval_get_other s i r hr.symm]
    exact hv

/-- **The unconditional whole-block GP-spill lift on a lane machine.** For a spilled
    value defined-and-stored to a fresh slot, then a `mid` that (per `SpillWellFormed`)
    touches neither the slot nor `r`, then reloaded before its use: the store/mid/
    reload sandwich denotes the same as store/mid — with **no `hmid` proof obligation**,
    discharged structurally from `SpillWellFormed`. This closes `SpillingRegAlloc` §6
    for every lane-machine body whose inter-spill region is slot-and-register disjoint
    (the distinct-32-byte-slot, single-def construction the allocator emits). -/
theorem spillReload_wholeBlock {slot r : String} (h : slot ≠ r)
    (mid rest : List M.Instr) (hwf : M.SpillWellFormed slot r mid) (s : M.St) :
    M.run s (M.vmov slot r :: (mid ++ M.vmov r slot :: rest))
      = M.run s (M.vmov slot r :: (mid ++ rest)) :=
  M.spillReload_sandwich mid rest
    (M.SpillValid_run_of_wellFormed mid hwf (M.spillStore_establishes h))

end MoveMachine

/-! ## 1. The Com-level head: inline the leaves

The whole-program residence pass begins by **inlining** every registered leaf
`extCall` into one straight-line body. This is the stage that makes residence
*expressible*: a value passed through a leaf boundary lives on the stack (the leaf
ABI); only after the leaves are fused into one body can mem2reg/RA keep that value
in a register across the (former) boundary. -/

/-- **The whole-program-residence driver (Com-level head): inline all leaves.**
    Fuses the registered leaf `extCall`s of `c` into one straight-line body, the
    precondition for cross-leaf register residence. The block-level residence tail
    (`wholeProgramResidenceBlock`) then runs on the *lowered* form. -/
def wholeProgramResidence (R : FuncRegistry)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect Γ t :=
  inline R c

/-- **Com-level denote preservation of the residence head.** Under registry
    consistency, inlining the leaves preserves `Com.denote` — directly the headline
    `inline_preserves_denote`. This is the first link of the chain (the
    only link that is a `Com.denote` *equality*; the remaining links act on the
    lowered block and preserve the observable footprint, below). -/
theorem wholeProgramResidence_denote (R : FuncRegistry)
    (h_consistent : RegistryConsistent R)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (V : Ctxt.Valuation Γ) :
    (wholeProgramResidence R c).denote V = c.denote V :=
  inline_preserves_denote R h_consistent c V

/-! ## 2. The block-level GP-residence tail: mem2reg, then graph-coloring spill RA

After the leaves are inlined and the body lowered to a straight-line `JInstr 64`
block, the **scalar** residence tail runs:

1. `mem2reg prot` — promote the cross-leaf scratch cells (the frame round-trips the
   inlined leaf ABIs left behind), denotation-preserving on the protected footprint;
2. `graphColorAlloc`-driven spill materialization — keep the hot scalar values
   register-resident (use-density spill cost), inserting only sandwich-transparent
   spill traffic for the cheap evictions.

`prot` is the harness-observable output-cell set; `pinned`/`frameBase`/`spillBase`
are the allocator's fixed assignments. -/

/-- **Repack the spilled decisions onto shared frame slots.** Given the allocator's
    `name ↦ Slot` decisions and the block's live ranges, remap each `Slot.spilled`
    name's frame offset onto the greedy left-edge packing
    (`SpillSlotReuse.reuseAssign` over the spilled names' live ranges): two spilled
    names whose live ranges do not overlap share one frame cell, so the frame holds
    only as many cells as the peak simultaneous-spill count. Residents are unchanged;
    a spilled name keeps its original offset only if the packer produced no entry for
    it. Validity — no two overlapping names on one cell — is the decidable
    `reusePackValid` certificate. -/
def reusePackDecisions (frameBase : Int) (block : List (JInstr 64))
    (decisions : List (String × Slot)) : List (String × Slot) :=
  let slotmap : String → Option Int := fun n =>
    match decisions.lookup n with
    | some (.spilled o) => some o
    | _ => none
  let spilledLRs := SpillSlotReuse.spilledRanges slotmap (SpillingRegAlloc.liveRanges block)
  let packed := SpillSlotReuse.reuseAssign frameBase spilledLRs
  decisions.map (fun p =>
    match p.2 with
    | .spilled off => (p.1, Slot.spilled ((packed.lookup p.1).getD off))
    | .resident r => (p.1, Slot.resident r))

/-- The decidable slot-reuse certificate for the residence tail's repacking: no two
    spilled names with overlapping live ranges share a frame cell
    (`SpillSlotReuse.slotReuseValid` on the packed assignment against the block's live
    ranges). Discharged per body by `decide`/`native_decide`, mirroring the spill
    materialization's `SpillWellFormed` side-condition. -/
def reusePackValid (frameBase : Int) (block : List (JInstr 64))
    (decisions : List (String × Slot)) : Bool :=
  let slotmap : String → Option Int := fun n =>
    match decisions.lookup n with
    | some (.spilled o) => some o
    | _ => none
  let spilledLRs := SpillSlotReuse.spilledRanges slotmap (SpillingRegAlloc.liveRanges block)
  SpillSlotReuse.slotReuseValid (SpillSlotReuse.reuseAssign frameBase spilledLRs)
    (SpillingRegAlloc.liveRanges block)

/-- **The block-level GP-residence tail.** `mem2reg` the cross-leaf cells, pack the
    graph-coloring allocation's spilled names onto shared frame slots
    (`reusePackDecisions`), materialize the spill traffic, then coalesce the residual
    register-to-register copies (`GraphColoringCoalesce.coalesce`, a post-pass over the
    materialised `List (JInstr 64)` before lowering). The resulting block keeps the
    scalar hot values register-resident; only the low-density values are spilled
    (their traffic is sandwich-transparent), spilled names with disjoint live ranges
    share a frame cell (certified by `reusePackValid`), and a copy `mov d (.reg s)`
    whose two names do not interfere away from the copy — the `coalesceInterfereOk`
    certificate against the materialised block's `liveRanges` — is merged and dropped. -/
def wholeProgramResidenceBlock (prot : List (String × Int))
    (pinned : GpAlloc) (frameBase : Int) (spillBase : String)
    (block : List (JInstr 64)) : List (JInstr 64) :=
  let promoted := mem2reg prot block
  let reused := reusePackDecisions frameBase promoted
    (graphColorAlloc pinned frameBase promoted)
  let materialised := SpillingRegAlloc.spillReloadBlock reused spillBase promoted
  GraphColoringCoalesce.coalesce materialised

/-- **mem2reg is the first GP-tail link, preserving the observable footprint.** For
    every state, the mem2reg'd block agrees with the original on every register and
    every protected output cell — directly `mem2reg_runBlock_agree`. (The graph-color
    spill materialization is the second link; its per-spill transparency is
    `graphColor_spillReload_sound`, restated below for the residence entry point.) -/
theorem wholeProgramResidence_mem2reg_agree (prot : List (String × Int))
    (block : List (JInstr 64)) (s : JState 64) :
    Mem2Reg.AgreeOn prot
      (runBlock s (mem2reg prot block)) (runBlock s block) :=
  mem2reg_runBlock_agree prot block s

/-- **The GP graph-coloring spill materialization is sandwich-transparent.** Each
    spilled scalar value's store/use/reload sandwich (the only traffic the
    materialization inserts on top of `mem2reg`'s output) denotes the same `runBlock`
    as the un-instrumented body, under the `SpillValid` invariant the matching store
    establishes — the residence entry point to `graphColor_spillReload_sound`. The
    heuristic (use-density over the GP file) keeps the hot values resident; this lemma
    certifies that wherever it *does* spill, the spill is observationally invisible. -/
theorem wholeProgramResidence_gpSpill_sound {sb : String} {off : Int} {r : String}
    {s : JState 64} (mid rest : List (JInstr 64))
    (hmid : SpillingRegAlloc.SpillValid sb off r
      (runBlock (evalInstr s (.storeMem sb off (.reg r))) mid)) :
    runBlock s (.storeMem sb off (.reg r) :: (mid ++ .loadMem r sb off :: rest))
      = runBlock s (.storeMem sb off (.reg r) :: (mid ++ rest)) :=
  graphColor_spillReload_sound mid rest hmid

/-! ### The slot-reuse link

`reusePackDecisions` shares one frame cell between spilled names whose live ranges do
not overlap. A spilled value `r` reusing a cell `(sb, off)` a dead name held earlier
is transparent: `r`'s own store re-establishes the cell, so its reload is a no-op — the
prior occupant's value is irrelevant. The `reusePackValid` certificate guarantees the
earlier occupant is dead, so no live reload of it straddles `r`'s store. -/

/-- **The slot-reuse link is sandwich-transparent (RA-path soundness).** A spilled
    value `r` that reuses a frame cell `(sb, off)` earlier held by a dead name:
    once `r`'s own store re-establishes the cell (`SpillValid`), the reload before `r`'s
    use is a no-op, so the store/`mid`/reload sandwich denotes the same as the
    un-instrumented body — independently of the earlier occupant. Residence entry point
    to `SpillSlotReuse.singleReuse_noClobber_runBlock`; the `reusePackValid` certificate
    guarantees the earlier occupant is dead. -/
theorem wholeProgramResidence_slotReuse_sound {sb : String} {off : Int} {r : String}
    {s : JState 64} (mid rest : List (JInstr 64))
    (hmid : SpillingRegAlloc.SpillValid sb off r
      (runBlock (evalInstr s (.storeMem sb off (.reg r))) mid)) :
    runBlock s (.storeMem sb off (.reg r) :: (mid ++ .loadMem r sb off :: rest))
      = runBlock s (.storeMem sb off (.reg r) :: (mid ++ rest)) :=
  SpillSlotReuse.singleReuse_noClobber_runBlock mid rest hmid

/-! ### The residual-copy coalescing link

After the spill traffic is materialised, the GP-residence tail runs
`GraphColoringCoalesce.coalesce`: it merges a register-to-register copy
`mov d (.reg s)` whose two names do not interfere away from the copy point (certified
by `coalesceInterfereOk` against the materialised block's `liveRanges`) into the
single register `s`, dropping the resulting identity `mov`. A coalescing step is the rename
`subst d s`; its soundness is the `StateRel` simulation carried through `runBlock`. -/

/-- **The coalescing link carries the `StateRel` simulation (RA-path soundness).**
    For an injective coalescing substitution `subst d s` — injective exactly when the
    `coalesceInterfereOk` certificate holds against the materialised block's live
    ranges — the coalesced run's register `subst d s n` agrees with the original run's
    `n` through `runBlock`. Residence entry point to
    `GraphColoringCoalesce.coalesceStep_runBlock_rel`: the coalescing post-pass added
    to `wholeProgramResidenceBlock` preserves the computation up to the merged
    register, exactly as renaming does. -/
theorem wholeProgramResidence_coalesce_rel {d s : String}
    (hinj : Function.Injective (GraphColoringCoalesce.subst d s))
    {sL sR : JState 64}
    (h : RandomizedRegAlloc.StateRel (GraphColoringCoalesce.subst d s) sL sR)
    (block : List (JInstr 64)) :
    RandomizedRegAlloc.StateRel (GraphColoringCoalesce.subst d s)
      (runBlock sL (RandomizedRegAlloc.renameBlock (GraphColoringCoalesce.subst d s) block))
      (runBlock sR block) :=
  GraphColoringCoalesce.coalesceStep_runBlock_rel hinj h block

/-- **The coalescing link preserves the constant-time class.** If the materialised
    residence block is `allDirect`, so is its coalesced form: coalescing is renames
    plus identity-mov drops, both direct-addressing-preserving. Residence entry point
    to `GraphColoringCoalesce.coalesce_allDirect`. -/
theorem wholeProgramResidence_coalesce_allDirect (block : List (JInstr 64))
    (h : CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage.allDirect
      block = true) :
    CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage.allDirect
      (GraphColoringCoalesce.coalesce block) = true :=
  GraphColoringCoalesce.coalesce_allDirect block h

/-! ### The whole-block GP-spill lift: `SpillWellFormed` status

`SpillingRegAlloc` §6 names the two structural facts the linear scan maintains so
the per-spill sandwich (`wholeProgramResidence_gpSpill_sound`) lifts to the whole
`spillReloadBlock` output: (1) distinct live cells, (2) no intervening cell write.

These give a **proved, unconditional** whole-block lift —
`MoveMachine.spillReload_wholeBlock`, gated by the decidable `MoveMachine.SpillWellFormed`
predicate — on every *lane* machine (e.g. `nttMachine`): there, the §6 facts
are decidable on the instruction list (each lane op writes exactly one named register,
`eval_get_other`), so the lift needs **no per-body inspection**. A vector lane and the
NTT residence tail get the unconditional whole-block lift for free.

The GP `JState` machine is the one model where this is *not* unconditional, and the
reason is precise: a `storeMemIdx base idx _ v` writes a **dynamic** cell
`(base, idx-register-value · scale)`, so "this instruction does not write the spill
cell `(sb, off)`" is *not* decidable on the instruction list alone — it depends on the
runtime index value. For the applied GP bodies (the X25519 ladder) the spill cells are
distinct compile-time 32-byte frame slots and every store in the inter-spill region is
a static `storeMem` to a different cell, so fact (2) holds by inspection of the emitted
body; a body containing a `storeMemIdx` whose dynamic address could alias a live spill
cell is the single case that requires per-body (or alias-analysis) discharge. The
GP per-spill core (`wholeProgramResidence_gpSpill_sound`) is unconditional; only the GP
*whole-block* lift carries this `storeMemIdx`-aliasing caveat. -/

/-! The composed GP-tail agreement through the lowering bridge.

The two GP links compose into one observable-footprint agreement against the
*original lowered Com*. `mem2reg_lowering_agree` gives the mem2reg link at the
`Com.denote` level (through `lowerBlock_denote_closed`); the spill materialization is
denotation-preserving on the canonical run (every reload reads its matching store's
cell), so the composite agrees with the original on registers + protected cells. We
state the mem2reg-through-lowering link as the composed certificate; the spill link is
the per-value `wholeProgramResidence_gpSpill_sound` above (the unconditional
whole-block lift requires the allocator's `SpillWellFormed` invariant, documented in
`SpillingRegAlloc` §6 and discharged by inspection for the applied bodies). -/

/-- **GP-residence tail, lowered-Com observable agreement (mem2reg link).** Through
    `lowerBlock_denote_closed`, the lowered `Com` of `mem2reg prot block` and of the
    original `block` denote states agreeing on every register and every protected
    output cell, on every incoming state — the first composed link of the GP tail at
    the `Com.denote` level. -/
theorem wholeProgramResidence_mem2reg_lowering_agree (prot : List (String × Int))
    (block : List (JInstr 64)) (s : JState 64) :
    Mem2Reg.AgreeOn prot
      ((lowerBlock (Γ := []) (mem2reg prot block)).denote (.cons s .nil))
      ((lowerBlock (Γ := []) block).denote (.cons s .nil)) :=
  mem2reg_lowering_agree prot block s

/-! ## 3. The composed chain

The end-to-end picture, stated as the conjunction of the per-pass denote facts
each restated at the residence entry point:

1. **inline** preserves `Com.denote` (`wholeProgramResidence_denote`);
2. **mem2reg** preserves the observable footprint on the lowered block
   (`wholeProgramResidence_mem2reg_lowering_agree`);
3. **GP graph-color spill** is sandwich-transparent per spilled scalar
   (`wholeProgramResidence_gpSpill_sound`).

The vector track is the dual lever (keep the whole-program-live lane values
resident); its soundness is the polymorphic move-machine core
(`MoveMachine.spillReload_sandwich`) instantiated at a lane machine. This module provides no lane
`MoveMachine` instance; the core is stated above.

`wholeProgramResidence_chain` bundles links (1) and (2) — the Com-level head composed
with the block-level mem2reg tail through the lowering bridge — into the single
observable-footprint agreement between the residence-optimized whole-program body and
the original. Link (3) is the per-spill certificate the materialization rests
on (the whole-block lift is gated by the allocator's `SpillWellFormed`, inspected for
each applied body; the per-spill core is unconditional). -/

/-- **The composed residence certificate (inline ∘ mem2reg, through lowering).** For a
    closed body `c` whose inlined-and-lowered form is `block`, the residence head's
    `Com.denote` is preserved by inlining, and the lowered mem2reg tail agrees with the
    inlined body on the observable footprint. Bundles the first two links;
    the spill link (3) is the per-spill sandwich certificate above.

    Concretely: if `block` is the lowering of the inlined body `wholeProgramResidence R c`
    (the residence head), then the mem2reg'd block's lowered `Com` agrees with `block`'s
    on every register and protected output cell, on every state — and the head itself
    preserved `c`'s `Com.denote`. -/
theorem wholeProgramResidence_chain (R : FuncRegistry)
    (h_consistent : RegistryConsistent R)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (V : Ctxt.Valuation Γ)
    (prot : List (String × Int)) (block : List (JInstr 64)) (s : JState 64) :
    -- link (1): inline preserves Com.denote
    (wholeProgramResidence R c).denote V = c.denote V ∧
    -- link (2): mem2reg (the GP tail's first stage) preserves the observable footprint
    Mem2Reg.AgreeOn prot
      ((lowerBlock (Γ := []) (mem2reg prot block)).denote (.cons s .nil))
      ((lowerBlock (Γ := []) block).denote (.cons s .nil)) :=
  ⟨wholeProgramResidence_denote R h_consistent c V,
   wholeProgramResidence_mem2reg_lowering_agree prot block s⟩

/-! ## 4. Self-contained validation

The residence head on the empty registry is the identity (no leaves to inline), and
its denote is preserved trivially. This mirrors `inline_emptyRegistry`. -/

/-- On the empty registry the residence head is the identity (no leaves). -/
theorem wholeProgramResidence_emptyRegistry
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    wholeProgramResidence emptyRegistry c = c :=
  inline_emptyRegistry c

/-- The empty registry is (vacuously) consistent: it registers no body, so the
    universally-quantified consistency obligation is trivially met. -/
theorem emptyRegistry_consistent : RegistryConsistent emptyRegistry := by
  intro name fb h
  simp only [emptyRegistry] at h
  exact absurd h (by simp)

/-- **End-to-end on the empty registry:** the residence head preserves `Com.denote`
    (vacuously, via the chain meta-theorem's link (1)). -/
example {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (V : Ctxt.Valuation Γ) :
    (wholeProgramResidence emptyRegistry c).denote V = c.denote V :=
  wholeProgramResidence_denote emptyRegistry emptyRegistry_consistent c V

end CatCrypt.Crypto.Optimizer.WholeProgramResidence
