/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllDirectRename
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT
public import CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-!
# Spill insertion preserves machine constant-time (the middle of the chain)

`SecureCompileChain.LoweringCTPreserving` is the **assumed middle** of the
secure-compiler chain: that the source→machine lowering — including register
allocation — carries a `NoSecretControl` source to a `CompilableCT` machine
block. The register-resident half of allocation (a renaming) is proved
CT-preserving in `AllDirectRename` (`allDirect_renameBlock`). This module
proves the **spill** half. The `Optimizer/RegAllocLeakTrace.RALeak` leakage
interface is instantiated only for the demonstrator (`DemoI`), so it does not
connect real spill insertion to the machine leakage theorem.

This module discharges the spill half directly over `JInstr 64`, with **no**
appeal to `RALeak`, the generic `MachineModel` instance, or any
`MachineModel`/`mulx` machinery (`JInstr`'s two-output `mulx` blocks the
single-`writtenName` `MachineModel` class). The observation is purely about
*addressing mode*:

> a spill store / reload to a **constant frame offset** is `storeMem`/`loadMem`,
> which is `IsDirect` (the only non-direct opcodes are the register-indexed
> `loadMemIdx`/`storeMemIdx`). So inserting spill traffic at constant offsets
> preserves `allDirect`, hence preserves constant-time.

x86's spill rendering (cf. `GenericRegAlloc`'s table) is exactly
`mkSpill r off = storeMem fb off (.reg r)` and `mkReload r off = loadMem r fb
off` — both at a compile-time-constant frame displacement `off`, never a
register-indexed access. The spilled body is the original block with each
instruction surrounded by reloads (before, for spilled reads) and stores (after,
for spilled writes), exactly the shape of `SpillingRegAlloc.spillRewriteInstr`.

## What is proved

* `spillReloads_allDirect` / `spillStores_allDirect` — every inserted reload /
  store is `IsDirect` (it is a constant-offset `loadMem`/`storeMem`).
* `spillRewrite_allDirect` (**the headline**) — `allDirect block = true ⇒
  allDirect (spillRewrite ρ frameBase slots block) = true`: spill insertion
  composed with the resident-half renaming (`renameInstr`) preserves the
  machine constant-time class.
* `spillRewrite_constant_time` — hence the full rename+spill rewrite has a
  state-independent machine leakage trace.
* `spillRewrite_CompilableCT` — the spilled block is `CompilableCT`.

`CompilableCT b` is definitionally `allDirect b = true`
(`CompilableCT.lean`), so the headline `allDirect` lemma yields `CompilableCT`
directly. The composition with the scalar-arith lowering `lowerSeq`
(`ourLowering_spill_CompilableCT`, `ourLowering_spill_constant_time`) is in
`RegAllocSpillLowerSeq`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RegAllocSpillCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc (renameInstr)
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc (readNames writtenNames)

/-! ## 1. The spill rendering at a constant frame offset

A *slot map* `slots : String → Option Int` records, for each spilled name, its
constant frame byte-offset (`none` for register-resident names). The spill
rendering against the frame base `frameBase` is the x86 one:

* reload (before a spilled read `n`): `loadMem n frameBase off`;
* store (after a spilled write `n`): `storeMem frameBase off (.reg n)`.

Both name a base register (`frameBase` resp. `n`) and a compile-time-constant
displacement `off` — direct addressing, never the register-indexed
`loadMemIdx`/`storeMemIdx`. -/

/-- The reload loads to prepend to an instruction: one `loadMem n frameBase off`
    for each read-name `n` the slot map sends to a constant offset `off`. -/
def spillReloads (frameBase : String) (slots : String → Option Int)
    (i : JInstr 64) : List (JInstr 64) :=
  (readNames i).filterMap (fun n => (slots n).map (fun off => JInstr.loadMem n frameBase off))

/-- The spill stores to append to an instruction: one
    `storeMem frameBase off (.reg n)` for each written-name `n` the slot map
    sends to a constant offset `off`. -/
def spillStores (frameBase : String) (slots : String → Option Int)
    (i : JInstr 64) : List (JInstr 64) :=
  (writtenNames i).filterMap (fun n => (slots n).map (fun off => JInstr.storeMem frameBase off (.reg n)))

/-- **The spill rewrite.** Each instruction of the block is surrounded by its
    reloads (before) and stores (after), with the instruction itself renamed by
    the resident-half allocation `ρ`. This is the shape of
    `SpillingRegAlloc.spillReloadBlock` composed with the resident renaming. -/
def spillRewrite (ρ : String → String) (frameBase : String) (slots : String → Option Int)
    (block : List (JInstr 64)) : List (JInstr 64) :=
  block.flatMap (fun i =>
    spillReloads frameBase slots i ++ (renameInstr ρ i :: spillStores frameBase slots i))

/-! ## 2. Every inserted reload / store is direct-addressed

The inserted traffic is exclusively `loadMem`/`storeMem` at a constant offset —
`IsDirect` by definition (only `loadMemIdx`/`storeMemIdx` are `¬ IsDirect`). -/

/-- A constant-offset reload `loadMem n frameBase off` is `IsDirect`. -/
theorem isDirect_loadMem (n frameBase : String) (off : Int) :
    IsDirect (w := 64) (JInstr.loadMem n frameBase off) := by
  simp [IsDirect]

/-- A constant-offset store `storeMem frameBase off (.reg n)` is `IsDirect`. -/
theorem isDirect_storeMem (frameBase : String) (off : Int) (n : String) :
    IsDirect (w := 64) (JInstr.storeMem frameBase off (.reg n)) := by
  simp [IsDirect]

/-- **Every reload is direct-addressed.** All instructions in `spillReloads` are
    constant-offset `loadMem`s, so the block of reloads is `allDirect`. -/
theorem spillReloads_allDirect (frameBase : String) (slots : String → Option Int)
    (i : JInstr 64) : allDirect (spillReloads frameBase slots i) = true := by
  unfold allDirect spillReloads
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_filterMap] at hj
  obtain ⟨n, _, hj⟩ := hj
  cases hslot : slots n with
  | none => simp [hslot] at hj
  | some off =>
    simp only [hslot, Option.map_some] at hj
    rw [Option.some.injEq] at hj
    subst hj
    exact decide_eq_true (isDirect_loadMem n frameBase off)

/-- **Every spill store is direct-addressed.** All instructions in `spillStores`
    are constant-offset `storeMem`s, so the block of stores is `allDirect`. -/
theorem spillStores_allDirect (frameBase : String) (slots : String → Option Int)
    (i : JInstr 64) : allDirect (spillStores frameBase slots i) = true := by
  unfold allDirect spillStores
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_filterMap] at hj
  obtain ⟨n, _, hj⟩ := hj
  cases hslot : slots n with
  | none => simp [hslot] at hj
  | some off =>
    simp only [hslot, Option.map_some] at hj
    rw [Option.some.injEq] at hj
    subst hj
    exact decide_eq_true (isDirect_storeMem frameBase off n)

/-! ## 3. The headline: spill insertion preserves `allDirect`

Each block instruction expands to `reloads ++ (renamed instr :: stores)`. The
reloads and stores are `allDirect` (constant-offset memory, §2); the renamed
instruction is `allDirect` because the original was (it is `IsDirect` from
`allDirect block`, and renaming preserves `IsDirect` —
`allDirect_renameInstr`). `allDirect` distributes over `++` and `::`
(`allDirect_append`), so the whole expansion is `allDirect`, and the flatMap
over the block stays `allDirect`. -/

/-- `allDirect` over a singleton instruction is `decide (IsDirect i)`. -/
theorem allDirect_singleton (i : JInstr 64) :
    allDirect [i] = decide (IsDirect i) := by simp [allDirect]

/-- **Spill insertion preserves the machine constant-time class.** If every
    instruction of `block` is direct-addressed (`allDirect block = true`), then
    the rename+spill rewrite `spillRewrite ρ frameBase slots block` is still
    direct-addressed: the inserted reloads/stores are constant-offset
    `loadMem`/`storeMem` (`IsDirect`), and the renamed body instruction inherits
    `IsDirect` from the original (`allDirect_renameInstr`). So constant-time
    survives spill insertion — the spill-path obligation
    `SecureCompileChain.LoweringCTPreserving` assumed. -/
theorem spillRewrite_allDirect (ρ : String → String) (frameBase : String)
    (slots : String → Option Int) (block : List (JInstr 64))
    (hblock : allDirect block = true) :
    allDirect (spillRewrite ρ frameBase slots block) = true := by
  unfold spillRewrite
  induction block with
  | nil => rfl
  | cons i is ih =>
    -- the head instruction is direct (from allDirect (i :: is))
    have hi : IsDirect i := allDirect_mem_isDirect _ hblock i (List.mem_cons_self ..)
    have htl : allDirect is = true := by
      have h := hblock
      unfold allDirect at h ⊢
      rw [List.all_cons] at h
      exact (Bool.and_eq_true_iff.mp h).2
    rw [List.flatMap_cons, allDirect_append]
    refine Bool.and_eq_true_iff.mpr ⟨?_, ih htl⟩
    -- the per-instruction expansion: reloads ++ (renamed i :: stores)
    rw [allDirect_append]
    refine Bool.and_eq_true_iff.mpr ⟨spillReloads_allDirect _ _ i, ?_⟩
    -- (renamed i :: stores): head is direct via rename, tail are stores
    rw [show renameInstr ρ i :: spillStores frameBase slots i
          = [renameInstr ρ i] ++ spillStores frameBase slots i from rfl,
        allDirect_append]
    refine Bool.and_eq_true_iff.mpr ⟨?_, spillStores_allDirect _ _ i⟩
    rw [allDirect_singleton, decide_eq_true_eq]
    exact (allDirect_renameInstr ρ i).mpr hi

/-! ## 4. Constant-time of the spilled block, and the `CompilableCT` discharge -/

/-- **Constant-time after spill insertion.** The rename+spill rewrite of a
    direct-addressed block produces the **same** machine leakage trace from any
    two initial states: its observable control-flow + memory-address sequence is
    a function of the program text alone, leaking nothing about register values.
    The spill traffic lands at constant frame offsets, so the cache-line sequence
    it adds is fixed by the slot map, not by any secret. -/
theorem spillRewrite_constant_time (ρ : String → String) (frameBase : String)
    (slots : String → Option Int) (block : List (JInstr 64))
    (hblock : allDirect block = true) (s₁ s₂ : JState 64) :
    blockLeak s₁ (spillRewrite ρ frameBase slots block)
      = blockLeak s₂ (spillRewrite ρ frameBase slots block) :=
  allDirect_constant_time _ (spillRewrite_allDirect ρ frameBase slots block hblock) s₁ s₂

/-- **The spilled block is `CompilableCT`.** Since `CompilableCT b` is
    definitionally `allDirect b = true`, the headline lemma gives the spilled
    block the machine constant-time contract directly. -/
theorem spillRewrite_CompilableCT (ρ : String → String) (frameBase : String)
    (slots : String → Option Int) (block : List (JInstr 64))
    (hblock : allDirect block = true) :
    CompilableCT (spillRewrite ρ frameBase slots block) :=
  spillRewrite_allDirect ρ frameBase slots block hblock

end CatCrypt.Crypto.SecureCompilation.X86Backend.RegAllocSpillCT
