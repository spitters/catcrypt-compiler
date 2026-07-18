/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
import CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped

/-!
# The verified-compiler theorem for the straight-line scalar fragment

`LowCTToJInstrCT` lowers a basic block of the homomorphic-scalar `LowCT` fragment
(`{add, mul, and, xor}`) to `JInstr`, with semantics-preservation (`lowerSeq_denote`)
and constant-time (`lowerSeq_constant_time`) proved separately. This module bundles
them into the single **compiler-correctness** statement of the CompCert/Jasmin shape —
*the compiled code computes the source function **and** is constant-time* — and shows
the constant-time property **survives the validated register-allocation pass**
(`renameBlock`), so the two-pass pipeline `allocate ∘ lower` is correct end-to-end on
the CT dimension.

* `scalarCompile_correct` — semantics-preservation ∧ machine-CT for `lowerSeq`,
  with the real-`LowCT` source guarantee `cmdCT (seqToLowCT ps) = true` as hypothesis.
* `allDirect_renameInstr` / `allDirect_renameBlock` — a register renaming preserves
  `allDirect` (it rewrites register *names*, never opcodes; `IsDirect` is an
  opcode property), so an aliasing-free allocation cannot turn a direct-addressed
  block into a secret-indexed one.
* `scalarCompileAlloc_constant_time` — the *allocated* lowered block is constant-time.

* `scalarCompileAlloc_denote` — the two-pass `compile = allocate ∘ lower` semantics:
  the fully-compiled block holds the source post-value at each allocated register
  `ρalloc (ρmap v)`, composing `lowerSeq_denote` (source→machine) with
  `regalloc_runBlock_sound_on` (machine→allocated, under the no-alias certificate),
  scoped to the block's live slots — and `scalarCompileAlloc_denote_checked` with the
  decidable `noAliasXsym` discharging the allocation.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Optimizer.GenericRegAlloc (RenInjOn)
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc (renameBlock)
open CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped
  (StateRelOn blockNamesXsym regalloc_runBlock_sound_on noAliasXsym noAliasXsym_sound)

/-! ## 1. The compiler-correctness theorem (semantics + constant-time) -/

/-- **Verified compiler — straight-line scalar fragment.** For a register map `ρ`
    injective on the live slots, a basic block `ps` of the homomorphic-scalar
    `LowCT` fragment whose source CT verdict `cmdCT (seqToLowCT ps)` is `true`,
    and a machine state matching the source state, the lowered block:

    1. **computes the source function** — the post-machine state matches the source
       post-state `srcDenote ps rs` (semantics-preservation); and
    2. **is constant-time** — its machine leakage trace is identical from any two
       states (so it leaks nothing about secret register values).

    The two guarantees a verified compiler delivers, for this fragment, in one
    statement. The `cmdCT` hypothesis is the genuine source-analyzer verdict on a
    real `LowCT` `RSeq` chain (`seqToLowCT`). -/
theorem scalarCompile_correct (ρ : RegMap) (hρ : Function.Injective ρ)
    (ps : List ArithSrc) (hwf : ∀ p ∈ ps, p.b ≠ p.dst)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (_hct : cmdCT (ArithSrc.seqToLowCT ps) lt leafCT = true)
    (rs : RustState) (js : JState 64) (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (srcDenote ps rs) (runBlock js (lowerSeq ρ ps))
    ∧ (∀ s₁ s₂ : JState 64,
        blockLeak s₁ (lowerSeq ρ ps) = blockLeak s₂ (lowerSeq ρ ps)) :=
  ⟨lowerSeq_denote ρ hρ ps hwf rs js hmatch,
   fun s₁ s₂ => lowerSeq_constant_time ρ ps s₁ s₂⟩

/-! ## 2. Constant-time survives register allocation -/

open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc in
/-- A renaming preserves `IsDirect`: it rewrites register *names*, never opcodes,
    and `IsDirect` excludes exactly the two register-indexed opcodes
    (`loadMemIdx`/`storeMemIdx`), whose constructor `renameInstr` preserves. -/
theorem allDirect_renameInstr (ρ : String → String) (i : JInstr 64) :
    IsDirect (renameInstr ρ i) ↔ IsDirect i := by
  cases i <;> simp [renameInstr, IsDirect]

open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc in
/-- A renaming preserves `allDirect` of a whole block. -/
theorem allDirect_renameBlock (ρ : String → String) (block : List (JInstr 64)) :
    allDirect (renameBlock ρ block) = allDirect block := by
  unfold allDirect renameBlock
  induction block with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.all_cons, ih]
    rw [decide_eq_decide.mpr (allDirect_renameInstr ρ i)]

open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc in
/-- **Constant-time after allocation.** The lowered block, after the validated
    register-allocation renaming `ρ`, is still constant-time: register allocation
    rewrites names, not the direct-addressing structure the CT proof relies on. So
    the two-pass `allocate ∘ lower` pipeline is constant-time. -/
theorem scalarCompileAlloc_constant_time (ρmap : RegMap) (ρalloc : String → String)
    (ps : List ArithSrc) (s₁ s₂ : JState 64) :
    blockLeak s₁ (renameBlock ρalloc (lowerSeq ρmap ps))
      = blockLeak s₂ (renameBlock ρalloc (lowerSeq ρmap ps)) :=
  allDirect_constant_time _
    (by rw [allDirect_renameBlock]; exact lowerSeq_allDirect ρmap ps) s₁ s₂

/-! ## 3. The two-pass `compile = allocate ∘ lower` semantics theorem -/

/-- **Two-pass compiler semantics-preservation (scalar fragment).** Composing the
    lowering (`lowerSeq_denote`, source→machine) with the validated register-allocation
    renaming (`regalloc_runBlock_sound_on`, machine→allocated under the no-alias
    certificate `RenInjOn`): the fully-compiled block `renameBlock ρalloc (lowerSeq
    ρmap ps)`, run from an allocated initial state `s` related to the source-matching
    `js`, holds at the allocated register `ρalloc (ρmap v)` exactly the source post-value
    `srcDenote ps rs` — for every live slot `v` (those the block mentions). The
    source→allocated-machine value theorem, scoped to the block's slots (the
    translation-validation discipline). -/
theorem scalarCompileAlloc_denote (ρmap : RegMap) (ρalloc : String → String)
    (hmapinj : Function.Injective ρmap) (ps : List ArithSrc)
    (hwf : ∀ p ∈ ps, p.b ≠ p.dst)
    (hallocinj : RenInjOn (blockNamesXsym (lowerSeq ρmap ps)) ρalloc)
    (rs : RustState) (js s : JState 64)
    (hmatch : StateMatch ρmap rs js)
    (hrel : StateRelOn (blockNamesXsym (lowerSeq ρmap ps)) ρalloc s js)
    (v : String) (hv : ρmap v ∈ blockNamesXsym (lowerSeq ρmap ps)) :
    (runBlock s (renameBlock ρalloc (lowerSeq ρmap ps))).get (ρalloc (ρmap v))
      = BitVec.ofNat 64 ((srcDenote ps rs).rsScalar v) := by
  have hreg := regalloc_runBlock_sound_on (lowerSeq ρmap ps) hallocinj s js hrel
  have h1 := hreg.regsOn (ρmap v) hv
  have h2 := lowerSeq_denote ρmap hmapinj ps hwf rs js hmatch v
  simp only [JState.get] at h1 h2 ⊢
  rw [h1]; exact h2

/-- The two-pass semantics theorem with the allocation discharged by the decidable
    no-alias checker (`noAliasXsym`). -/
theorem scalarCompileAlloc_denote_checked (ρmap : RegMap) (ρalloc : String → String)
    (hmapinj : Function.Injective ρmap) (ps : List ArithSrc)
    (hwf : ∀ p ∈ ps, p.b ≠ p.dst)
    (hchk : noAliasXsym ρalloc (lowerSeq ρmap ps) = true)
    (rs : RustState) (js s : JState 64)
    (hmatch : StateMatch ρmap rs js)
    (hrel : StateRelOn (blockNamesXsym (lowerSeq ρmap ps)) ρalloc s js)
    (v : String) (hv : ρmap v ∈ blockNamesXsym (lowerSeq ρmap ps)) :
    (runBlock s (renameBlock ρalloc (lowerSeq ρmap ps))).get (ρalloc (ρmap v))
      = BitVec.ofNat 64 ((srcDenote ps rs).rsScalar v) :=
  scalarCompileAlloc_denote ρmap ρalloc hmapinj ps hwf
    (noAliasXsym_sound ρalloc (lowerSeq ρmap ps) hchk) rs js s hmatch hrel v hv

end CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect
