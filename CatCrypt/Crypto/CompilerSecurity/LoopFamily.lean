/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.RHPProvenance
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect

/-!
# Owned CT-provenance witnesses: scalar, bounded-loop, and regalloc'd blocks

This module wires owned-emit blocks of the verified `LowCT → JInstr` backend
into `RHPProvenance.MachineCTWitness.ownedConcrete`, the U2 CT-provenance
route. Each witness carries a concrete `List (JInstr 64)` block together with
an *unconditional* `∀ s₁ s₂, blockLeak s₁ b = blockLeak s₂ b` proof drawn from
the backend's own CT lemmas — so its `isCT` projection is axiom-free of
`jasminc_preserves_ct` (the cited axiom is never touched). This is the
`RHPProvenance.§4` piggyback applied to three further owned shapes.

## What is wired

* **`lowerArith` (single scalar assignment)** — the smallest owned block: a
  two-instruction `mov ; ⟨op⟩` lowering of `x := a ⟨op⟩ b`, CT by
  `LowCTToJInstrCT.lowerArith_constant_time` (all-`IsDirect`, no memory operand).
* **`lowerFor` (bounded counter loop)** — the loop family. A literal-bound
  scalar-arith for-loop, unrolled to a straight-line all-`IsDirect` block, CT
  by `LowCTForCT.lowerFor_constant_time`. The trip count and per-iteration index
  are literals (public), so no secret-dependent branch is emitted.
* **`renameBlock ∘ lowerSeq` (register-allocated block)** — the two-pass
  `allocate ∘ lower` pipeline output, CT by
  `ScalarCompileCorrect.scalarCompileAlloc_constant_time` (register allocation
  rewrites names, not the direct-addressing structure the CT proof relies on).

## Axiom-freeness

Each witness's `isCT` is its own CT proof term; `#print axioms` on the
`*_axiomFree` lemmas below shows `jasminc_preserves_ct` absent. The
`provenanceTag` of every witness is `CTProvenance.owned`. These are the
`#print axioms`-checkable demonstrations the orchestrator runs.

## Import closure

`RHPProvenance` (the witness type + the cited axiom it contrasts with),
`LowCTForCT` (the loop CT lemma, transitively `LowCTToJInstrCT` for the scalar
CT lemma), and `ScalarCompileCorrect` (the regalloc CT lemma). Nothing under
`Bridges/` or `IrisBridge/`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CTWitnesses

open CatCrypt.Crypto.SecureCompilation.X86Backend.RHPProvenance
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc (renameBlock)

/-! ## §1. Scalar-arith owned witness (the smallest owned block) -/

/-- **Owned CT witness for a single scalar-arith assignment.** The owned block
    `lowerArith ρ p` (`mov ρdst, ρa ; ⟨op⟩ ρdst, ρb`) wired into `ownedConcrete`
    via its unconditional CT lemma `lowerArith_constant_time`. -/
def scalarArithCTWitness (ρ : RegMap) (p : ArithSrc) : MachineCTWitness :=
  MachineCTWitness.ownedConcrete (lowerArith ρ p)
    (fun s₁ s₂ => lowerArith_constant_time ρ p s₁ s₂)

/-- The scalar-arith witness carries the `owned` provenance tag. -/
theorem scalarArithCTWitness_tag (ρ : RegMap) (p : ArithSrc) :
    (scalarArithCTWitness ρ p).provenanceTag = CTProvenance.owned := rfl

/-- **The scalar-arith witness's `isCT` is the concrete block CT, axiom-free of
    `jasminc_preserves_ct`.** Its proof term is exactly `lowerArith_constant_time`.
    `#print axioms` shows no `jasminc_preserves_ct`. -/
theorem scalarArithCTWitness_axiomFree (ρ : RegMap) (p : ArithSrc) :
    (scalarArithCTWitness ρ p).isCT :=
  fun s₁ s₂ => lowerArith_constant_time ρ p s₁ s₂

/-! ## §2. Bounded-loop owned witness (the loop family) -/

/-- **Owned CT witness for a bounded counter loop.** The owned unrolled block
    `lowerFor ρ f` of a literal-bound scalar-arith for-loop wired into
    `ownedConcrete` via its unconditional CT lemma `lowerFor_constant_time`.
    This is the loop-family analogue of `RHPProvenance.ownedKernelCTWitness`:
    the bounded loop is the shape `LprogControlFlow.loopLcmd` emits for every
    public-counter pass. -/
def loopCTWitness (ρ : RegMap) (f : ForSrc) : MachineCTWitness :=
  MachineCTWitness.ownedConcrete (lowerFor ρ f)
    (fun s₁ s₂ => lowerFor_constant_time ρ f s₁ s₂)

/-- The bounded-loop witness carries the `owned` provenance tag. -/
theorem loopCTWitness_tag (ρ : RegMap) (f : ForSrc) :
    (loopCTWitness ρ f).provenanceTag = CTProvenance.owned := rfl

/-- **The bounded-loop witness's `isCT` is the concrete block CT, axiom-free of
    `jasminc_preserves_ct`.** Its proof term is exactly `lowerFor_constant_time`.
    `#print axioms` shows no `jasminc_preserves_ct`. -/
theorem loopCTWitness_axiomFree (ρ : RegMap) (f : ForSrc) :
    (loopCTWitness ρ f).isCT :=
  fun s₁ s₂ => lowerFor_constant_time ρ f s₁ s₂

/-! ## §3. Register-allocated owned witness (the two-pass pipeline output) -/

/-- **Owned CT witness for the register-allocated block.** The two-pass
    `allocate ∘ lower` output `renameBlock ρalloc (lowerSeq ρmap ps)` wired into
    `ownedConcrete` via its unconditional CT lemma
    `scalarCompileAlloc_constant_time`. This is the regalloc-bridge witness:
    register allocation rewrites names, not the direct-addressing structure, so
    the allocated block is still CT. -/
def regAllocCTWitness (ρmap : RegMap) (ρalloc : String → String)
    (ps : List ArithSrc) : MachineCTWitness :=
  MachineCTWitness.ownedConcrete (renameBlock ρalloc (lowerSeq ρmap ps))
    (fun s₁ s₂ => scalarCompileAlloc_constant_time ρmap ρalloc ps s₁ s₂)

/-- The register-allocated witness carries the `owned` provenance tag. -/
theorem regAllocCTWitness_tag (ρmap : RegMap) (ρalloc : String → String)
    (ps : List ArithSrc) :
    (regAllocCTWitness ρmap ρalloc ps).provenanceTag = CTProvenance.owned := rfl

/-- **The register-allocated witness's `isCT` is the concrete block CT, axiom-free
    of `jasminc_preserves_ct`.** Its proof term is exactly
    `scalarCompileAlloc_constant_time`. `#print axioms` shows no
    `jasminc_preserves_ct`. -/
theorem regAllocCTWitness_axiomFree (ρmap : RegMap) (ρalloc : String → String)
    (ps : List ArithSrc) :
    (regAllocCTWitness ρmap ρalloc ps).isCT :=
  fun s₁ s₂ => scalarCompileAlloc_constant_time ρmap ρalloc ps s₁ s₂

/-! ## §4. A concrete closed loop witness (a fully-applied instance)

To exhibit a *closed* (no free variable) owned loop witness — the shape a
flipped owned leaf becomes — we instantiate `loopCTWitness` on a concrete
identity register map and a 4-iteration `acc := acc + acc` loop body. -/

/-- A concrete 4-iteration bounded loop `for i = 0 to 4 { acc := acc + acc }`
    over the identity register map. A closed `ForSrc` (no free variable). -/
def demoLoop : ForSrc :=
  { x := "i", n := 4, body := [{ dst := "acc", a := "acc", op := .add, b := "acc" }] }

/-- The concrete owned loop witness — `loopCTWitness` fully applied. -/
def demoLoopCTWitness : MachineCTWitness :=
  loopCTWitness (fun s => s) demoLoop

/-- The concrete loop witness carries the `owned` provenance tag. -/
theorem demoLoopCTWitness_tag :
    demoLoopCTWitness.provenanceTag = CTProvenance.owned := rfl

/-- **The concrete loop witness's `isCT` is axiom-free of `jasminc_preserves_ct`.**
    `#print axioms` shows no `jasminc_preserves_ct` — a closed owned loop leaf
    discharging machine CT with no appeal to the cited axiom. -/
theorem demoLoopCTWitness_axiomFree : demoLoopCTWitness.isCT :=
  fun s₁ s₂ => lowerFor_constant_time (fun s => s) demoLoop s₁ s₂

-- Orchestrator: confirm no `jasminc_preserves_ct` in any of these:
-- #print axioms scalarArithCTWitness_axiomFree
-- #print axioms loopCTWitness_axiomFree
-- #print axioms regAllocCTWitness_axiomFree
-- #print axioms demoLoopCTWitness_axiomFree

end CatCrypt.Crypto.SecureCompilation.X86Backend.CTWitnesses
