/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.BorrowToMemoryBridge
import CatCrypt.Crypto.SecureCompilation.RustStateSubstrate
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim

/-!
# B2.3: integrating B1's `RustStateInterp` with the borrow ↔ memory bridge

This file is the **B2.3** follow-up to `BorrowToMemoryBridge.lean`.
With B1 closed (`rustExecSimulatesCryptoSSA` Qed at `[propext,
Classical.choice, Quot.sound]`) the bridge can compose its
memory-frame conclusion with B1's CryptoSSA-side valuation existence
into a single statement: from a `borrowOk` source program, an
interpreted initial state, and pairwise-disjoint tracked regions, we
get *both* that the memory invariants survive the step *and* that the
CryptoSSA valuation V' exists at the post-state.

This is the compositional shape Track A2 needs to lift RHP from the
verified middle to the front-end boundary, and what the writeup's
"borrow ↔ memory bridge composes with the byte-layout simulation"
sentence is supposed to denote.

## What's stated here

* `bridge_with_rustState` — the integrated theorem: combines
  `borrowOk_implies_memory_invariants_preserved` with
  `rustExecSimulatesCryptoSSA`, producing a single existential at
  the post-state.
* `bridge_smoke_RScalarSet` — a smoke test on a non-memory-touching
  `RScalarSet`, which closes without the operational hypothesis.

The operational hypothesis (`StepSimulatesJasmin`) is still required
to lift `RustExec` to the abstract `step` relation; B4 will discharge
it. The compositional shape stated here is what callers will hold.

**0 sorries.** Standard axioms + the operational hypothesis.
-/

namespace CatCrypt.Crypto.SecureCompilation.BorrowToMemoryBridgeRustState

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.SemBridge
open CatCrypt.Crypto.Jasmin.Hoare
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.BorrowToMemoryBridge
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim

set_option autoImplicit false

/-! ## §1. The integrated bridge theorem

Combines:
* `borrowOk_implies_memory_invariants_preserved` (memory-side, B2)
* `rustExecSimulatesCryptoSSA`                   (state-side, B1)

into one statement. Caller supplies the state interpretation, the
borrow proof, the disjoint-region structure, and the operational
glue; the theorem produces both halves of the compositional result.

The hypothesis `h_disjoint_body` is the per-region disjointness
between the body's footprint and each tracked region, exactly as in
the underlying B2 theorem. `h_step` lifts `RustExec` to the abstract
`step`. -/

/-- **Integrated bridge** (B2 ⊗ B1). Given a translated `borrowOk`
LowCT source, an interpreted initial rust state, and pairwise-disjoint
tracked regions, the post-step state preserves every region's
`array64` invariant *and* a CryptoSSA-side valuation V' satisfies
`RustStateInterp` at the post-state. -/
theorem bridge_with_rustState
    {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) (out : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec)
    -- Coverage on the `CProg`-free dialect front (covered control fragment):
    (hCov : IsCoveredCtl c)
    -- Translation evidence (front-end side, `CProg`-free dialect front):
    (hT : translateDialectControl vm c = some out)
    -- Initial-state interpretation (B1 byte-layout invariant):
    (rs rs' : RustState) (V : HVec Γ)
    (hInv : RustStateInterp vm rs V)
    -- Borrow-check + memory disjointness (B2 framing):
    (_h_borrow : borrowOk c = true)
    (regions : List TrackedRegion)
    (_h_pairwise : TrackedRegions.PairwiseDisjoint regions)
    (step : StepRel) (footprint : WriteFootprint)
    (h_resp : RespectsFootprint step footprint)
    (h_disjoint_body :
        ∀ r ∈ regions,
          MemoryModel.Disjoint (footprint (toJasminCmd c))
                   (array64Footprint r.base r.words))
    -- Operational glue (B4 will discharge):
    (mem mem' : Mem)
    (h_init  : TrackedRegions.InitArrays regions mem)
    (h_step  : step (toJasminCmd c)
                 { regs := rs,  mem := mem }
                 { regs := rs', mem := mem' })
    -- Front-end execution (rust-side):
    (hExec : RustExec N leafSpec c rs rs') :
    -- Memory side: every tracked region's array64 survives.
    TrackedRegions.InitArrays regions mem' ∧
    -- State side: a CryptoSSA valuation V' satisfies the byte-layout.
    ∃ V' : HVec out.Γ', RustStateInterp out.vm rs' V' := by
  refine ⟨?_, ?_⟩
  · -- Memory preservation reduces to the B2 framing theorem.
    exact borrowOk_implies_memory_invariants_preserved
            step footprint h_resp c _h_borrow
            regions _h_pairwise h_disjoint_body
            { regs := rs, mem := mem } { regs := rs', mem := mem' }
            h_init h_step
  · -- State witness comes from the `CProg`-free dialect-front simulation theorem.
    exact rustExecSimulatesDialect vm c out N leafSpec rs rs' hCov hT hExec V hInv

/-! ## §2. Smoke

Specialise on `RScalarSet x v` (no memory writes, no nontrivial
translate, no IH). The smoke verifies the integrated statement's
shape; the operational hypothesis is admitted as the bridge's
documented B4-deferred glue. -/

namespace Smoke

/-- The trivial RScalarSet program. -/
def progSet : LowCT := .RScalarSet "x" 42

/-- For `RScalarSet`, `borrowOk` accepts trivially (no memory). -/
example : borrowOk progSet = true := by decide

/-- A footprint that returns "false" everywhere — i.e., the body
    writes nothing — necessarily disjoint from any region. This is
    the inhabitant supplied by the per-arm `footprint_RScalarSet_disjoint`
    closure in `BorrowToMemoryBridge.lean`. -/
def emptyFootprint : WriteFootprint := fun _ _ => False

/-- The empty footprint disjoint from any region. -/
theorem emptyFootprint_disjoint (region : TrackedRegion) :
    MemoryModel.Disjoint
      (emptyFootprint (toJasminCmd progSet))
      (array64Footprint region.base region.words) := by
  intro a ⟨ha, _⟩
  exact ha.elim

end Smoke

end CatCrypt.Crypto.SecureCompilation.BorrowToMemoryBridgeRustState
