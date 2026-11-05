/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.UnitarySoundL2
public import CatCrypt.Quantum.Optimization.RotMergeSound
public import CatCrypt.Quantum.Optimization.SwapConj

/-!
# Level-3 optimizer under the real unitary semantics

`optimizeLevel3 cg = insertSwaps (rotationMergingPass (optimizeLevel2 ·)) cg`.

The logical core — `rotationMergingPass ∘ optimizeLevel2` — preserves
`unitaryDenote` (`optimizeLevel3_core_unitaryCorrect`). The final stage
`insertSwaps` is hardware routing: it wraps each non-adjacent two-qubit gate as
`swapGate i mid ; g.relabel i mid ; swapGate i mid`, whose unitary is
`S · U_{g.relabel} · S = U_g` (`SwapConj.insertSwaps_unitaryDenote`), so it too
preserves `unitaryDenote`. Composing the two gives
`optimizeLevel3_unitaryCorrect`: Level 3 preserves the quantum meaning,
like Levels 1 and 2.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.UnitaryChannel
open CatCrypt.Quantum.Optimization.FullOptimizer
open CatCrypt.Quantum.Optimization.HardwareRouting
open CatCrypt.Quantum.Optimization.RotationMerging
open CatCrypt.Quantum.Optimization.UnitarySoundL2
open CatCrypt.Quantum.Optimization.RotMergeSound
open CatCrypt.Quantum.Optimization.RoutingPerm
open CatCrypt.Quantum.Optimization.SwapConj

namespace CatCrypt.Quantum.Optimization.UnitarySoundL3

variable {n : ℕ}

/-- The semantics-preserving logical core of Level 3 (before routing):
`rotationMergingPass ∘ optimizeLevel2` preserves `unitaryDenote`. -/
theorem optimizeLevel3_core_unitaryCorrect (c : Circuit n) :
    unitaryDenote (rotationMergingPass (optimizeLevel2 c)) = unitaryDenote c := by
  rw [rotationMergingPass_unitaryDenote]
  exact (optimizeLevel2_unitaryCorrect c).symm

/-- **Level 3 preserves the real unitary semantics.** The logical passes preserve
`unitaryDenote` (`optimizeLevel3_core_unitaryCorrect`); the routing stage
`insertSwaps` preserves it too (`insertSwaps_unitaryDenote`), since each routed
gate's `swapGate ; g.relabel ; swapGate` block realizes the original `U_g`. -/
theorem optimizeLevel3_unitaryCorrect (cg : CouplingGraph n) :
    UnitaryCorrectQ (optimizeLevel3 cg : Circuit n → Circuit n) := by
  intro c
  show unitaryDenote c = unitaryDenote (optimizeLevel3 cg c)
  rw [optimizeLevel3, insertSwaps_unitaryDenote]
  exact (optimizeLevel3_core_unitaryCorrect c).symm

end CatCrypt.Quantum.Optimization.UnitarySoundL3
