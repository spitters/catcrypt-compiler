/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.UnitarySoundFull
public import CatCrypt.Quantum.Optimization.CommuteMergeSound
public import CatCrypt.Quantum.Optimization.TMergeSound
public import CatCrypt.Quantum.Optimization.NotPropSound

/-!
# Level-2 optimizer soundness under the real unitary semantics

`optimizeLevel2 = notPropagationPass ∘ tMerge ∘ commuteAndMerge ∘ optimizeLevel1`.
Each stage preserves the unitary-channel denotation `unitaryDenote`
(ρ ↦ UρU†), so their composition does too — `optimizeLevel2_unitaryCorrect`.
This replaces the vacuous `FullOptimizer.optimizeLevel2_correct` (proved against
the trivial `qpure ()` denotation) with the real-semantics statement.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.FullOptimizer
open CatCrypt.Quantum.Optimization.UnitarySoundFull
open CatCrypt.Quantum.Optimization.CommuteMergeSound
open CatCrypt.Quantum.Optimization.TMergeSound
open CatCrypt.Quantum.Optimization.NotPropSound

namespace CatCrypt.Quantum.Optimization.UnitarySoundL2

variable {n : ℕ}

/-- **The full Level-2 optimizer preserves the real unitary semantics.** -/
theorem optimizeLevel2_unitaryCorrect :
    UnitaryCorrectQ (optimizeLevel2 : Circuit n → Circuit n) := by
  intro c
  show unitaryDenote c = unitaryDenote (optimizeLevel2 c)
  rw [optimizeLevel2, notPropagationPass_unitaryDenote, unitaryDenote_tMerge,
    unitaryDenote_commuteAndMerge]
  exact optimizeLevel1_unitaryCorrect c

end CatCrypt.Quantum.Optimization.UnitarySoundL2
