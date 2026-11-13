/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.UnitarySoundL2
public import CatCrypt.Quantum.Optimization.UnitarySoundL3
public import CatCrypt.Quantum.Optimization.EGraphSound
public import CatCrypt.Quantum.Optimization.PassPipeline
public import CatCrypt.Quantum.Optimization.QPass

/-!
# Full optimizer soundness under the real unitary semantics

`fullOptimize level` runs the pass list `PassPipeline.levelPasses level`. Every
named pass preserves the unitary-channel denotation `unitaryDenote` (ρ ↦ UρU†),
so all four levels do: `fullOptimize_unitaryCorrect`. Level 3's final stage is
hardware routing (`insertSwaps`); its `swapGate ; g.relabel ; swapGate` block
realizes the original gate's unitary `S · U_{g.relabel} · S = U_g`, so routing
preserves the semantics too (`UnitarySoundL3`).

## Main results

* `fullOptimize_unitaryCorrect` — every level preserves `unitaryDenote`
* `fullOptimize_preserves_quc`  — every level preserves a `qdist` bound
  against an ideal functionality
* `fullOptimizePass`            — `fullOptimize` packaged as a `QPass`
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

open CatCrypt.Quantum
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.FullOptimizer
open CatCrypt.Quantum.Optimization.UnitarySoundFull
open CatCrypt.Quantum.Optimization.UnitarySoundL2
open CatCrypt.Quantum.Optimization.UnitarySoundL3
open CatCrypt.Quantum.Optimization.RewriteFixpoint
open CatCrypt.Quantum.Optimization.HardwareRouting

namespace CatCrypt.Quantum.Optimization.UnitarySoundCapstone

variable {n : ℕ}

/-- **The full optimizer preserves the real unitary semantics at every level.**
For all four levels — including Level 3, whose routing stage emits relabelled
gates inside SWAP-conjugation blocks that realize the original unitaries —
`fullOptimize` preserves `unitaryDenote`. (Level 3 uses the default
`CouplingGraph.linear n` topology; see `PassPipeline.routedPipeline_unitaryDenote`.) -/
theorem fullOptimize_unitaryCorrect (level : OptLevel) :
    UnitaryCorrectQ (fullOptimize level : Circuit n → Circuit n) :=
  PassPipeline.runNamed_unitaryCorrect _

/-! ## QUC security preservation -/

/-- The full optimizer preserves quantum UC security bounds at every level: if
    the source circuit is `ε`-close in `qdist` to an ideal functionality, so is
    the optimized circuit. -/
theorem fullOptimize_preserves_quc {ε : ℝ≥0∞}
    (level : OptLevel)
    (F_ideal : QComp (2 ^ n) Unit)
    (c : Circuit n)
    (hsec : UCMonad.QuantumUC.qdist
              (fun () => unitaryDenote c) (fun () => F_ideal) ≤ ε) :
    UCMonad.QuantumUC.qdist
      (fun () => unitaryDenote (fullOptimize level c)) (fun () => F_ideal) ≤ ε :=
  unitaryCorrect_preserves_quc _ (fullOptimize_unitaryCorrect level) F_ideal c hsec

/-- The full optimizer as a `QPass`: the pass `fullOptimize level` with its proof of
    `UnitaryCorrect`. -/
noncomputable def fullOptimizePass (level : OptLevel) : QPass n where
  transform := fullOptimize level
  correct := fullOptimize_unitaryCorrect level

end CatCrypt.Quantum.Optimization.UnitarySoundCapstone
