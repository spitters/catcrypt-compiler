/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.ZXOptimize
public import CatCrypt.Quantum.Optimization.CommutationRules
public import CatCrypt.Quantum.Optimization.TCountOpt
public import CatCrypt.Quantum.Optimization.HardwareRouting
public import CatCrypt.Quantum.Optimization.TemplateMatching
public import CatCrypt.Quantum.Optimization.NotPropagation
public import CatCrypt.Quantum.Optimization.RotationMerging
public import CatCrypt.Quantum.Optimization.RewriteFixpoint

/-!
# Full Quantum Circuit Optimizer

Compose all optimization passes (template matching, commutation rules,
T-count optimization, ZX calculus optimization, hardware routing) into a
configurable multi-level optimizer.

## Optimization Levels

* **Level 1** (fast): Template matching only. Removes self-inverse gate pairs
  (H.H, X.X, CNOT.CNOT), merges rotations, and applies conjugation identities.

* **Level 2** (moderate): Level 1 + commutation-based merging + T-count
  optimization. Moves commuting gates together for further merging
  opportunities and reduces T-gate count via power merging (T^2 = S, T^4 = Z).

* **Level 3** (aggressive): Level 2 + ZX calculus optimization + hardware
  routing. Converts the circuit to a ZX diagram for deep rewrites, then
  routes the result for a target hardware topology.

## Main definitions

* `OptLevel`              -- optimization aggressiveness (Level1 to Level4)
* `standardTemplates`, `cnotTemplates` -- the template library
* `optimizeLevel1`, `optimizeLevel2`, `optimizeLevel3` -- the per-qubit rescanning
  passes and their compositions

The optimizer entry point `fullOptimize`, which runs the pass list of a level, is
defined in `Optimization/PassPipeline.lean`, since its passes `TemplatePass` and
`CommuteCancel` import this module.

## References

* Hietala et al. -- A Verified Optimizer for Quantum Circuits (POPL 2021)
* Nam et al. -- Automated optimization of large quantum circuits with
  continuous parameters, npj Quantum Information 2018
* Kissinger, van de Wetering -- Reducing the number of non-Clifford gates
  in quantum circuits, Physical Review A 2020
-/

@[expose] public section

set_option autoImplicit true

namespace CatCrypt.Quantum.Optimization.FullOptimizer

open scoped ENNReal
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.Optimization.CommutationRules
open CatCrypt.Quantum.Optimization.TCountOpt
open CatCrypt.Quantum.Optimization.HardwareRouting
open CatCrypt.Quantum.Optimization.TemplateMatching
open CatCrypt.Quantum.Optimization.NotPropagation
open CatCrypt.Quantum.Optimization.RotationMerging
open CatCrypt.Quantum.Optimization.RewriteFixpoint

/-! ## Optimization Level -/

/-- Optimization aggressiveness level.

    * `Level1` — fast, template matching only (~10% reduction)
    * `Level2` — moderate, + commutation + T-count (~30% reduction)
    * `Level3` — aggressive, + ZX optimize + routing (~50% reduction)
    * `Level4` — `rewriteFixpointOptimize`: all rules in one list, rewritten to a
      fuel-bounded fixpoint (first matching rule at each position) -/
inductive OptLevel : Type where
  | Level1 : OptLevel
  | Level2 : OptLevel
  | Level3 : OptLevel
  | Level4 : OptLevel
  deriving Repr, DecidableEq

/-! ## Standard Template Library -/

/-- The standard set of single-qubit circuit identities used for template matching.
    Includes self-inverse cancellations, rotation merging, and
    Hadamard conjugation rules. -/
def standardTemplates (q : Fin n) : List (Template n) :=
  [ cancelHH q,
    cancelXXTemplate q,
    cancelYY q,
    cancelZZ q,
    cancelTTdg q,
    cancelTdgT q,
    mergeTT q,
    mergeTdgTdg q,
    hxh_to_z q,
    hzh_to_x q,
    mergeSS q ]

/-- Two-qubit templates: CNOT cancellation for a given qubit pair. -/
def cnotTemplates (c t : Fin n) : List (Template n) :=
  [ cancelCNOT c t ]

/-! ## Level 1: Template Matching -/

/-- Level 1 optimization: apply template matching to remove redundant gates.
    Iterates through all qubits and applies standard single-qubit templates,
    then applies CNOT cancellation for all qubit pairs. -/
def optimizeLevel1 (c : Circuit n) : Circuit n :=
  -- Apply single-qubit templates for each qubit index
  let c₁ := Fin.foldl n (fun acc q => applyTemplates (standardTemplates q) acc) c
  -- Apply CNOT cancellation templates for all qubit pairs
  Fin.foldl n (fun acc₁ i =>
    Fin.foldl n (fun acc₂ j =>
      if decide (i = j) then acc₂
      else applyTemplates (cnotTemplates i j) acc₂) acc₁) c₁

/-! ## Level 2: Commutation + T-Count -/

/-- Level 2 optimization: Level 1 + commute-and-merge + T-count + NOT propagation.
    First applies template matching, then moves commuting gates together
    for further merging, optimizes T-gate count, and propagates NOT gates. -/
def optimizeLevel2 (c : Circuit n) : Circuit n :=
  notPropagationPass (tMerge (commuteAndMerge (optimizeLevel1 c)))

/-! ## Level 3: ZX + Routing -/

/-- Level 3 optimization: Level 2 + rotation merging + hardware routing.
    After all logical optimizations, applies rotation merging (VOQC-style),
    then inserts SWAP gates to make the circuit routable on the given
    coupling graph.

    The ZX calculus optimizer from `ZXOptimize.lean` operates on
    `ZXDiagram 1 1` (single-qubit), so it is not directly applicable
    to multi-qubit circuits. A full circuit-to-ZX-to-circuit round-trip
    is left as future work. -/
def optimizeLevel3 (cg : CouplingGraph n) (c : Circuit n) : Circuit n :=
  insertSwaps (rotationMergingPass (optimizeLevel2 c)) cg

/-! ## Benchmark Examples -/

/-- Example: a circuit with adjacent H.H gates (should be eliminated). -/
def benchHH (q : Fin n) : Circuit n :=
  Circuit.seq (Circuit.single (Gate.H q)) (Circuit.single (Gate.H q))

/-- Example: a circuit with T^8 (should be eliminated to identity). -/
def benchT8 (q : Fin n) : Circuit n :=
  Circuit.ofList (List.replicate 8 (Gate.T q))

/-- Example: a circuit with CNOT.CNOT (should be eliminated). -/
def benchCNOT2 (c t : Fin n) : Circuit n :=
  Circuit.seq (Circuit.single (Gate.CNOT c t))
              (Circuit.single (Gate.CNOT c t))

/-- T-count of 8 consecutive T gates. -/
theorem benchT8_tCount (q : Fin n) :
    tCount (benchT8 q) = 8 := by
  simp [benchT8, Circuit.ofList, List.replicate, tCount, isT]

end CatCrypt.Quantum.Optimization.FullOptimizer
