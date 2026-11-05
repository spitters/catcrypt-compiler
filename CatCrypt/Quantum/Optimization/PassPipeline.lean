/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.UnitarySoundL3
public import CatCrypt.Quantum.Optimization.EGraphSound
public import CatCrypt.Quantum.Optimization.TemplatePass
public import CatCrypt.Quantum.Optimization.CommuteCancel
public import CatCrypt.Quantum.Optimization.RzQCanon
public meta import CatCrypt.Quantum.Optimization.UnitarySoundL3
public meta import CatCrypt.Quantum.Optimization.EGraphSound
public meta import CatCrypt.Quantum.Optimization.TemplatePass
public meta import CatCrypt.Quantum.Optimization.CommuteCancel
public meta import CatCrypt.Quantum.Optimization.RzQCanon

/-!
# The circuit optimizer as a list of passes

A pipeline is a list of passes `Circuit n → Circuit n`, run left to right by
`runPasses`. If every pass in the list preserves the unitary-channel denotation
`unitaryDenote`, so does the pipeline (`runPasses_unitaryCorrect`).

`NamedPass` enumerates the optimizer's passes: template matching (the per-qubit
rescan and the single left-to-right pass), commutation merging, commutation-aware
cancellation, rewriting of exact rotations at Clifford+T angles to `T`, `T†`, `S`,
`Z` or no gate (`RzQCanon.rzqCanonPass`), T merging, NOT propagation (unguarded
and where it does not lengthen the circuit), rotation merging, routing on a
coupling graph, and e-graph saturation. Each is sound
(`NamedPass.run_unitaryCorrect`), so every list of named passes, in any order
and with any coupling graph, is sound (`runNamed_unitaryCorrect`). The four
`OptLevel`s are particular lists (`levelPasses`), and
`FullOptimizer.fullOptimize level` is the run of `levelPasses level`. Every pass
evaluates, so the optimizer runs.

## Main definitions

* `runPasses`        — run a list of passes by a left fold
* `notPropagationNoLonger` — NOT propagation where it does not lengthen the circuit
* `NamedPass`        — the optimizer's passes, `routing` taking a coupling graph
* `runNamed`         — run a list of named passes
* `routedPipeline`   — the logical passes followed by routing on `cg`
* `levelPasses`      — the pass list of each `OptLevel`
* `FullOptimizer.fullOptimize` — the optimizer at a level

## Main results

* `runPasses_unitaryCorrect` — a list of sound passes is a sound pipeline
* `NamedPass.run_unitaryCorrect` — each named pass preserves `unitaryDenote`
* `runNamed_unitaryCorrect` — every list of named passes preserves `unitaryDenote`
* `routedPipeline_unitaryDenote` — routing on any coupling graph `cg`, after the
  logical passes, preserves `unitaryDenote`
* `fullOptimize_eq_runNamed` — the levels as pass lists, by unfolding
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.FullOptimizer
open CatCrypt.Quantum.Optimization.CommutationRules
open CatCrypt.Quantum.Optimization.TCountOpt
open CatCrypt.Quantum.Optimization.NotPropagation
open CatCrypt.Quantum.Optimization.RotationMerging
open CatCrypt.Quantum.Optimization.HardwareRouting
open CatCrypt.Quantum.Optimization.RewriteFixpoint
open CatCrypt.Quantum.Optimization.UnitarySoundFull
open CatCrypt.Quantum.Optimization.CommuteMergeSound
open CatCrypt.Quantum.Optimization.TMergeSound
open CatCrypt.Quantum.Optimization.NotPropSound
open CatCrypt.Quantum.Optimization.RotMergeSound
open CatCrypt.Quantum.Optimization.SwapConj

namespace CatCrypt.Quantum.Optimization.PassPipeline

variable {n : ℕ}

/-! ## Pipelines of arbitrary passes -/

/-- Run a list of passes left to right: the head of the list is applied first. -/
def runPasses (ps : List (Circuit n → Circuit n)) (c : Circuit n) : Circuit n :=
  ps.foldl (fun acc p => p acc) c

@[simp] theorem runPasses_nil (c : Circuit n) : runPasses [] c = c := rfl

@[simp] theorem runPasses_cons (p : Circuit n → Circuit n)
    (ps : List (Circuit n → Circuit n)) (c : Circuit n) :
    runPasses (p :: ps) c = runPasses ps (p c) := rfl

theorem runPasses_append (ps qs : List (Circuit n → Circuit n)) (c : Circuit n) :
    runPasses (ps ++ qs) c = runPasses qs (runPasses ps c) := by
  simp only [runPasses, List.foldl_append]

/-- A pipeline whose passes each preserve `unitaryDenote` preserves it. -/
theorem runPasses_unitaryCorrect (ps : List (Circuit n → Circuit n))
    (h : ∀ p ∈ ps, UnitaryCorrectQ p) : UnitaryCorrectQ (runPasses ps) := by
  induction ps with
  | nil => exact fun _ => rfl
  | cons p ps ih =>
    intro c
    have hp : UnitaryCorrectQ p := h p List.mem_cons_self
    have hps : UnitaryCorrectQ (runPasses ps) :=
      ih fun q hq => h q (List.mem_cons_of_mem p hq)
    exact Eq.trans (hp c) (hps (p c))

/-! ## NOT propagation where it does not lengthen the circuit -/

/-- `notPropagationPass` where it does not lengthen the circuit, else the identity.
    On `mod_mult_55`, `rc_adder_6` and `mod_red_21` the pass adds gates (127 to 142,
    200 to 208, 280 to 297) and leaves the T-count unchanged. -/
@[irreducible] def notPropagationNoLonger (c : Circuit n) : Circuit n :=
  if (notPropagationPass c).gateCount ≤ c.gateCount then notPropagationPass c else c

theorem notPropagationNoLonger_unitaryDenote (c : Circuit n) :
    unitaryDenote (notPropagationNoLonger c) = unitaryDenote c := by
  unfold notPropagationNoLonger
  split
  · exact notPropagationPass_unitaryDenote c
  · rfl

theorem gateCount_notPropagationNoLonger_le (c : Circuit n) :
    (notPropagationNoLonger c).gateCount ≤ c.gateCount := by
  unfold notPropagationNoLonger
  split
  · assumption
  · exact le_rfl

/-! ## The named passes -/

/-- The passes of the circuit optimizer. `routing cg` inserts SWAP blocks so
that every two-qubit gate acts on qubits adjacent in the coupling graph `cg`. -/
inductive NamedPass (n : ℕ) : Type where
  /-- Template matching, rescanning per qubit and qubit pair (`optimizeLevel1`). -/
  | templateMatching : NamedPass n
  /-- One left-to-right template pass over the standard and CNOT templates
  (`TemplatePass.templatePassC`). -/
  | templatePass : NamedPass n
  /-- Commutation followed by merging (`commuteAndMerge`). -/
  | commuteMerging : NamedPass n
  /-- Commutation-aware cancellation and `RzQ` merging (`CommuteCancel.commuteCancel`). -/
  | commuteCancel : NamedPass n
  /-- `RzQ` at a Clifford+T angle rewritten to its gate (`RzQCanon.rzqCanonPass`). -/
  | rzqCanon : NamedPass n
  /-- T-gate merging (`tMerge`). -/
  | tMerging : NamedPass n
  /-- NOT propagation (`notPropagationPass`). -/
  | notPropagation : NamedPass n
  /-- NOT propagation where it does not lengthen the circuit (`notPropagationNoLonger`). -/
  | notPropNoLonger : NamedPass n
  /-- Rotation merging (`rotationMergingPass`). -/
  | rotationMerging : NamedPass n
  /-- Routing on the coupling graph `cg` (`insertSwaps`). -/
  | routing (cg : CouplingGraph n) : NamedPass n
  /-- Rule rewriting to a fixpoint (`rewriteFixpointOptimize`). -/
  | eGraph : NamedPass n

namespace NamedPass

/-- The circuit transformation of a named pass. -/
def run : NamedPass n → Circuit n → Circuit n
  | .templateMatching => optimizeLevel1
  | .templatePass => TemplatePass.level1Pass standardTemplates cnotTemplates
  | .commuteMerging => commuteAndMerge
  | .commuteCancel => CommuteCancel.commuteCancel
  | .rzqCanon => RzQCanon.rzqCanonPass
  | .tMerging => TCountOpt.tMerge
  | .notPropagation => notPropagationPass
  | .notPropNoLonger => notPropagationNoLonger
  | .rotationMerging => rotationMergingPass
  | .routing cg => fun c => insertSwaps c cg
  | .eGraph => rewriteFixpointOptimize

/-- Every named pass preserves `unitaryDenote`. -/
theorem run_unitaryCorrect : ∀ p : NamedPass n, UnitaryCorrectQ p.run
  | .templateMatching => optimizeLevel1_unitaryCorrect
  | .templatePass => fun c => by
    rw [run, TemplatePass.level1Pass_eq]
    exact (TemplatePass.unitaryDenote_templatePassC _
      (TemplatePass.level1Family_correctU standardTemplates_correctU
        (fun _ _ h => cnotTemplates_correctU h)) c).symm
  | .commuteMerging => fun c => (unitaryDenote_commuteAndMerge c).symm
  | .commuteCancel => fun c => (CommuteCancel.unitaryDenote_commuteCancel c).symm
  | .rzqCanon => RzQCanon.rzqCanonPass_unitaryCorrect
  | .tMerging => fun c => (unitaryDenote_tMerge c).symm
  | .notPropagation => fun c => (notPropagationPass_unitaryDenote c).symm
  | .notPropNoLonger => fun c => (notPropagationNoLonger_unitaryDenote c).symm
  | .rotationMerging => fun c => (rotationMergingPass_unitaryDenote c).symm
  | .routing cg => fun c => (insertSwaps_unitaryDenote c cg).symm
  | .eGraph => rewriteFixpointOptimize_unitaryCorrect

end NamedPass

/-- Run a list of named passes left to right. -/
def runNamed (ps : List (NamedPass n)) : Circuit n → Circuit n :=
  runPasses (ps.map NamedPass.run)

/-- Every list of named passes, in any order and with any coupling graphs in its
routing passes, preserves `unitaryDenote`. -/
theorem runNamed_unitaryCorrect (ps : List (NamedPass n)) :
    UnitaryCorrectQ (runNamed ps) :=
  runPasses_unitaryCorrect _ fun _ hp => by
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
    exact q.run_unitaryCorrect

/-- `unitaryDenote` form of `runNamed_unitaryCorrect`. -/
theorem runNamed_unitaryDenote (ps : List (NamedPass n)) (c : Circuit n) :
    unitaryDenote (runNamed ps c) = unitaryDenote c :=
  (runNamed_unitaryCorrect ps c).symm

/-! ## Routing on an arbitrary coupling graph -/

/-- The logical passes of Level 3. -/
def logicalPasses : List (NamedPass n) :=
  [.templatePass, .commuteMerging, .commuteCancel, .rzqCanon, .tMerging, .notPropagation,
    .rotationMerging]

/-- The logical passes followed by routing on the coupling graph `cg`. -/
def routedPipeline (cg : CouplingGraph n) : List (NamedPass n) :=
  logicalPasses ++ [.routing cg]

/-- For every coupling graph `cg`, the logical passes followed by routing on `cg`
preserve `unitaryDenote`. -/
theorem routedPipeline_unitaryDenote (cg : CouplingGraph n) (c : Circuit n) :
    unitaryDenote (runNamed (routedPipeline cg) c) = unitaryDenote c :=
  runNamed_unitaryDenote _ c

/-! ## The optimization levels as pass lists -/

/-- The pass list of each optimization level. Level 3 routes on
`CouplingGraph.linear n`. -/
def levelPasses : OptLevel → List (NamedPass n)
  | .Level1 => [.templatePass]
  | .Level2 =>
    [.templatePass, .commuteMerging, .commuteCancel, .rzqCanon, .tMerging, .notPropNoLonger]
  | .Level3 => routedPipeline (CouplingGraph.linear n)
  | .Level4 => [.eGraph]

theorem runNamed_level4 (c : Circuit n) :
    runNamed [.eGraph] c = rewriteFixpointOptimize c := by
  simp only [runNamed, List.map_cons, List.map_nil, runPasses_cons, runPasses_nil,
    NamedPass.run]

end CatCrypt.Quantum.Optimization.PassPipeline

namespace CatCrypt.Quantum.Optimization.FullOptimizer

open CatCrypt.Quantum.Optimization.PassPipeline

variable {n : ℕ}

/-! ## The optimizer at a level -/

/-- The main optimizer entry point: the run of the pass list of `level`. For
    Level 3 the coupling graph is `CouplingGraph.linear n`; `routedPipeline cg`
    routes on another topology. -/
def fullOptimize (level : OptLevel) (c : Circuit n) : Circuit n :=
  runNamed (levelPasses level) c

/-- The unfolding lemma of `fullOptimize`: `fullOptimize level` is the run of the
    pass list `levelPasses level`. -/
theorem fullOptimize_eq_runNamed (level : OptLevel) (c : Circuit n) :
    fullOptimize level c = runNamed (levelPasses level) c := rfl

/-- Gate count does not increase at Level 4 (rule rewriting to a fixpoint).
    Level 3 may increase it by SWAP insertion for routing. -/
theorem fullOptimize_gateCount_le (c : Circuit n) {level : OptLevel}
    (hlevel : level = OptLevel.Level4) :
    (fullOptimize level c).gateCount ≤ c.gateCount := by
  subst hlevel
  rw [fullOptimize_eq_runNamed, levelPasses, runNamed_level4]
  exact rewriteFixpointOptimize_gateCount_le c

/-! ## Metrics -/

/-- The optimization ratio: gate count of optimized circuit divided by
    gate count of the original. A ratio < 1 indicates gate reduction. -/
noncomputable def optimizationRatio (c : Circuit n) (level : OptLevel) : ℝ :=
  if c.gateCount = 0 then 1
  else (fullOptimize level c).gateCount / c.gateCount

/-- T-count reduction ratio for a given optimization level. -/
noncomputable def tCountRatio (c : Circuit n) (level : OptLevel) : ℝ :=
  if tCount c = 0 then 1
  else tCount (fullOptimize level c) / tCount c

/-! ## The `T†;T†` template fires

`T†;T†` merges into the one rotation `RzQ q (-1/2)`. -/

#guard (fullOptimize .Level1 (Circuit.ofList
  [Gate.Tdg (0 : Fin 1), Gate.Tdg (0 : Fin 1)])).gateCount = 1

#guard (Circuit.ofList [Gate.Tdg (0 : Fin 1), Gate.Tdg (0 : Fin 1)]).gateCount = 2

end CatCrypt.Quantum.Optimization.FullOptimizer
