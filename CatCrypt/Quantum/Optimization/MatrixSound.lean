/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.PassPipeline

/-!
# The passes of Levels 1 and 2 preserve the circuit unitary

`RoutingPerm.circuitUnitary c` is the unitary a circuit realizes, and `unitaryDenote c`
is the channel `ρ ↦ U ρ Uᴴ` of that unitary (`RoutingPerm.unitaryDenote_eq_channel`).
Equality of channels determines the unitary up to a global phase only. Each pass of
`levelPasses .Level1` and `levelPasses .Level2` preserves the unitary itself, so both
levels preserve the global phase of every circuit.

Each rewrite is proved once, at the unitary, in its pass module, and the channel
statements `PassPipeline.NamedPass.run_unitaryCorrect` uses are its corollaries
(`MatrixCorrect`, `MatrixCorrect.unitaryCorrectQ` in `MatrixCorrect`):
`CommuteMergeSound.commuteAndMerge_matrixCorrect`,
`CommuteCancel.commuteCancel_matrixCorrect`, `RzQCanon.rzqCanonPass_matrixCorrect`,
`TMergeSound.tMerge_matrixCorrect`, `NotPropSound.notPropagationPass_matrixCorrect`, and
`UnitarySoundFull.standardTemplates_correctM` with the pass lemma
`TemplatePass.templatePassAuxC_preserves`, which serves both semantics.

## Main results

* `circuitUnitary_templatePassC` — the template pass, for templates whose pattern
  and replacement realize one unitary
* `templatePass_matrixCorrect`, `notPropagationNoLonger_matrixCorrect` — the named
  passes that `PassPipeline` defines
* `runNamed_matrixCorrect` — a list of matrix-correct named passes is matrix-correct
* `runNamed_level1_matrixCorrect`, `runNamed_level2_matrixCorrect` — Levels 1 and 2
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.FullOptimizer
open CatCrypt.Quantum.Optimization.RoutingPerm (circuitUnitary)
open CatCrypt.Quantum.Optimization.PhasePolySemantics (circuitUnitary_ofList_append)
open CatCrypt.Quantum.Optimization.MatrixSound
open CatCrypt.Quantum.Optimization.PassPipeline
open CatCrypt.Quantum.Optimization.UnitarySoundFull (CorrectM standardTemplates_correctM
  cnotTemplates_correctM)
open CatCrypt.Quantum.Optimization.CommuteMergeSound (commuteAndMerge_matrixCorrect)
open CatCrypt.Quantum.Optimization.CommuteCancel (commuteCancel_matrixCorrect)
open CatCrypt.Quantum.Optimization.RzQCanon (rzqCanonPass_matrixCorrect)
open CatCrypt.Quantum.Optimization.TMergeSound (tMerge_matrixCorrect)
open CatCrypt.Quantum.Optimization.NotPropSound (notPropagationPass_matrixCorrect)

namespace CatCrypt.Quantum.Optimization.MatrixSound

variable {n : ℕ}

/-! ## Gate lists -/

/-- `QCircuit.circuitToList` preserves `circuitUnitary`. -/
theorem circuitUnitary_ofList_circuitToList_template (c : Circuit n) :
    circuitUnitary (Circuit.ofList (QCircuit.circuitToList c)) = circuitUnitary c :=
  circuitUnitary_ofList_flatten _ rfl (fun _ _ => rfl) (fun _ _ => rfl) c

/-! ## The template pass -/

section TemplatePass

open CatCrypt.Quantum.Optimization.TemplateMatching
open CatCrypt.Quantum.Optimization.TemplatePass

/-- A compiled template is matrix-sound when its pattern and its replacement realize
one unitary. -/
def CTemplateSoundM (c : CTemplate n) : Prop :=
  circuitUnitary (Circuit.ofList c.revPat.reverse) = circuitUnitary (Circuit.ofList c.rep)

/-- The compiled templates of a family of matrix-correct templates are matrix-sound. -/
theorem sound_compileFamilyM {ts : Gate n → List (Template n)}
    (hts : ∀ g, ∀ t ∈ ts g, CorrectM t) :
    ∀ g, ∀ c ∈ compileFamily ts g, CTemplateSoundM c :=
  compileFamily_preserves (fun l => circuitUnitary (Circuit.ofList l)) (P := CorrectM)
    (fun t ht => by
      rw [circuitUnitary_ofList_circuitToList_template,
        circuitUnitary_ofList_circuitToList_template]
      exact ht) hts

/-- Each step of the compiled pass preserves the unitary of the stack (in circuit
order) followed by the remaining input. -/
theorem circuitUnitary_templatePassAuxC (cs : Gate n → List (CTemplate n))
    (hcs : ∀ g, ∀ c ∈ cs g, CTemplateSoundM c) (stk todo : List (Gate n)) :
    circuitUnitary (Circuit.ofList (templatePassAuxC cs stk todo)) =
      circuitUnitary (Circuit.ofList (stk.reverse ++ todo)) :=
  templatePassAuxC_preserves (fun l => circuitUnitary (Circuit.ofList l))
    (fun _ _ _ _ h => by simp only [circuitUnitary_ofList_append, h]) cs hcs stk todo

/-- The template pass preserves `circuitUnitary` when every template of the family is
matrix-correct. -/
theorem circuitUnitary_templatePassC (ts : Gate n → List (Template n))
    (hts : ∀ g, ∀ t ∈ ts g, CorrectM t) : MatrixCorrect (templatePassC ts) := by
  intro c
  rw [templatePassC, compiledPassC, compiledPass,
    circuitUnitary_templatePassAuxC _ (sound_compileFamilyM hts)]
  simpa using circuitUnitary_ofList_circuitToList_template c

/-- Every template of `level1Family` is matrix-correct when those of `single` are and
those of `two` are on distinct qubits. -/
theorem level1Family_correctM {single : Fin n → List (Template n)}
    {two : Fin n → Fin n → List (Template n)}
    (hs : ∀ q, ∀ t ∈ single q, CorrectM t)
    (ht : ∀ c t, c ≠ t → ∀ u ∈ two c t, CorrectM u) :
    ∀ g, ∀ t ∈ level1Family single two g, CorrectM t :=
  level1Family_forall hs ht

end TemplatePass

/-- The `templatePass` named pass preserves `circuitUnitary`. -/
theorem templatePass_matrixCorrect :
    MatrixCorrect (NamedPass.templatePass.run : Circuit n → Circuit n) := by
  rw [NamedPass.run, TemplatePass.level1Pass_eq]
  exact circuitUnitary_templatePassC _
    (level1Family_correctM standardTemplates_correctM (fun _ _ h => cnotTemplates_correctM h))

/-! ## NOT propagation where it does not lengthen the circuit -/

/-- `notPropagationNoLonger` preserves `circuitUnitary`. -/
theorem notPropagationNoLonger_matrixCorrect :
    MatrixCorrect (notPropagationNoLonger : Circuit n → Circuit n) := by
  intro c
  unfold notPropagationNoLonger
  split
  · exact notPropagationPass_matrixCorrect c
  · rfl

/-! ## Pipelines -/

/-- A pipeline of matrix-correct passes is matrix-correct. -/
theorem runPasses_matrixCorrect (ps : List (Circuit n → Circuit n))
    (h : ∀ p ∈ ps, MatrixCorrect p) : MatrixCorrect (runPasses ps) := by
  induction ps with
  | nil => exact fun _ => rfl
  | cons p ps ih =>
    intro c
    rw [runPasses_cons, ih (fun q hq => h q (List.mem_cons_of_mem p hq)),
      h p List.mem_cons_self]

/-- A list of matrix-correct named passes is matrix-correct. -/
theorem runNamed_matrixCorrect (ps : List (NamedPass n))
    (h : ∀ p ∈ ps, MatrixCorrect p.run) : MatrixCorrect (runNamed ps) :=
  runPasses_matrixCorrect _ fun _ hp => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact h q hq

/-- **Level 1 preserves the circuit unitary**, global phase included. -/
theorem runNamed_level1_matrixCorrect :
    MatrixCorrect (runNamed (levelPasses (n := n) .Level1)) :=
  runNamed_matrixCorrect _ fun p hp => by
    simp only [levelPasses, List.mem_singleton] at hp
    subst hp
    exact templatePass_matrixCorrect

/-- **Level 2 preserves the circuit unitary**, global phase included. -/
theorem runNamed_level2_matrixCorrect :
    MatrixCorrect (runNamed (levelPasses (n := n) .Level2)) :=
  runNamed_matrixCorrect _ fun p hp => by
    simp only [levelPasses, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact templatePass_matrixCorrect
    · exact commuteAndMerge_matrixCorrect
    · exact commuteCancel_matrixCorrect
    · exact rzqCanonPass_matrixCorrect
    · exact tMerge_matrixCorrect
    · exact notPropagationNoLonger_matrixCorrect

/-- `fullOptimize .Level1` preserves `circuitUnitary`. -/
theorem fullOptimize_level1_circuitUnitary (c : Circuit n) :
    circuitUnitary (fullOptimize .Level1 c) = circuitUnitary c := by
  rw [fullOptimize_eq_runNamed]
  exact runNamed_level1_matrixCorrect c

/-- `fullOptimize .Level2` preserves `circuitUnitary`. -/
theorem fullOptimize_level2_circuitUnitary (c : Circuit n) :
    circuitUnitary (fullOptimize .Level2 c) = circuitUnitary c := by
  rw [fullOptimize_eq_runNamed]
  exact runNamed_level2_matrixCorrect c

end CatCrypt.Quantum.Optimization.MatrixSound
