/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.UnitarySoundCapstone
public import CatCrypt.Quantum.QPLToCircuit
public import CatCryptCore.Refinement.WRPLevelsQuantum

/-!
# Circuit passes as refinement squares of channels

A circuit on `n` qubits is a horizontal arrow of the level of channels of dimension `2 ^ n`,
`WRPLevelsQuantum.channelLevel`, through its unitary channel `unitaryDenote` (`circuitH`). A
circuit `c` refines a circuit `a` when the square of that level with top `a`, bottom `c` and
identity vertical arrows holds. Such a square holds exactly when the two channels are equal
(`circuitRefines_iff`, `circuitRefines_both_iff`), and squares along identity arrows paste
vertically (`CircuitRefines.trans`).

A pass refines when each circuit and its image give squares in both directions. This is
equivalent to `UnitaryCorrectQ` (`passRefines_iff`). It is a property of soundness only: the
identity pass has it (`passRefines_id`), and it states nothing about the cost of the image.
The pipeline of a list of passes refines by vertical pasting along the list.

The compilation of a unitary tree to a circuit, `UnitaryTree.toCircuit`, gives a square of the
same level between the compiled computation and the circuit's channel (`toCircuit_sq`,
`toCircuit_sq_symm`).

## Main definitions

* `circuitH c`: the horizontal arrow of the channel level of the circuit `c`.
* `CircuitRefines c a`: the square with top `circuitH a`, bottom `circuitH c` and identity
  vertical arrows.
* `PassRefines pass`: each circuit and its image under `pass` refine each other.

## Main results

* `circuitRefines_iff`, `circuitRefines_both_iff`: a square is equality of channels.
* `CircuitRefines.trans`, `PassRefines.comp`, `runPasses_passRefines`: composition of passes by
  vertical pasting of squares.
* `passRefines_iff`: a pass refines exactly when it satisfies `UnitaryCorrectQ`.
* `fullOptimize_passRefines`: every level of the optimizer refines in both directions.
* `runNamed_passRefines`: every list of named passes refines in both directions.
* `toCircuit_sq`, `toCircuit_sq_symm`: the circuit of a unitary tree and its compiled
  computation form squares in both directions.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.FullOptimizer CatCrypt.Quantum.Optimization.PassPipeline
open CatCrypt.Quantum.QPLToCircuit
open CatCrypt.Refinement CatCrypt.Refinement.WRPLevelsQuantum

noncomputable section

namespace CatCrypt.Quantum.Optimization.PassRefinesWP

variable {n : ℕ}

/-- The horizontal arrow of the level of channels of dimension `2 ^ n` of a circuit: its
unitary channel. -/
abbrev circuitH (c : Circuit n) :
    WRPLevels.HHom (channelFamily (2 ^ n)) (chanObj (2 ^ n)) (chanObj (2 ^ n)) :=
  .mk (unitaryDenote c)

/-- `c` refines `a`: the square of the channel level with top `circuitH a`, bottom
`circuitH c` and identity vertical arrows. -/
abbrev CircuitRefines (c a : Circuit n) : Prop :=
  WRPLevels.Sq (channelFamily (2 ^ n)) (circuitH a) (𝟙 (chanObj (2 ^ n))) (𝟙 (chanObj (2 ^ n)))
    (circuitH c)

/-- A square between two circuits along identity arrows, in one direction, is equality of
channels. -/
theorem circuitRefines_iff {c a : Circuit n} :
    CircuitRefines c a ↔ unitaryEquiv a c :=
  sq_id_iff (unitaryDenote a) (unitaryDenote c)

/-- Squares between two circuits along identity arrows in both directions are equality of
channels. -/
theorem circuitRefines_both_iff {c a : Circuit n} :
    CircuitRefines c a ∧ CircuitRefines a c ↔ unitaryEquiv a c := by
  grind [circuitRefines_iff, unitaryEquiv]

/-- Squares along identity arrows compose, by vertical pasting. -/
theorem CircuitRefines.trans {c b a : Circuit n} (h₂ : CircuitRefines c b)
    (h₁ : CircuitRefines b a) : CircuitRefines c a := by
  have h := WRPLevels.Sq.vcomp h₁ h₂
  rwa [show WRPTransformers.VHom.comp (𝟙 (chanObj (2 ^ n))) (𝟙 (chanObj (2 ^ n))) =
    𝟙 (chanObj (2 ^ n)) from Category.id_comp (obj := WRPTransformers.Obj) _] at h

/-! ## Passes -/

/-- Each circuit and its image under `pass` refine each other: the squares of the channel
level along identity arrows in both directions. This is soundness only: the identity pass
satisfies it. -/
def PassRefines (pass : Circuit n → Circuit n) : Prop :=
  ∀ c, CircuitRefines (pass c) c ∧ CircuitRefines c (pass c)

/-- A pass refines in both directions exactly when it preserves the channel of every circuit. -/
theorem passRefines_iff {pass : Circuit n → Circuit n} :
    PassRefines pass ↔ UnitaryCorrectQ pass :=
  forall_congr' fun _ => circuitRefines_both_iff

/-- The identity pass refines, by the vertical identity square. -/
theorem passRefines_id : PassRefines (id : Circuit n → Circuit n) :=
  fun c => ⟨WRPLevels.Sq.vid (circuitH c), WRPLevels.Sq.vid (circuitH c)⟩

/-- Passes that refine compose, by vertical pasting of their squares. -/
theorem PassRefines.comp {p₂ p₁ : Circuit n → Circuit n} (h₂ : PassRefines p₂)
    (h₁ : PassRefines p₁) : PassRefines (p₂ ∘ p₁) :=
  fun c => ⟨(h₂ (p₁ c)).1.trans (h₁ c).1, (h₁ c).2.trans (h₂ (p₁ c)).2⟩

/-- A list of passes that refine is a pipeline that refines, by vertical pasting along the
list. -/
theorem runPasses_passRefines (ps : List (Circuit n → Circuit n))
    (h : ∀ p ∈ ps, PassRefines p) : PassRefines (runPasses ps) := by
  induction ps with
  | nil => exact passRefines_id
  | cons p ps ih =>
    exact (ih fun q hq => h q (List.mem_cons_of_mem p hq)).comp (h p List.mem_cons_self)

/-! ## The optimizer -/

/-- At every level of the optimizer, each circuit and its optimized circuit refine each other. -/
theorem fullOptimize_passRefines (level : OptLevel) :
    PassRefines (fullOptimize level : Circuit n → Circuit n) :=
  passRefines_iff.mpr (UnitarySoundCapstone.fullOptimize_unitaryCorrect level)

/-- For every list of named passes, each circuit and its image refine each other. -/
theorem runNamed_passRefines (ps : List (NamedPass n)) : PassRefines (runNamed ps) :=
  passRefines_iff.mpr (runNamed_unitaryCorrect ps)

/-! ## Compilation of unitary trees -/

/-- The circuit of a unitary tree refines its compiled computation: the square of the channel
level with top `t.compile`, bottom `circuitH t.toCircuit` and identity vertical arrows. -/
theorem toCircuit_sq (t : UnitaryTree n) :
    WRPLevels.Sq (channelFamily (2 ^ n)) (.mk t.compile) (𝟙 (chanObj (2 ^ n)))
      (𝟙 (chanObj (2 ^ n))) (circuitH t.toCircuit) :=
  (sq_id_iff _ _).2 (UnitaryTree.toCircuit_correct t).symm

/-- The compiled computation of a unitary tree refines its circuit: the square of the channel
level with top `circuitH t.toCircuit`, bottom `t.compile` and identity vertical arrows. -/
theorem toCircuit_sq_symm (t : UnitaryTree n) :
    WRPLevels.Sq (channelFamily (2 ^ n)) (circuitH t.toCircuit) (𝟙 (chanObj (2 ^ n)))
      (𝟙 (chanObj (2 ^ n))) (.mk t.compile) :=
  (sq_id_iff _ _).2 (UnitaryTree.toCircuit_correct t)

end CatCrypt.Quantum.Optimization.PassRefinesWP
