/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.RoutingPerm

/-!
# Matrix-correct passes and the unitary of a gate list

`RoutingPerm.circuitUnitary c` is the unitary a circuit realizes and `unitaryDenote c`
is the channel `ρ ↦ U ρ Uᴴ` of that unitary (`RoutingPerm.unitaryDenote_eq_channel`).
A pass that preserves the unitary therefore preserves the channel. The rewrites of
the optimizer are proved at the unitary, in their pass modules, and their channel
statements are the corollaries `unitaryDenote_eq_of_circuitUnitary_eq` and
`MatrixCorrect.unitaryCorrectQ`.

## Main results

* `MatrixCorrect` — a pass preserves `circuitUnitary`
* `MatrixCorrect.unitaryCorrectQ` — a matrix-correct pass preserves `unitaryDenote`
* `unitaryDenote_eq_of_circuitUnitary_eq` — one unitary, one channel
* `PhasePolySemantics.circuitUnitary_ofList_append` — the unitary of a gate list is
  multiplicative over `++`
* `circuitUnitary_ofList_flatten` — a flattening with the equations of
  `circuitToList` preserves `circuitUnitary`
* `circuitUnitary_ofList_circuitToList` — flattening with `circuitToList` and
  rebuilding preserves `circuitUnitary`
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.RoutingPerm (circuitUnitary)

namespace CatCrypt.Quantum.Optimization.PhasePolySemantics

variable {n : ℕ}

/-- Appending gate lists multiplies their unitaries, the second on the left. -/
theorem circuitUnitary_ofList_append (l₁ l₂ : List (Gate n)) :
    RoutingPerm.circuitUnitary (Circuit.ofList (l₁ ++ l₂))
      = RoutingPerm.circuitUnitary (Circuit.ofList l₂) *
          RoutingPerm.circuitUnitary (Circuit.ofList l₁) := by
  induction l₁ with
  | nil => simp [Circuit.ofList, RoutingPerm.circuitUnitary]
  | cons g gs ih =>
    simp only [List.cons_append, Circuit.ofList, RoutingPerm.circuitUnitary, ih, mul_assoc]

theorem circuitUnitary_ofList_single (g : Gate n) :
    RoutingPerm.circuitUnitary (Circuit.ofList [g]) = gateEmbedding_unitaryGroup g := by
  simp [Circuit.ofList, RoutingPerm.circuitUnitary]

end CatCrypt.Quantum.Optimization.PhasePolySemantics

open CatCrypt.Quantum.Optimization.PhasePolySemantics
  (circuitUnitary_ofList_append circuitUnitary_ofList_single)

namespace CatCrypt.Quantum.Optimization.MatrixSound

variable {n : ℕ}

/-! ## Matrix-correct passes -/

/-- Circuits realizing one unitary denote one channel. -/
theorem unitaryDenote_eq_of_circuitUnitary_eq {c c' : Circuit n}
    (h : circuitUnitary c = circuitUnitary c') : unitaryDenote c = unitaryDenote c' := by
  rw [RoutingPerm.unitaryDenote_eq_channel, RoutingPerm.unitaryDenote_eq_channel, h]

/-- A pass is matrix-correct when it preserves the unitary `circuitUnitary` of every
circuit. -/
def MatrixCorrect (pass : Circuit n → Circuit n) : Prop :=
  ∀ c, circuitUnitary (pass c) = circuitUnitary c

/-- A matrix-correct pass preserves `unitaryDenote`. -/
theorem MatrixCorrect.unitaryCorrectQ {pass : Circuit n → Circuit n}
    (h : MatrixCorrect pass) : UnitaryCorrectQ pass := fun c =>
  (unitaryDenote_eq_of_circuitUnitary_eq (h c)).symm

/-! ## Gate lists -/

/-- Unfolding lemma of `circuitUnitary` at the circuit of a cons. -/
theorem circuitUnitary_ofList_cons (g : Gate n) (l : List (Gate n)) :
    circuitUnitary (Circuit.ofList (g :: l)) =
      circuitUnitary (Circuit.ofList l) * gateEmbedding_unitaryGroup g := rfl

/-- Equal tails realize equal unitaries after a common head gate. -/
theorem circuitUnitary_ofList_cons_congr (g : Gate n) {l l' : List (Gate n)}
    (h : circuitUnitary (Circuit.ofList l) = circuitUnitary (Circuit.ofList l')) :
    circuitUnitary (Circuit.ofList (g :: l)) = circuitUnitary (Circuit.ofList (g :: l')) := by
  rw [circuitUnitary_ofList_cons, circuitUnitary_ofList_cons, h]

/-- Two leading gates whose embeddings commute can be swapped. -/
theorem circuitUnitary_ofList_swap {g₁ g₂ : Gate n}
    (h : gateEmbedding g₂ * gateEmbedding g₁ = gateEmbedding g₁ * gateEmbedding g₂)
    (l : List (Gate n)) :
    circuitUnitary (Circuit.ofList (g₁ :: g₂ :: l)) =
      circuitUnitary (Circuit.ofList (g₂ :: g₁ :: l)) := by
  simp only [circuitUnitary_ofList_cons, mul_assoc]
  congr 1
  exact Subtype.ext h

/-- A head gate `g₁` commuting with `g₂` moves behind `g₂` when the tail realizes the
unitary of `g₂ :: l'`. -/
theorem circuitUnitary_cons_swap_of {g₁ g₂ : Gate n} {l l' : List (Gate n)}
    (hl : circuitUnitary (Circuit.ofList l) = circuitUnitary (Circuit.ofList (g₂ :: l')))
    (h : gateEmbedding g₂ * gateEmbedding g₁ = gateEmbedding g₁ * gateEmbedding g₂) :
    circuitUnitary (Circuit.ofList (g₁ :: l)) =
      circuitUnitary (Circuit.ofList (g₂ :: g₁ :: l')) := by
  rw [circuitUnitary_ofList_cons, hl, ← circuitUnitary_ofList_cons, circuitUnitary_ofList_swap h]

/-- A flattening function with the equations of `circuitToList` preserves
`circuitUnitary`. -/
theorem circuitUnitary_ofList_flatten (f : Circuit n → List (Gate n))
    (h₀ : f .empty = []) (h₁ : ∀ g c, f (.gate g c) = g :: f c)
    (h₂ : ∀ c₁ c₂, f (.seq c₁ c₂) = f c₁ ++ f c₂) (c : Circuit n) :
    circuitUnitary (Circuit.ofList (f c)) = circuitUnitary c := by
  induction c with
  | empty => rw [h₀]; rfl
  | gate g c ih => rw [h₁, circuitUnitary_ofList_cons, ih]; rfl
  | seq c₁ c₂ ih₁ ih₂ => rw [h₂, circuitUnitary_ofList_append, ih₁, ih₂]; rfl

/-- Flattening a circuit with `circuitToList` and rebuilding preserves
`circuitUnitary`. -/
theorem circuitUnitary_ofList_circuitToList (c : Circuit n) :
    circuitUnitary (Circuit.ofList (circuitToList c)) = circuitUnitary c :=
  circuitUnitary_ofList_flatten _ rfl (fun _ _ => rfl) (fun _ _ => rfl) c

/-- The unitary of a one-gate circuit is the gate's embedding. -/
theorem circuitUnitary_single (g : Gate n) :
    circuitUnitary (Circuit.single g) = gateEmbedding_unitaryGroup g :=
  circuitUnitary_ofList_single g

end CatCrypt.Quantum.Optimization.MatrixSound
