/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.Optimization.CommutationRules

/-!
# Rotation Merging Optimization

VOQC's key optimization: merge non-adjacent Rz gates separated by commuting
gates.  The idea is that `Rz(α); G₁; G₂; ... ; Gₖ; Rz(β)` equals
`G₁; G₂; ... ; Gₖ; Rz(α + β)` whenever each `Gᵢ` commutes with `Rz(α)`.
Since T, S, and Z are special cases of Rz (at angles π/4, π/2, π
respectively), we first normalize these into Rz form, merge, then convert
back where possible.

## Main definitions

* `isRzGate`                  -- the qubit and real angle of an Rz/T/S/Z gate
* `RzAngle`, `rzAngle?`       -- the qubit and angle (real, or rational times π)
* `normalizeToRz`             -- convert T → RzQ(1/4), S → RzQ(1/2), Z → RzQ(1)
* `findMergePartner`          -- find the next Rz on same qubit reachable by commuting
* `mergeRotations`            -- single pass: find Rz pairs and merge
* `rotationMergingPass`       -- convert to gate list, merge, convert back
* `rotationMergingPass_gateCount_le` -- does not increase gate count (proved)

Semantic preservation is stated over `unitaryDenote` in the companion module
`RotMergeSound` (`rotationMergingPass_unitaryCorrect`).

## References

* Hietala et al. -- A Verified Optimizer for Quantum Circuits (POPL 2021)
* Nam et al. -- Automated optimization of large quantum circuits with
  continuous parameters, npj Quantum Information 2018
-/

@[expose] public section

set_option autoImplicit true

namespace CatCrypt.Quantum.Optimization.RotationMerging

open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.Optimization.CommutationRules

/-! ## Rz Gate Recognition -/

/-- Extract qubit and rotation angle from an Rz-family gate.
    T = Rz(π/4), S = Rz(π/2), Z = Rz(π), Tdg = Rz(-π/4). The angle is a real
    number, so the function is a specification; the pass reads angles with
    `rzAngle?`. -/
noncomputable def isRzGate : Gate n → Option (Fin n × ℝ)
  | .Rz i θ => some (i, θ)
  | .RzQ i a => some (i, PiLin.toReal a)
  | .T i    => some (i, Real.pi / 4)
  | .Tdg i  => some (i, -(Real.pi / 4))
  | .S i    => some (i, Real.pi / 2)
  | .Z i    => some (i, Real.pi)
  | _       => none

/-- Check whether a gate belongs to the Rz family (T, Tdg, S, Z, or Rz). -/
def isRzFamily : Gate n → Bool
  | .Rz _ _ => true
  | .RzQ _ _ => true
  | .T _    => true
  | .Tdg _  => true
  | .S _    => true
  | .Z _    => true
  | _       => false

/-! ## Rotation angles -/

/-- The angle of an `Rz`-family gate: a real angle (`Rz`) or an exact angle
    `a + b·π` (`RzQ`, and `T`, `Tdg`, `S`, `Z`). -/
inductive RzAngle : Type where
  /-- The real angle of an `Rz` gate. -/
  | real (θ : ℝ) : RzAngle
  /-- The exact angle `a + b·π` of an `RzQ` gate. -/
  | pi (a : PiLin) : RzAngle

namespace RzAngle

/-- The sum of two angles of the same kind; `none` for a real angle and an
    exact angle. -/
def add? : RzAngle → RzAngle → Option RzAngle
  | .real θ, .real φ => some (.real (θ + φ))
  | .pi a, .pi b => some (.pi (a + b))
  | _, _ => none

/-- The rotation by an angle on qubit `q`. -/
def gate (q : Fin n) : RzAngle → Gate n
  | .real θ => .Rz q θ
  | .pi a => .RzQ q a

/-- The angle as a real number. -/
noncomputable def toReal : RzAngle → ℝ
  | .real θ => θ
  | .pi a => PiLin.toReal a

end RzAngle

/-- The qubit and angle of an `Rz`-family gate: `T = RzQ(1/4)`, `Tdg = RzQ(-1/4)`,
    `S = RzQ(1/2)`, `Z = RzQ(1)`. -/
def rzAngle? : Gate n → Option (Fin n × RzAngle)
  | .Rz i θ => some (i, .real θ)
  | .RzQ i a => some (i, .pi a)
  | .T i    => some (i, .pi (1 / 4))
  | .Tdg i  => some (i, .pi (-(1 / 4)))
  | .S i    => some (i, .pi (1 / 2))
  | .Z i    => some (i, .pi 1)
  | _       => none

/-! ## Normalization -/

/-- Normalize T/Tdg/S/Z gates into `RzQ` form; other gates pass through. -/
def normalizeToRz : Gate n → Gate n
  | .T i   => .RzQ i (1 / 4)
  | .Tdg i => .RzQ i (-(1 / 4))
  | .S i   => .RzQ i (1 / 2)
  | .Z i   => .RzQ i 1
  | g      => g

/-- Normalize all gates in a list to explicit Rz form. -/
def normalizeList (gs : List (Gate n)) : List (Gate n) :=
  gs.map normalizeToRz

/-! ## Merge Partner Search -/

/-- Find the index of the next Rz gate on qubit `q` that can be reached
    by commuting through all intermediate gates.
    Returns `none` if no such partner exists within the remaining list.
    The index is relative to the start of `rest`. -/
def findMergePartner (rest : List (Gate n)) (q : Fin n) (idx : ℕ := 0) :
    Option ℕ :=
  match rest with
  | [] => none
  | g :: gs =>
    match rzAngle? g with
    | some (q', _) =>
      if decide (q = q') then some idx
      else if gateCommutes (.Rz q 0) g then findMergePartner gs q (idx + 1)
      else none
    | none =>
      if gateCommutes (.Rz q 0) g then findMergePartner gs q (idx + 1)
      else none

/-! ## Single-Pass Merging -/

/-- Remove the element at position `k` from a list (identity if out of bounds). -/
def List.removeAt' : List α → ℕ → List α
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, k + 1 => x :: List.removeAt' xs k

/-- Read the element at position `k` from a list. -/
def List.getAt? : List α → ℕ → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, k + 1 => List.getAt? xs k

/-- Merge rotations in a single left-to-right pass.
    For each Rz-family gate, search forward for a merge partner on the
    same qubit reachable through commuting gates.  If found and the two angles
    are of the same kind (`RzAngle.add?`), combine the angles and remove the
    partner from the list.  Uses a fuel parameter for termination. -/
def mergeRotations (gs : List (Gate n)) (fuel : ℕ := gs.length + 1) :
    List (Gate n) :=
  match fuel with
  | 0 => gs
  | fuel' + 1 =>
    match gs with
    | [] => []
    | g :: rest =>
      match rzAngle? g with
      | some (q, θ₁) =>
        match findMergePartner rest q with
        | some k =>
          match List.getAt? rest k with
          | some partner =>
            match rzAngle? partner with
            | some (_, θ₂) =>
              match θ₁.add? θ₂ with
              | some θ =>
                -- Merge: replace current gate with combined rotation,
                -- remove the partner from the rest
                θ.gate q :: mergeRotations (List.removeAt' rest k) fuel'
              | none => g :: mergeRotations rest fuel'
            | none => g :: mergeRotations rest fuel'
          | none => g :: mergeRotations rest fuel'
        | none => g :: mergeRotations rest fuel'
      | none => g :: mergeRotations rest fuel'

/-! ## Full Pass -/

/-- The rotation merging pass: flatten the circuit to a gate list,
    normalize Rz-family gates, merge compatible rotations, and rebuild. -/
def rotationMergingPass (c : Circuit n) : Circuit n :=
  let gs := circuitToList c
  let normalized := normalizeList gs
  Circuit.ofList (mergeRotations normalized)

/-! ## Correctness -/

private theorem normalizeList_length (gs : List (Gate n)) :
    (normalizeList gs).length = gs.length := by
  simp [normalizeList]

private theorem removeAt'_length_le : ∀ (l : List α) (k : Nat),
    (List.removeAt' l k).length ≤ l.length
  | [], _ => le_refl _
  | _ :: _, 0 => Nat.le_succ _
  | _ :: xs, k + 1 => by
    simp only [List.removeAt', List.length_cons]
    exact Nat.succ_le_succ (removeAt'_length_le xs k)

private theorem mergeRotations_length_le :
    ∀ (gs : List (Gate n)) (fuel : Nat), (mergeRotations gs fuel).length ≤ gs.length := by
  intro gs fuel
  induction fuel generalizing gs with
  | zero => simp [mergeRotations]
  | succ fuel' ih =>
    simp only [mergeRotations]
    split -- [] vs g :: rest
    · exact le_refl _
    · -- g :: rest case
      repeat split
      all_goals (simp only [List.length_cons]; first
        | exact Nat.succ_le_succ (le_trans (ih _) (removeAt'_length_le _ _))
        | exact Nat.succ_le_succ (ih _))

private theorem circuitToList_length (c : Circuit n) :
    (circuitToList c).length = c.gateCount := by
  induction c with
  | empty => simp [circuitToList]
  | gate g c ih => simp [circuitToList, ih, Nat.add_comm]
  | seq c₁ c₂ ih₁ ih₂ => simp [circuitToList, ih₁, ih₂]

/-- The rotation merging pass does not increase gate count.
    Each merge strictly reduces the number of gates by one. -/
theorem rotationMergingPass_gateCount_le (c : Circuit n) :
    (rotationMergingPass c).gateCount ≤ c.gateCount := by
  simp only [rotationMergingPass, gateCount_ofList]
  calc (mergeRotations (normalizeList (circuitToList c))).length
      ≤ (normalizeList (circuitToList c)).length := mergeRotations_length_le _ _
    _ = (circuitToList c).length := normalizeList_length _
    _ = c.gateCount := circuitToList_length c

/-! ## Example -/

/-- Example: `Rz(π/4)` on qubit 0, `H` on qubit 1, `Rz(π/4)` on qubit 0.
    The H on qubit 1 commutes with Rz on qubit 0 (disjoint qubits), so the
    two rotations merge to `Rz(π/2)`. -/
noncomputable def exampleBeforeMerge : Circuit 2 :=
  .gate (.Rz 0 (Real.pi / 4))
    (.gate (.H 1)
      (.gate (.Rz 0 (Real.pi / 4)) .empty))

/-- After merging: `Rz(π/2)` on qubit 0, `H` on qubit 1. -/
noncomputable def exampleAfterMerge : Circuit 2 :=
  .gate (.Rz 0 (Real.pi / 2))
    (.gate (.H 1) .empty)

/-- The merged circuit has fewer gates. -/
theorem example_gateCount_reduced :
    exampleAfterMerge.gateCount < exampleBeforeMerge.gateCount := by
  simp [exampleAfterMerge, exampleBeforeMerge, Circuit.gateCount]

/-- Gate counts of the example circuits. -/
theorem exampleBeforeMerge_gateCount :
    exampleBeforeMerge.gateCount = 3 := by rfl

theorem exampleAfterMerge_gateCount :
    exampleAfterMerge.gateCount = 2 := by rfl

end CatCrypt.Quantum.Optimization.RotationMerging
