/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.AngleQ
public import CatCrypt.Quantum.Optimization.PhasePolyExtract

/-!
# Exact rotations at the Clifford+T angles

`Gate.RzQ q p` rotates qubit `q` by `p.a + p.b·π`. At `p.a = 0` the rotation
depends only on `p.b` modulo `2`, and five residues are gate constructors:
`0` is the identity, `1/4` is `T`, `7/4` is `T†`, `1/2` is `S` and `1` is `Z`.
`rzqCanon` rewrites an `RzQ` at one of them to that gate (to no gate at a whole
number of turns, `PiLin.isTrivial`) and leaves every other gate alone. Each rule
is an equality of the gate's matrix, since `rzGate t = diag(1, e^{it})` is
`2π`-periodic in `t`.

## Main definitions

* `residue2` — a rational modulo `2`, in `[0, 2)`.
* `rzqCanon` — the recogniser, one gate to a list of gates.
* `rzqCanonPass` — `rzqCanon` at every gate of a circuit.

## Main results

* `unitaryDenote_rzqCanon` — the gates `rzqCanon g` denote the channel of `g`.
* `unitaryDenote_rzqCanonPass` — the pass preserves `unitaryDenote`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.Optimization.RzQCanon

open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.Optimization.PhasePolyExtract
open CatCrypt.Quantum.Optimization.RoutingPerm (circuitUnitary)
open CatCrypt.Quantum.Optimization.PhasePolySemantics (circuitUnitary_ofList_single)
open CatCrypt.Quantum.Optimization.MatrixSound

variable {n : ℕ}

/-! ## The residue of an angle -/

/-- The residue of `b` modulo `2`, in `[0, 2)`. -/
def residue2 (b : ℚ) : ℚ := b - 2 * ⌊b / 2⌋

/-- An angle `b·π` is its residue times `π` plus a whole number of turns. -/
theorem toReal_eq_residue2 (p : PiLin) (ha : p.a = 0) :
    PiLin.toReal p = (residue2 p.b : ℝ) * Real.pi + (⌊p.b / 2⌋ : ℤ) * (2 * Real.pi) := by
  simp only [PiLin.toReal, ha, residue2]
  push_cast
  ring

/-- The `Rz` matrix of an angle with `a = 0` is the one of its residue. -/
theorem gateEmbedding_RzQ_residue2 (q : Fin n) (p : PiLin) (ha : p.a = 0) :
    gateEmbedding (Gate.RzQ q p) = embedGate1 n q (rzGate ((residue2 p.b : ℝ) * Real.pi)) := by
  change embedGate1 n q (rzGate (PiLin.toReal p)) = _
  rw [toReal_eq_residue2 p ha, rzGate_add_int_mul_two_pi]

/-! ## The recogniser -/

/-- The Clifford+T gates of an exact rotation: no gate at a whole number of turns,
    `T`, `T†`, `S` or `Z` at the residues `1/4`, `7/4`, `1/2` and `1` of `p.b`
    modulo `2` when `p.a = 0`, and the gate itself otherwise. -/
def rzqCanon : Gate n → List (Gate n)
  | .RzQ q p =>
    if p.isTrivial then []
    else if p.a = 0 ∧ residue2 p.b = 1 / 4 then [.T q]
    else if p.a = 0 ∧ residue2 p.b = 7 / 4 then [.Tdg q]
    else if p.a = 0 ∧ residue2 p.b = 1 / 2 then [.S q]
    else if p.a = 0 ∧ residue2 p.b = 1 then [.Z q]
    else [.RzQ q p]
  | g => [g]

/-- Two gates with one embedding denote one channel. -/
theorem unitaryDenote_single_of_gateEmbedding {g g' : Gate n}
    (h : gateEmbedding g = gateEmbedding g') :
    unitaryDenote (Circuit.single g) = unitaryDenote (Circuit.single g') := by
  have hu : gateEmbedding_unitaryGroup g = gateEmbedding_unitaryGroup g' := Subtype.ext h
  simp only [unitaryDenote_single, denoteGateU, hu]

/-- A gate whose embedding is the identity denotes the empty circuit's channel. -/
theorem unitaryDenote_single_of_gateEmbedding_one {g : Gate n}
    (h : gateEmbedding g = 1) :
    unitaryDenote (Circuit.single g) = unitaryDenote (Circuit.empty : Circuit n) := by
  have hu : gateEmbedding_unitaryGroup g = 1 := Subtype.ext h
  simp only [unitaryDenote_single, denoteGateU, hu, unitaryChannel_one_eq_qpure,
    unitaryDenote_empty]

/-- The gates `rzqCanon g` realize the unitary of `g`. -/
theorem circuitUnitary_ofList_rzqCanon (g : Gate n) :
    circuitUnitary (Circuit.ofList (rzqCanon g)) = gateEmbedding_unitaryGroup g := by
  cases g with
  | RzQ q p =>
    simp only [rzqCanon]
    split_ifs with h0 h1 h2 h3 h4
    · obtain ⟨k, hk⟩ := (PiLin.isTrivial_iff p).1 h0
      apply Subtype.ext
      change (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) =
        embedGate1 n q (rzGate (PiLin.toReal p))
      rw [hk, show 2 * Real.pi * k = 0 + k * (2 * Real.pi) by ring,
        rzGate_add_int_mul_two_pi, (rzGate_eq_one_iff 0).2 (by simp), embedGate1_one]
    · rw [circuitUnitary_ofList_single]
      apply Subtype.ext
      change gateEmbedding (Gate.T q) = gateEmbedding (Gate.RzQ q p)
      rw [gateEmbedding_RzQ_residue2 q p h1.1, h1.2]
      change embedGate1 n q tGate = _
      rw [tGate_eq_rzGate]
      congr 2
      push_cast
      ring
    · rw [circuitUnitary_ofList_single]
      apply Subtype.ext
      change gateEmbedding (Gate.Tdg q) = gateEmbedding (Gate.RzQ q p)
      rw [gateEmbedding_RzQ_residue2 q p h2.1, h2.2]
      change embedGate1 n q tDaggerGate = _
      rw [tDaggerGate_eq_rzGate, ← rzGate_add_int_mul_two_pi _ 1]
      congr 2
      push_cast
      ring
    · rw [circuitUnitary_ofList_single]
      apply Subtype.ext
      change gateEmbedding (Gate.S q) = gateEmbedding (Gate.RzQ q p)
      rw [gateEmbedding_RzQ_residue2 q p h3.1, h3.2]
      change embedGate1 n q phaseS = _
      rw [phaseS_eq_rzGate]
      congr 2
      push_cast
      ring
    · rw [circuitUnitary_ofList_single]
      apply Subtype.ext
      change gateEmbedding (Gate.Z q) = gateEmbedding (Gate.RzQ q p)
      rw [gateEmbedding_RzQ_residue2 q p h4.1, h4.2]
      change embedGate1 n q pauliZ = _
      rw [pauliZ_eq_rzGate]
      congr 2
      push_cast
      ring
    · exact circuitUnitary_ofList_single _
  | _ => exact circuitUnitary_ofList_single _

/-- **The gates `rzqCanon g` denote the channel of `g`.** -/
theorem unitaryDenote_rzqCanon (g : Gate n) :
    unitaryDenote (Circuit.ofList (rzqCanon g)) = unitaryDenote (Circuit.single g) :=
  unitaryDenote_eq_of_circuitUnitary_eq (by
    rw [circuitUnitary_ofList_rzqCanon, circuitUnitary_single])

/-! ## The pass -/

/-- `rzqCanon` at every gate of a circuit. -/
def rzqCanonPass : Circuit n → Circuit n
  | .empty => .empty
  | .gate g c => .seq (Circuit.ofList (rzqCanon g)) (rzqCanonPass c)
  | .seq c₁ c₂ => .seq (rzqCanonPass c₁) (rzqCanonPass c₂)

/-- `rzqCanonPass` preserves `circuitUnitary`. -/
theorem rzqCanonPass_matrixCorrect :
    MatrixCorrect (rzqCanonPass : Circuit n → Circuit n) := by
  intro c
  induction c with
  | empty => rfl
  | gate g c ih =>
    change circuitUnitary (rzqCanonPass c) *
      circuitUnitary (Circuit.ofList (rzqCanon g)) = _
    rw [ih, circuitUnitary_ofList_rzqCanon]
    rfl
  | seq c₁ c₂ ih₁ ih₂ =>
    change circuitUnitary (rzqCanonPass c₂) *
      circuitUnitary (rzqCanonPass c₁) = _
    rw [ih₁, ih₂]
    rfl

/-- **The pass preserves `unitaryDenote`.** -/
theorem unitaryDenote_rzqCanonPass (c : Circuit n) :
    unitaryDenote (rzqCanonPass c) = unitaryDenote c :=
  unitaryDenote_eq_of_circuitUnitary_eq (rzqCanonPass_matrixCorrect c)

/-- `rzqCanonPass` is a unitary-correct pass. -/
theorem rzqCanonPass_unitaryCorrect : UnitaryCorrectQ (rzqCanonPass : Circuit n → Circuit n) :=
  rzqCanonPass_matrixCorrect.unitaryCorrectQ

end CatCrypt.Quantum.Optimization.RzQCanon
