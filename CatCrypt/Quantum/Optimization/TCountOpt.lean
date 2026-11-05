/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.AngleQ

/-!
# T-Gate Count Optimization

T-gate count is the dominant cost metric for fault-tolerant quantum computing.
While Clifford gates (H, S, CNOT, CZ, X, Y, Z) can be implemented
transversally with low overhead, each T gate requires expensive magic state
distillation. Reducing T-count is therefore critical for practical quantum
circuits.

## Main definitions

* `tCount`               -- count T and Tdg gates in a circuit
* `cliffordCount`        -- count non-T gates
* `eliminateTOnZero`     -- remove T gates immediately after initialization
* `tMerge`               -- merge T gate powers (T*T = S, T^4 = Z, T^8 = I)
* the phase-polynomial pass lives in `Optimization.RotationMergingV2`, proved
  correct over `unitaryDenote` by `phasePolynomialOpt_unitaryCorrect`

## References

* Amy, Maslov, Mosca -- Polynomial-time T-depth optimization of Clifford+T
  circuits via matroid partitioning, IEEE Trans. on CAD, 2014
* Heyfron, Campbell -- An efficient quantum compiler that reduces T count,
  Quantum Science and Technology, 2018
-/

@[expose] public section

set_option autoImplicit true

noncomputable section

namespace CatCrypt.Quantum.Optimization.TCountOpt

open CatCrypt.Quantum.QCircuit

/-! ## T-Count and Clifford Count -/

/-- Whether a gate is a T or Tdg gate. -/
def isT : Gate n → Bool
  | .T _   => true
  | .Tdg _ => true
  | _      => false

/-- Count the number of T and Tdg gates in a circuit.
    This is the primary cost metric for fault-tolerant quantum computing. -/
def tCount : Circuit n → ℕ
  | .empty     => 0
  | .gate g c  => (if isT g then 1 else 0) + tCount c
  | .seq c₁ c₂ => tCount c₁ + tCount c₂

/-- Count the number of non-T gates. -/
def cliffordCount : Circuit n → ℕ
  | .empty     => 0
  | .gate g c  => (if isT g then 0 else 1) + cliffordCount c
  | .seq c₁ c₂ => cliffordCount c₁ + cliffordCount c₂

/-- Total gate count equals T-count plus Clifford count. -/
theorem tCount_add_cliffordCount (c : Circuit n) :
    tCount c + cliffordCount c = c.gateCount := by
  induction c with
  | empty => simp [tCount, cliffordCount, Circuit.gateCount]
  | gate g c ih =>
    simp only [tCount, cliffordCount, Circuit.gateCount]
    split <;> omega
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [tCount, cliffordCount, Circuit.gateCount]
    omega

/-! ## T-on-Zero Elimination -/

/-- Remove T/Tdg gates at the beginning of a circuit (which act on freshly
    initialized |0> qubits). A more sophisticated version would track qubit
    state through the circuit. -/
def eliminateTOnZero : Circuit n → Circuit n
  | .empty => .empty
  | .gate g c =>
    if isT g then
      -- T at the start of a circuit acts on |0>, so it's identity
      eliminateTOnZero c
    else
      .gate g (eliminateTOnZero c)
  | .seq c₁ c₂ => .seq (eliminateTOnZero c₁) c₂

/-- T-on-zero elimination does not increase T-count. -/
theorem eliminateTOnZero_reduces_tcount (c : Circuit n) :
    tCount (eliminateTOnZero c) ≤ tCount c := by
  induction c with
  | empty => simp [eliminateTOnZero, tCount]
  | gate g c ih =>
    simp only [eliminateTOnZero]
    split
    · simp only [tCount]; omega
    · simp only [tCount]; omega
  | seq c₁ c₂ _ _ =>
    simp only [eliminateTOnZero, tCount]; omega

/-! ## T-Gate Merging -/

/-- Count consecutive T gates on a given qubit at the head of a gate list. -/
def countConsecutiveT (q : Fin n) : List (Gate n) → ℕ × List (Gate n)
  | [] => (0, [])
  | g :: gs =>
    match g with
    | .T i =>
      if decide (i = q) then
        let (count, rest) := countConsecutiveT q gs
        (count + 1, rest)
      else (0, g :: gs)
    | _ => (0, g :: gs)

/-- Convert a T-power count modulo 8 to the equivalent gate:
    T^0 = I, T^1 = T, T^2 = S, T^3 = T*S, T^4 = Z,
    T^5 = T*Z, T^6 = Sdg = S*Z, T^7 = Tdg. -/
def tPowerToGates (q : Fin n) (k : ℕ) : List (Gate n) :=
  match k % 8 with
  | 0 => []                              -- T^0 = I
  | 1 => [Gate.T q]                      -- T^1 = T
  | 2 => [Gate.S q]                      -- T^2 = S
  | 3 => [Gate.T q, Gate.S q]            -- T^3 = T*S
  | 4 => [Gate.Z q]                      -- T^4 = Z
  | 5 => [Gate.T q, Gate.Z q]            -- T^5 = T*Z
  | 6 => [Gate.S q, Gate.Z q]            -- T^6 = S*Z (= Sdg)
  | 7 => [Gate.Tdg q]                    -- T^7 = Tdg
  | _ => [Gate.T q]                      -- unreachable

/-- Merge consecutive T gates on a gate list: T*T = S, T^4 = Z, T^8 = I.
    Uses a fuel parameter for guaranteed termination. -/
def tMergeList (gs : List (Gate n)) (fuel : ℕ := gs.length + 1) : List (Gate n) :=
  match fuel with
  | 0 => gs
  | fuel' + 1 =>
    match gs with
    | [] => []
    | g :: rest =>
      match g with
      | .T q =>
        let (count, remaining) := countConsecutiveT q rest
        tPowerToGates q (count + 1) ++ tMergeList remaining fuel'
      | _ => g :: tMergeList rest fuel'

/-- T-gate merging optimization: flatten, merge T powers, rebuild. -/
def tMerge (c : Circuit n) : Circuit n :=
  Circuit.ofList (tMergeList (circuitToList c))

/-! ## What `tCount` measures -/

/-- A one-gate circuit that `tCount` scores zero and whose gate is the `T`
    gate.

    `isT` tests the constructor, so `Rz` scores zero at every angle, while
    `Rz` at `AngleQ.tAngle` has the `T` matrix (`AngleQ.rzGate_tAngle`) and
    costs one `T` by `AngleQ.tCost`. Every rotation-merging pass in the tree
    emits merged angles as `Rz`, so a pass that rewrites `T; T` to `Rz (π/2)`
    and one that rewrites it to `Rz (π/4)` both score zero here, though the
    second still contains a `T`.

    `AngleQ.tCost` is the angle-level metric that separates them. -/
theorem tCount_zero_of_rz_tAngle (i : Fin n) :
    tCount (Circuit.single (Gate.Rz i (AngleQ.toReal AngleQ.tAngle))) = 0
      ∧ gateEmbedding (Gate.Rz i (AngleQ.toReal AngleQ.tAngle))
          = gateEmbedding (Gate.T i)
      ∧ AngleQ.tCost AngleQ.tAngle = some 1 := by
  refine ⟨rfl, ?_, AngleQ.tCost_tAngle⟩
  show embedGate1 n i (QCircuit.rzGate _) = embedGate1 n i Programs.Qubit.tGate
  rw [AngleQ.rzGate_tAngle]

/-! ## A T-count that declines to guess -/

/-- The `T` cost of a gate, `none` where it is not determined. The Clifford gates
    cost none; `T` and `Tdg` cost one; an `Rz` carries a real angle and gets
    `none`; an `RzQ` at a multiple of `π/4` costs `PiLin.tCost` of its angle (one
    at an odd multiple, zero at an even one) and gets `none` at any other angle,
    which no Clifford+T gate sequence realizes exactly. -/
def gateTCost : Gate n → Option ℕ
  | .T _    => some 1
  | .Tdg _  => some 1
  | .Rz _ _ => none
  | .RzQ _ p => if p.isPiQuarterMul then some p.tCost else none
  | _       => some 0

/-- Whether `gateTCost` answers for a gate with the count `tCount` gives it. Every
    constructor but `Rz` and `RzQ` does; an `RzQ` does exactly at an even multiple
    of `π/4`, since `tCount` scores every `RzQ` zero. -/
def costKnown (g : Gate n) : Bool :=
  gateTCost g == some (if isT g then 1 else 0)

/-- Whether every gate of a circuit has a constructor-determined cost. -/
def costKnownCircuit : Circuit n → Bool
  | .empty     => true
  | .gate g c  => costKnown g && costKnownCircuit c
  | .seq c₁ c₂ => costKnownCircuit c₁ && costKnownCircuit c₂

/-- The `T` count of a circuit, `none` when it contains an `Rz` or an `RzQ` off
    the multiples of `π/4`.

    `tCount` answers `0` for an `Rz` at every angle, including the angles that
    are `T` gates (`tCount_zero_of_rz_tAngle`). This one answers `none` there
    instead of a number it cannot justify, and counts an `RzQ` at an odd
    multiple of `π/4` as one `T`, where `tCount` counts zero. On circuits
    without either case the two agree (`circuitTCost_eq_tCount`). -/
def circuitTCost : Circuit n → Option ℕ
  | .empty     => some 0
  | .gate g c  => match gateTCost g, circuitTCost c with
    | some a, some b => some (a + b)
    | _, _           => none
  | .seq c₁ c₂ => match circuitTCost c₁, circuitTCost c₂ with
    | some a, some b => some (a + b)
    | _, _           => none

/-- On the fragment it answers for, `circuitTCost` agrees with `tCount`: the
    two metrics differ only where `tCount` reports a number for an `Rz`. -/
theorem circuitTCost_eq_tCount (c : Circuit n) (h : costKnownCircuit c = true) :
    circuitTCost c = some (tCount c) := by
  induction c with
  | empty => rfl
  | gate g c ih =>
    simp only [costKnownCircuit, Bool.and_eq_true] at h
    have hg : gateTCost g = some (if isT g then 1 else 0) := by
      simpa [costKnown] using h.1
    rw [circuitTCost, ih h.2, hg, tCount]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [costKnownCircuit, Bool.and_eq_true] at h
    rw [circuitTCost, ih₁ h.1, ih₂ h.2, tCount]

/-- The circuit of `tCount_zero_of_rz_tAngle` is where the two part: `tCount`
    reports `0`, `circuitTCost` reports `none`, and the gate is a `T`. -/
theorem circuitTCost_none_of_rz (i : Fin n) (θ : ℝ) :
    circuitTCost (Circuit.single (Gate.Rz i θ)) = none := rfl

/-! ## The Clifford fragment of a circuit -/

/-- Whether a gate is a Clifford generator. `Rz` is not certified here at any
    angle: it records a real, which no classifier reads. `RzQ` is certified at an
    even multiple of `π/4`, a multiple of `π/2`. -/
def isCliffordGate : Gate n → Bool
  | .T _    => false
  | .Tdg _  => false
  | .Rz _ _ => false
  | .RzQ _ p => p.isPiQuarterMul && p.tCost == 0
  | _       => true

/-- Whether every gate of a circuit is a Clifford generator. Conservative at
    `Rz`, so a `true` answer is sound and a `false` one is not a proof that the
    circuit leaves the fragment. -/
def isCliffordCircuit : Circuit n → Bool
  | .empty     => true
  | .gate g c  => isCliffordGate g && isCliffordCircuit c
  | .seq c₁ c₂ => isCliffordCircuit c₁ && isCliffordCircuit c₂

/-- A circuit of Clifford generators costs no `T`, and `circuitTCost` says so
    rather than declining: certifying the fragment also settles the count. -/
theorem circuitTCost_eq_zero_of_isClifford (c : Circuit n)
    (h : isCliffordCircuit c = true) : circuitTCost c = some 0 := by
  induction c with
  | empty => rfl
  | gate g c ih =>
    simp only [isCliffordCircuit, Bool.and_eq_true] at h
    rw [circuitTCost, ih h.2]
    cases g <;> simp_all [gateTCost, isCliffordGate]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [isCliffordCircuit, Bool.and_eq_true] at h
    rw [circuitTCost, ih₁ h.1, ih₂ h.2]

/-- A Clifford circuit's cost is known, so the two metrics agree on it. -/
theorem tCount_eq_zero_of_isClifford (c : Circuit n)
    (h : isCliffordCircuit c = true) : tCount c = 0 := by
  induction c with
  | empty => rfl
  | gate g c ih =>
    simp only [isCliffordCircuit, Bool.and_eq_true] at h
    simp only [tCount, ih h.2]
    cases g <;> simp_all [isT, isCliffordGate]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [isCliffordCircuit, Bool.and_eq_true] at h
    simp only [tCount, ih₁ h.1, ih₂ h.2]

end CatCrypt.Quantum.Optimization.TCountOpt
