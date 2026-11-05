/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit

/-!
# Gate Commutation Rules for Circuit Optimization

Gate commutation analysis enables circuit optimizations by identifying when
adjacent gates can be reordered without changing semantics. When commuting
gates are identified, they can be moved past each other to enable merging
(e.g., Rz(alpha) ... Rz(beta) on the same qubit with only commuting gates
between them can be merged to Rz(alpha + beta)).

## Main definitions

* `targetQubits`       -- set of qubits a gate acts on
* `disjointQubits`     -- two gates act on disjoint qubits
* `gateCommutes`       -- conservative commutation check
* `commuteAndMerge`    -- move commuting gates together and merge Rz rotations

Semantic preservation is stated over `unitaryDenote` in the companion module
`CommuteMergeSound` (`commuteAndMerge_unitaryCorrect`).

## References

* Nam et al. -- Automated optimization of large quantum circuits with continuous
  parameters, npj Quantum Information 2018
* Kissinger, van de Wetering -- Reducing the number of non-Clifford gates in
  quantum circuits, Physical Review A 2020
-/

@[expose] public section

set_option autoImplicit true

noncomputable section

namespace CatCrypt.Quantum.Optimization.CommutationRules

open CatCrypt.Quantum.QCircuit

/-! ## Qubit Targets -/

/-- The set of qubit indices that a gate acts on (as a list). -/
def targetQubits : Gate n → List (Fin n)
  | .H i       => [i]
  | .X i       => [i]
  | .Y i       => [i]
  | .Z i       => [i]
  | .T i       => [i]
  | .Tdg i     => [i]
  | .S i       => [i]
  | .Rz i _    => [i]
  | .RzQ i _   => [i]
  | .CNOT c t  => [c, t]
  | .CZ i j    => [i, j]

/-- Two gates act on disjoint qubits (no shared qubit index). -/
def disjointQubits (g₁ g₂ : Gate n) : Bool :=
  (targetQubits g₁).all fun q => !((targetQubits g₂).contains q)

/-- Check whether a gate is a diagonal gate in the computational basis.
    Diagonal gates (Z, S, T, Tdg, Rz, CZ) commute with each other on the
    same qubit. -/
def isDiagonal : Gate n → Bool
  | .Z _    => true
  | .S _    => true
  | .T _    => true
  | .Tdg _  => true
  | .Rz _ _ => true
  | .CZ _ _ => true
  | _       => false

/-- Extract the target qubit of a single-qubit gate, if applicable. -/
def singleTarget : Gate n → Option (Fin n)
  | .H i    => some i
  | .X i    => some i
  | .Y i    => some i
  | .Z i    => some i
  | .T i    => some i
  | .Tdg i  => some i
  | .S i    => some i
  | .Rz i _ => some i
  | .RzQ i _ => some i
  | _       => none

/-! ## Conservative Commutation Check -/

/-- Conservative check for whether two gates commute.

    Returns `true` when we can guarantee commutativity:
    - Gates on disjoint qubits always commute.
    - Diagonal gates (Z, S, T, Tdg, Rz, CZ) commute with each other.
    - CNOT(c,t) commutes with X on the control qubit.
    - CNOT(c,t) commutes with Z on the target qubit.
    - CNOT(c,t) commutes with Rz on the control qubit: both are diagonal in
      the computational basis on that wire.
    - Two Rz on the same qubit commute (abelian group of rotations).

    Returns `false` when commutativity is unknown or when gates do not
    commute (e.g., H and Z on the same qubit: HZ != ZH). -/
def gateCommutes (g₁ g₂ : Gate n) : Bool :=
  if disjointQubits g₁ g₂ then true
  else if isDiagonal g₁ && isDiagonal g₂ then true
  else match g₁, g₂ with
  -- CNOT(c,t) commutes with X on control
  | .CNOT c _, .X i => decide (c = i)
  | .X i, .CNOT c _ => decide (c = i)
  -- CNOT(c,t) commutes with Z on target
  | .CNOT _ t, .Z i => decide (t = i)
  | .Z i, .CNOT _ t => decide (t = i)
  -- CNOT(c,t) commutes with Rz on control
  | .CNOT c _, .Rz i _ => decide (c = i)
  | .Rz i _, .CNOT c _ => decide (i = c)
  -- Rz on same qubit commutes with Rz
  | .Rz i _, .Rz j _ => decide (i = j)
  | _, _ => false

/-! ## Commute-and-Merge Optimization -/

/-- Check if a gate is an Rz rotation and extract the qubit and angle. -/
def asRz : Gate n → Option (Fin n × ℝ)
  | .Rz i θ => some (i, θ)
  | _       => none

/-- Try to move an Rz gate forward past a sequence of commuting gates,
    looking for another Rz on the same qubit to merge with.
    Returns `none` if no merge is possible. -/
def tryMergeRz (i : Fin n) (θ₁ : ℝ) : List (Gate n) → Option (List (Gate n))
  | []      => none
  | g :: gs =>
    match asRz g with
    | some (j, θ₂) =>
      if decide (i = j) then some (Gate.Rz i (θ₁ + θ₂) :: gs)
      else if gateCommutes (Gate.Rz i θ₁) g then
        (tryMergeRz i θ₁ gs).map (g :: ·)
      else none
    | none =>
      if gateCommutes (Gate.Rz i θ₁) g then
        (tryMergeRz i θ₁ gs).map (g :: ·)
      else none

/-- One pass of commute-and-merge on a gate list: for each Rz gate,
    try to merge it with a later Rz on the same qubit.
    Uses a fuel parameter to guarantee termination when merges reduce
    the list or when no merge is found. -/
def mergePass (gs : List (Gate n)) (fuel : ℕ := gs.length + 1) : List (Gate n) :=
  match fuel with
  | 0 => gs
  | fuel' + 1 =>
    match gs with
    | [] => []
    | g :: rest =>
      match asRz g with
      | some (i, θ) =>
        match tryMergeRz i θ rest with
        | some rest' => mergePass rest' fuel'
        | none       => g :: mergePass rest fuel'
      | none => g :: mergePass rest fuel'

/-- The commute-and-merge optimization: flatten the circuit, apply the merge
    pass, and rebuild the circuit. -/
def commuteAndMerge (c : Circuit n) : Circuit n :=
  Circuit.ofList (mergePass (circuitToList c))

end CatCrypt.Quantum.Optimization.CommutationRules
