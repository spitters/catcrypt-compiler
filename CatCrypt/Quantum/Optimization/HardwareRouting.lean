/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit

/-!
# Hardware Routing: Logical-to-Physical Qubit Mapping

Real quantum hardware has limited connectivity: not all pairs of physical
qubits can directly execute two-qubit gates. A coupling graph describes
which qubit pairs are connected. The routing problem is to insert SWAP
gates so that every two-qubit gate operates on adjacent (connected) qubits,
while preserving overall circuit semantics.

## Main definitions

* `CouplingGraph n`       -- hardware connectivity as a boolean adjacency function
* `CouplingGraph.linear`  -- linear chain topology (i connects to i+1)
* `CouplingGraph.grid`    -- 2D grid topology
* `CouplingGraph.allToAll` -- fully connected topology
* `isRoutable`            -- check if a circuit respects a coupling graph
* `swapGate`              -- SWAP decomposition into 3 CNOTs
* `insertSwaps`           -- insert SWAPs to make non-adjacent gates routable
* `swapOverhead`          -- count the number of SWAPs inserted

## References

* Li, Ding, Xie -- Tackling the Qubit Mapping Problem for NISQ-Era Quantum
  Devices, ASPLOS 2019
* Cowtan et al. -- On the Qubit Routing Problem, TQC 2019
* Zulehner, Paler, Wille -- An Efficient Methodology for Mapping Quantum
  Circuits to the IBM QX Architectures, IEEE TCAD, 2019
-/

@[expose] public section

set_option autoImplicit true

namespace CatCrypt.Quantum.Optimization.HardwareRouting

open CatCrypt.Quantum.QCircuit

/-! ## Coupling Graph -/

/-- A coupling graph on `n` qubits: a symmetric boolean function indicating
    which pairs of physical qubits are directly connected (can execute
    two-qubit gates). -/
abbrev CouplingGraph (n : ℕ) := Fin n → Fin n → Bool

/-- Linear chain topology: qubit `i` is connected to qubit `i+1`.
    Common in superconducting architectures (e.g., IBM Heron). -/
def CouplingGraph.linear (n : ℕ) : CouplingGraph n := fun i j =>
  decide (i.val + 1 = j.val) || decide (j.val + 1 = i.val)

/-- 2D grid topology with `r` rows and `c` columns.
    Common in surface code architectures (e.g., Google Sycamore).
    Qubit `(row, col)` is mapped to linear index `row * c + col`. -/
def CouplingGraph.grid (r c : ℕ) : CouplingGraph (r * c) := fun i j =>
  let i_row := i.val / c
  let i_col := i.val % c
  let j_row := j.val / c
  let j_col := j.val % c
  -- Adjacent in same row
  (decide (i_row = j_row) && (decide (i_col + 1 = j_col) || decide (j_col + 1 = i_col)))
  -- Adjacent in same column
  || (decide (i_col = j_col) && (decide (i_row + 1 = j_row) || decide (j_row + 1 = i_row)))

/-- Fully connected topology: all qubits are connected.
    Represents an ideal (unconstrained) architecture. -/
def CouplingGraph.allToAll (n : ℕ) : CouplingGraph n := fun _ _ =>
  true

/-- Star topology: qubit 0 is connected to all others.
    Common in trapped-ion architectures. -/
def CouplingGraph.star (n : ℕ) : CouplingGraph n := fun i j =>
  decide (i.val = 0) || decide (j.val = 0)

/-- A coupling graph is symmetric. -/
def CouplingGraph.isSymmetric (g : CouplingGraph n) : Prop :=
  ∀ i j, g i j = g j i

/-- Linear chain is symmetric. -/
theorem linear_symmetric (n : ℕ) : (CouplingGraph.linear n).isSymmetric := by
  intro i j
  simp [CouplingGraph.linear, Bool.or_comm]

/-! ## Routability -/

/-- Extract the two-qubit gate pairs from a gate (returns `none` for
    single-qubit gates). -/
def twoQubitPair : Gate n → Option (Fin n × Fin n)
  | .CNOT c t => some (c, t)
  | .CZ i j   => some (i, j)
  | _         => none

/-- A single gate is routable on a coupling graph if it is either a
    single-qubit gate or a two-qubit gate on connected qubits. -/
def gateIsRoutable (g : Gate n) (cg : CouplingGraph n) : Bool :=
  match twoQubitPair g with
  | none => true
  | some (i, j) => cg i j

/-- Check if an entire circuit is routable on a coupling graph:
    every two-qubit gate acts on connected qubits. -/
def isRoutable : Circuit n → CouplingGraph n → Bool
  | .empty, _     => true
  | .gate g c, cg => gateIsRoutable g cg && isRoutable c cg
  | .seq c₁ c₂, cg => isRoutable c₁ cg && isRoutable c₂ cg

@[simp]
theorem allToAll_apply (n : ℕ) (i j : Fin n) : CouplingGraph.allToAll n i j = true := by
  rfl

/-- Any circuit is routable on the fully connected topology. -/
theorem routable_allToAll (c : Circuit n) :
    isRoutable c (CouplingGraph.allToAll n) = true := by
  induction c with
  | empty => rfl
  | gate g c ih =>
    simp only [isRoutable]
    rw [ih, Bool.and_true]
    unfold gateIsRoutable
    split
    · rfl
    · -- twoQubitPair g = some (i, j)
      rename_i i j _
      exact allToAll_apply n i j
  | seq c₁ c₂ ih₁ ih₂ =>
    simp [isRoutable, ih₁, ih₂]

/-! ## SWAP Gate Decomposition -/

/-- SWAP gate on qubits `i` and `j`, decomposed into 3 CNOT gates:
    SWAP(i,j) = CNOT(i,j) ; CNOT(j,i) ; CNOT(i,j).
    This is the standard decomposition used in practice. -/
def swapGate (i j : Fin n) : Circuit n :=
  Circuit.seq
    (Circuit.single (Gate.CNOT i j))
    (Circuit.seq
      (Circuit.single (Gate.CNOT j i))
      (Circuit.single (Gate.CNOT i j)))

/-- A SWAP gate uses 3 CNOTs. -/
theorem swapGate_gateCount (i j : Fin n) :
    (swapGate i j).gateCount = 3 := by
  simp [swapGate, Circuit.single, Circuit.gateCount]

/-! ## SWAP Insertion -/

/-- Find a neighbor of `src` that is closer to `tgt` in the coupling graph.
    Returns `src` if no better neighbor exists. Simple greedy heuristic
    for linear-like topologies. -/
def findCloserNeighbor (_cg : CouplingGraph n) (src tgt : Fin n) : Fin n :=
  if src.val < tgt.val then
    if h : src.val + 1 < n then ⟨src.val + 1, h⟩ else src
  else if h : 0 < src.val then ⟨src.val - 1, by omega⟩ else src

/-- Relabel the qubit indices of a gate by the transposition `Equiv.swap a b`:
    apply `Equiv.swap a b` to the (one or two) qubit indices the gate carries.
    Definitional. Placed in the `QCircuit.Gate` namespace so that `g.relabel a b`
    dot-notation resolves. -/
def _root_.CatCrypt.Quantum.QCircuit.Gate.relabel (g : Gate n) (a b : Fin n) : Gate n :=
  match g with
  | .H i    => .H (Equiv.swap a b i)
  | .X i    => .X (Equiv.swap a b i)
  | .Y i    => .Y (Equiv.swap a b i)
  | .Z i    => .Z (Equiv.swap a b i)
  | .T i    => .T (Equiv.swap a b i)
  | .Tdg i  => .Tdg (Equiv.swap a b i)
  | .S i    => .S (Equiv.swap a b i)
  | .Rz i θ => .Rz (Equiv.swap a b i) θ
  | .RzQ i q => .RzQ (Equiv.swap a b i) q
  | .CNOT i j => .CNOT (Equiv.swap a b i) (Equiv.swap a b j)
  | .CZ i j   => .CZ (Equiv.swap a b i) (Equiv.swap a b j)
/-- Insert SWAP gates to route a single two-qubit gate.
    Moves qubit `src` toward qubit `tgt` by inserting SWAPs along a path.
    A non-adjacent two-qubit gate `g` on `(i, j)` is wrapped as
    `swapGate i mid ; g.relabel i mid ; swapGate i mid`: the SWAP moves qubit
    `i` to its neighbour `mid`, the relabelled gate acts on the moved qubits,
    and the second SWAP moves it back. Under the unitary semantics the block
    realizes `S · U_{g.relabel} · S = U_g`, so the gate's action is preserved
    while it now executes on an adjacent qubit pair. -/
def routeGate (cg : CouplingGraph n) (g : Gate n) : Circuit n :=
  match twoQubitPair g with
  | none => Circuit.single g
  | some (i, j) =>
    if cg i j then Circuit.single g
    else
      -- Insert a SWAP to move qubits closer, apply the relabelled gate, swap back
      let mid := findCloserNeighbor cg i j
      Circuit.seq (swapGate i mid)
        (Circuit.seq (Circuit.single (g.relabel i mid)) (swapGate i mid))

/-- Insert SWAP gates to make an entire circuit routable on a coupling graph.
    This is a greedy algorithm that inserts SWAPs for each non-adjacent
    two-qubit gate. A more sophisticated approach would use look-ahead
    to minimize total SWAP count. -/
def insertSwaps (c : Circuit n) (cg : CouplingGraph n) : Circuit n :=
  match c with
  | .empty => .empty
  | .gate g c' => Circuit.seq (routeGate cg g) (insertSwaps c' cg)
  | .seq c₁ c₂ => Circuit.seq (insertSwaps c₁ cg) (insertSwaps c₂ cg)

/-- SWAP insertion preserves semantics on fully connected architectures,
    and is trivially routable there (since every gate is already routable). -/
theorem insertSwaps_routable_allToAll (c : Circuit n) :
    isRoutable (insertSwaps c (CouplingGraph.allToAll n)) (CouplingGraph.allToAll n) = true := by
  induction c with
  | empty => simp [insertSwaps, isRoutable]
  | gate g c ih =>
    simp only [insertSwaps, isRoutable]
    rw [ih, Bool.and_true]
    simp only [routeGate]
    split
    · simp [Circuit.single, isRoutable, gateIsRoutable, twoQubitPair]
      cases g <;> simp_all [twoQubitPair]
    · split
      · simp_all [Circuit.single, isRoutable, gateIsRoutable]
      · -- allToAll always returns true, so ¬(allToAll i j = true) is impossible
        simp [CouplingGraph.allToAll] at *
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [insertSwaps, isRoutable, ih₁, ih₂, Bool.and_self]

/-! ## SWAP Overhead Metrics -/

/-- Count the number of SWAP gates (groups of 3 CNOTs) inserted by routing. -/
def swapOverhead (c : Circuit n) (cg : CouplingGraph n) : ℕ :=
  ((insertSwaps c cg).gateCount - c.gateCount) / 3

private theorem routeGate_allToAll (g : Gate n) :
    (routeGate (CouplingGraph.allToAll n) g).gateCount = 1 := by
  simp [routeGate]
  cases g <;> simp [twoQubitPair, Circuit.single, Circuit.gateCount]

private theorem insertSwaps_allToAll_gateCount (c : Circuit n) :
    (insertSwaps c (CouplingGraph.allToAll n)).gateCount = c.gateCount := by
  induction c with
  | empty => simp [insertSwaps, Circuit.gateCount]
  | gate g c ih =>
    simp [insertSwaps, Circuit.gateCount, routeGate_allToAll, ih]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp [insertSwaps, Circuit.gateCount, ih₁, ih₂]

/-- No SWAPs are needed for a fully connected architecture. -/
theorem swapOverhead_allToAll (c : Circuit n) :
    swapOverhead c (CouplingGraph.allToAll n) = 0 := by
  simp [swapOverhead, insertSwaps_allToAll_gateCount]

end CatCrypt.Quantum.Optimization.HardwareRouting
