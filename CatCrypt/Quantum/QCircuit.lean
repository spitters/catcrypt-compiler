/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Instrument
public import CatCrypt.Quantum.UnitaryChannel
public import CatCrypt.Quantum.TensorProduct
public import CatCrypt.Quantum.Programs.Qubit
public import CatCrypt.Crypto.UCMonad.QuantumUC
public import CatCrypt.Quantum.QasmAngle
public meta import CatCrypt.Quantum.QasmAngle
public import CatCrypt.Quantum.PiLin
public meta import CatCrypt.Quantum.PiLin

/-!
# Quantum Circuit IR

A SQIR-style (Hietala et al., POPL 2021) quantum circuit intermediate
representation adapted to the CatCrypt QComp framework, together with the
`2^n × 2^n` unitary matrix of each gate.

## Design

A quantum circuit operates on `n` qubits (Hilbert space dimension `2^n`).
Gates are applied sequentially.  The gate set is Clifford+T universal
(H, X, Y, Z, S, T, T-dagger, CNOT, CZ, Rz); every gate is unitary.

## Main definitions

* `Gate n`          -- standard gate set on `n` qubits
* `QFT.mapGate f`   -- a gate relabelled along a map `f` of qubit indices
* `Circuit n`       -- circuit data type (empty / single gate / sequential composition)
* `gateMatrix1`     -- 1-qubit matrix of each gate
* `embedGate1`      -- embed a 1-qubit gate at position `i` in `2^n` space
* `gateEmbedding`   -- the `2^n × 2^n` unitary of a gate
* `Circuit.gateCount` -- gate count (circuit size)

The denotational semantics of a circuit, its semantic equivalence, and the
compiler-correctness framework built on them are in `GateUnitarity.lean`
(`unitaryDenote`, `unitaryEquiv`, `UnitaryCorrectQ`,
`unitaryCorrect_preserves_quc`).

## References

* Hietala et al. -- A Verified Optimizer for Quantum Circuits (POPL 2021)
* Watrous -- The Theory of Quantum Information, Chapters 2-4
* Nielsen & Chuang -- Quantum Computation and Quantum Information, Chapters 1, 4
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Complex CatCrypt.Quantum CatCrypt.Quantum.UnitaryChannel
open CatCrypt.Quantum.TensorProduct
open CatCrypt.Quantum.Programs.Qubit

noncomputable section

namespace CatCrypt.Quantum.QCircuit

variable {n : ℕ}

/-! ## Gate Set -/

/-- Standard quantum gate set (Clifford+T universal) on `n` qubits.

    Single-qubit gates are indexed by the target qubit `Fin n`.
    Two-qubit gates take (control, target). -/
inductive Gate (n : ℕ) : Type where
  | H    : Fin n → Gate n               -- Hadamard
  | X    : Fin n → Gate n               -- Pauli X
  | Y    : Fin n → Gate n               -- Pauli Y
  | Z    : Fin n → Gate n               -- Pauli Z
  | T    : Fin n → Gate n               -- T gate (pi/4 phase)
  | Tdg  : Fin n → Gate n               -- T-dagger
  | S    : Fin n → Gate n               -- Phase gate S (pi/2 phase)
  | CNOT : Fin n → Fin n → Gate n       -- CNOT (control, target)
  | CZ   : Fin n → Fin n → Gate n       -- Controlled-Z
  | Rz   : Fin n → ℝ → Gate n           -- Z-rotation by angle theta
  | RzQ  : Fin n → PiLin → Gate n        -- Z-rotation by an exact angle a + b*pi

/-- A gate on `m` qubits relabelled along a map of qubit indices into `n`
    qubits. -/
def _root_.CatCrypt.Quantum.QFT.mapGate {m : ℕ} (f : Fin m → Fin n) : Gate m → Gate n
  | .H i      => .H (f i)
  | .X i      => .X (f i)
  | .Y i      => .Y (f i)
  | .Z i      => .Z (f i)
  | .T i      => .T (f i)
  | .Tdg i    => .Tdg (f i)
  | .S i      => .S (f i)
  | .CNOT c t => .CNOT (f c) (f t)
  | .CZ c t   => .CZ (f c) (f t)
  | .Rz i θ   => .Rz (f i) θ
  | .RzQ i q  => .RzQ (f i) q

theorem _root_.CatCrypt.Quantum.QFT.mapGate_id (g : Gate n) : QFT.mapGate id g = g := by
  cases g <;> rfl

theorem _root_.CatCrypt.Quantum.QFT.map_mapGate_id (l : List (Gate n)) :
    l.map (QFT.mapGate id) = l :=
  (List.map_congr_left fun g _ => QFT.mapGate_id g).trans (List.map_id l)

/-! ## Circuit Type -/

/-- A quantum circuit on `n` qubits is a sequence of gates.

    * `empty`      -- identity circuit (no gates)
    * `gate g c`   -- apply gate `g`, then continue with circuit `c`
    * `seq c1 c2`  -- sequential composition: run `c1` then `c2` -/
inductive Circuit (n : ℕ) : Type where
  | empty : Circuit n
  | gate  : Gate n → Circuit n → Circuit n
  | seq   : Circuit n → Circuit n → Circuit n

/-! ## Gate Count -/

/-- Total number of gates in a circuit (circuit size). -/
def Circuit.gateCount : Circuit n → ℕ
  | .empty      => 0
  | .gate _ c   => 1 + c.gateCount
  | .seq c₁ c₂  => c₁.gateCount + c₂.gateCount

@[simp]
theorem gateCount_empty :
    (Circuit.empty : Circuit n).gateCount = 0 := rfl

@[simp]
theorem gateCount_gate (g : Gate n) (c : Circuit n) :
    (Circuit.gate g c).gateCount = 1 + c.gateCount := rfl

@[simp]
theorem gateCount_seq (c₁ c₂ : Circuit n) :
    (Circuit.seq c₁ c₂).gateCount = c₁.gateCount + c₂.gateCount := rfl

/-! ## Single-Qubit Gate Matrices -/

/-- T-dagger gate matrix: conjugate transpose of the T gate.
    `|0> -> |0>`, `|1> -> e^{-i pi/4} |1>`. -/
def tDaggerGate : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![1, 0], ![0, Complex.exp (-Complex.I * ↑(Real.pi / 4))]]

/-- Z-rotation gate by angle theta: `diag(1, e^{i theta})`. -/
def rzGate (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![1, 0], ![0, Complex.exp (Complex.I * ↑θ)]]

/-- Controlled-Z gate on 2 qubits:
    `|00> -> |00>, |01> -> |01>, |10> -> |10>, |11> -> -|11>`. -/
def czGate : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,-1]]

/-- Map a single-qubit gate to its 2x2 unitary matrix.
    Returns `none` for 2-qubit gates. -/
def gateMatrix1 : Gate n → Option (Matrix (Fin 2) (Fin 2) ℂ)
  | .H _    => some hadamard
  | .X _    => some pauliX
  | .Y _    => some pauliY
  | .Z _    => some pauliZ
  | .T _    => some tGate
  | .Tdg _  => some tDaggerGate
  | .S _    => some phaseS
  | .Rz _ θ => some (rzGate θ)
  | .RzQ _ a => some (rzGate (PiLin.toReal a))
  | .CNOT _ _ => none
  | .CZ _ _   => none

/-! ## Gate Embedding into n-Qubit Space -/

/-- Embed a 1-qubit gate acting on qubit `i` into the full `2^n`-dimensional space.

    Mathematically: `I_{2^i} (x) G (x) I_{2^(n-1-i)}`

    The entry `(r, c)` decomposes into (left, gate, right) parts via
    integer division and modular arithmetic. The gate matrix `G` is
    applied at bit position `i`, while the identity is enforced on all
    other bit positions. -/
def embedGate1 (n : ℕ) (i : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.of fun r c =>
    let i_val := i.val
    let n_sub := n - 1 - i_val
    let r_val := r.val
    let c_val := c.val
    let r_right := r_val % (2 ^ n_sub)
    let c_right := c_val % (2 ^ n_sub)
    let r_gate := (r_val / (2 ^ n_sub)) % 2
    let c_gate := (c_val / (2 ^ n_sub)) % 2
    let r_left := r_val / (2 ^ (n_sub + 1))
    let c_left := c_val / (2 ^ (n_sub + 1))
    if r_left = c_left ∧ r_right = c_right then
      G ⟨r_gate, Nat.mod_lt _ (by omega)⟩ ⟨c_gate, Nat.mod_lt _ (by omega)⟩
    else
      0

/-- Embed a 2-qubit gate (given as a 4x4 matrix) acting on qubits `i` and `j`
    into the full `2^n`-dimensional space.

    Extracts bits at positions `i` and `j` from row/column indices, forms
    a 2-bit index into `G`, and requires all other bit positions to match. -/
def embedGate2 (n : ℕ) (i j : Fin n) (G : Matrix (Fin 4) (Fin 4) ℂ)
    (_hij : i ≠ j) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.of fun r c =>
    let r_val := r.val
    let c_val := c.val
    -- Extract bit at position k (counting from MSB)
    let bit (v : ℕ) (k : Fin n) : Fin 2 :=
      ⟨(v / (2 ^ (n - 1 - k.val))) % 2, Nat.mod_lt _ (by omega)⟩
    let r_i := bit r_val i
    let r_j := bit r_val j
    let c_i := bit c_val i
    let c_j := bit c_val j
    -- Check that all other bits match between row and column
    let other_bits_match :=
      ∀ k : Fin n, k ≠ i → k ≠ j → bit r_val k = bit c_val k
    -- 2-bit index: qubit i is the high bit, qubit j is the low bit
    let r_2q : Fin 4 := ⟨r_i.val * 2 + r_j.val, by omega⟩
    let c_2q : Fin 4 := ⟨c_i.val * 2 + c_j.val, by omega⟩
    if other_bits_match then G r_2q c_2q else 0

/-- `embedGate2` is linear in its gate matrix: scaling the gate scales the
    embedding. -/
theorem embedGate2_smul {n : ℕ} (i j : Fin n) (s : ℂ) (G : Matrix (Fin 4) (Fin 4) ℂ)
    (h : i ≠ j) : embedGate2 n i j (s • G) h = s • embedGate2 n i j G h := by
  ext r c
  simp only [embedGate2, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split <;> simp

/-! ## Gate Matrices -/

/-- The unitary matrix corresponding to a gate in the full `2^n` space.

    For 1-qubit gates, uses `embedGate1`.
    For 2-qubit gates, uses `embedGate2`. -/
def gateEmbedding (g : Gate n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  match g with
  | .H i    => embedGate1 n i hadamard
  | .X i    => embedGate1 n i pauliX
  | .Y i    => embedGate1 n i pauliY
  | .Z i    => embedGate1 n i pauliZ
  | .T i    => embedGate1 n i tGate
  | .Tdg i  => embedGate1 n i tDaggerGate
  | .S i    => embedGate1 n i phaseS
  | .Rz i θ => embedGate1 n i (rzGate θ)
  | .RzQ i a => embedGate1 n i (rzGate (PiLin.toReal a))
  | .CNOT i j => if h : i = j then 1 else embedGate2 n i j cnot h
  | .CZ i j   => if h : i = j then 1 else embedGate2 n i j czGate h

/-! ## Circuit Constructors -/

/-- Single-gate circuit (no continuation). -/
def Circuit.single (g : Gate n) : Circuit n :=
  .gate g .empty

/-- Build a circuit from a list of gates (applied left to right). -/
def Circuit.ofList : List (Gate n) → Circuit n
  | []      => .empty
  | g :: gs => .gate g (Circuit.ofList gs)

/-- Gate count of `ofList` equals list length. -/
theorem gateCount_ofList (gs : List (Gate n)) :
    (Circuit.ofList gs).gateCount = gs.length := by
  induction gs with
  | nil => simp [Circuit.ofList]
  | cons g gs ih => simp [Circuit.ofList, ih, Nat.add_comm]

/-- Flatten a circuit to its gate list, applied left to right; `Circuit.ofList` rebuilds it. -/
def circuitToList : Circuit n → List (Gate n)
  | .empty     => []
  | .gate g c  => g :: circuitToList c
  | .seq c₁ c₂ => circuitToList c₁ ++ circuitToList c₂

/-- `circuitToList` preserves gate count as list length. -/
theorem circuitToList_length (c : Circuit n) :
    (circuitToList c).length = c.gateCount := by
  induction c with
  | empty => simp [circuitToList]
  | gate g c ih => simp [circuitToList, ih, Nat.add_comm]
  | seq c₁ c₂ ih₁ ih₂ => simp [circuitToList, ih₁, ih₂]

/-! ## Gate Count Properties -/

/-- Gate count is additive under sequential composition. -/
theorem gateCount_add (c₁ c₂ : Circuit n) :
    (Circuit.seq c₁ c₂).gateCount = c₁.gateCount + c₂.gateCount := rfl

/-- Empty circuit has zero gates. -/
theorem gateCount_zero :
    (Circuit.empty : Circuit n).gateCount = 0 := rfl

/-- Single-gate circuit has one gate. -/
theorem gateCount_single (g : Gate n) :
    (Circuit.single g).gateCount = 1 := by
  simp [Circuit.single, Circuit.gateCount]

end CatCrypt.Quantum.QCircuit
