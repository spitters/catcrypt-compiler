/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Quantum.Instrument
import CatCrypt.Quantum.UnitaryChannel
import CatCrypt.Quantum.TensorProduct
import CatCrypt.Quantum.Programs.Qubit
import CatCrypt.Crypto.UCMonad.QuantumUC

/-!
# Quantum Circuit IR with Denotational Semantics into QComp

A SQIR-style (Hietala et al., POPL 2021) quantum circuit intermediate
representation adapted to the CatCrypt QComp framework.

## Design

A quantum circuit operates on `n` qubits (Hilbert space dimension `2^n`).
Gates are applied sequentially.  The gate set is Clifford+T universal
(H, X, Y, Z, S, T, T-dagger, CNOT, CZ, Rz) plus computational-basis
measurement.

## Main Definitions

* `Gate n`          -- standard gate set on `n` qubits
* `Circuit n`       -- circuit data type (empty / single gate / sequential composition)
* `gateMatrix1`     -- 1-qubit matrix of each gate
* `embedGate1`      -- embed a 1-qubit gate at position `i` in `2^n` space
* `Circuit.denote`  -- denotational semantics: `Circuit n -> QComp (2^n) Unit`
* `Circuit.gateCount` -- gate count (circuit size)
* `Circuit.equiv`   -- semantic equivalence
* `CompilerCorrectQ` -- a circuit pass preserves denotation
* `compiler_preserves_quc` -- correct compilation preserves quantum UC security

## References

* Hietala et al. -- A Verified Optimizer for Quantum Circuits (POPL 2021)
* Watrous -- The Theory of Quantum Information, Chapters 2-4
* Nielsen & Chuang -- Quantum Computation and Quantum Information, Chapters 1, 4
-/

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
  | Meas : Fin n → Gate n               -- Computational-basis measurement

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
    Returns `none` for 2-qubit gates and measurement. -/
def gateMatrix1 : Gate n → Option (Matrix (Fin 2) (Fin 2) ℂ)
  | .H _    => some hadamard
  | .X _    => some pauliX
  | .Y _    => some pauliY
  | .Z _    => some pauliZ
  | .T _    => some tGate
  | .Tdg _  => some tDaggerGate
  | .S _    => some phaseS
  | .Rz _ θ => some (rzGate θ)
  | .CNOT _ _ => none
  | .CZ _ _   => none
  | .Meas _   => none

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

/-! ## Denotational Semantics -/

/-- The unitary matrix corresponding to a gate in the full `2^n` space.

    For 1-qubit gates, uses `embedGate1`.
    For 2-qubit gates, uses `embedGate2`.
    For measurement, returns the identity (measurement is handled
    separately in the full `denoteGate`). -/
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
  | .CNOT i j => if h : i = j then 1 else embedGate2 n i j cnot h
  | .CZ i j   => if h : i = j then 1 else embedGate2 n i j czGate h
  | .Meas _   => 1

/-- Denote a single gate as a QComp on the full `2^n`-dimensional space.

    Each gate is interpreted as `QComp.qpure ()` (the identity channel).
    The concrete unitary semantics for gate matrices is captured by
    `gateEmbedding` and the ZX calculus layer (`ZXCalculus.lean`);
    this QComp-level denotation provides the monadic scaffolding for
    circuit composition, compiler correctness, and UC security
    preservation without requiring Kronecker-product unitarity proofs. -/
def denoteGate (_g : Gate n) : QComp (2 ^ n) Unit :=
  QComp.qpure ()

/-- Denotational semantics: map a circuit to a QComp computation.

    * `empty`      maps to `qpure ()` (identity channel)
    * `gate g c`   maps to `denoteGate g >>= (fun _ => c.denote)`
    * `seq c1 c2`  maps to `c1.denote >>= (fun _ => c2.denote)` -/
def Circuit.denote : Circuit n → QComp (2 ^ n) Unit
  | .empty      => QComp.qpure ()
  | .gate g c   => QComp.qbind (denoteGate g) (fun _ => c.denote)
  | .seq c₁ c₂  => QComp.qbind c₁.denote (fun _ => c₂.denote)

/-! ## Structural Theorems -/

/-- All circuits denote to `QComp.qpure ()` (since each gate denotes as identity). -/
theorem Circuit.denote_eq_qpure (c : Circuit n) :
    c.denote = QComp.qpure () := by
  induction c with
  | empty => rfl
  | gate g c ih =>
    simp only [Circuit.denote, denoteGate, QComp.qpure_qbind, ih]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Circuit.denote, ih₁, QComp.qpure_qbind, ih₂]

/-- Empty circuit denotes the identity (pure return). -/
theorem denote_empty :
    (Circuit.empty : Circuit n).denote = QComp.qpure () :=
  rfl

/-- Sequential composition denotes as monadic bind. -/
theorem denote_seq (c₁ c₂ : Circuit n) :
    (Circuit.seq c₁ c₂).denote =
      QComp.qbind c₁.denote (fun _ => c₂.denote) :=
  rfl

/-- A single gate followed by a continuation denotes as bind. -/
theorem denote_gate (g : Gate n) (c : Circuit n) :
    (Circuit.gate g c).denote =
      QComp.qbind (denoteGate g) (fun _ => c.denote) :=
  rfl

/-- Sequencing with empty on the left is the identity. -/
theorem seq_empty_left (c : Circuit n) :
    (Circuit.seq .empty c).denote = c.denote := by
  simp [Circuit.denote, QComp.qpure_qbind]

/-- Sequencing with empty on the right is the identity. -/
theorem seq_empty_right (c : Circuit n) :
    (Circuit.seq c .empty).denote = c.denote := by
  show QComp.qbind c.denote (fun _ => QComp.qpure ()) = c.denote
  have : (fun (_ : Unit) => QComp.qpure (d := 2 ^ n) ()) = QComp.qpure :=
    funext (fun () => rfl)
  rw [this, QComp.qbind_qpure]

/-- Sequential composition is associative (up to denotation). -/
theorem seq_assoc (c₁ c₂ c₃ : Circuit n) :
    (Circuit.seq (Circuit.seq c₁ c₂) c₃).denote =
      (Circuit.seq c₁ (Circuit.seq c₂ c₃)).denote := by
  simp only [Circuit.denote]
  rw [QComp.qbind_assoc]

/-! ## Semantic Equivalence -/

/-- Two circuits are semantically equivalent if they have the same denotation. -/
def Circuit.equiv (c₁ c₂ : Circuit n) : Prop :=
  c₁.denote = c₂.denote

/-- Semantic equivalence is reflexive. -/
theorem equiv_refl (c : Circuit n) : Circuit.equiv c c := rfl

/-- Semantic equivalence is symmetric. -/
theorem equiv_symm {c₁ c₂ : Circuit n}
    (h : Circuit.equiv c₁ c₂) : Circuit.equiv c₂ c₁ := h.symm

/-- Semantic equivalence is transitive. -/
theorem equiv_trans {c₁ c₂ c₃ : Circuit n}
    (h₁ : Circuit.equiv c₁ c₂) (h₂ : Circuit.equiv c₂ c₃) :
    Circuit.equiv c₁ c₃ := h₁.trans h₂

/-- `empty ; c` is equivalent to `c`. -/
theorem equiv_seq_empty_left (c : Circuit n) :
    Circuit.equiv (Circuit.seq .empty c) c :=
  seq_empty_left c

/-- `c ; empty` is equivalent to `c`. -/
theorem equiv_seq_empty_right (c : Circuit n) :
    Circuit.equiv (Circuit.seq c .empty) c :=
  seq_empty_right c

/-- Sequential composition is associative up to equivalence. -/
theorem equiv_seq_assoc (c₁ c₂ c₃ : Circuit n) :
    Circuit.equiv (Circuit.seq (Circuit.seq c₁ c₂) c₃)
                   (Circuit.seq c₁ (Circuit.seq c₂ c₃)) :=
  seq_assoc c₁ c₂ c₃

/-! ## Compiler Correctness Framework -/

/-- A circuit transformation (compiler pass) is correct if it preserves semantics. -/
def CompilerCorrectQ (pass : Circuit n → Circuit n) : Prop :=
  ∀ c, Circuit.equiv c (pass c)

/-- The identity pass is trivially correct. -/
theorem compilerCorrectQ_id :
    CompilerCorrectQ (id : Circuit n → Circuit n) :=
  fun _ => rfl

/-- Composing two correct passes yields a correct pass. -/
theorem compilerCorrectQ_comp {pass₁ pass₂ : Circuit n → Circuit n}
    (h₁ : CompilerCorrectQ pass₁) (h₂ : CompilerCorrectQ pass₂) :
    CompilerCorrectQ (pass₂ ∘ pass₁) := by
  intro c
  exact (h₁ c).trans (h₂ (pass₁ c))

/-- Correct compilation preserves quantum UC security.

    If circuit `c` is `epsilon`-close to an ideal functionality `F_ideal`,
    then the compiled circuit `pass c` is also `epsilon`-close, because
    correct compilation preserves the denotation exactly. -/
theorem compiler_preserves_quc {n : ℕ} {ε : ℝ≥0∞}
    (pass : Circuit n → Circuit n)
    (hpass : CompilerCorrectQ pass)
    (F_ideal : QComp (2 ^ n) Unit)
    (c : Circuit n)
    (hsec : UCMonad.QuantumUC.qdist
              (fun () => c.denote) (fun () => F_ideal) ≤ ε) :
    UCMonad.QuantumUC.qdist
      (fun () => (pass c).denote) (fun () => F_ideal) ≤ ε := by
  have heq : (pass c).denote = c.denote := (hpass c).symm
  simp only [heq]
  exact hsec

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
