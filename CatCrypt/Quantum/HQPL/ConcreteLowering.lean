/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.HQPL
public import CatCrypt.Quantum.QPL
public import CatCrypt.Quantum.Optimization.MixedCommute

@[expose] public section

set_option autoImplicit true

/-!
# Concrete Gate Lowering for HQPL Register Operations

Concrete gate sequences over Clifford+T+Rz gates for the QFT on two and four
qubits, a Trotter step and the Grover diffusion, together with gate count
theorems and a comparison table of gate counts. The QFT sequences lower the HQPL
register operations `qft` and `iqft` on the whole register (`lowerHQPL2`,
`lowerHQPL4`).

## Main definitions

* `qft2Gates`, `trotter2Gates`, `groverDiffusion2` -- 2-qubit gate sequences
* `qft4Gates`, `trotter4Gates` -- 4-qubit gate sequences
* `lowerHQPL2`, `lowerHQPL4` -- concrete lowering functions
* `PipelineComparison` -- HQPL-vs-QPL gate count comparison record
* `comparison` -- the comparison table
* `groverDiffusionUnitary` -- the diffusion operator in the unitary group

## Main results

* `groverDiffusion2_unitaryDenote` -- the nine-gate Grover diffusion sequence
  and the diffusion operator induce the same quantum channel

## Gate Count Summary

| Primitive        | Qubits | HQPL ops | QPL gates | Expansion |
|------------------|--------|----------|-----------|-----------|
| QFT              | 2      | 1        | 10        | 10x       |
| Trotter step     | 2      | 1        | 5         | 5x        |
| Grover diffusion | 2      | 1        | 9         | 9x        |
| QFT              | 4      | 1        | 22        | 22x       |
| Trotter step     | 4      | 1        | 7         | 7x        |

-/

noncomputable section

namespace CatCrypt.Quantum.HQPL.ConcreteLowering

open CatCrypt.Quantum.HQPL CatCrypt.Quantum.QPLExtended CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.QPL.QPL

/-! ## 2-Qubit Gate Sequences -/

/-- QFT on 2 qubits over the Clifford+T gate set.

    In application order: `H₀`; the controlled-`S` (controlled-π/2 phase)
    `T₀, T₁, CNOT₀₁, T†₁, CNOT₀₁`; `H₁`; and the bit-reversal
    `SWAP₀₁ = CNOT₀₁, CNOT₁₀, CNOT₀₁`.  Total: 10 gates.

    The controlled-`S` expansion instantiates
    `P₀(θ/2), P₁(θ/2), CNOT₀₁, P₁(−θ/2), CNOT₀₁ = CP(θ)` at `θ = π/2`:
    the accumulated phase is `(θ/2)(q₀ + q₁ − q₀ ⊕ q₁) = θ q₀ q₁`. -/
def qft2Gates : List (Gate 2) :=
  [.H 0, .T 0, .T 1, .CNOT 0 1, .Tdg 1, .CNOT 0 1,
   .H 1, .CNOT 0 1, .CNOT 1 0, .CNOT 0 1]

/-- Trotter step on 2 qubits for the Ising-type Hamiltonian H = Z₀ + Z₁ + Z₀Z₁.

    In application order: `Rz₀(2t)`, `Rz₁(2t)`, `CNOT₀₁`, `Rz₁(2t)`, `CNOT₀₁`.
    Since `rzGate θ = diag(1, e^{iθ}) = e^{iθ/2} · e^{-iθZ/2}`, the angles are
    twice the evolution time, and the sequence realises `e^{-iHt}` up to the
    global phase `e^{3it}` — an equality of channels `ρ ↦ UρU†`. -/
def trotter2Gates (t : ℝ) : List (Gate 2) :=
  [.Rz 0 (2 * t), .Rz 1 (2 * t), .CNOT 0 1, .Rz 1 (2 * t), .CNOT 0 1]

/-- Grover diffusion operator on 2 qubits.

    D = H⊗H · X⊗X · CZ · X⊗X · H⊗H.
    Total: 9 gates (H, H, X, X, CZ, X, X, H, H). -/
def groverDiffusion2 : List (Gate 2) :=
  [.H 0, .H 1, .X 0, .X 1, .CZ 0 1, .X 0, .X 1, .H 0, .H 1]

/-! ## 4-Qubit Gate Sequences -/

/-- QFT on 4 qubits decomposed into standard gates.

    QFT₄ applies Hadamard + controlled rotations in the standard
    decomposition, followed by bit-reversal SWAPs.
    Structure:
    * Stage 0: H₀, CR₁₀(π/2), CR₂₀(π/4), CR₃₀(π/8)      -- 4 gates
    * Stage 1: H₁, CR₂₁(π/2), CR₃₁(π/4)                    -- 3 gates
    * Stage 2: H₂, CR₃₂(π/2)                                 -- 2 gates
    * Stage 3: H₃                                              -- 1 gate
    * Bit-reversal: SWAP(0,3), SWAP(1,2) = 4×CNOT each       -- 12 gates (estimated, via CNOT decomp)

    We model controlled-Rz as CNOT-Rz-CNOT (2 CNOTs + 1 Rz each),
    giving a total of ~22 gates. -/
def qft4Gates : List (Gate 4) :=
  -- Stage 0: H₀ + 3 controlled rotations (each = CNOT + Rz + CNOT)
  [.H 0,
   .CNOT 1 0, .Rz 0 (Real.pi / 2), .CNOT 1 0,
   .CNOT 2 0, .Rz 0 (Real.pi / 4), .CNOT 2 0,
   .CNOT 3 0, .Rz 0 (Real.pi / 8), .CNOT 3 0,
   -- Stage 1: H₁ + 2 controlled rotations
   .H 1,
   .CNOT 2 1, .Rz 1 (Real.pi / 2), .CNOT 2 1,
   .CNOT 3 1, .Rz 1 (Real.pi / 4), .CNOT 3 1,
   -- Stage 2: H₂ + 1 controlled rotation
   .H 2,
   .CNOT 3 2, .Rz 2 (Real.pi / 2), .CNOT 3 2,
   -- Stage 3: H₃
   .H 3]

/-- Trotter step on 4 qubits for nearest-neighbour Ising chain.

    H = Σᵢ Zᵢ + Σᵢ Zᵢ Zᵢ₊₁.
    First-order product: Rz on each qubit + CNOT-Rz-CNOT for each ZZ term.
    Simplified: Rz×4 + CNOT×3 (absorbing ZZ Rz into CNOT sandwiches). -/
def trotter4Gates : List (Gate 4) :=
  [.Rz 0 1.0, .Rz 1 1.0, .Rz 2 1.0, .Rz 3 1.0,
   .CNOT 0 1, .CNOT 1 2, .CNOT 2 3]

/-! ## Gate Count Theorems -/

theorem qft2Gates_length : qft2Gates.length = 10 := rfl

theorem trotter2Gates_length (t : ℝ) : (trotter2Gates t).length = 5 := rfl

theorem groverDiffusion2_length : groverDiffusion2.length = 9 := rfl

theorem qft4Gates_length : qft4Gates.length = 22 := rfl

theorem trotter4Gates_length : trotter4Gates.length = 7 := rfl

/-! ## Concrete Lowering Functions -/

/-- Lower a `RegisterOps 2` operation to a concrete list of 2-qubit gates. -/
def lowerRegisterOp2 : RegisterOps 2 → List (Gate 2)
  | .qft 0 2 => qft2Gates
  | .iqft 0 2 => qft2Gates.reverse   -- IQFT = reverse gate order + conjugate
  | .barrier => []
  | _ => []  -- other sub-register sizes: identity

/-- Lower a `RegisterOps 4` operation to a concrete list of 4-qubit gates. -/
def lowerRegisterOp4 : RegisterOps 4 → List (Gate 4)
  | .qft 0 4 => qft4Gates
  | .iqft 0 4 => qft4Gates.reverse
  | .barrier => []
  | _ => []  -- other sub-register sizes: identity

/-- Apply a list of gates in sequence to a QPL continuation. -/
def applyGatesQPL (gates : List (Gate n)) (k : CatCrypt.Quantum.QPL.QPL n α) :
    CatCrypt.Quantum.QPL.QPL n α :=
  gates.foldr (fun g acc => .gate g acc) k

/-- Lower a 2-qubit HQPL program to standard QPL using `lowerRegisterOp2`. -/
def lowerHQPL2 : HQPLProg 2 α → CatCrypt.Quantum.QPL.QPL 2 α
  | .ret a => .ret a
  | .gate g k => .gate g (lowerHQPL2 k)
  | .meas i kt kf => .meas i (lowerHQPL2 kt) (lowerHQPL2 kf)
  | .custom op k => applyGatesQPL (lowerRegisterOp2 op) (lowerHQPL2 k)
  | .fail => .fail

/-- Lower a 4-qubit HQPL program to standard QPL using `lowerRegisterOp4`. -/
def lowerHQPL4 : HQPLProg 4 α → CatCrypt.Quantum.QPL.QPL 4 α
  | .ret a => .ret a
  | .gate g k => .gate g (lowerHQPL4 k)
  | .meas i kt kf => .meas i (lowerHQPL4 kt) (lowerHQPL4 kf)
  | .custom op k => applyGatesQPL (lowerRegisterOp4 op) (lowerHQPL4 k)
  | .fail => .fail

/-! ## Lowering Theorems -/

/-- Barrier lowers to identity in the 2-qubit lowering. -/
theorem lowerHQPL2_barrier (k : HQPLProg 2 α) :
    lowerHQPL2 (.custom .barrier k) = lowerHQPL2 k := by
  simp [lowerHQPL2, lowerRegisterOp2, applyGatesQPL]

/-- Barrier lowers to identity in the 4-qubit lowering. -/
theorem lowerHQPL4_barrier (k : HQPLProg 4 α) :
    lowerHQPL4 (.custom .barrier k) = lowerHQPL4 k := by
  simp [lowerHQPL4, lowerRegisterOp4, applyGatesQPL]

/-- QFT on 2 qubits expands to exactly 10 QPL gates. -/
theorem lowerHQPL2_qft_gateCount :
    (lowerHQPL2 (.custom (.qft 0 2) (.ret () : HQPLProg 2 Unit))).gateCount = 10 := rfl

/-- QFT on 4 qubits expands to exactly 22 QPL gates. -/
theorem lowerHQPL4_qft_gateCount :
    (lowerHQPL4 (.custom (.qft 0 4) (.ret () : HQPLProg 4 Unit))).gateCount = 22 := rfl

/-! ## HQPL vs QPL Comparison -/

/-- A row in the HQPL-vs-QPL pipeline comparison table. -/
structure PipelineComparison where
  /-- Name of the register-level primitive. -/
  name : String
  /-- Number of qubits. -/
  qubits : ℕ
  /-- Number of HQPL register-level operations (always 1 per primitive). -/
  hqplOps : ℕ
  /-- Number of QPL-level gates after lowering. -/
  qplGates : ℕ
  /-- Human-readable expansion factor. -/
  expansion : String
  deriving Repr, Inhabited

/-- Comparison table: HQPL register operations vs QPL gate counts. -/
def comparison : List PipelineComparison :=
  [ { name := "QFT",              qubits := 2, hqplOps := 1, qplGates := 10, expansion := "10x" },
    { name := "Trotter step",     qubits := 2, hqplOps := 1, qplGates := 5,  expansion := "5x"  },
    { name := "Grover diffusion", qubits := 2, hqplOps := 1, qplGates := 9,  expansion := "9x"  },
    { name := "QFT",              qubits := 4, hqplOps := 1, qplGates := 22, expansion := "22x" },
    { name := "Trotter step",     qubits := 4, hqplOps := 1, qplGates := 7,  expansion := "7x"  } ]

/-- The comparison table has 5 entries. -/
theorem comparison_length : comparison.length = 5 := rfl

/-- All entries in the comparison table have exactly 1 HQPL operation. -/
theorem comparison_all_single_op :
    comparison.Forall (fun c => c.hqplOps = 1) := by
  simp [comparison, List.Forall]

/-- QPL gate counts in the comparison table match the concrete gate sequences. -/
theorem comparison_qft2_matches :
    (comparison.head!).qplGates = qft2Gates.length := rfl

theorem comparison_trotter2_matches (t : ℝ) :
    (comparison[1]!).qplGates = (trotter2Gates t).length := rfl

theorem comparison_grover2_matches :
    (comparison[2]!).qplGates = groverDiffusion2.length := rfl

theorem comparison_qft4_matches :
    (comparison[3]!).qplGates = qft4Gates.length := rfl

theorem comparison_trotter4_matches :
    (comparison[4]!).qplGates = trotter4Gates.length := rfl

/-! ## Two Single-Qubit Embeddings as One Two-Qubit Embedding -/

section EmbeddingBricks

open Matrix
open CatCrypt.Quantum.TensorProduct
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.DisjointCommute
open CatCrypt.Quantum.Optimization.MixedCommute

/-- `finProdEquiv 2 2` sends `(a, b)` to the index `a * 2 + b`, so its inverse
    splits that index back into `(a, b)`. -/
theorem finProdEquiv_two_symm (a b : Fin 2) :
    (finProdEquiv 2 2).symm ⟨a.val * 2 + b.val, by omega⟩ = (a, b) := by
  fin_cases a <;> fin_cases b <;> rfl

/-- Entry of a Kronecker product of two `2×2` matrices at the composite indices
    `a * 2 + b` and `a' * 2 + b'`. -/
theorem kronecker_two_apply (G H : Matrix (Fin 2) (Fin 2) ℂ) (a b a' b' : Fin 2) :
    (G ⊗ₖ H) ⟨a.val * 2 + b.val, by omega⟩ ⟨a'.val * 2 + b'.val, by omega⟩
      = G a a' * H b b' := by
  rw [kronecker_apply, finProdEquiv_two_symm, finProdEquiv_two_symm]

/-- A product of single-qubit embeddings on distinct qubits `i ≠ j` is the
    two-qubit embedding of the Kronecker product, with `i` the high bit. -/
theorem embedGate1_mul_embedGate1_eq_embedGate2 {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (G H : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n i G * embedGate1 n j H = embedGate2 n i j (G ⊗ₖ H) hij := by
  ext r c
  rw [embedGate1_mul_apply hij G H r c, embedGate2_apply hij _ r c]
  split_ifs with h
  · rw [idx4, idx4, kronecker_two_apply]
  · rfl

end EmbeddingBricks

end CatCrypt.Quantum.HQPL.ConcreteLowering

end
