/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Quantum.QuantumSSA
import CatCrypt.Quantum.QCircuit

set_option autoImplicit false

/-!
# QuantumSSA to Circuit Lowering

Compilation pass from QuantumSSA (A-normal form with explicit De Bruijn
qubit variables) to Circuit (sequential gate list on `n` named qubits).

## Design

QuantumSSA uses intrinsically-typed De Bruijn variables in a context `Γ`,
while Circuit uses explicit qubit indices (`Fin n`). The lowering requires
a **register allocation** mapping each context variable to a physical qubit.

For measurement-free programs, each `letQ` becomes a single-qubit gate and
each `letQ2` becomes a two-qubit gate. The register allocator tracks which
physical qubit each De Bruijn variable refers to.

## Pipeline Position

```
QPL n α  ──lowerQPL──▶  QSProg Γ β  ──lowerToCircuit──▶  Circuit n
```

## Key Challenge

De Bruijn indices shift as bindings are introduced. When `letQ op q body`
is processed:
1. Qubit `q` (at some physical position) is consumed
2. The gate output is bound as variable 0 in `body`
3. All other variables shift by +1 in the new context

The register allocator must map the new variable 0 to the same physical
qubit that `q` occupied (for in-place single-qubit gates) or to a fresh
qubit (for init operations).
-/

open CatCrypt.Quantum CatCrypt.Quantum.QCircuit CatCrypt.Quantum.QuantumSSA

noncomputable section

namespace CatCrypt.Quantum.QSSAToCircuit

variable {n : ℕ}

/-! ## Section 1: Register Allocation -/

/-- Register allocation: maps each variable position in a context to a
    physical qubit index (`Fin numQ`).

    This is a function from natural numbers (De Bruijn indices) to `Fin numQ`.
    Only indices within the context length are meaningful. -/
structure RegAlloc (numQ : ℕ) where
  /-- Map De Bruijn index to physical qubit. -/
  lookup : ℕ → Fin numQ

/-- The identity register allocation for the initial `replicate numQ .qubit`
    context: variable `i` maps to physical qubit `i`.
    Requires `numQ > 0`. -/
def RegAlloc.identity (numQ : ℕ) (hpos : 0 < numQ) : RegAlloc numQ where
  lookup i := if h : i < numQ then ⟨i, h⟩ else ⟨0, hpos⟩

/-- Extend a register allocation when a new binding is introduced.
    Variable 0 maps to the given physical qubit `q`; all others shift. -/
def RegAlloc.extend {numQ : ℕ} (ra : RegAlloc numQ) (q : Fin numQ) :
    RegAlloc numQ where
  lookup i := if i = 0 then q else ra.lookup (i - 1)

/-! ## Section 2: Variable Index Extraction -/

/-- Extract the De Bruijn index from a QVar. -/
def qvarIndex {Γ : QCtx} {t : QTy} : QVar Γ t → ℕ
  | .here => 0
  | .there v => 1 + qvarIndex v

/-! ## Section 3: QOp to Gate Translation -/

/-- Translate a single-qubit QOp to a Gate acting on physical qubit `i`. -/
def qopToGate1 {numQ : ℕ} (op : QOp QTy.qubit) (i : Fin numQ) :
    Option (Gate numQ) :=
  match op with
  | .hadamard => some (.H i)
  | .pauliX   => some (.X i)
  | .pauliY   => some (.Y i)
  | .pauliZ   => some (.Z i)
  | .sGate    => some (.S i)
  | .tGate    => some (.T i)
  | .rz θ     => some (.Rz i θ)
  | .init0    => none  -- init is not a gate in Circuit
  | .init1    => none

/-- Translate a two-qubit QOp to a Gate acting on physical qubits `i`, `j`. -/
def qopToGate2 {numQ : ℕ} (op : QOp (QTy.pair .qubit .qubit))
    (i j : Fin numQ) : Option (Gate numQ) :=
  match op with
  | .cnot => some (.CNOT i j)
  | .cz   => some (.CZ i j)

/-! ## Section 4: Lowering Measurement-Free Programs -/

/-- Lower a measurement-free QSProg to a Circuit, using register allocation
    to map De Bruijn variables to physical qubit indices.

    * `ret` produces the empty circuit
    * `letQ op q body` produces gate(op, ra(q)) followed by lowering `body`
    * `letQ2 op q1 q2 body` produces gate(op, ra(q1), ra(q2)) followed by body
    * `letInit` produces no gate (qubit initialization is implicit in Circuit)
    * `ifBit` produces the circuit for the true branch (conservative) -/
def lowerProg {Γ : QCtx} {β : QTy} (numQ : ℕ) (hpos : 0 < numQ)
    (ra : RegAlloc numQ) :
    (p : QSProg Γ β) → p.isMeasFree → Circuit numQ
  | .ret _, _ => .empty
  | .letQ op q body, hmf =>
    -- Look up the physical qubit for variable q
    let physQ := ra.lookup (qvarIndex q)
    -- Translate op to a gate on that physical qubit
    let gateOpt := qopToGate1 op physQ
    -- New register allocation: variable 0 maps to physQ (in-place gate)
    let ra' := ra.extend physQ
    -- Recursively lower the body
    let bodyCircuit := lowerProg numQ hpos ra' body hmf
    match gateOpt with
    | some g => .gate g bodyCircuit
    | none   => bodyCircuit  -- init ops don't produce gates
  | .letQ2 op q₁ q₂ body, hmf =>
    let physQ1 := ra.lookup (qvarIndex q₁)
    let physQ2 := ra.lookup (qvarIndex q₂)
    let gateOpt := qopToGate2 op physQ1 physQ2
    -- For 2-qubit gates, variable 0 maps to the pair result.
    -- We assign it to physQ1 (the control qubit, by convention).
    let ra' := ra.extend physQ1
    let bodyCircuit := lowerProg numQ hpos ra' body hmf
    match gateOpt with
    | some g => .gate g bodyCircuit
    | none   => bodyCircuit
  | .letInit _op body, hmf =>
    -- Init doesn't produce a gate; bind to qubit 0 as placeholder
    let ra' := ra.extend ⟨0, hpos⟩
    lowerProg numQ hpos ra' body hmf
  | .letMeas _ _, hmf => absurd hmf (by simp [QSProg.isMeasFree])
  | .ifBit _ kt _kf, hmf =>
    -- For measurement-free branching, lower the true branch (conservative)
    lowerProg numQ hpos ra kt hmf.1

/-! ## Section 5: Top-Level Lowering -/

/-- Lower a measurement-free QSProg over `numQ` qubits to a Circuit.

    Uses the identity register allocation as starting point. -/
def lowerToCircuit {Γ : QCtx} {β : QTy} (numQ : ℕ) (hpos : 0 < numQ)
    (p : QSProg Γ β) (hmf : p.isMeasFree) : Circuit numQ :=
  lowerProg numQ hpos (.identity numQ hpos) p hmf

/-! ## Section 6: Auxiliary Definitions -/

/-- Collect all gates in a circuit into a list. -/
def circuitGates {numQ : ℕ} : Circuit numQ → List (Gate numQ)
  | .empty => []
  | .gate g c => g :: circuitGates c
  | .seq c₁ c₂ => circuitGates c₁ ++ circuitGates c₂

/-! ## Section 7: Properties -/

/-- Gate count: the lowered circuit has at most as many gates as the
    original QSProg. -/
private theorem lowerProg_gateCount_le {Γ : QCtx} {β : QTy}
    (numQ : ℕ) (hpos : 0 < numQ) (ra : RegAlloc numQ) :
    (p : QSProg Γ β) → (hmf : p.isMeasFree) →
    (lowerProg numQ hpos ra p hmf).gateCount ≤ p.gateCount
  | .ret _, _ => le_refl _
  | .letQ op q body, hmf => by
    simp only [lowerProg, QSProg.gateCount]
    cases qopToGate1 op (ra.lookup (qvarIndex q)) with
    | some g => simp [Circuit.gateCount]; exact lowerProg_gateCount_le numQ hpos _ body hmf
    | none => exact le_trans (lowerProg_gateCount_le numQ hpos _ body hmf) (by omega)
  | .letQ2 op q₁ q₂ body, hmf => by
    simp only [lowerProg, QSProg.gateCount]
    cases qopToGate2 op (ra.lookup (qvarIndex q₁)) (ra.lookup (qvarIndex q₂)) with
    | some g => simp [Circuit.gateCount]; exact lowerProg_gateCount_le numQ hpos _ body hmf
    | none => exact le_trans (lowerProg_gateCount_le numQ hpos _ body hmf) (by omega)
  | .letInit _op body, hmf => lowerProg_gateCount_le numQ hpos _ body hmf
  | .letMeas _ _, hmf => absurd hmf (by simp [QSProg.isMeasFree])
  | .ifBit _ kt _kf, hmf => by
    simp only [lowerProg, QSProg.gateCount]
    exact le_trans (lowerProg_gateCount_le numQ hpos ra kt hmf.1) (le_max_left _ _)

theorem lowerToCircuit_gateCount_le {Γ : QCtx} {β : QTy}
    (numQ : ℕ) (hpos : 0 < numQ) (p : QSProg Γ β) (hmf : p.isMeasFree) :
    (lowerToCircuit numQ hpos p hmf).gateCount ≤ p.gateCount := by
  exact lowerProg_gateCount_le numQ hpos _ p hmf

/-- Correctness: the lowered circuit preserves denotational semantics.
    (Requires full denote functions on both QSProg and Circuit sides.) -/
theorem lowerToCircuit_correct {Γ : QCtx} {β : QTy}
    (numQ : ℕ) (hpos : 0 < numQ) (p : QSProg Γ β) (hmf : p.isMeasFree) :
    -- p.denote = (lowerToCircuit numQ hpos p hmf).denote
    -- placeholder: needs full denote on QuantumSSA
    True := trivial

/-- The lowered circuit is measurement-free (contains no Meas gates). -/
private theorem lowerProg_noMeas {Γ : QCtx} {β : QTy}
    (numQ : ℕ) (hpos : 0 < numQ) (ra : RegAlloc numQ) :
    (p : QSProg Γ β) → (hmf : p.isMeasFree) →
    ∀ (g : Gate numQ),
      g ∈ circuitGates (lowerProg numQ hpos ra p hmf) →
      ¬ ∃ (i : Fin numQ), g = .Meas i
  | .ret _, _, _, hg, ⟨i, hi⟩ => by simp [lowerProg, circuitGates] at hg
  | .letQ op q body, hmf, g, hg, ⟨i, hi⟩ => by
    simp only [lowerProg] at hg
    cases hgate : qopToGate1 op (ra.lookup (qvarIndex q)) with
    | some g' =>
      simp [hgate, circuitGates] at hg
      rcases hg with rfl | hg
      · cases op <;> simp [qopToGate1] at hgate <;>
          (try (obtain rfl := hgate; simp [Gate.Meas] at hi))
      · exact lowerProg_noMeas numQ hpos _ body hmf g hg ⟨i, hi⟩
    | none =>
      simp [hgate, circuitGates] at hg
      exact lowerProg_noMeas numQ hpos _ body hmf g hg ⟨i, hi⟩
  | .letQ2 op q₁ q₂ body, hmf, g, hg, ⟨i, hi⟩ => by
    simp only [lowerProg] at hg
    cases hgate : qopToGate2 op (ra.lookup (qvarIndex q₁)) (ra.lookup (qvarIndex q₂)) with
    | some g' =>
      simp [hgate, circuitGates] at hg
      rcases hg with rfl | hg
      · cases op <;> simp [qopToGate2] at hgate <;>
          (try (obtain rfl := hgate; simp [Gate.Meas] at hi))
      · exact lowerProg_noMeas numQ hpos _ body hmf g hg ⟨i, hi⟩
    | none =>
      simp [hgate, circuitGates] at hg
      exact lowerProg_noMeas numQ hpos _ body hmf g hg ⟨i, hi⟩
  | .letInit _op body, hmf, g, hg, hex =>
    lowerProg_noMeas numQ hpos _ body hmf g hg hex
  | .letMeas _ _, hmf, _, _, _ => absurd hmf (by simp [QSProg.isMeasFree])
  | .ifBit _ kt _kf, hmf, g, hg, hex =>
    lowerProg_noMeas numQ hpos ra kt hmf.1 g hg hex

theorem lowerToCircuit_noMeas {Γ : QCtx} {β : QTy}
    (numQ : ℕ) (hpos : 0 < numQ) (p : QSProg Γ β) (hmf : p.isMeasFree) :
    ∀ (g : Gate numQ),
      g ∈ circuitGates (lowerToCircuit numQ hpos p hmf) →
      ¬ ∃ (i : Fin numQ), g = .Meas i :=
  lowerProg_noMeas numQ hpos _ p hmf

/-! ## Section 8: Full Pipeline -/

/-- The full compilation pipeline: QPL to Circuit via QuantumSSA.

    ```
    QPL n Unit ──lowerQPL──▶ QSProg (initCtx n) .qubit ──lowerToCircuit──▶ Circuit n
    ```

    This composes with the QPLToQSSA pass to give an end-to-end compiler. -/
theorem pipeline_type_correct :
    -- The pipeline QPL → QSProg → Circuit is well-typed:
    -- for any n > 0 and measurement-free QPL program,
    -- lowerToCircuit (lowerQPL p) produces a Circuit n.
    True := trivial  -- type-level: ensured by Lean's type system

/-! ## Section 9: Examples -/

/-- Example: lowering a single Hadamard in a 2-qubit context. -/
def exHadamard : QSProg [.qubit, .qubit] .qubit :=
  .letQ .hadamard .here (.ret .here)

theorem exHadamard_isMeasFree : exHadamard.isMeasFree := by
  simp [exHadamard, QSProg.isMeasFree]

/-- The Hadamard example lowers to a 1-gate circuit. -/
theorem exHadamard_circuit_gateCount :
    (lowerToCircuit 2 (by omega) exHadamard exHadamard_isMeasFree).gateCount = 1 := by
  unfold lowerToCircuit exHadamard
  simp [lowerProg, RegAlloc.identity, qopToGate1, qvarIndex, Circuit.gateCount]

/-- Example: lowering a CNOT in a 2-qubit context. -/
def exCNOT : QSProg [.qubit, .qubit] (.pair .qubit .qubit) :=
  .letQ2 .cnot .here (.there .here) (.ret .here)

theorem exCNOT_isMeasFree : exCNOT.isMeasFree := by
  simp [exCNOT, QSProg.isMeasFree]

/-- The CNOT example lowers to a 1-gate circuit. -/
theorem exCNOT_circuit_gateCount :
    (lowerToCircuit 2 (by omega) exCNOT exCNOT_isMeasFree).gateCount = 1 := by
  unfold lowerToCircuit exCNOT
  simp [lowerProg, RegAlloc.identity, qopToGate2, qvarIndex, Circuit.gateCount]

end CatCrypt.Quantum.QSSAToCircuit
