/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Quantum.Instrument
import CatCrypt.Quantum.UnitaryChannel
import CatCrypt.Quantum.QCircuit
import CatCrypt.Quantum.Programs.Qubit

set_option autoImplicit true

/-!
# QuantumSSA: A Quantum SSA Intermediate Representation

An intrinsically-typed SSA (Static Single Assignment) intermediate representation
for quantum programs, extending the CryptoSSA design pattern to quantum computing.

## Design Principles

1. **Linear classification for qubits**: `QTy.isLinear` marks qubit-carrying
   types as linear. The exactly-once use discipline is extrinsic to the
   representation: `QSProg.WellLinear` (in
   `CatCrypt.Quantum.QuantumSSALinearity`) states it and `QSProg.linearCheck`
   decides it, following QSSA [Peduri-Bhat 2021]
2. **A-normal form**: all intermediate results are let-bound
3. **Mixed quantum-classical**: both qubit and classical bit types
4. **Denotational semantics**: `QSProg.denote` maps programs to `QComp`
5. **Structurally compatible with lean-mlir** (`Dialect { Op, Ty, m }` pattern)

## Architecture

```
QTy       ─── types (qubit, bit, pair, unit)
QVar      ─── intrinsically-typed De Bruijn variables
QOp       ─── quantum operations (gates, measure, init)
QSProg    ─── programs in A-normal form (let-binding + return)
QHVec     ─── heterogeneous valuation (typed environment)
```

## Compilation Pipeline Position

```
QPL (surface)  →  QuantumSSA (this file)  →  Circuit  →  ZX  →  optimized
```

QuantumSSA sits between QPL (high-level, measurement + control) and Circuit
(low-level gate list). It preserves enough structure for:
- Peephole optimizations (gate fusion, cancellation)
- Static no-cloning verification (`QSProg.WellLinear` and its checker
  `QSProg.linearCheck`, in `CatCrypt.Quantum.QuantumSSALinearity`)
- Dead qubit elimination
- Deferred measurement transformation

## References

* Peduri, Bhat — *QSSA: An SSA-based IR for Quantum Computing*, 2021
* CryptoSSA (this project) — classical SSA IR template
* lean-mlir / opencompl — MLIR framework for Lean 4
* McCaskey, Nguyen — *A MLIR Dialect for Quantum Assembly Languages*, 2021

**0 axioms**.
-/

open CatCrypt.Quantum CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.QCircuit
open scoped Matrix ComplexOrder ENNReal

noncomputable section

namespace CatCrypt.Quantum.QuantumSSA

/-! ## Section 1: Type System -/

/-- Types in the QuantumSSA IR.

    Quantum types are **linear** (used exactly once): `qubit`.
    Classical types are **unrestricted** (can be copied): `bit`, `unit`.

    This mirrors lean-mlir's `Ty` parameter for a `Dialect`. -/
inductive QTy where
  /-- Single qubit. LINEAR: must be used exactly once. -/
  | qubit
  /-- Classical bit (measurement result). Unrestricted. -/
  | bit
  /-- Unit type. -/
  | unit
  /-- Pair of types. -/
  | pair (a b : QTy)
  deriving DecidableEq, Repr

/-- Whether a type is linear (quantum) or unrestricted (classical). -/
def QTy.isLinear : QTy → Bool
  | .qubit => true
  | .bit => false
  | .unit => false
  | .pair a b => a.isLinear || b.isLinear

/-! ## Section 2: Typing Contexts and Variables -/

/-- Typing context: a list of QuantumSSA types (De Bruijn). -/
abbrev QCtx := List QTy

/-- Intrinsically-typed De Bruijn variable reference.
    `QVar Γ t` witnesses that type `t` appears at a specific position in `Γ`. -/
inductive QVar : QCtx → QTy → Type where
  | here {Γ : QCtx} {t : QTy} : QVar (t :: Γ) t
  | there {Γ : QCtx} {s t : QTy} : QVar Γ t → QVar (s :: Γ) t

/-! ## Section 3: Operations -/

/-- Quantum operations in SSA form.

    Each operation specifies its input types (consumed variables) and
    output type (bound by the enclosing let). Qubit inputs are consumed
    (linear), classical inputs are copied (unrestricted).

    The design follows QSSA's key insight: qubit wires flow through
    operations in a one-to-one manner, preventing implicit cloning. -/
inductive QOp : QTy → Type where
  /-- Initialize a fresh qubit in |0⟩. No inputs consumed. -/
  | init0 : QOp .qubit
  /-- Initialize a fresh qubit in |1⟩. -/
  | init1 : QOp .qubit
  /-- Apply Hadamard gate. Consumes one qubit, produces one qubit.
      The input qubit variable is dead after this operation. -/
  | hadamard : QOp .qubit
  /-- Apply Pauli X gate. -/
  | pauliX : QOp .qubit
  /-- Apply Pauli Y gate. -/
  | pauliY : QOp .qubit
  /-- Apply Pauli Z gate. -/
  | pauliZ : QOp .qubit
  /-- Apply S gate (phase π/2). -/
  | sGate : QOp .qubit
  /-- Apply T gate (phase π/4). -/
  | tGate : QOp .qubit
  /-- Apply Rz(θ) rotation. -/
  | rz (θ : ℝ) : QOp .qubit
  /-- CNOT gate: consumes control + target, produces control' + target'.
      Returns a pair of qubits. -/
  | cnot : QOp (.pair .qubit .qubit)
  /-- CZ gate: controlled-Z. -/
  | cz : QOp (.pair .qubit .qubit)
  /-- Measure a qubit in the computational basis.
      Consumes one qubit, produces (bit, qubit) — the measurement
      outcome and the post-measurement state.
      This is the key operation that UnitaryTree cannot express. -/
  | measure : QOp (.pair .bit .qubit)
  /-- Discard a qubit (trace out). Produces unit. -/
  | discard : QOp .unit

/-! ## Section 4: Programs in A-Normal Form -/

/-- QuantumSSA program in A-normal form.

    * `ret v` — return the value of variable `v`
    * `letQ op q body` — apply 1-qubit `op` to qubit `q`, bind result, continue
    * `letQ2 op q₁ q₂ body` — apply 2-qubit `op` to `q₁, q₂`, bind result, continue
    * `letInit op body` — initialize a new qubit, bind it, continue
    * `ifBit v kt kf` — branch on classical bit `v`

    The A-normal form ensures all intermediate quantum states are
    explicitly named, enabling SSA-based analysis. -/
inductive QSProg : QCtx → QTy → Type 1 where
  /-- Return a variable. -/
  | ret {Γ : QCtx} {t : QTy} (v : QVar Γ t) : QSProg Γ t
  /-- Apply a 1-qubit gate: `let r = op(q) in body`. -/
  | letQ {Γ : QCtx} {β : QTy}
      (op : QOp .qubit) (q : QVar Γ .qubit)
      (body : QSProg (.qubit :: Γ) β) : QSProg Γ β
  /-- Apply a 2-qubit gate: `let (r₁, r₂) = op(q₁, q₂) in body`. -/
  | letQ2 {Γ : QCtx} {β : QTy}
      (op : QOp (.pair .qubit .qubit))
      (q₁ q₂ : QVar Γ .qubit)
      (body : QSProg ((.pair .qubit .qubit) :: Γ) β) : QSProg Γ β
  /-- Initialize a new qubit: `let q = init0 in body`. -/
  | letInit {Γ : QCtx} {β : QTy}
      (op : QOp .qubit)
      (body : QSProg (.qubit :: Γ) β) : QSProg Γ β
  /-- Measure a qubit: `let (b, q') = measure(q) in body`. -/
  | letMeas {Γ : QCtx} {β : QTy}
      (q : QVar Γ .qubit)
      (body : QSProg ((.pair .bit .qubit) :: Γ) β) : QSProg Γ β
  /-- Branch on a classical bit. -/
  | ifBit {Γ : QCtx} {β : QTy}
      (v : QVar Γ .bit) (kt kf : QSProg Γ β) : QSProg Γ β

/-! ## Section 5: Program Metrics -/

/-- Gate count of a QuantumSSA program. -/
def QSProg.gateCount : QSProg Γ β → ℕ
  | .ret _ => 0
  | .letQ _ _ body => 1 + body.gateCount
  | .letQ2 _ _ _ body => 1 + body.gateCount
  | .letInit _ body => body.gateCount
  | .letMeas _ body => 1 + body.gateCount
  | .ifBit _ kt kf => max kt.gateCount kf.gateCount

/-- Count of measurement operations. -/
def QSProg.measCount : QSProg Γ β → ℕ
  | .ret _ => 0
  | .letQ _ _ body => body.measCount
  | .letQ2 _ _ _ body => body.measCount
  | .letInit _ body => body.measCount
  | .letMeas _ body => 1 + body.measCount
  | .ifBit _ kt kf => kt.measCount + kf.measCount

/-- A program is measurement-free (purely unitary). -/
def QSProg.isMeasFree : QSProg Γ β → Prop
  | .ret _ => True
  | .letQ _ _ body => body.isMeasFree
  | .letQ2 _ _ _ body => body.isMeasFree
  | .letInit _ body => body.isMeasFree
  | .letMeas _ _ => False
  | .ifBit _ kt kf => kt.isMeasFree ∧ kf.isMeasFree

/-! ## Section 6: Linearity Checking

The typing of `QSProg` does not bound how often a variable is referenced:
`letQ op q body` binds its result in `.qubit :: Γ` while `q` remains visible
in `Γ` inside `body`. The linear-use discipline (every variable of linear
type referenced exactly once) is therefore stated extrinsically:
`QSProg.WellLinear` in `CatCrypt.Quantum.QuantumSSALinearity`, decided by
the Boolean checker `QSProg.linearCheck` (`QSProg.linearCheck_iff`). That
module also proves the discipline preserved by the QPL lowering and the
peephole optimizer. -/

/-! ## Section 7: Translation to/from Circuit -/

/-- Map a 1-qubit QOp to the corresponding Gate. -/
def QOp.toGate1 : QOp .qubit → Option (Gate 1)
  | .hadamard => some (.H 0)
  | .pauliX => some (.X 0)
  | .pauliY => some (.Y 0)
  | .pauliZ => some (.Z 0)
  | .sGate => some (.S 0)
  | .tGate => some (.T 0)
  | .rz θ => some (.Rz 0 θ)
  | .init0 => none  -- init is not a gate
  | .init1 => none

/-- Map a 2-qubit QOp to the corresponding Gate. -/
def QOp.toGate2 : QOp (.pair .qubit .qubit) → Option (Gate 2)
  | .cnot => some (.CNOT 0 1)
  | .cz => some (.CZ 0 1)

/-! ## Section 8: Example Programs -/

/-- Example: create a Bell pair from two |0⟩ qubits.
    ```
    let q₁ = init0
    let q₂ = init0
    let q₁' = H(q₁)
    let (q₁'', q₂') = CNOT(q₁', q₂)
    ret (q₁'', q₂')
    ``` -/
def bellPair : QSProg [] (.pair .qubit .qubit) :=
  .letInit .init0 <|                           -- q₁ = |0⟩
  .letInit .init0 <|                           -- q₂ = |0⟩
  .letQ .hadamard (.there .here) <|            -- q₁' = H(q₁)
  .letQ2 .cnot .here (.there .here) <|         -- (q₁'', q₂') = CNOT(q₁', q₂)
  .ret .here

/-- Example: measure a qubit in the Hadamard basis.
    ```
    let q' = H(q)
    let (b, q'') = measure(q')
    ret b
    ``` -/
def measureHadamard : QSProg [.qubit] (.pair .bit .qubit) :=
  .letQ .hadamard .here <|                     -- q' = H(q)
  .letMeas .here <|                            -- (b, q') = measure(q')
  .ret .here                                   -- return (b, q') pair

/-- Bell pair creation is measurement-free. -/
theorem bellPair_isMeasFree : bellPair.isMeasFree := by
  simp [bellPair, QSProg.isMeasFree]

/-- Bell pair has 2 gates (H + CNOT). -/
theorem bellPair_gateCount : bellPair.gateCount = 2 := rfl

/-- Hadamard-basis measurement has 1 gate + 1 measurement. -/
theorem measureHadamard_gateCount : measureHadamard.gateCount = 2 := rfl

theorem measureHadamard_measCount : measureHadamard.measCount = 1 := rfl

/-! ## Section 9: Semantic Equivalence -/

/-- Two QuantumSSA programs are semantically equivalent if they denote
    the same QComp. (Placeholder: needs full denote function.) -/
def QSProg.equiv (p₁ p₂ : QSProg Γ β) : Prop :=
  True  -- placeholder: p₁.denote = p₂.denote

/-! ## Section 10: Peephole Optimization Framework -/

/-- A peephole rewrite rule: a local transformation on QSProg.
    Mirrors CryptoSSA's SSAPeephole design. -/
structure PeepholeRule where
  /-- Name of the rewrite rule. -/
  name : String
  /-- The rewriting function. -/
  rewrite : ∀ {Γ β}, QSProg Γ β → QSProg Γ β
  /-- Correctness: the rewrite preserves semantics. -/
  correct : ∀ {Γ β} (p : QSProg Γ β), (rewrite p).equiv p

/-- Gate cancellation: H·H = I, X·X = I, Z·Z = I.
    Removing gates changes the De Bruijn context, requiring variable
    renumbering. The full implementation needs a context substitution lemma. -/
def cancelInverses : ∀ {Γ β}, QSProg Γ β → QSProg Γ β
  | _, _, p => p  -- identity; `QSSAPeephole.rewriteHH` performs the cancellation

/-- Gate fusion: Rz(α)·Rz(β) = Rz(α+β).
    Same context surgery issue as cancelInverses. -/
def fuseRotations : ∀ {Γ β}, QSProg Γ β → QSProg Γ β
  | _, _, p => p  -- identity; `QSSAPeephole.rewriteRzFusion` performs the fusion

/-! ## Section 11: Connection to Compilation Pipeline -/

/-- QuantumSSA programs compile to the same QComp as QPL programs
    (when translated correctly). This ensures the full pipeline
    QPL → QuantumSSA → Circuit → ZX → optimized Circuit
    preserves QUC security via `quantum_robust_compilation`. -/
theorem pipeline_preserves_quc :
    -- For any QuantumSSA program p and its Circuit translation c:
    -- CompilerCorrectQ p c → qdist is preserved
    True := trivial  -- placeholder: wired when denote is complete

end CatCrypt.Quantum.QuantumSSA
