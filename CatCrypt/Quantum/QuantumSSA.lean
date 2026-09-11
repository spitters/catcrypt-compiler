/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Instrument
public import CatCrypt.Quantum.UnitaryChannel
public import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.GateUnitarity
public import CatCrypt.Quantum.Programs.Qubit

@[expose] public section

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
4. **Denotational semantics**: `QSProg.unitaryDenote` maps a program of the
   measurement- and branch-free fragment, together with a `RegAlloc`, to a
   `QComp (2 ^ numQ) Unit`
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

/-- The purely unitary fragment: a program built from `ret`, `letQ`, `letQ2`
    and `letInit` alone. Both `letMeas` and `ifBit` are excluded — `letMeas`
    because measurement is not a unitary channel, `ifBit` because classical
    control has no interpretation in `QComp (2 ^ numQ) Unit`. On this fragment
    the lowering `QSSAToCircuit.lowerProg` is total and discards no branch. -/
def QSProg.isMeasFree : QSProg Γ β → Prop
  | .ret _ => True
  | .letQ _ _ body => body.isMeasFree
  | .letQ2 _ _ _ body => body.isMeasFree
  | .letInit _ body => body.isMeasFree
  | .letMeas _ _ => False
  | .ifBit _ _ _ => False

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

/-! ## Section 8: Register Allocation

A `QSProg` names its wires by De Bruijn index in a context; a `Circuit numQ`
and the channel semantics name them by physical index `Fin numQ`. A
`RegAlloc numQ` is the translation between the two, carried through the
program by the lowering and by the denotation. -/

/-- Register allocation: a physical qubit for each De Bruijn index, together
    with the number of physical qubits already handed out to `letInit`
    bindings.

    `lookup` is total; only indices below the length of the context it was
    built for are meaningful. -/
structure RegAlloc (numQ : ℕ) where
  /-- Map De Bruijn index to physical qubit. -/
  lookup : ℕ → Fin numQ
  /-- Number of physical qubits already claimed by fresh allocation. The next
      fresh qubit is `next`, reduced mod `numQ`. -/
  next : ℕ

/-- The allocation for the context `replicate k .qubit`, in which variable `i`
    occupies physical qubit `i` and fresh allocation resumes at `nextFree`.
    Indices at or above `numQ` are outside the intended context and take the
    default physical qubit `0`. -/
def RegAlloc.identityFrom (numQ : ℕ) (hpos : 0 < numQ) (nextFree : ℕ) :
    RegAlloc numQ where
  lookup i := if h : i < numQ then ⟨i, h⟩ else ⟨0, hpos⟩
  next := nextFree

/-- The identity register allocation: variable `i` maps to physical qubit `i`,
    and fresh allocation starts at physical qubit `0`. -/
def RegAlloc.identity (numQ : ℕ) (hpos : 0 < numQ) : RegAlloc numQ :=
  RegAlloc.identityFrom numQ hpos 0

/-- Extend a register allocation when a new binding is introduced.
    Variable 0 maps to the given physical qubit `q`; all others shift.
    The fresh-allocation pointer is unchanged: `q` is a qubit that the
    allocation already holds. -/
def RegAlloc.extend {numQ : ℕ} (ra : RegAlloc numQ) (q : Fin numQ) :
    RegAlloc numQ where
  lookup i := if i = 0 then q else ra.lookup (i - 1)
  next := ra.next

/-- The physical qubit a fresh allocation hands out next. -/
def RegAlloc.freshQubit {numQ : ℕ} (ra : RegAlloc numQ) (hpos : 0 < numQ) :
    Fin numQ :=
  ⟨ra.next % numQ, Nat.mod_lt _ hpos⟩

/-- Extend a register allocation with a freshly allocated physical qubit:
    variable 0 maps to `ra.freshQubit hpos`, all others shift, and the
    fresh-allocation pointer advances. -/
def RegAlloc.allocFresh {numQ : ℕ} (ra : RegAlloc numQ) (hpos : 0 < numQ) :
    RegAlloc numQ where
  lookup i := if i = 0 then ra.freshQubit hpos else ra.lookup (i - 1)
  next := ra.next + 1

@[simp]
theorem RegAlloc.identity_lookup {numQ i : ℕ} (hpos : 0 < numQ) (h : i < numQ) :
    (RegAlloc.identity numQ hpos).lookup i = ⟨i, h⟩ :=
  dif_pos h

/-- Distinct variables of the initial context occupy distinct physical
    qubits. -/
theorem RegAlloc.identity_lookup_inj {numQ i j : ℕ} (hpos : 0 < numQ)
    (hi : i < numQ) (hj : j < numQ)
    (h : (RegAlloc.identity numQ hpos).lookup i =
      (RegAlloc.identity numQ hpos).lookup j) : i = j := by
  rw [RegAlloc.identity_lookup hpos hi, RegAlloc.identity_lookup hpos hj] at h
  simpa using congrArg Fin.val h

@[simp]
theorem RegAlloc.allocFresh_next {numQ : ℕ} (ra : RegAlloc numQ)
    (hpos : 0 < numQ) : (ra.allocFresh hpos).next = ra.next + 1 :=
  rfl

@[simp]
theorem RegAlloc.allocFresh_lookup_zero {numQ : ℕ} (ra : RegAlloc numQ)
    (hpos : 0 < numQ) :
    (ra.allocFresh hpos).lookup 0 = ra.freshQubit hpos :=
  rfl

@[simp]
theorem RegAlloc.allocFresh_lookup_succ {numQ : ℕ} (ra : RegAlloc numQ)
    (hpos : 0 < numQ) (i : ℕ) :
    (ra.allocFresh hpos).lookup (i + 1) = ra.lookup i := by
  show (if i + 1 = 0 then ra.freshQubit hpos else ra.lookup (i + 1 - 1)) =
    ra.lookup i
  simp

/-- Two fresh allocations in a row occupy distinct physical qubits, as long as
    the fresh-allocation pointer has not run past `numQ`. In the context they
    build, the second allocation is variable 0 and the first is variable 1. -/
theorem RegAlloc.allocFresh_lookup_zero_ne_one {numQ : ℕ} (ra : RegAlloc numQ)
    (hpos : 0 < numQ) (h : ra.next + 1 < numQ) :
    ((ra.allocFresh hpos).allocFresh hpos).lookup 0 ≠
      ((ra.allocFresh hpos).allocFresh hpos).lookup 1 := by
  have h0 : ra.next < numQ := by omega
  intro hEq
  have hval := congrArg Fin.val hEq
  simp only [RegAlloc.allocFresh_lookup_zero, RegAlloc.freshQubit,
    RegAlloc.allocFresh_next, RegAlloc.allocFresh_lookup_succ (i := 0)] at hval
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt h0] at hval
  omega

/-! ## Section 9: Variable Indices and Gate Translation -/

/-- Extract the De Bruijn index from a `QVar`. -/
def qvarIndex {Γ : QCtx} {t : QTy} : QVar Γ t → ℕ
  | .here => 0
  | .there v => 1 + qvarIndex v

/-- Translate a single-qubit `QOp` to a `Gate` acting on physical qubit `i`.
    The two initialization operations produce no gate. -/
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
  | .init0    => none
  | .init1    => none

/-- Translate a two-qubit `QOp` to a `Gate` acting on physical qubits
    `i`, `j`. -/
def qopToGate2 {numQ : ℕ} (op : QOp (QTy.pair .qubit .qubit))
    (i j : Fin numQ) : Option (Gate numQ) :=
  match op with
  | .cnot => some (.CNOT i j)
  | .cz   => some (.CZ i j)

/-! ## Section 10: Unitary-Channel Semantics

The semantics of the fragment cut out by `QSProg.isMeasFree`, on `numQ`
physical qubits under a register allocation. A gate operation contributes
`GateUnitarity.denoteGateU g`, the channel `ρ ↦ U ρ U†` for `U` the gate's
embedding; `letInit` contributes no channel and advances the allocation. -/

/-- Unitary-channel semantics of a program in the fragment cut out by
    `QSProg.isMeasFree`, relative to a register allocation.

    * `ret` denotes `QComp.qpure ()`.
    * `letQ op q body` denotes the channel of the gate `qopToGate1 op (ra q)`
      bound to the denotation of `body` under the allocation that rebinds
      variable 0 to the same physical qubit.
    * `letQ2 op q₁ q₂ body` likewise, with the gate
      `qopToGate2 op (ra q₁) (ra q₂)` and variable 0 rebound to `ra q₁`.
    * `letInit op body` denotes `body` under a freshly allocated qubit.

    An operation that translates to no gate (`init0`, `init1` used in `letQ`)
    contributes no channel. -/
def QSProg.unitaryDenote {Γ : QCtx} {β : QTy} (numQ : ℕ) (hpos : 0 < numQ)
    (ra : RegAlloc numQ) :
    (p : QSProg Γ β) → p.isMeasFree → QComp (2 ^ numQ) Unit
  | .ret _, _ => QComp.qpure ()
  | .letQ op q body, hmf =>
    let physQ := ra.lookup (qvarIndex q)
    let rest := QSProg.unitaryDenote numQ hpos (ra.extend physQ) body hmf
    match qopToGate1 op physQ with
    | some g => QComp.qbind (GateUnitarity.denoteGateU g) (fun _ => rest)
    | none   => rest
  | .letQ2 op q₁ q₂ body, hmf =>
    let physQ1 := ra.lookup (qvarIndex q₁)
    let physQ2 := ra.lookup (qvarIndex q₂)
    let rest := QSProg.unitaryDenote numQ hpos (ra.extend physQ1) body hmf
    match qopToGate2 op physQ1 physQ2 with
    | some g => QComp.qbind (GateUnitarity.denoteGateU g) (fun _ => rest)
    | none   => rest
  | .letInit _op body, hmf =>
    QSProg.unitaryDenote numQ hpos (ra.allocFresh hpos) body hmf
  | .letMeas _ _, hmf => absurd hmf (by simp [QSProg.isMeasFree])
  | .ifBit _ _ _, hmf => absurd hmf (by simp [QSProg.isMeasFree])

/-! ## Section 11: Example Programs -/

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

/-! ## Section 12: Semantic Equivalence -/

/-- Two QuantumSSA programs are semantically equivalent when they denote the
    same channel on the fragment `QSProg.isMeasFree` cuts out, for every qubit
    count and every register allocation.

    Outside that fragment the condition is empty: `QSProg.unitaryDenote`
    interprets no program containing `letMeas` or `ifBit`, so a pair in which
    either side measures or branches carries no constraint. -/
def QSProg.equiv (p₁ p₂ : QSProg Γ β) : Prop :=
  ∀ (numQ : ℕ) (hpos : 0 < numQ) (ra : RegAlloc numQ)
    (h₁ : p₁.isMeasFree) (h₂ : p₂.isMeasFree),
    p₁.unitaryDenote numQ hpos ra h₁ = p₂.unitaryDenote numQ hpos ra h₂

/-- Every program is equivalent to every other as soon as one of them leaves
    the measurement-free fragment, because the hypothesis `QSProg.equiv`
    quantifies over is then uninhabited. This bounds what a
    `PeepholeRule.correct` field can be read as claiming: on a program
    containing `letMeas` or `ifBit` it constrains the rewrite not at all. -/
theorem QSProg.equiv_of_not_isMeasFree_left {Γ : QCtx} {β : QTy}
    (p₁ p₂ : QSProg Γ β) (h : ¬ p₁.isMeasFree) : p₁.equiv p₂ :=
  fun _ _ _ h₁ _ => absurd h₁ h

/-- The same on the right. -/
theorem QSProg.equiv_of_not_isMeasFree_right {Γ : QCtx} {β : QTy}
    (p₁ p₂ : QSProg Γ β) (h : ¬ p₂.isMeasFree) : p₁.equiv p₂ :=
  fun _ _ _ _ h₂ => absurd h₂ h

/-! ## Section 13: Peephole Optimization Framework -/

/-- A peephole rewrite rule: a local transformation on QSProg.
    Mirrors CryptoSSA's SSAPeephole design. -/
structure PeepholeRule where
  /-- Name of the rewrite rule. -/
  name : String
  /-- The rewriting function. -/
  rewrite : ∀ {Γ β}, QSProg Γ β → QSProg Γ β
  /-- The rewrite preserves the unitary denotation on the measurement-free
      fragment. It says nothing about a program containing `letMeas` or
      `ifBit`: `QSProg.equiv_of_not_isMeasFree_left` holds for any pair as soon
      as one side leaves that fragment. -/
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

end CatCrypt.Quantum.QuantumSSA
