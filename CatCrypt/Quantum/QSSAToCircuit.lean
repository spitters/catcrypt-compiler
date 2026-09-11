/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QuantumSSA
public import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.GateUnitarity

@[expose] public section

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

## Main results

* `lowerProg` / `lowerToCircuit` — the lowering.
* `lowerProg_unitaryDenote`, `lowerToCircuit_unitaryDenote` — the lowering
  denotes the channel `QSProg.unitaryDenote` assigns to the source program
  under the same register allocation.
* `lowerToCircuit_gateCount_le` — the lowering emits no more gates than the
  source program counts.
* `lowerToCircuit_noMeas` — the lowered circuit contains no `Meas` gate.
-/

open CatCrypt.Quantum CatCrypt.Quantum.QCircuit CatCrypt.Quantum.QuantumSSA

noncomputable section

namespace CatCrypt.Quantum.QSSAToCircuit

variable {n : ℕ}

/-! ## Section 1: Register Allocation and Gate Translation

The register allocation `RegAlloc`, the De Bruijn index extractor
`qvarIndex` and the two op-to-gate translations are declared in
`CatCrypt.Quantum.QuantumSSA`, alongside the channel semantics
`QSProg.unitaryDenote` that uses them, and are re-exported here. -/

export CatCrypt.Quantum.QuantumSSA
  (RegAlloc qvarIndex qopToGate1 qopToGate2)

namespace RegAlloc

export CatCrypt.Quantum.QuantumSSA.RegAlloc
  (identity identityFrom extend freshQubit allocFresh)

end RegAlloc

/-! ## Section 2: Lowering Measurement-Free Programs -/

/-- Lower a program of the fragment cut out by `QSProg.isMeasFree` to a
    Circuit, using register allocation to map De Bruijn variables to physical
    qubit indices.

    * `ret` produces the empty circuit
    * `letQ op q body` produces gate(op, ra(q)) followed by lowering `body`,
      with the bound variable on the same physical qubit
    * `letQ2 op q1 q2 body` produces gate(op, ra(q1), ra(q2)) followed by
      body, with the bound pair on `ra(q1)`
    * `letInit` produces no gate and binds the new wire to a freshly
      allocated physical qubit
    * `letMeas` and `ifBit` are excluded by `QSProg.isMeasFree` -/
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
    -- Init produces no gate and claims a fresh physical qubit for the
    -- variable it binds.
    let ra' := ra.allocFresh hpos
    lowerProg numQ hpos ra' body hmf
  | .letMeas _ _, hmf => absurd hmf (by simp [QSProg.isMeasFree])
  | .ifBit _ _ _, hmf => absurd hmf (by simp [QSProg.isMeasFree])

/-! ## Section 3: Top-Level Lowering -/

/-- Lower a `QSProg` of the fragment cut out by `QSProg.isMeasFree` over
    `numQ` qubits to a Circuit.

    Uses the identity register allocation as starting point. -/
def lowerToCircuit {Γ : QCtx} {β : QTy} (numQ : ℕ) (hpos : 0 < numQ)
    (p : QSProg Γ β) (hmf : p.isMeasFree) : Circuit numQ :=
  lowerProg numQ hpos (.identity numQ hpos) p hmf

/-! ## Section 4: Auxiliary Definitions -/

/-- Collect all gates in a circuit into a list. -/
def circuitGates {numQ : ℕ} : Circuit numQ → List (Gate numQ)
  | .empty => []
  | .gate g c => g :: circuitGates c
  | .seq c₁ c₂ => circuitGates c₁ ++ circuitGates c₂

/-! ## Section 5: Properties -/

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
  | .ifBit _ _ _, hmf => absurd hmf (by simp [QSProg.isMeasFree])

theorem lowerToCircuit_gateCount_le {Γ : QCtx} {β : QTy}
    (numQ : ℕ) (hpos : 0 < numQ) (p : QSProg Γ β) (hmf : p.isMeasFree) :
    (lowerToCircuit numQ hpos p hmf).gateCount ≤ p.gateCount := by
  exact lowerProg_gateCount_le numQ hpos _ p hmf

/-- The lowering preserves the unitary-channel semantics: the circuit
    `lowerProg numQ hpos ra p hmf` denotes the channel that
    `QSProg.unitaryDenote` assigns to `p` under the same allocation. -/
theorem lowerProg_unitaryDenote {Γ : QCtx} {β : QTy}
    (numQ : ℕ) (hpos : 0 < numQ) (ra : RegAlloc numQ) :
    (p : QSProg Γ β) → (hmf : p.isMeasFree) →
    GateUnitarity.unitaryDenote (lowerProg numQ hpos ra p hmf) =
      p.unitaryDenote numQ hpos ra hmf
  | .ret _, _ => rfl
  | .letQ op q body, hmf => by
    have ih := lowerProg_unitaryDenote numQ hpos
      (ra.extend (ra.lookup (qvarIndex q))) body hmf
    show GateUnitarity.unitaryDenote
        (match qopToGate1 op (ra.lookup (qvarIndex q)) with
          | some g => .gate g _
          | none => _) = _
    cases hg : qopToGate1 op (ra.lookup (qvarIndex q)) with
    | none => simpa [QSProg.unitaryDenote, hg] using ih
    | some g =>
      simp only [QSProg.unitaryDenote, hg, GateUnitarity.unitaryDenote]
      exact congrArg _ (funext fun _ => ih)
  | .letQ2 op q₁ q₂ body, hmf => by
    have ih := lowerProg_unitaryDenote numQ hpos
      (ra.extend (ra.lookup (qvarIndex q₁))) body hmf
    show GateUnitarity.unitaryDenote
        (match qopToGate2 op (ra.lookup (qvarIndex q₁))
            (ra.lookup (qvarIndex q₂)) with
          | some g => .gate g _
          | none => _) = _
    cases hg : qopToGate2 op (ra.lookup (qvarIndex q₁))
        (ra.lookup (qvarIndex q₂)) with
    | none => simpa [QSProg.unitaryDenote, hg] using ih
    | some g =>
      simp only [QSProg.unitaryDenote, hg, GateUnitarity.unitaryDenote]
      exact congrArg _ (funext fun _ => ih)
  | .letInit _op body, hmf =>
    lowerProg_unitaryDenote numQ hpos (ra.allocFresh hpos) body hmf
  | .letMeas _ _, hmf => absurd hmf (by simp [QSProg.isMeasFree])
  | .ifBit _ _ _, hmf => absurd hmf (by simp [QSProg.isMeasFree])

/-- The top-level lowering preserves the unitary-channel semantics. -/
theorem lowerToCircuit_unitaryDenote {Γ : QCtx} {β : QTy}
    (numQ : ℕ) (hpos : 0 < numQ) (p : QSProg Γ β) (hmf : p.isMeasFree) :
    GateUnitarity.unitaryDenote (lowerToCircuit numQ hpos p hmf) =
      p.unitaryDenote numQ hpos (.identity numQ hpos) hmf :=
  lowerProg_unitaryDenote numQ hpos _ p hmf

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
  | .ifBit _ _ _, hmf, _, _, _ => absurd hmf (by simp [QSProg.isMeasFree])

theorem lowerToCircuit_noMeas {Γ : QCtx} {β : QTy}
    (numQ : ℕ) (hpos : 0 < numQ) (p : QSProg Γ β) (hmf : p.isMeasFree) :
    ∀ (g : Gate numQ),
      g ∈ circuitGates (lowerToCircuit numQ hpos p hmf) →
      ¬ ∃ (i : Fin numQ), g = .Meas i :=
  lowerProg_noMeas numQ hpos _ p hmf

/-! ## Section 6: Examples -/

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

/-- Example: two freshly initialised qubits joined by a CNOT, in the empty
    context. -/
def exInitInitCNOT : QSProg [] (.pair .qubit .qubit) :=
  .letInit .init0 <|
  .letInit .init0 <|
  .letQ2 .cnot (.there .here) .here <|
  .ret .here

theorem exInitInitCNOT_isMeasFree : exInitInitCNOT.isMeasFree := by
  simp [exInitInitCNOT, QSProg.isMeasFree]

/-- The two `letInit` bindings receive distinct physical qubits, so the CNOT
    joins wire 0 to wire 1. -/
theorem exInitInitCNOT_circuit :
    lowerToCircuit 2 (by omega) exInitInitCNOT exInitInitCNOT_isMeasFree =
      .gate (.CNOT 0 1) .empty := rfl

/-- `qbind` against the constant-`qpure` continuation on `2 ^ numQ`. -/
private theorem qbind_const_qpure {numQ : ℕ} (c : QComp (2 ^ numQ) Unit) :
    QComp.qbind c (fun _ => QComp.qpure ()) = c := by
  have hf : (fun (_ : Unit) => QComp.qpure (d := 2 ^ numQ) ()) = QComp.qpure :=
    funext fun () => rfl
  rw [hf, QComp.qbind_qpure]

/-- The Hadamard example denotes the unitary channel of `H` on wire 0. -/
theorem exHadamard_unitaryDenote :
    exHadamard.unitaryDenote 2 (by omega) (.identity 2 (by omega))
        exHadamard_isMeasFree =
      GateUnitarity.denoteGateU (Gate.H 0) :=
  qbind_const_qpure _

/-- The two-`letInit` example denotes the unitary channel of `CNOT` between
    wires 0 and 1. -/
theorem exInitInitCNOT_unitaryDenote :
    exInitInitCNOT.unitaryDenote 2 (by omega) (.identity 2 (by omega))
        exInitInitCNOT_isMeasFree =
      GateUnitarity.denoteGateU (Gate.CNOT 0 1) :=
  qbind_const_qpure _

end CatCrypt.Quantum.QSSAToCircuit
