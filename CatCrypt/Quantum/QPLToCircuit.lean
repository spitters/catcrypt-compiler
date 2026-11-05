/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QTree
public import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.GateUnitarity

/-!
# Translation from QTree (QPL Syntax) to QCircuit

This file defines a translation from the unitary fragment of `QTree`
(the QPL-style computation tree) to `Circuit` (the SQIR-style gate IR).

## Design

`QTree d alpha` allows arbitrary `QComp d alpha` operations, while `Circuit n`
only allows gates from a fixed universal gate set.  A general translation is
not possible, so we restrict to the **unitary fragment**: `QTree (2^n) Unit`
programs where every operation is a unitary channel.

Circuits are read through `GateUnitarity.unitaryDenote`, which sends a gate `g`
to the channel `ρ ↦ U ρ U†` for `U = gateEmbedding g`.

## Main definitions

* `GateDecomp` -- typeclass: a `QComp (2^n) Unit` that decomposes into a circuit
* `UnitaryTree` -- inductive type of unitary QTree programs (with circuit witness)
* `translateGate` -- embed a `Gate n` as a `QComp (2^n) Unit`
* `toCircuit` -- translate a `UnitaryTree` to a `Circuit`
* `UnitaryTree.circuitsBounded` -- every node's circuit has bounded gate count
* `toCircuit_correct` -- correctness: `unitaryDenote` of the circuit is the
  compiled `QComp` of the tree
* `toCircuit_cost` -- cost bound: gate count bounded by query cost

## References

* Hietala et al. -- A Verified Optimizer for Quantum Circuits (POPL 2021)
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum CatCrypt.Quantum.QCircuit CatCrypt.Quantum.UnitaryChannel
open CatCrypt.Quantum.GateUnitarity
open scoped Matrix ComplexOrder ENNReal

noncomputable section

namespace CatCrypt.Quantum.QPLToCircuit

variable {n : ℕ}

/-! ## GateDecomp: QComp operations that decompose into gate sequences -/

/-- A `QComp (2^n) Unit` that can be decomposed into a circuit of gates.

    The `correct` field states that the circuit's unitary-channel semantics
    equals the original QComp operation. -/
class GateDecomp (n : ℕ) (C : QComp (2 ^ n) Unit) where
  /-- The circuit that implements `C`. -/
  circuit : Circuit n
  /-- The circuit's unitary-channel semantics equals `C`. -/
  correct : unitaryDenote circuit = C

/-! ## Translating Gates to QComp -/

/-- Embed a `Gate n` as a `QComp (2^n) Unit`: the unitary channel
    `ρ ↦ U ρ U†` for `U = gateEmbedding g`. -/
def translateGate (g : Gate n) : QComp (2 ^ n) Unit :=
  denoteGateU g

/-- Every gate decomposes into the single-gate circuit. -/
instance gateDecomp_single (g : Gate n) : GateDecomp n (denoteGateU g) where
  circuit := Circuit.single g
  correct := by
    simp only [Circuit.single, unitaryDenote]
    show QComp.qbind (denoteGateU g) (fun _ => QComp.qpure ()) = denoteGateU g
    have : (fun (_ : Unit) => QComp.qpure (d := 2 ^ n) ()) = QComp.qpure :=
      funext (fun () => rfl)
    rw [this, QComp.qbind_qpure]

/-! ## UnitaryTree: Unitary fragment of QTree with circuit decomposition -/

/-- A `UnitaryTree n` is a syntactic representation of a unitary quantum
    program on `n` qubits where every operation carries its own circuit
    decomposition.

    * `ret` -- the trivial program returning `()`.
    * `op C circ hcirc k` -- apply operation `C` (decomposed by `circ`),
      then continue with `k`. The decomposition proof `hcirc` witnesses
      that `unitaryDenote circ = C`. -/
inductive UnitaryTree (n : ℕ) : Type 1 where
  | ret : UnitaryTree n
  | op (C : QComp (2 ^ n) Unit) (circ : Circuit n) (hcirc : unitaryDenote circ = C)
       (k : UnitaryTree n) : UnitaryTree n

namespace UnitaryTree

/-- Erase the circuit witness and produce the underlying `QTree`. -/
def toQTree : UnitaryTree n → QTree (2 ^ n) Unit
  | .ret => .ret ()
  | .op C _ _ k => .op Unit inferInstance C (fun () => k.toQTree)

/-- Compile a `UnitaryTree` to its QComp semantics (via `QTree.compile`). -/
def compile (t : UnitaryTree n) : QComp (2 ^ n) Unit :=
  t.toQTree.compile

/-- Query cost of the unitary tree (number of operations). -/
def cost : UnitaryTree n → ℕ
  | .ret => 0
  | .op _ _ _ k => 1 + k.cost

/-! ## Translation to Circuit -/

/-- Translate a `UnitaryTree` to a `Circuit`.

    * `ret` becomes the empty circuit (identity).
    * `op C circ _ k` becomes `circ ; toCircuit k`. -/
def toCircuit : UnitaryTree n → Circuit n
  | .ret => Circuit.empty
  | .op _ circ _ k => Circuit.seq circ k.toCircuit

/-! ## Correctness -/

/-- The translation preserves the unitary-channel semantics: the circuit
    produced by `toCircuit` denotes the same QComp as compiling the
    UnitaryTree. -/
theorem toCircuit_correct (t : UnitaryTree n) :
    unitaryDenote t.toCircuit = t.compile := by
  induction t with
  | ret => simp [toCircuit, compile, toQTree, unitaryDenote]
  | op C circ hcirc k ih =>
    simp only [toCircuit, compile, toQTree, unitaryDenote, QTree.compile]
    rw [hcirc]
    congr 1
    funext ()
    exact ih

/-! ## Cost Bound -/

/-- Every operation of the tree is decomposed by a circuit of at most
    `maxGates` gates. -/
def circuitsBounded (maxGates : ℕ) : UnitaryTree n → Prop
  | .ret => True
  | .op _ circ _ k => circ.gateCount ≤ maxGates ∧ k.circuitsBounded maxGates

/-- The gate count of the translated circuit is bounded by the cost
    of the original UnitaryTree, when every operation is decomposed by a
    single-gate circuit. -/
theorem toCircuit_cost (t : UnitaryTree n) (hsize : t.circuitsBounded 1) :
    t.toCircuit.gateCount ≤ t.cost := by
  induction t with
  | ret => simp [toCircuit, cost]
  | op C circ hcirc k ih =>
    simp only [toCircuit, Circuit.gateCount, cost]
    have hc := hsize.1
    have hk := ih hsize.2
    omega

/-- General cost bound: gate count is bounded by `cost * maxGates` when every
    operation is decomposed by a circuit of at most `maxGates` gates. -/
theorem toCircuit_cost_general (t : UnitaryTree n) (maxGates : ℕ)
    (hsize : t.circuitsBounded maxGates) :
    t.toCircuit.gateCount ≤ t.cost * maxGates := by
  induction t with
  | ret => simp [toCircuit, cost]
  | op C circ hcirc k ih =>
    simp only [toCircuit, Circuit.gateCount, cost]
    have hc := hsize.1
    have hk := ih hsize.2
    calc circ.gateCount + k.toCircuit.gateCount
        ≤ maxGates + k.cost * maxGates := by omega
      _ = (1 + k.cost) * maxGates := by ring

end UnitaryTree

/-! ## Smart Constructors -/

/-- Build a `UnitaryTree` node from a gate. -/
def UnitaryTree.gate (g : Gate n) (k : UnitaryTree n) : UnitaryTree n :=
  .op (denoteGateU g) (Circuit.single g) (GateDecomp.correct (self := gateDecomp_single g)) k

/-- A node built by `UnitaryTree.gate` carries a one-gate circuit, so the
    one-gate bound propagates from the continuation. -/
theorem UnitaryTree.circuitsBounded_gate (g : Gate n) (k : UnitaryTree n)
    (hk : k.circuitsBounded 1) : (UnitaryTree.gate g k).circuitsBounded 1 :=
  ⟨le_of_eq (gateCount_single g), hk⟩

/-! ## Examples: Concrete Gate Programs as UnitaryTrees -/

/-- A single Hadamard gate on qubit `i` as a UnitaryTree. -/
def hadamardTree (i : Fin n) : UnitaryTree n :=
  .gate (.H i) .ret

/-- The Hadamard tree has cost 1. -/
theorem cost_hadamard (i : Fin n) :
    (hadamardTree i).cost = 1 := by
  simp [hadamardTree, UnitaryTree.gate, UnitaryTree.cost]

/-- Translating the Hadamard tree produces a circuit with 1 gate. -/
theorem toCircuit_gateCount_hadamard (i : Fin n) :
    (hadamardTree i).toCircuit.gateCount = 1 := by
  simp [hadamardTree, UnitaryTree.gate, UnitaryTree.toCircuit,
        Circuit.gateCount, Circuit.single]

/-- A CNOT followed by a Hadamard as a UnitaryTree. -/
def cnotThenH (ctrl tgt hq : Fin n) : UnitaryTree n :=
  .gate (.CNOT ctrl tgt) (.gate (.H hq) .ret)

/-- The CNOT-then-H program has cost 2. -/
theorem cost_cnotThenH (ctrl tgt hq : Fin n) :
    (cnotThenH ctrl tgt hq).cost = 2 := by
  simp [cnotThenH, UnitaryTree.gate, UnitaryTree.cost]

/-- Translating CNOT-then-H yields a two-gate circuit. -/
theorem toCircuit_gateCount_cnotThenH (ctrl tgt hq : Fin n) :
    (cnotThenH ctrl tgt hq).toCircuit.gateCount = 2 := by
  simp [cnotThenH, UnitaryTree.gate, UnitaryTree.toCircuit,
        Circuit.gateCount, Circuit.single]

/-- The CNOT-then-H translation preserves the unitary-channel semantics. -/
theorem toCircuit_correct_cnotThenH (ctrl tgt hq : Fin n) :
    unitaryDenote (cnotThenH ctrl tgt hq).toCircuit =
      (cnotThenH ctrl tgt hq).compile :=
  UnitaryTree.toCircuit_correct _

/-! ## Composition -/

/-- Sequential composition of UnitaryTrees. -/
def UnitaryTree.seq : UnitaryTree n → UnitaryTree n → UnitaryTree n
  | .ret, t₂ => t₂
  | .op C circ hcirc k, t₂ => .op C circ hcirc (k.seq t₂)

/-- Cost of sequential composition is additive. -/
theorem UnitaryTree.cost_seq (t₁ t₂ : UnitaryTree n) :
    (t₁.seq t₂).cost = t₁.cost + t₂.cost := by
  induction t₁ with
  | ret => simp [seq, cost]
  | op C circ hcirc k ih => simp only [seq, cost, ih]; omega

/-- Translation of sequential composition equals circuit sequential composition
    (up to denotational equivalence). -/
theorem UnitaryTree.toCircuit_seq_correct (t₁ t₂ : UnitaryTree n) :
    (t₁.seq t₂).compile = QComp.qbind t₁.compile (fun () => t₂.compile) := by
  induction t₁ with
  | ret =>
    simp only [seq, compile, toQTree, QTree.compile]
    exact (QComp.qpure_qbind () (fun () => t₂.compile)).symm
  | op C circ hcirc k ih =>
    simp only [seq, compile, toQTree, QTree.compile]
    rw [QComp.qbind_assoc]
    congr 1
    funext ()
    exact ih

end CatCrypt.Quantum.QPLToCircuit
