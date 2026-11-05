/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QTree
public import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.QPLToCircuit
public import CatCrypt.Quantum.GateUnitarity
public import CatCrypt.Quantum.UnitaryChannel
public import CatCrypt.Quantum.Measurement
public import CatCrypt.Quantum.Programs.Qubit

@[expose] public section

set_option autoImplicit false

/-!
# QPL: Quantum Programming Language

A typed quantum programming language (following Selinger 2004) with
denotational semantics into `QComp` and compilation to circuits.

## Language Design

QPL programs operate on an `n`-qubit register (Hilbert space `ℂ^{2^n}`).
The language provides:
- **Gate application**: apply a gate from the Clifford+T universal set
- **Measurement**: measure a qubit in the computational basis, branch on result
- **Classical control**: choose different continuations based on measurement outcomes
- **Sequential composition**: `QPL.bind`, substitution at the `ret` leaves
- **Reset**: the derived program `reset i k` measures qubit `i` and applies `X` on
  outcome `|1⟩`, leaving qubit `i` in `|0⟩` (`reset_qubit_zero`)

## Key Difference from UnitaryTree

`UnitaryTree` restricts to unitary operations (no measurement, no branching).
`QPL` supports **measurement + classical branching**, compiled to circuits via
the **deferred measurement principle**: measurements can be pushed to the end
of a circuit, with classically-controlled gates replacing conditional branches.

## Main definitions

* `QPL n α` — QPL program on `n` qubits with classical output `α`
* `QPL.denote` — denotational semantics into `QComp (2^n) α`
* `QPL.toQTree` — compilation to `QTree` (intermediate representation)
* `QPL.gateCount` — gate complexity metric
* `QPL.deferMeasurement` — deferred measurement compilation to `UnitaryTree`

## Compilation Pipeline

```
QPL n α  ──denote──▶  QComp (2^n) α     (denotational semantics)
   │
   ├──toQTree──▶  QTree (2^n) α          (intermediate, preserves branching)
   │
   └──deferCirc──▶  Circuit (n+k)        (deferred measurement: one ancilla per
                                         measurement node, branches controlled on it)
```

## References

* Selinger, P. — *Towards a Quantum Programming Language*, MSCS 2004
* Nielsen & Chuang — *QCQI*, §4.4 (deferred measurement)
* Rand et al. — *QWIRE: A Core Language for Quantum Circuits*, POPL 2017
-/

open CatCrypt.Quantum CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement
open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.QPLToCircuit
open scoped Matrix ComplexOrder ENNReal

noncomputable section

namespace CatCrypt.Quantum.QPL

variable {n : ℕ}

/-! ## QPL Syntax -/

/-- A QPL program on `n` qubits producing a classical value of type `α`.

    * `ret a` — return classical value `a`
    * `gate g k` — apply gate `g`, continue with `k`
    * `meas i kt kf` — measure qubit `i`, branch: `kt` if |1⟩, `kf` if |0⟩
    * `fail` — abort (probability 0 branch)

    Sequential composition is the derived operation `QPL.bind`. -/
inductive QPL (n : ℕ) : Type → Type 1 where
  | ret {α : Type} : α → QPL n α
  | gate {α : Type} : Gate n → QPL n α → QPL n α
  | meas {α : Type} : Fin n → QPL n α → QPL n α → QPL n α
  | fail {α : Type} : QPL n α

namespace QPL

variable {α β : Type}

/-! ## Computational-basis measurement of one qubit -/

/-- The single-qubit projector onto `|1⟩` for `true` and onto `|0⟩` for `false`. -/
def qubitProj (b : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  if b then !![0, 0; 0, 1] else !![1, 0; 0, 0]

theorem qubitProj_conjTranspose (b : Bool) : (qubitProj b)ᴴ = qubitProj b := by
  cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [qubitProj]

theorem qubitProj_mul_self (b : Bool) : qubitProj b * qubitProj b = qubitProj b := by
  cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [qubitProj, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two single-qubit projectors sum to the identity. -/
theorem qubitProj_false_add_true : qubitProj false + qubitProj true = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qubitProj]

/-- The projective measurement of qubit `i` of an `n`-qubit register in the
    computational basis: outcome `b` has projector `embedGate1 n i (qubitProj b)`,
    with `true` for `|1⟩` and `false` for `|0⟩`. -/
def measQubitPM (i : Fin n) : ProjectiveMeasurement (2 ^ n) Bool where
  op b := embedGate1 n i (qubitProj b)
  completeness := by
    rw [Fintype.sum_bool]
    simp only [GateUnitarity.embedGate1_conjTranspose, GateUnitarity.embedGate1_mul,
      qubitProj_conjTranspose, qubitProj_mul_self]
    rw [← GateUnitarity.embedGate1_map_add, add_comm, qubitProj_false_add_true, GateUnitarity.embedGate1_one]
  self_adjoint b := by
    rw [GateUnitarity.embedGate1_conjTranspose, qubitProj_conjTranspose]
  idempotent b := by
    rw [GateUnitarity.embedGate1_mul, qubitProj_mul_self]

/-- The instrument measuring qubit `i` in the computational basis. -/
def measQubit (i : Fin n) : QComp (2 ^ n) Bool :=
  projectiveMeasure (measQubitPM i)

/-! ## Denotational Semantics -/

/-- Denotational semantics: interpret a QPL program as a `QComp`.

    * `ret a` → `qpure a`
    * `gate g k` → `denoteGateU g >>= fun () => k.denote`
    * `meas i kt kf` → `measQubit i >>= fun b => if b then kt.denote else kf.denote`
    * `fail` → `qfail` -/
def denote : QPL n α → QComp (2 ^ n) α
  | .ret a => QComp.qpure a
  | .gate g k => QComp.qbind (GateUnitarity.denoteGateU g) (fun () => k.denote)
  | .meas i kt kf =>
    QComp.qbind (measQubit i) fun b => if b then kt.denote else kf.denote
  | .fail => QComp.qfail

/-- Translate QPL to QTree (preserving measurement structure). -/
def toQTree : QPL n α → QTree (2 ^ n) α
  | .ret a => .ret a
  | .gate g k => .op Unit inferInstance (GateUnitarity.denoteGateU g) (fun () => k.toQTree)
  | .meas i kt kf =>
    .op Bool inferInstance (measQubit i) (fun b => if b then kt.toQTree else kf.toQTree)
  | .fail => .fail

/-! ## Gate Count -/

/-- Gate count: number of gate + measurement operations on longest path. -/
def gateCount : QPL n α → ℕ
  | .ret _ => 0
  | .gate _ k => 1 + k.gateCount
  | .meas _ kt kf => 1 + max kt.gateCount kf.gateCount
  | .fail => 0

/-! ## Structural Properties -/

@[simp] theorem denote_ret (a : α) :
    (QPL.ret a : QPL n α).denote = QComp.qpure a := rfl

@[simp] theorem denote_fail :
    (QPL.fail : QPL n α).denote = QComp.qfail := rfl

theorem denote_gate (g : Gate n) (k : QPL n α) :
    (QPL.gate g k).denote = QComp.qbind (GateUnitarity.denoteGateU g) (fun () => k.denote) :=
  rfl

theorem denote_meas (i : Fin n) (kt kf : QPL n α) :
    (QPL.meas i kt kf).denote =
      QComp.qbind (measQubit i) (fun b => if b then kt.denote else kf.denote) :=
  rfl

@[simp] theorem gateCount_ret (a : α) :
    (QPL.ret a : QPL n α).gateCount = 0 := rfl

@[simp] theorem gateCount_fail :
    (QPL.fail : QPL n α).gateCount = 0 := rfl

theorem gateCount_gate (g : Gate n) (k : QPL n α) :
    (QPL.gate g k).gateCount = 1 + k.gateCount := rfl

theorem gateCount_meas (i : Fin n) (kt kf : QPL n α) :
    (QPL.meas i kt kf).gateCount = 1 + max kt.gateCount kf.gateCount := rfl

/-! ## Monadic Bind -/

/-- Monadic bind: substitute at `ret` leaves. -/
def bind : QPL n α → (α → QPL n β) → QPL n β
  | .ret a, f => f a
  | .gate g k, f => .gate g (k.bind f)
  | .meas i kt kf, f => .meas i (kt.bind f) (kf.bind f)
  | .fail, _ => .fail

@[simp] theorem bind_ret (a : α) (f : α → QPL n β) :
    (QPL.ret a).bind f = f a := rfl

@[simp] theorem bind_fail (f : α → QPL n β) :
    (QPL.fail : QPL n α).bind f = .fail := rfl

theorem bind_gate (g : Gate n) (k : QPL n α) (f : α → QPL n β) :
    (QPL.gate g k).bind f = .gate g (k.bind f) := rfl

theorem bind_meas (i : Fin n) (kt kf : QPL n α) (f : α → QPL n β) :
    (QPL.meas i kt kf).bind f = .meas i (kt.bind f) (kf.bind f) := rfl

/-! ## Deferred Measurement Principle

The deferred measurement principle says that any QPL program with
mid-circuit measurements can be transformed into an equivalent program
that:
1. Adds ancilla qubits for each measurement
2. Replaces measurements with CNOTs to ancillae
3. Uses classically-controlled gates (controlled on ancillae)
4. Measures all ancillae at the end

This transforms `QPL n α` (with measurements) into `QPL (n + k) Unit`
(measurement-free), where `k` is the number of mid-circuit measurements. -/

/-- Count the number of measurement operations in a QPL program. -/
def measCount : QPL n α → ℕ
  | .ret _ => 0
  | .gate _ k => k.measCount
  | .meas _ kt kf => 1 + kt.measCount + kf.measCount
  | .fail => 0

/-- A QPL program is measurement-free (purely unitary). -/
def isMeasFree : QPL n α → Prop
  | .ret _ => True
  | .gate _ k => k.isMeasFree
  | .meas _ _ _ => False
  | .fail => False

/-- A measurement-free QPL program can be converted to a UnitaryTree. -/
def toUnitaryTree : (p : QPL n Unit) → p.isMeasFree →
    CatCrypt.Quantum.QPLToCircuit.UnitaryTree n
  | .ret (), _ => .ret
  | .gate g k, h => .op (GateUnitarity.denoteGateU g) (Circuit.single g)
      (CatCrypt.Quantum.QPLToCircuit.GateDecomp.correct
        (self := CatCrypt.Quantum.QPLToCircuit.gateDecomp_single g))
      (k.toUnitaryTree h)
  | .fail, _ => .ret  -- fail → identity (vacuously measurement-free)

/-! ## Example Programs -/

/-- Hadamard on qubit i, then return. -/
def hadamard (i : Fin n) : QPL n Unit :=
  .gate (.H i) (.ret ())

/-- CNOT controlled by c targeting t, then return. -/
def cnot (c t : Fin n) : QPL n Unit :=
  .gate (.CNOT c t) (.ret ())

/-- Measure qubit i and return the result as a Bool. -/
def measure (i : Fin n) : QPL n Bool :=
  .meas i (.ret true) (.ret false)

/-- Prepare Bell state: H on qubit 0, CNOT 0→1. -/
def prepareBell : QPL 2 Unit :=
  .gate (.H 0) (.gate (.CNOT 0 1) (.ret ()))

/-- Teleportation protocol in QPL:
    Given 3 qubits (0 = Alice's state, 1-2 = shared Bell pair):
    1. CNOT 0→1
    2. H on 0
    3. Measure 0 and 1
    4. Classically-controlled corrections on qubit 2 -/
def teleport : QPL 3 (Bool × Bool) :=
  .gate (.CNOT 0 1)
    (.gate (.H 0)
      (.meas 0
        -- qubit 0 measured |1⟩
        (.meas 1
          (.gate (.X 2) (.gate (.Z 2) (.ret (true, true))))    -- both |1⟩
          (.gate (.Z 2) (.ret (true, false))))                  -- 0=|1⟩, 1=|0⟩
        -- qubit 0 measured |0⟩
        (.meas 1
          (.gate (.X 2) (.ret (false, true)))                   -- 0=|0⟩, 1=|1⟩
          (.ret (false, false)))))                               -- both |0⟩

/-- BB84 prepare-and-measure in QPL:
    Prepare qubit in basis b with bit x, then measure. -/
def bb84Round : QPL 1 Bool :=
  -- Prepare: H if basis=1, X if bit=1 (simplified: just H then measure)
  .gate (.H 0) (measure 0)

/-! ## Properties of Examples -/

theorem prepareBell_isMeasFree : prepareBell.isMeasFree := trivial

theorem prepareBell_gateCount : prepareBell.gateCount = 2 := rfl

theorem teleport_measCount : teleport.measCount = 3 := rfl

theorem bb84Round_measCount : bb84Round.measCount = 1 := rfl

/-! ## Full Compilation Pipeline -/

/-- Compile a measurement-free QPL program all the way to a Circuit. -/
def toCircuit (p : QPL n Unit) (h : p.isMeasFree) : Circuit n :=
  (p.toUnitaryTree h).toCircuit

/-- Full pipeline cost bound. -/
theorem toCircuit_gateCount_le (p : QPL n Unit) (h : p.isMeasFree) :
    (p.toCircuit h).gateCount ≤ p.gateCount := by
  induction p with
  | ret a => cases a; simp [toCircuit, toUnitaryTree, UnitaryTree.toCircuit]
  | gate g k ih =>
    have hk : k.isMeasFree := h
    have ihk := ih hk
    simp only [toCircuit, toUnitaryTree, UnitaryTree.toCircuit, Circuit.gateCount,
      gateCount_single, gateCount_gate]
    exact Nat.add_le_add_left ihk 1
  | meas i kt kf => exact absurd h (by simp [isMeasFree])
  | fail => exact absurd h id

/-! ## Reset -/

/-- Reset of qubit `i`, then `k`: measure qubit `i`, apply `X` to it on outcome `|1⟩`,
    and continue with `k` on both branches. -/
def reset (i : Fin n) (k : QPL n α) : QPL n α :=
  .meas i (.gate (.X i) k) k

/-- The reset channel: on `ρ`, `reset i (ret ())` outputs
    `X P₁ ρ P₁ X† + P₀ ρ P₀`, where `P_b` is the projector of qubit `i` onto `|b⟩`
    and `X` the embedded Pauli X on qubit `i`. -/
theorem denote_reset (i : Fin n) (ρ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    (reset i (.ret ())).denote.branch () ρ =
      gateEmbedding (.X i) * (embedGate1 n i (qubitProj true) * ρ *
          embedGate1 n i (qubitProj true)) * (gateEmbedding (.X i))ᴴ +
        embedGate1 n i (qubitProj false) * ρ * embedGate1 n i (qubitProj false) := by
  simp only [reset, denote, QComp.qbind, measQubit, projectiveMeasure, measureOps, measQubitPM,
    GateUnitarity.denoteGateU, unitaryChannel, GateUnitarity.gateEmbedding_unitaryGroup,
    QComp.qpure, LinearMap.coe_mk, AddHom.coe_mk, tsum_fintype, Fintype.sum_bool, ite_true,
    Bool.false_eq_true, ite_false, Fintype.univ_punit, Finset.sum_singleton, LinearMap.id_apply,
    conjugate_apply, GateUnitarity.embedGate1_conjTranspose, qubitProj_conjTranspose,
    Matrix.mul_assoc]

/-- On one qubit, the projector onto `|1⟩` annihilates `X` conjugated by itself and the
    projector onto `|0⟩`. -/
theorem qubitProj_true_mul_pauliX_mul :
    qubitProj true * pauliX * qubitProj true = 0 ∧
      qubitProj true * qubitProj false = 0 := by
  constructor <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [qubitProj, pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- After `reset i`, qubit `i` is in `|0⟩`: the projector of qubit `i` onto `|1⟩`
    annihilates the output state of `reset i (ret ())` on every input `ρ`. -/
theorem reset_qubit_zero (i : Fin n) (ρ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    embedGate1 n i (qubitProj true) * (reset i (.ret ())).denote.branch () ρ = 0 := by
  rw [denote_reset]
  simp only [gateEmbedding, mul_add, ← Matrix.mul_assoc, GateUnitarity.embedGate1_mul,
    qubitProj_true_mul_pauliX_mul.1, qubitProj_true_mul_pauliX_mul.2,
    GateUnitarity.embedGate1_map_zero, zero_mul, add_zero]

end QPL

end CatCrypt.Quantum.QPL
