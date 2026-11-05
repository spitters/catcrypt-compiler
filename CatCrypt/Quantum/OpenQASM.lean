/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit

/-!
# OpenQASM 3.0 Export for Quantum Circuits

Translates `Circuit n` (the SQIR-style gate IR) into OpenQASM 3.0 text format.
There is one emitter, `emitDQASM`, over the exact gate set `DGate n`, whose `Rz`
angle is a rational multiple of `π` (`QasmAngle`). A `Circuit n` is printed by
mapping each gate into `DGate n` with `DGate.ofGate?`; a real-valued `Gate.Rz`
has no finite QASM literal, so `DGate.ofGate?` declines it, and `toQASMStr`
returns `none` for a circuit that contains one. An `RzQ` angle `a + b·π` is
printed by `PiLin.toQASM` as `num/den+k*pi/d`, for instance `-1/3+pi/2`.

## Main definitions

* `PiLin.toQASM` — an exact angle as an OpenQASM 3.0 angle expression
* `DGate` — the gate set with exact angles
* `DGate.ofGate?` — the partial map `Gate n → DGate n`, `none` on a real `Rz`
* `DGate.toQASM` — one gate as an OpenQASM 3.0 statement
* `emitDQASM` — full QASM 3.0 program for a list of exact gates
* `toGateList` — flatten a circuit to a list of gates
* `toQASMStr` — full QASM 3.0 program for a circuit over the exact gate set
* `toGateList_length` — gate list length equals gate count

## OpenQASM 3.0 Format

```qasm
OPENQASM 3.0;
include "stdgates.inc";
qubit[n] q;
h q[0];
cx q[0], q[1];
rz(pi/4) q[1];
```

## References

* Cross et al. — *OpenQASM 3: A Broader and Deeper Quantum Assembly Language*,
  ACM Transactions on Quantum Computing 3(3), 2022
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum

open CatCrypt.Quantum.QCircuit

namespace PiLin

/-- An exact angle `a + b·π` as an OpenQASM 3.0 angle expression: the rational
part `a` as `num/den` (`num` when `den = 1`), then `+`, then the `π` part `b` as
`QasmAngle.toQASM` prints it. A zero rational part is omitted, a zero `π` part
is omitted when the rational part is not zero, and the zero angle is `0`. -/
def toQASM (p : PiLin) : String :=
  if p.a = 0 then QasmAngle.toQASM p.b
  else if p.b = 0 then toString p.a
  else s!"{p.a}+{QasmAngle.toQASM p.b}"

@[simp] theorem toQASM_ofPi (q : QasmAngle) : (ofPi q).toQASM = QasmAngle.toQASM q := by
  simp [toQASM]

end PiLin

/-- A gate of the exact gate set: identical to `Gate` except that the only
rotation is `Rz` by an exact angle `PiLin` (`a + b·π` with rational `a`, `b`).
Every gate of this set has a finite OpenQASM 3.0 literal. -/
inductive DGate (n : ℕ) : Type where
  | H : Fin n → DGate n
  | X : Fin n → DGate n
  | Y : Fin n → DGate n
  | Z : Fin n → DGate n
  | T : Fin n → DGate n
  | Tdg : Fin n → DGate n
  | S : Fin n → DGate n
  | CNOT : Fin n → Fin n → DGate n
  | CZ : Fin n → Fin n → DGate n
  | Rz : Fin n → PiLin → DGate n
  deriving DecidableEq, Repr

namespace DGate

variable {n : ℕ}

/-- The partial map from `Gate` to the exact gate set: `RzQ` by `p` becomes
`Rz` by `p`, and the real-valued `Gate.Rz` is declined. -/
def ofGate? : Gate n → Option (DGate n)
  | .H i => some (.H i)
  | .X i => some (.X i)
  | .Y i => some (.Y i)
  | .Z i => some (.Z i)
  | .T i => some (.T i)
  | .Tdg i => some (.Tdg i)
  | .S i => some (.S i)
  | .CNOT c t => some (.CNOT c t)
  | .CZ c t => some (.CZ c t)
  | .Rz _ _ => none
  | .RzQ i p => some (.Rz i p)

/-- An exact gate as one OpenQASM 3.0 statement; the `Rz` angle is printed by
`PiLin.toQASM`. -/
def toQASM : DGate n → String
  | .H i => s!"h q[{i.val}];"
  | .X i => s!"x q[{i.val}];"
  | .Y i => s!"y q[{i.val}];"
  | .Z i => s!"z q[{i.val}];"
  | .T i => s!"t q[{i.val}];"
  | .Tdg i => s!"tdg q[{i.val}];"
  | .S i => s!"s q[{i.val}];"
  | .CNOT c t => s!"cx q[{c.val}], q[{t.val}];"
  | .CZ c t => s!"cz q[{c.val}], q[{t.val}];"
  | .Rz i q => s!"rz({PiLin.toQASM q}) q[{i.val}];"

end DGate

namespace OpenQASM

variable {n : ℕ}

/-! ## Program text -/

/-- Join a list of strings with newlines. -/
def joinLines (ls : List String) : String :=
  "\n".intercalate ls

/-- The three header lines of an OpenQASM 3.0 program on `numQubits` qubits. -/
def qasmHeaderLines (numQubits : ℕ) : List String :=
  ["OPENQASM 3.0;", "include \"stdgates.inc\";", s!"qubit[{numQubits}] q;"]

/-- The OpenQASM 3.0 header with qubit declaration. -/
def qasmHeader (numQubits : ℕ) : String :=
  joinLines (qasmHeaderLines numQubits)

/-- The OpenQASM 3.0 program of a list of exact gates: the header, then one
statement per line. -/
def emitDQASM (n : ℕ) (gs : List (DGate n)) : String :=
  joinLines (qasmHeaderLines n ++ gs.map DGate.toQASM)

/-! ## Gate to QASM String -/

/-- A gate as an OpenQASM 3.0 statement, through the exact gate set; `none` for a
real-valued `Rz`. -/
def Gate.toQASM (g : Gate n) : Option String :=
  (DGate.ofGate? g).map DGate.toQASM

/-! ## Circuit to Gate List -/

/-- Flatten a circuit into a list of gates (applied left-to-right). -/
def toGateList : Circuit n → List (Gate n)
  | .empty      => []
  | .gate g c   => g :: toGateList c
  | .seq c₁ c₂  => toGateList c₁ ++ toGateList c₂

/-! ## Gate List Properties -/

@[simp]
theorem toGateList_empty :
    toGateList (Circuit.empty : Circuit n) = [] := rfl

@[simp]
theorem toGateList_gate (g : Gate n) (c : Circuit n) :
    toGateList (Circuit.gate g c) = g :: toGateList c := rfl

@[simp]
theorem toGateList_seq (c₁ c₂ : Circuit n) :
    toGateList (Circuit.seq c₁ c₂) = toGateList c₁ ++ toGateList c₂ := rfl

/-- The gate list length equals the circuit's gate count. -/
theorem toGateList_length (c : Circuit n) :
    (toGateList c).length = c.gateCount := by
  induction c with
  | empty => rfl
  | gate g c ih => simp [toGateList, Circuit.gateCount, ih]; omega
  | seq c₁ c₂ ih₁ ih₂ => simp [toGateList, Circuit.gateCount, ih₁, ih₂]

/-- Round-tripping: `ofList (toGateList c)` has the same gate count. -/
theorem ofList_toGateList_gateCount (c : Circuit n) :
    (Circuit.ofList (toGateList c)).gateCount = c.gateCount := by
  rw [gateCount_ofList, toGateList_length]

/-! ## QASM Program Generation -/

/-- The gate list of a circuit in the exact gate set; `none` when the circuit
contains a real-valued `Rz`. -/
def toDGateList (c : Circuit n) : Option (List (DGate n)) :=
  (toGateList c).mapM DGate.ofGate?

/-- Translate a circuit over the exact gate set to an OpenQASM 3.0 program
string, `emitDQASM` of its exact gate list; `none` when the circuit contains a
real-valued `Rz`. -/
def toQASMStr (c : Circuit n) : Option String :=
  (toDGateList c).map (emitDQASM n)

/-! ## Structural Properties -/

/-- Empty circuit produces a program with only the header. -/
theorem toQASM_empty :
    toQASMStr (Circuit.empty : Circuit n) = some (qasmHeader n) := by
  simp [toQASMStr, toDGateList, emitDQASM, qasmHeader]

/-- Sequential composition produces concatenated gate lists. -/
theorem toGateList_seq_append (c₁ c₂ : Circuit n) :
    toGateList (Circuit.seq c₁ c₂) = toGateList c₁ ++ toGateList c₂ := rfl

/-! ## Example Circuits -/

/-- Bell circuit: H on qubit 0, CNOT 0→1. -/
def bellCircuit : Circuit 2 :=
  .gate (.H 0) (.gate (.CNOT 0 1) .empty)

/-- Bell circuit gate list. -/
theorem bellCircuit_gateList :
    toGateList bellCircuit = [Gate.H 0, Gate.CNOT 0 1] := rfl

/-- Bell circuit has 2 gates. -/
theorem bellCircuit_gateCount : bellCircuit.gateCount = 2 := rfl

/-- GHZ-3 circuit: H, CNOT 0→1, CNOT 1→2. -/
def ghz3Circuit : Circuit 3 :=
  .gate (.H 0) (.gate (.CNOT 0 1) (.gate (.CNOT 1 2) .empty))

/-- GHZ-3 circuit has 3 gates. -/
theorem ghz3_gateCount : ghz3Circuit.gateCount = 3 := rfl

end OpenQASM

end CatCrypt.Quantum
