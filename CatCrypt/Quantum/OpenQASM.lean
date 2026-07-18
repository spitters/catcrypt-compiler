/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Quantum.QCircuit

set_option autoImplicit false

/-!
# OpenQASM 3.0 Export for Quantum Circuits

Translates `Circuit n` (the SQIR-style gate IR) into OpenQASM 3.0 text format.

## Main Definitions

* `Gate.toQASM` — translate a single gate to QASM syntax
* `toGateList` — flatten a circuit to a list of gates
* `Circuit.toQASM` — full QASM 3.0 program with header
* `toGateList_length` — gate list length equals gate count

## OpenQASM 3.0 Format

```qasm
OPENQASM 3.0;
include "stdgates.inc";
qubit[n] q;
h q[0];
cx q[0], q[1];
```

## References

* Cross et al. — *OpenQASM 3: A Broader and Deeper Quantum Assembly Language*,
  ACM Transactions on Quantum Computing 3(3), 2022
-/

namespace CatCrypt.Quantum.OpenQASM

open CatCrypt.Quantum.QCircuit

variable {n : ℕ}

/-! ## Gate to QASM String -/

/-- Translate a single gate to its OpenQASM 3.0 string representation.

    Maps each gate in the Clifford+T universal set to standard QASM syntax:
    - Single-qubit gates: `h q[i];`, `x q[i];`, etc.
    - Two-qubit gates: `cx q[c], q[t];`, `cz q[c], q[t];`
    - Parameterized gates: `rz(theta) q[i];`
    - Measurement: `measure q[i];` -/
def Gate.toQASM : Gate n → String
  | .H i    => s!"h q[{i.val}];"
  | .X i    => s!"x q[{i.val}];"
  | .Y i    => s!"y q[{i.val}];"
  | .Z i    => s!"z q[{i.val}];"
  | .T i    => s!"t q[{i.val}];"
  | .Tdg i  => s!"tdg q[{i.val}];"
  | .S i    => s!"s q[{i.val}];"
  | .CNOT c t => s!"cx q[{c.val}], q[{t.val}];"
  | .CZ c t   => s!"cz q[{c.val}], q[{t.val}];"
  | .Rz i _θ  => s!"rz(theta) q[{i.val}];"  -- θ : ℝ has no ToString
  | .Meas i    => s!"measure q[{i.val}];"

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

/-- Join a list of strings with newlines. -/
def joinLines (ls : List String) : String :=
  ls.foldl (fun acc s => if acc.isEmpty then s else acc ++ "\n" ++ s) ""

/-- Generate the body of a QASM program: one gate per line. -/
def gateListToQASM (gs : List (Gate n)) : String :=
  joinLines (gs.map Gate.toQASM)

/-- The OpenQASM 3.0 header with qubit declaration. -/
def qasmHeader (numQubits : ℕ) : String :=
  s!"OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[{numQubits}] q;"

/-- Translate a full circuit to an OpenQASM 3.0 program string.

    Produces a complete, valid QASM program:
    ```qasm
    OPENQASM 3.0;
    include "stdgates.inc";
    qubit[n] q;
    <gate instructions>
    ``` -/
def toQASMStr (c : Circuit n) : String :=
  let header := qasmHeader n
  let body := gateListToQASM (toGateList c)
  if body.isEmpty then header else header ++ "\n" ++ body

/-! ## Structural Properties -/

/-- Empty circuit produces a program with only the header. -/
theorem toQASM_empty :
    toQASMStr (Circuit.empty : Circuit n) = qasmHeader n := by
  rfl

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

/-- Bell circuit QASM output. -/
theorem bellCircuit_qasm :
    toQASMStr bellCircuit =
      "OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[2] q;\nh q[0];\ncx q[0], q[1];" := by
  native_decide

/-- GHZ-3 circuit: H, CNOT 0→1, CNOT 1→2. -/
def ghz3Circuit : Circuit 3 :=
  .gate (.H 0) (.gate (.CNOT 0 1) (.gate (.CNOT 1 2) .empty))

/-- GHZ-3 circuit has 3 gates. -/
theorem ghz3_gateCount : ghz3Circuit.gateCount = 3 := rfl

end CatCrypt.Quantum.OpenQASM
