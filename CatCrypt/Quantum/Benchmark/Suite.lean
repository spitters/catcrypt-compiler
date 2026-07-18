/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Quantum.QCircuit
import CatCrypt.Quantum.OpenQASM

/-!
# Quantum Circuit Benchmark Suite

A collection of standard quantum circuits used for benchmarking circuit
optimizers and QASM export.  Each circuit is defined concretely and fully proved.

## Main Definitions

* 15 benchmark circuits: Bell, GHZ-3, SWAP, QFT-2, Deutsch-Jozsa,
  Grover-4, H-pair, CNOT-ladder, teleportation, VQE-H2, QAOA-1,
  random Clifford, T-depth-1, phase estimation, Bernstein-Vazirani
* `BenchmarkEntry` -- metadata for a circuit (name, qubit count, gate count, QASM)
* `allBenchmarks` -- list of all benchmark entries

## References

* Cross et al. -- OpenQASM 3: A Broader and Deeper Quantum Assembly Language
* Nielsen & Chuang -- Quantum Computation and Quantum Information
-/

set_option autoImplicit false

namespace CatCrypt.Quantum.Benchmark.Suite

open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.OpenQASM

/-! ## Benchmark Circuits (computable — no Real.pi) -/

/-- Bell state preparation: H on qubit 0, CNOT 0->1. -/
def bell : Circuit 2 :=
  .gate (.H 0) (.gate (.CNOT 0 1) .empty)

/-- GHZ-3 state: H, CNOT 0->1, CNOT 1->2. -/
def ghz3 : Circuit 3 :=
  .gate (.H 0) (.gate (.CNOT 0 1) (.gate (.CNOT 1 2) .empty))

/-- SWAP via three CNOTs. -/
def swap2 : Circuit 2 :=
  .gate (.CNOT 0 1) (.gate (.CNOT 1 0) (.gate (.CNOT 0 1) .empty))

/-- Deutsch-Jozsa for 2 qubits: H, H, oracle (CNOT), H. -/
def deutschJozsa2 : Circuit 2 :=
  .gate (.H 0) (.gate (.H 1) (.gate (.CNOT 0 1) (.gate (.H 0) .empty)))

/-- Grover search for N=4 (2 qubits): superposition, oracle, diffusion (12 gates). -/
def grover4 : Circuit 2 :=
  .gate (.H 0) (.gate (.H 1)
    (.gate (.Z 0)
      (.gate (.H 0) (.gate (.H 1)
        (.gate (.X 0) (.gate (.X 1)
          (.gate (.CZ 0 1)
            (.gate (.X 0) (.gate (.X 1)
              (.gate (.H 0) (.gate (.H 1) .empty)))))))))))

/-- Hadamard pair: H on both qubits. -/
def hPair : Circuit 2 :=
  .gate (.H 0) (.gate (.H 1) .empty)

/-- CNOT ladder on 3 qubits: CNOT 0->1, CNOT 1->2. -/
def cnotLadder3 : Circuit 3 :=
  .gate (.CNOT 0 1) (.gate (.CNOT 1 2) .empty)

/-- Quantum teleportation circuit (3 qubits):
    Create Bell pair (H, CNOT 0->1), then CNOT 1->2, H 1, measure 1. -/
def teleport3 : Circuit 3 :=
  .gate (.H 0)
  (.gate (.CNOT 0 1)
  (.gate (.CNOT 1 2)
  (.gate (.H 1)
  (.gate (.Meas 1)
  .empty))))

/-- Random Clifford circuit (3 qubits): mix of H, S, CNOT. -/
def randomClifford3 : Circuit 3 :=
  .gate (.H 0)
  (.gate (.S 1)
  (.gate (.CNOT 0 1)
  (.gate (.H 2)
  (.gate (.CNOT 1 2)
  (.gate (.S 0)
  (.gate (.H 1)
  .empty))))))

/-- T-depth-1 circuit: single layer of T gates sandwiched by Cliffords. -/
def tDepth1 : Circuit 3 :=
  .gate (.H 0)
  (.gate (.H 1)
  (.gate (.H 2)
  (.gate (.T 0)
  (.gate (.T 1)
  (.gate (.T 2)
  (.gate (.CNOT 0 1)
  (.gate (.CNOT 1 2)
  .empty)))))))

/-- Bernstein-Vazirani for s=1 (2 qubits): H, H, oracle (CNOT), H, H. -/
def bernsteinVazirani2 : Circuit 2 :=
  .gate (.H 0)
  (.gate (.H 1)
  (.gate (.CNOT 0 1)
  (.gate (.H 0)
  (.gate (.H 1)
  .empty))))

/-! ## Benchmark Circuits (noncomputable — use Rz with Real parameters) -/

/-- 2-qubit QFT: H, Rz(pi/2), H, SWAP. -/
noncomputable def qft2 : Circuit 2 :=
  .gate (.H 0)
  (.gate (.Rz 1 (Real.pi / 2))
  (.gate (.H 1)
  (.gate (.CNOT 0 1)
  (.gate (.CNOT 1 0)
  (.gate (.CNOT 0 1)
  .empty)))))

/-- VQE ansatz for H2 molecule (2-qubit): Rz layers + entangling CNOTs. -/
noncomputable def vqeH2 : Circuit 2 :=
  .gate (.Rz 0 0.5)
  (.gate (.Rz 1 0.3)
  (.gate (.CNOT 0 1)
  (.gate (.Rz 0 0.7)
  (.gate (.Rz 1 0.2)
  (.gate (.CNOT 0 1)
  .empty)))))

/-- QAOA layer for MaxCut on 3 vertices: Rz mixing + CNOT entangling + H. -/
noncomputable def qaoa1 : Circuit 3 :=
  .gate (.Rz 0 0.5)
  (.gate (.Rz 1 0.5)
  (.gate (.Rz 2 0.5)
  (.gate (.CNOT 0 1)
  (.gate (.CNOT 1 2)
  (.gate (.H 0)
  (.gate (.H 1)
  (.gate (.H 2)
  .empty)))))))

/-- Phase estimation skeleton (2 qubits): H, controlled-Rz, H. -/
noncomputable def phaseEst2 : Circuit 2 :=
  .gate (.H 0)
  (.gate (.CNOT 0 1)
  (.gate (.Rz 1 0.25)
  (.gate (.CNOT 0 1)
  (.gate (.H 0)
  .empty))))

/-! ## Gate Count Verification -/

theorem bell_gateCount : bell.gateCount = 2 := by rfl
theorem ghz3_gateCount : ghz3.gateCount = 3 := by rfl
theorem swap2_gateCount : swap2.gateCount = 3 := by rfl
theorem qft2_gateCount : qft2.gateCount = 6 := by rfl
theorem deutschJozsa2_gateCount : deutschJozsa2.gateCount = 4 := by rfl
theorem grover4_gateCount : grover4.gateCount = 12 := by rfl
theorem hPair_gateCount : hPair.gateCount = 2 := by rfl
theorem cnotLadder3_gateCount : cnotLadder3.gateCount = 2 := by rfl
theorem teleport3_gateCount : teleport3.gateCount = 5 := by rfl
theorem vqeH2_gateCount : vqeH2.gateCount = 6 := by rfl
theorem qaoa1_gateCount : qaoa1.gateCount = 8 := by rfl
theorem randomClifford3_gateCount : randomClifford3.gateCount = 7 := by rfl
theorem tDepth1_gateCount : tDepth1.gateCount = 8 := by rfl
theorem phaseEst2_gateCount : phaseEst2.gateCount = 5 := by rfl
theorem bernsteinVazirani2_gateCount : bernsteinVazirani2.gateCount = 5 := by rfl

/-! ## Benchmark Entry -/

/-- Metadata for a single benchmark circuit. -/
structure BenchmarkEntry where
  /-- Human-readable name. -/
  name : String
  /-- Number of qubits. -/
  numQubits : Nat
  /-- Total gate count. -/
  gateCount : Nat
  /-- OpenQASM 3.0 program text. -/
  qasm : String
deriving Repr

/-- Create a benchmark entry from a named circuit. -/
noncomputable def mkBenchmark {n : Nat} (name : String) (c : Circuit n) : BenchmarkEntry :=
  { name := name
    numQubits := n
    gateCount := c.gateCount
    qasm := toQASMStr c }

/-- All benchmark circuits as a list of entries. -/
noncomputable def allBenchmarks : List BenchmarkEntry :=
  [ mkBenchmark "Bell" bell
  , mkBenchmark "GHZ-3" ghz3
  , mkBenchmark "SWAP-2" swap2
  , mkBenchmark "QFT-2" qft2
  , mkBenchmark "Deutsch-Jozsa-2" deutschJozsa2
  , mkBenchmark "Grover-4" grover4
  , mkBenchmark "H-Pair" hPair
  , mkBenchmark "CNOT-Ladder-3" cnotLadder3
  , mkBenchmark "Teleport-3" teleport3
  , mkBenchmark "VQE-H2" vqeH2
  , mkBenchmark "QAOA-1" qaoa1
  , mkBenchmark "Random-Clifford-3" randomClifford3
  , mkBenchmark "T-Depth-1" tDepth1
  , mkBenchmark "Phase-Est-2" phaseEst2
  , mkBenchmark "Bernstein-Vazirani-2" bernsteinVazirani2
  ]

/-- Total number of benchmarks. -/
theorem allBenchmarks_length : allBenchmarks.length = 15 := by rfl

/-! ## QASM Export (computable circuits only) -/

#eval toQASMStr bell
#eval toQASMStr ghz3
#eval toQASMStr swap2
#eval toQASMStr deutschJozsa2
#eval toQASMStr grover4
#eval toQASMStr hPair
#eval toQASMStr cnotLadder3
#eval toQASMStr teleport3
#eval toQASMStr randomClifford3
#eval toQASMStr tDepth1
#eval toQASMStr bernsteinVazirani2

end CatCrypt.Quantum.Benchmark.Suite
