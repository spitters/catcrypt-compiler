/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QrunchExport
public import CatCrypt.Quantum.HQPL
public import CatCrypt.Quantum.OpenQASMImport

/-!
# The export executable for algorithm gate lists

`lake exe catq-export [dir]` writes the OpenQASM 2 export (`QrunchExport.exportQASM`) of the
gate lists of the algorithms below to `<dir>/<name>.qasm`, over `{rx, ry, cx, p}` with exact
angles, and prints one line `<name> <phase>` per file with the exact global phase
`QrunchExport.exportPhase` (`qelibListMatrix_importQ_exportQASM`). The default directory is
`../catcrypt-compiler/bench/qasm/catcrypt`, relative to the build root.

* `qft4`, `qft6` — `QFT.qftGates` on 4 and 6 qubits;
* `qpe3_t` — `HQPL.phaseEstimationGates` with a 3-qubit counting register and `U = T` on the
  fourth qubit;
* `grover2` — `HQPL.amplitudeAmplificationGates` with oracle `CZ`, state preparation `H ⊗ H`,
  one iteration;
* `amp3_ccz` — `HQPL.amplitudeAmplificationGates` on 3 qubits with oracle `CCZ`
  (`OpenQASMImport.cczGates`), state preparation `H^⊗3`, two iterations.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.Benchmark.QrunchExportMain

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.QrunchExport

/-- `H` on every qubit. -/
def hadamards (n : ℕ) : List (Gate n) := (List.finRange n).map Gate.H

/-- The exported programs: a name and the text and phase of the export, `none` for a list
    with the real-angle `Rz`. -/
def exportedPrograms : List (String × Option (String × PiLin)) :=
  [("qft4", exportChecked (QFT.qftGates 4)),
   ("qft6", exportChecked (QFT.qftGates 6)),
   ("qpe3_t", exportChecked (n := 4) (HQPL.phaseEstimationGates 0 3 [Gate.T 3])),
   ("grover2", exportChecked
      (HQPL.amplitudeAmplificationGates [Gate.CZ (0 : Fin 2) 1] (hadamards 2) 1)),
   ("amp3_ccz", exportChecked
      (HQPL.amplitudeAmplificationGates (OpenQASMImport.cczGates (0 : Fin 3) 1 2)
        (hadamards 3) 2))]

/-- Write each program to `<dir>/<name>.qasm` and print its phase. -/
def run (dir : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll dir
  let mut rc : UInt32 := 0
  for (name, r) in exportedPrograms do
    match r with
    | some (text, ph) =>
      IO.FS.writeFile (dir / s!"{name}.qasm") text
      IO.println s!"{name} {ph.toQASM}"
    | none =>
      IO.println s!"{name} error: the list has a real-angle Rz"
      rc := 1
  pure rc

end CatCrypt.Quantum.Benchmark.QrunchExportMain

/-- The entry point of `lake exe catq-export [dir]`. -/
def main (args : List String) : IO UInt32 :=
  let dir : System.FilePath := match args with
    | [d] => d
    | _ => "../catcrypt-compiler/bench/qasm/catcrypt"
  CatCrypt.Quantum.Benchmark.QrunchExportMain.run dir
