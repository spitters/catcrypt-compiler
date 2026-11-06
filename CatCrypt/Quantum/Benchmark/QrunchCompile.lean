/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.OpenQASMBytes
public import CatCrypt.Quantum.Optimization.ResynthLevel
public import CatCrypt.Quantum.Qelib
public import CatCrypt.Quantum.QrunchBasis
public import CatCrypt.Quantum.QrunchFuse
public import CatCrypt.Quantum.QrunchCommute
public import CatCrypt.Quantum.QrunchRound

/-!
# The compiler executable of the Qrunch bridge

`lake exe catq-compile` reads an OpenQASM 2 file as qelib1 statements
(`OpenQASMBytes.importQB`), elides its `swap` statements into an output permutation
(`SwapElide.elideQ`), snaps its angles (`AngleSnap.snapQ`) and iterates the round
`QrunchRound.round` of the pipeline to a fixed point (`QrunchRound.runCompile`). A round
lowers the statements
(`OpenQASMImport.lowerQ`), runs one level of the optimizer (`levelStage`): `1` and `2` are
`fullOptimize .Level1` and `fullOptimize .Level2` (`PassPipeline.levelPasses`), `2r` is the
resynthesis level `ResynthLevel.resynthAt`: Level 2, then the KAK pass and the ZYZ pass at the
fits of `QrunchFit`. It translates the result to the Qrunch basis `{rx, ry, cx, p}`
(`QrunchBasis.toQelib`, then `QrunchFuse.fuseQ`, the backward commutation pass
`QrunchCommute.commuteQ`, the Pauli frame pass `QrunchFuse.pauliQ` and `fuseQ` again). The
iteration runs further rounds while a round lowers the CX count of its input, or keeps it and
lowers the statement count, at most `--rounds k` rounds (8 by default), and returns the best
iterate (`QrunchRound.better_runRounds`). The executable writes it with `printQelib`.

The answer line reports the phase that relates the qelib1 matrices of input and output, the
sum of the exact phases of the rounds (`QrunchRound.sumPhase`), the bound, the snap bound plus
the sum of the bounds of the rounds (`QrunchRound.sumEps`), and the output permutation. By the
compile theorem `QrunchRound.norm_runCompile_sub_le` the qelib1 matrix of the input is within
the bound of the output permutation after the phase times the qelib1 matrix of the output, in
the `ℓ²` operator norm, at every level whose stage satisfies `QrunchRound.StageBound`: `2r`
with `--check` (`stageBound_levelStage_l2r`) and `2`, with bound `0` for the rounds
(`stageBound_levelStage_l2`).

`catq-compile <in.qasm> <out.qasm> [level] [--check] [--no-elide] [--no-snap] [--rounds k]`
compiles one file (`2r` by default); `--no-elide` and `--no-snap` turn off swap elision and
angle snapping. At `2r`, `--check` runs `resynthAt` at the checked fits and reports its bound;
without it `resynthAt` runs at the unchecked fits, which replace the same blocks and runs when
every fit passes the checker, and the bound is reported as `unchecked`. `--rounds 1` runs one
round. `catq-compile --serve` reads request lines from standard input and answers each with
one line, so a caller pays the start-up of the executable once.

## Main definitions

* `Level` — the levels the executable runs: `1`, `2`, `2r`.
* `levelStage` — the stage of a round at a level.
* `compileFile` — one file to the compiled program, its CNOT counts and times.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.Benchmark.QrunchCompile

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.Synthesis.KAKPass (cnotCount)
open CatCrypt.Quantum.Synthesis.KAKFloat (piLinF piF)
open CatCrypt.Quantum.Synthesis.QrunchFit (roundQ)
open CatCrypt.Quantum.Optimization.ResynthLevel

/-- A rational `q ≥ 0` as the decimal upper bound `⌈q·10¹⁸⌉e-18`. -/
def epsString (q : ℚ) : String := s!"{⌈q * 10 ^ 18⌉}e-18"

/-- A permutation of the qubits as `π 0,π 1,…,π (n-1)`, or `-` on no qubits. -/
def permString {n : ℕ} (σ : Equiv.Perm (Fin n)) : String :=
  if n = 0 then "-" else ",".intercalate ((List.finRange n).map fun q => toString (σ q).val)

/-- Force `f ()` between two clock reads: its value and the elapsed microseconds. -/
def timed {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  pure (a, (t1 - t0) / 1000)

/-- The levels of the executable: `fullOptimize .Level1`, `fullOptimize .Level2` and the
resynthesis level `ResynthLevel.resynth`. -/
inductive Level where
  /-- `fullOptimize .Level1`. -/
  | l1
  /-- `fullOptimize .Level2`. -/
  | l2
  /-- The resynthesis level `resynth`: Level 2, then the checked KAK and ZYZ passes. -/
  | l2r
  deriving DecidableEq

/-- The level named by a request argument: `1`, `2` or `2r`. -/
def Level.ofString? : String → Option Level
  | "1" => some .l1
  | "2" => some .l2
  | "2r" => some .l2r
  | _ => none

/-- The fit pair of `resynthAt`: the checked fits of `resynth` when `check`, else the unchecked
fits `qrunchFitUnchecked`, `qrunchZFitUnchecked`. -/
def fits {n : ℕ} (check : Bool) :
    Synthesis.KAKPassSmall.BlockFit n Payload ×
      (Array Synthesis.ZYZPass.Axis → Synthesis.ZYZPass.ZFit n Payload) :=
  if check then (Synthesis.QrunchFit.qrunchFitChecked, Synthesis.QrunchFit.qrunchZFitChecked)
  else (Synthesis.QrunchFit.qrunchFitUnchecked, Synthesis.QrunchFit.qrunchZFitUnchecked)

/-- The stage of a round at a level, as a `Resynth` record: at `1` and `2` the gates of
`fullOptimize` in every stage and no payload, at `2r` `resynthAt` at `fits check`. -/
def levelStage {n : ℕ} (level : Level) (check : Bool) (c : Circuit n) : Resynth n :=
  match level with
  | .l1 =>
    let l := OpenQASM.toGateList (Optimization.FullOptimizer.fullOptimize .Level1 c)
    ⟨l, l, [], l, []⟩
  | .l2 =>
    let l := level2Gates c
    ⟨l, l, [], l, []⟩
  | .l2r => resynthAt (fits check).1 (fits check).2 c

/-- The resynthesis stage at the checked fits satisfies its bound
(`norm_listMatrix_resynth_sub_le`). -/
theorem stageBound_levelStage_l2r {n : ℕ} :
    QrunchRound.StageBound (n := n) (levelStage .l2r true) :=
  QrunchRound.stageBound_resynth

/-- The stage of Level 2 satisfies the bound `0` at the phase `0`
(`fullOptimize_level2_circuitUnitary`). -/
theorem stageBound_levelStage_l2 {n : ℕ} (check : Bool) :
    QrunchRound.StageBound (n := n) (levelStage .l2 check) := by
  open scoped Matrix.Norms.L2Operator in
  intro c
  simp [levelStage, Resynth.phase, Resynth.eps, Resynth.payloads, listMatrix_level2Gates]

/-- The number of rounds of a request and its other arguments: `--rounds k` gives `k`, else
`8`. -/
def roundsArg : List String → Option (ℕ × List String)
  | [] => some (8, [])
  | "--rounds" :: k :: rest => do
    let r ← k.toNat?
    let (_, l) ← roundsArg rest
    pure (r, l)
  | a :: rest => do
    let (r, l) ← roundsArg rest
    pure (r, a :: l)

/-- Compile the OpenQASM 2 file `inp` at `level` into the OpenQASM 2 file `outp` over the
    Qrunch basis `{rx, ry, cx, p}` by swap elision (when `elide`), angle snapping (when
    `snap`) and at most `rounds` rounds (`QrunchRound.runCompile` at the stage
    `levelStage level check`, `printQelib`), and return the answer line `ok <qubits> <cx_in>
    <cx_l2> <cx_out> <gates_out> <us> <us_import> <us_rounds> <us_kak> <us_zyz> <us_print>
    <phase> <eps> <rounds_run> <perm>` or `error <reason>`. `<cx_in>` is the CNOT count of the
    lowered input, `<cx_l2>` that of Level 2 in the first round, `<cx_out>` and `<gates_out>`
    the `cx` and statement counts of the output; `<us_rounds>` is the time of elision,
    snapping and all rounds, and `<us_kak>`, `<us_zyz>` are `0`. `<perm>` is the output
    permutation `π 0,π 1,…` (`permString`): the state of input qubit `q` at the end is on
    output wire `π q`.

    The phase relates the qelib1 matrices of the two files: `M_in ≈ W(π) e^{i·phase} M_out`,
    `W(π)` the permutation matrix `SwapElide.wireMatrix π`. It is `-Φ`,
    `Φ = QrunchRound.sumPhase` the exact sum of the phases of the rounds; it is evaluated in
    floating point, reduced to `[-π, π]` and printed as the rational `roundQ` gives.

    With `check`, or at `1` and `2`, `<eps>` is the snap bound plus `QrunchRound.sumEps`
    (`epsString`): by `QrunchRound.norm_runCompile_sub_le` the qelib1 matrix of the input is
    within `eps` of `W(π) e^{-iΦ}` times the qelib1 matrix of the output, in the `ℓ²` operator
    norm. Without it the `2r` fits are unchecked and `<eps>` is `unchecked`. -/
def compileFile (inp outp : String) (level : Level := .l2r) (check : Bool := false)
    (rounds : ℕ := 8) (elide snap : Bool := true) : IO String := do
  let src ← IO.FS.readFile inp
  let some n := OpenQASMImport.qregSize src | pure "error no qreg declaration"
  -- The byte importer; `importQB_eq` equates it with `importQ` on ASCII sources.
  let (qs?, tI) ← timed fun _ => OpenQASMBytes.importQB n src.toUTF8
  let some qs := qs? | pure "error a line the importer does not recognise"
  let (o, tR) ← timed fun _ =>
    QrunchRound.runCompile (levelStage level check) rounds elide snap qs
  let rs := o.rounds
  let some o₁ := rs.head? |
    pure "error a statement with repeated operands or a real-valued Rz in the output"
  let qOut := o.out
  let (text, tP) ← timed fun _ => QrunchBasis.printQelib n qOut
  IO.FS.writeFile outp text
  let eps := if check || level != .l2r then epsString (o.snapEps + QrunchRound.sumEps rs)
    else "unchecked"
  let phase := -piLinF (QrunchRound.sumPhase rs)
  let twoPi := 2 * piF
  let phase := phase - twoPi * Float.round (phase / twoPi)
  pure s!"ok {n} {cnotCount (qs.flatMap OpenQASMImport.lowerQ)} {cnotCount o₁.stage.l2} \
    {QrunchFuse.cxCount qOut} {qOut.length} {tI + tR + tP} {tI} {tR} 0 0 {tP} \
    {roundQ phase} {eps} {rs.length} {permString o.perm}"

/-- The flags of a request that are not `--rounds`: `--check`, `--no-elide`, `--no-snap`. -/
def flagArgs : List String := ["--check", "--no-elide", "--no-snap"]

/-- The answer to the arguments of one request,
    `<in.qasm> <out.qasm> [level] [--check] [--no-elide] [--no-snap] [--rounds k]`. -/
def request (args : List String) : IO String :=
  let check := args.contains "--check"
  let elide := !args.contains "--no-elide"
  let snap := !args.contains "--no-snap"
  match roundsArg (args.filter (· ∉ flagArgs)) with
  | none => pure "error --rounds expects a natural number"
  | some (k, [inp, outp]) => compileFile inp outp .l2r check k elide snap
  | some (k, [inp, outp, lv]) =>
    match Level.ofString? lv with
    | some l => compileFile inp outp l check k elide snap
    | none => pure "error level 1, 2 or 2r"
  | some _ => pure "error expected <in.qasm> <out.qasm> [level] [--check] [--no-elide] \
      [--no-snap] [--rounds k]"

/-- Answer the request lines `<in.qasm> <out.qasm> [level] [--check] [--no-elide] [--no-snap]
    [--rounds k]` of standard input until it ends. -/
partial def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop : IO Unit := do
    let l ← stdin.getLine
    if l.isEmpty then return
    let args := (l.trimAscii.toString.splitOn " ").filter (· ≠ "")
    let ans ← try request args catch e => pure s!"error {e}"
    stdout.putStrLn ans
    stdout.flush
    loop
  loop

end CatCrypt.Quantum.Benchmark.QrunchCompile

/-- The entry point of `lake exe catq-compile`: `<in.qasm> <out.qasm> [level]`
    compiles one file, `--serve` answers request lines on standard input. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--serve"] => CatCrypt.Quantum.Benchmark.QrunchCompile.serve; pure 0
  | _ =>
    let ans ← CatCrypt.Quantum.Benchmark.QrunchCompile.request args
    IO.println ans
    pure (if ans.startsWith "ok" then 0 else 1)
