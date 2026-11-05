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

/-!
# The compiler executable of the Qrunch bridge

`lake exe catq-compile` reads an OpenQASM 2 file as qelib1 statements
(`OpenQASMBytes.importQB`, lowered by `OpenQASMImport.lowerQ`) and runs one level of the
optimizer: `1` and `2` are `fullOptimize .Level1` and `fullOptimize .Level2`
(`PassPipeline.levelPasses`), `2r` is the resynthesis level `ResynthLevel.resynth`: Level 2,
then the checked KAK pass and the checked ZYZ pass at the fits of `QrunchFit`. It writes the
result as OpenQASM 2 over the Qrunch basis `{rx, ry, rz, cx, p}` (`QrunchBasis.toQelib`, then
`QrunchFuse.fuseQ`, the backward commutation pass `QrunchCommute.commuteQ`, the Pauli frame
pass `QrunchFuse.pauliQ` and `fuseQ` again, `printQelib`).

The answer line reports the phase that relates the qelib1 matrices of input and output: the
exact phases of the lowering (`Qelib.listPhase`), of `toQelib` and of `pauliQ`, and at `2r`
the phase `Resynth.phase` of the level. At `2r` it also reports `Resynth.eps`, the bound of
`ResynthLevel.norm_listMatrix_resynth_sub_le` on the distance of the matrix of the output of
the level from the unitary of its input, up to that phase, in the `ℓ²` operator norm; at `1`
and `2` the bound is `0` (`fullOptimize_level2_circuitUnitary`).

`catq-compile <in.qasm> <out.qasm> [level] [--check]` compiles one file (`2r` by default).
At `2r`, `--check` runs `resynth` (`resynthAt` at the checked fits) and reports its bound;
without it `resynthAt` runs at the unchecked fits, which replace the same blocks and runs when
every fit passes the checker, and the bound is reported as `unchecked`.
`catq-compile --serve` reads lines `<in.qasm> <out.qasm> [level] [--check]` from standard
input and answers each with one line, so a caller pays the start-up of the executable once.

## Main definitions

* `Level` — the levels the executable runs: `1`, `2`, `2r`.
* `compileFile` — one file to the compiled program, its CNOT counts and stage times.
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

/-- Force `f ()` between two clock reads: its value and the elapsed microseconds. -/
def timed {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  pure (a, (t1 - t0) / 1000)

/-- Whether a gate is the real-angle `Gate.Rz`, which has no exact OpenQASM statement. -/
def isRealRz {n : ℕ} : Gate n → Bool
  | .Rz _ _ => true
  | _ => false

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

/-- The value of a level on a circuit as a `Resynth` record: at `1` and `2` the gates of
`fullOptimize` in every stage and no payload, at `2r` the stages of `resynthAt` at `fits check`,
as its unfolding `resynthAt kf zf c = Resynth.ofKak zf (level2Gates c) (kakEmit kf (level2Gates
c))`, each stage forced under its own clock; with the microseconds of Level 2, of the KAK stage
and of the ZYZ stage. -/
def runLevel {n : ℕ} (level : Level) (check : Bool) (c : Circuit n) :
    IO (Resynth n × Nat × Nat × Nat) := do
  match level with
  | .l1 =>
    let (l, t) ← timed fun _ =>
      OpenQASM.toGateList (Optimization.FullOptimizer.fullOptimize .Level1 c)
    pure (⟨l, l, [], l, []⟩, t, 0, 0)
  | .l2 =>
    let (l, t) ← timed fun _ => level2Gates c
    pure (⟨l, l, [], l, []⟩, t, 0, 0)
  | .l2r =>
    let (l, tL) ← timed fun _ => level2Gates c
    let (kf, zf) := fits check
    let (k, tK) ← timed fun _ => Synthesis.KAKPassSmall.kakEmit kf l
    let (r, tZ) ← timed fun _ => Resynth.ofKak zf l k
    pure (r, tL, tK, tZ)

/-- Compile the OpenQASM 2 file `inp` at `level` into the OpenQASM 2 file `outp` over the
    Qrunch basis `{rx, ry, rz, cx, p}` (`QrunchBasis.toQelib`, `printQelib`), and return the
    answer line `ok <qubits> <cx_in> <cx_l2> <cx_out> <gates_out> <us> <us_import> <us_l2>
    <us_kak> <us_zyz> <us_print> <phase> <eps>` or `error <reason>`.

    The phase relates the qelib1 matrices of the two files: `M_in ≈ e^{i·phase} M_out`.
    It is `-α_in - Φ - α_out` with `α_in = Qelib.listPhase` of the input statements
    (`listMatrix_flatMap_lowerQ`), `α_out` the sum of the phases of `toQelib`
    (`qelibListMatrix_toQelib`) and of `pauliQ` (`qelibListMatrix_pauliQ`; `fuseQ` and
    `commuteQ` are exact, `qelibListMatrix_fuseQ`, `qelibListMatrix_commuteQ`)
    and `Φ = Resynth.phase` of the level, all exact; it is evaluated in floating point,
    reduced to `[-π, π]` and printed as the rational `roundQ` gives.

    With `check`, `<eps>` is `Resynth.eps` (`epsString`): by `norm_listMatrix_resynth_sub_le`
    the matrix of the gates of the level is within `eps` of the unitary of the lowered input,
    up to `e^{iΦ}`, in the `ℓ²` operator norm. Without it the `2r` fits are unchecked and
    `<eps>` is `unchecked`; at `1` and `2` it is `0` either way. -/
def compileFile (inp outp : String) (level : Level := .l2r) (check : Bool := false) :
    IO String := do
  let src ← IO.FS.readFile inp
  let some n := OpenQASMImport.qregSize src | pure "error no qreg declaration"
  -- The byte importer; `importQB_eq` equates it with `importQ` on ASCII sources.
  let (qs?, tI) ← timed fun _ => OpenQASMBytes.importQB n src.toUTF8
  let some qs := qs? | pure "error a line the importer does not recognise"
  let lin := qs.flatMap OpenQASMImport.lowerQ
  let (r, tL, tK, tZ) ← runLevel level check (Circuit.ofList lin)
  let eps := if check || level != .l2r then epsString r.eps else "unchecked"
  let out := r.out
  if out.any isRealRz then return "error a real-valued Rz in the output"
  let ((qOut, αOut), tP) ← timed fun _ =>
    let (q, α) := QrunchBasis.toQelib out
    let (q, β) := QrunchFuse.pauliQ (QrunchCommute.commuteQ (QrunchFuse.fuseQ q))
    (QrunchFuse.fuseQ q, α + β)
  IO.FS.writeFile outp (QrunchBasis.printQelib n qOut)
  let αIn := Qelib.listPhase qs
  let Φ := r.payloads.foldl (fun s b => s + piLinF b.2.1) 0
  let phase := -piLinF αOut - Φ - piLinF αIn
  let twoPi := 2 * piF
  let phase := phase - twoPi * Float.round (phase / twoPi)
  pure s!"ok {n} {cnotCount lin} {cnotCount r.l2} {cnotCount out} \
    {qOut.length} {tI + tL + tK + tZ + tP} {tI} {tL} {tK} {tZ} {tP} {roundQ phase} \
    {eps}"

/-- The answer to the arguments of one request, `<in.qasm> <out.qasm> [level] [--check]`. -/
def request (args : List String) : IO String :=
  let check := args.contains "--check"
  match args.filter (· ≠ "--check") with
  | [inp, outp] => compileFile inp outp .l2r check
  | [inp, outp, lv] =>
    match Level.ofString? lv with
    | some l => compileFile inp outp l check
    | none => pure "error level 1, 2 or 2r"
  | _ => pure "error expected <in.qasm> <out.qasm> [level] [--check]"

/-- Answer the request lines `<in.qasm> <out.qasm> [level]` of standard input until
    it ends. -/
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
