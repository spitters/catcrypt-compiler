/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.SKReplaceChecked
public import CatCrypt.Quantum.Synthesis.SKFloat

/-!
# Measurement driver for the checked `H`, `T`, `T†` replacement

`lake exe catq-sk-measure <idx> <L0> <depth>` measures one row: the float generator
`SK.skGenFloat L₀ depth` on the sixteen angles `k/32 · π`, `k = 1, …, 16`, each proposal
certified by `SK.checkGate` (and so by `checkRun`) against the precision bound
`ε ∈ {1e-2, 1e-3, 1e-4, 1e-5, 1e-6}` selected by `idx ∈ {0, …, 4}`. The row can also be given
as `--only e<idx>-L<L0>-d<depth>`, the form `scripts/run-exe-rows.sh` passes.

The first output line is a `#` header with the net size and the net construction time. Each
further line is tab-separated: the angle as `k/32`, the word length, the `Float` operator
distance up to phase of the word's matrix to the target (`SK.distUpToPhase`, `-` without a
proposal), the certified bound as a decimal (`-` when refused), `accepted` or `refused`, the
generator time in ms and the check time in ms. The exit code is `0` when every angle is
accepted and `3` otherwise.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.Benchmark.SKMeasure

open CatCrypt.Quantum CatCrypt.Quantum.QCircuit CatCrypt.Quantum.Synthesis.SK
  CatCrypt.Quantum.Synthesis.KAKFloat

/-- The precision bounds `1e-2, …, 1e-6`, indexed by `0, …, 4`. -/
def epsilons : List ℚ := [1 / 100, 1 / 1000, 1 / 10000, 1 / 100000, 1 / 1000000]

/-- The one-qubit gate `Rz(k/32 · π)`. -/
def angleGate (k : ℕ) : Gate 1 := .RzQ (0 : Fin 1) ⟨0, (k : ℚ) / 32⟩

/-- Run `f ()` once and return its value with the elapsed milliseconds. -/
def timed {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoMsNow
  pure (r, t1 - t0)

/-- Measure one angle: generator, then certification of its proposal. Returns whether it was
accepted. -/
def measureAngle (net : Net) (depth : Nat) (bound : ℚ) (k : ℕ) : IO Bool := do
  let g := angleGate k
  let (prop, genMs) ← timed fun _ => (skGenWith net depth g).map fun p => (p, p.1.length)
  match prop with
  | none =>
    IO.println s!"{k}/32\t0\t-\t-\trefused\t{genMs}\t0"
    pure false
  | some (p, len) =>
    let d : String :=
      match gateMatF g, p.1.mapM fun x => gateMatF x with
      | some U, some ms => (distUpToPhase (ms.foldl (fun acc m => m * acc) M2.id) U).toString
      | _, _ => "-"
    let (res, chkMs) ← timed fun _ =>
      (checkGate (n := 1) (fun _ => some p) bound g).map fun r => r.2.2
    match res with
    | some e =>
      IO.println s!"{k}/32\t{len}\t{d}\t{(ratToFloat e).toString}\taccepted\t{genMs}\t{chkMs}"
      pure true
    | none =>
      -- The certified bound the checker reaches, read with a bound it always accepts.
      let cert := match checkGate (n := 1) (fun _ => some p) 10 g with
        | some r => s!"({(ratToFloat r.2.2).toString})"
        | none => "-"
      IO.println s!"{k}/32\t{len}\t{d}\t{cert}\trefused\t{genMs}\t{chkMs}"
      pure false

/-- Run the row `(idx, L₀, depth)`. -/
def runRow (idx L0 depth : Nat) : IO UInt32 := do
  match epsilons[idx]? with
  | none =>
    IO.eprintln s!"catq-sk-measure: precision index {idx} is not in 0..4"
    pure 2
  | some bound =>
    let (net, netMs) ← timed fun _ => buildNet L0
    IO.println s!"# idx={idx} eps={(ratToFloat bound).toString} L0={L0} depth={depth} \
      net={net.size} net_ms={netMs}"
    let mut rc : UInt32 := 0
    for k in List.range 16 do
      let ok ← measureAngle net depth bound (k + 1)
      if !ok then rc := 3
    pure rc

/-- Parse the row from `idx L0 depth` or `--only e<idx>-L<L0>-d<depth>`. -/
def parseRow : List String → Option (Nat × Nat × Nat)
  | [a, b, c] => do pure (← a.toNat?, ← b.toNat?, ← c.toNat?)
  | "--only" :: row :: _ =>
    match row.splitOn "-" with
    | [a, b, c] => do
      pure (← (a.drop 1).toNat?, ← (b.drop 1).toNat?, ← (c.drop 1).toNat?)
    | _ => none
  | _ => none

end CatCrypt.Quantum.Benchmark.SKMeasure

/-- The entry point of `lake exe catq-sk-measure <idx> <L0> <depth>`. -/
def main (args : List String) : IO UInt32 :=
  match CatCrypt.Quantum.Benchmark.SKMeasure.parseRow args with
  | some (idx, L0, depth) => CatCrypt.Quantum.Benchmark.SKMeasure.runRow idx L0 depth
  | none => do
    IO.eprintln "usage: catq-sk-measure <idx 0..4> <L0> <depth> | --only e<idx>-L<L0>-d<depth>"
    pure 2
