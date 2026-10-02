/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed

/-!
# Native lowering-cost comparison, framed vs scalar point-op front

`lake exe pointopframedprobe` forces `jacDblLowered.isSome` (the scalar
half-limb-flowing front) and `jacDblLoweredFramed.isSome` (the frame-relative
front) as NATIVE compiled code, each with a flushed timestamp, so a killed run
still attributes its time. The interpreter is a false oracle here — its ceiling
is output-term size, which framing slightly worsens — so only a native `#eval`
measures the `Θ(nodes × reference-range × depth)` lowering the frame re-tile
targets.

## Main results

* `main` — with argv `scalar`, forces `jacDblLowered.isSome`; with `framed`,
  forces `jacDblLoweredFramed.isSome`. One side per process, so an OOM in one
  cannot mask the other's measurement.
-/

@[expose] public section

open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront (jacDblLowered)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed (jacDblLoweredFramed)

def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  let which := args.head?.getD "framed"
  out.putStrLn s!"probe start: {which}"; out.flush
  let t0 ← IO.monoMsNow
  let b := if which == "scalar" then (jacDblLowered ()).isSome else jacDblLoweredFramed.isSome
  let t1 ← IO.monoMsNow
  out.putStrLn s!"{which.toUpper} isSome={b} {t1 - t0} ms"; out.flush
