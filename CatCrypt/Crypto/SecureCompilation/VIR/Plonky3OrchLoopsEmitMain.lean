/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3OrchLoopsEmit

/-!
# Emit driver for the Plonky3 whole-prover orchestration loops

Root entry point for `lake exe plonky3orch`. It runs
`Plonky3OrchLoopsEmit.emitMain`, which writes two `.s` files into
`bench/plonky3_compare/gen_com`: the composed whole-prover object (five owned
field-kernel leaves plus the five orchestration-loop drivers as owned `loopLcmd`
back-edges), and the variant whose Poseidon2 permute call is routed to the owned
AVX-512 ZMM leaf.

The driver sits in its own module because a root-namespace `main` collides on
import with any other root-namespace `main`. A module needing the orchestration
emit closure alongside a second driver's closure imports `Plonky3OrchLoopsEmit`
instead.
-/

@[expose] public section

/-- Top-level entry point for `lake exe plonky3orch`. -/
def main : IO UInt32 := do
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3OrchLoopsEmit.emitMain
  return 0
