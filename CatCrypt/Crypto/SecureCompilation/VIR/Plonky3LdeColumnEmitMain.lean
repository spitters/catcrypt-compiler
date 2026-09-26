/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnEmit

/-!
# Emit driver for the Plonky3 column-LDE leaves

Root entry point that runs `Plonky3LdeColumnEmit.emitMain`, which writes the
seven coset-NTT column-LDE leaves as one owned AT&T `.s` into
`bench/plonky3_compare/gen_com`.

The driver sits in its own module because a root-namespace `main` collides on
import with any other root-namespace `main`. A module needing the column-LDE
closure alongside a second driver's closure imports `Plonky3LdeColumnEmit`
instead.
-/

@[expose] public section

/-- Top-level entry point for the column-LDE owned emit. -/
def main : IO UInt32 := do
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnEmit.emitMain
  return 0
