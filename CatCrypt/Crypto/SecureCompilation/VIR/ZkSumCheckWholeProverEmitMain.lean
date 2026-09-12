/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ZkSumCheckWholeProverEmit

/-!
# Emit driver for the Spartan / Jolt BabyBear sum-check field-core whole-prover

Root entry point for `lake exe zksumcheckwhole`. It runs
`ZkSumCheckWholeProverEmit.emitMain`, which writes the single composed `.s`
(owned BabyBear Poseidon2 compress / squeeze, the Horner round step, the
BabyBear inverse, plus the Spartan two-phase and Jolt sum-check
orchestration-loop drivers) into `bench/spartan_compare/gen_com`.

The driver sits in its own module because a root-namespace `main` collides on
import with any other root-namespace `main`. A module needing the field-core
emit closure alongside a second driver's closure imports
`ZkSumCheckWholeProverEmit` instead.
-/

@[expose] public section

/-- Top-level entry point for `lake exe zksumcheckwhole`. -/
def main : IO UInt32 := do
  CatCrypt.Crypto.SecureCompilation.VIR.ZkSumCheckWholeProverEmit.emitMain
  return 0
