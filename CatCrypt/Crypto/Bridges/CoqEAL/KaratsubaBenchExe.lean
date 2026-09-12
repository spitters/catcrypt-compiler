/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Bridges.CoqEAL.KaratsubaBench

/-!
# Native entry point for the 4c Karatsuba benchmark

A top-level `main` (outside any namespace, so it becomes the executable's entry
symbol) delegating to the namespaced harness `KaratsubaBench.main`. Built as the
`karatsuba_bench` `lean_exe` so the crossover sweep runs on a native binary
rather than `lean --run` (whose elaboration startup swamps the compute).
-/

@[expose] public section

def main (args : List String) : IO Unit :=
  CatCrypt.Crypto.Bridges.CoqEAL.KaratsubaBench.main args
