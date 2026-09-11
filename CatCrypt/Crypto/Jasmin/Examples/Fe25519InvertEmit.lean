/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert


@[expose] public section
/-- Driver script: `lake env lean --run …/Fe25519InvertEmit.lean`. -/
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert.runEmit
