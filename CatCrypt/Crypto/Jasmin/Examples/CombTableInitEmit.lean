/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.CombTableInit


@[expose] public section
/-- Driver: `lake env lean --run …/CombTableInitEmit.lean`. -/
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.CombTableInit.runEmit
