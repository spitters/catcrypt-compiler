/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2


@[expose] public section
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2.runEmit
