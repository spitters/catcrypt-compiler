/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.HmacSha256Jasmin


@[expose] public section
/-- Driver script: `lake env lean --run …/HmacSha256JasminEmit.lean`. -/
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.HmacSha256Jasmin.runEmit
