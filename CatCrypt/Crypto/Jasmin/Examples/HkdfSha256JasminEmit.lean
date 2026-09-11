/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.HkdfSha256Jasmin


@[expose] public section
/-- Driver script: `lake env lean --run …/HkdfSha256JasminEmit.lean`. -/
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.HkdfSha256Jasmin.runEmit
