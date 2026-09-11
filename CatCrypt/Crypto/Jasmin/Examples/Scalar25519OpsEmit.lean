/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops


@[expose] public section
/-- Driver script: `lake env lean --run …/Scalar25519OpsEmit.lean`. -/
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.runEmit
