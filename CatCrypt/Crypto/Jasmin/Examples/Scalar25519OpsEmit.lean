/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops

/-!
# Emit driver for the Ed25519 scalar operations

`main` runs `Scalar25519Ops.runEmit`, which writes the Rust rendering of the scalar
functions (byte conversion, add, sub, negate) to `/tmp/scalar25519_emitted.rs` and prints it.
-/

@[expose] public section
/-- Driver script: `lake env lean --run …/Scalar25519OpsEmit.lean`. -/
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.runEmit
