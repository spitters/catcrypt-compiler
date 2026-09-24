/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert

/-!
# Emit driver for field inversion in GF(2^255 - 19)

`main` runs `Fe25519Invert.runEmit`, which writes the Rust rendering of `fe25519_invert`
to `/tmp/fe25519_invert.rs`.
-/

@[expose] public section
/-- Driver script: `lake env lean --run …/Fe25519InvertEmit.lean`. -/
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert.runEmit
