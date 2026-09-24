/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards

/-!
# Emit driver for the Montgomery-u to Edwards-y field map

`main` runs `MontUToEdwards.runEmit`, which writes the Rust rendering of
`mont_u_to_edwards_field` to `/tmp/mont_u_to_edwards_field.rs` and prints it.
-/

@[expose] public section
/-- Driver script: `lake env lean --run …/MontUToEdwardsEmit.lean`. -/
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards.runEmit
