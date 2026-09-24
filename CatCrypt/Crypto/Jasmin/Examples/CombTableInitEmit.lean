/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.CombTableInit

/-!
# Emit driver for the comb-table initialisation

`main` runs `CombTableInit.runEmit`, which writes the Rust rendering of
`build_comb_table_emitted` to `/tmp/build_comb_table.rs`.
-/

@[expose] public section
/-- Driver: `lake env lean --run …/CombTableInitEmit.lean`. -/
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.CombTableInit.runEmit
