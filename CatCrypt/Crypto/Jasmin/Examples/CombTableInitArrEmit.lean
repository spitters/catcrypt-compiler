/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.CombTableInitArr

/-!
# Emit driver for the array-based comb-table initialisation

`main` runs `CombTableInitArr.runEmit`, which writes the Rust rendering of
`build_comb_table_arr` to `/tmp/build_comb_table_arr.rs`.
-/

@[expose] public section
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.CombTableInitArr.runEmit
