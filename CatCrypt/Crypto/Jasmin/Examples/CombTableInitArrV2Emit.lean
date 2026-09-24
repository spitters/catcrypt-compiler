/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2

/-!
# Emit driver for the second array-based comb-table initialisation

`main` runs `CombTableInitArrV2.runEmit`, which writes the Rust rendering of
`build_comb_table_arr_v2` to `/tmp/build_comb_table_arr_v2.rs` and prints it.
-/

@[expose] public section
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2.runEmit
