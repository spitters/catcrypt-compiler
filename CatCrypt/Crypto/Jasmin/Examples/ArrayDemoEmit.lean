/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.ArrayDemo

/-!
# Emit driver for the array demo

`main` runs `ArrayDemo.runEmit`, which writes the Rust rendering of the array load/store
loop to `/tmp/array_demo.rs` and prints it.
-/

@[expose] public section
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.ArrayDemo.runEmit
