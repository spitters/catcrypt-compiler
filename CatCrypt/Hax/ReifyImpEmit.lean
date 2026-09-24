/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.ReifyImpDriver

/-!
# The Rust text of the `reifyImp%` pilots, as a compiled program

`main` writes, for each entry of `CatCrypt.Hax.ReifyImp.pilots`, the printed Rust function
to `DIR/FN.rs` and its leaf stubs to `DIR/FN_leaves.rs`, with `DIR` the first argument
(default `bench/reify_roundtrip`). `scripts/reify-roundtrip.sh` runs it as
`lake exe reify-emit` from the repository root before it compiles the crate.

## Main definitions

* `main` — the driver entry point
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Hax.ReifyImp in
/-- Write the printed function and the leaf stubs of every pilot. -/
def main (args : List String) : IO Unit := do
  let dir := args.headD "bench/reify_roundtrip"
  IO.FS.createDirAll dir
  for p in pilots do
    match p.text with
    | none => throw (IO.userError s!"{p.fn}: the literal is outside the printed fragment")
    | some t =>
      IO.FS.writeFile s!"{dir}/{p.fn}.rs" t
      IO.FS.writeFile s!"{dir}/{p.fn}_leaves.rs" p.leaves
      IO.println s!"wrote {dir}/{p.fn}.rs and {dir}/{p.fn}_leaves.rs"

end
