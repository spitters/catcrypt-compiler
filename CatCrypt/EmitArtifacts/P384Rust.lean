/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.P384Reflect
public import CatCrypt.Crypto.Jasmin.P384EcdsaReflect
public import CatCrypt.Crypto.Jasmin.P384DhkemReflect

/-!
# Emitted-artifact driver: P-384 Rust source

Runs the three P-384 Rust emitters as a compiled program:

```
lake exe emit-p384-rust
```

The emitters render `LowCT` bodies to Rust with `ppRustFunction` and write the
sources under `bench/p384_ecdsa_rust/gen/`, where the shim crate includes them.
Running them here rather than as `#eval` keeps the render out of every build of
the three front modules.

## Main definitions

* `emitters`: the P-384 Rust emitters, each with its module name.
* `main`: runs them in order, reporting each.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.EmitArtifacts.P384Rust

/-- The P-384 Rust emitters. -/
def emitters : List (String × IO Unit) :=
  [ ("CatCrypt.Crypto.Jasmin.P384Reflect",
      CatCrypt.Crypto.Jasmin.LowCTReflect.emitP384Rust)
  , ("CatCrypt.Crypto.Jasmin.P384EcdsaReflect",
      CatCrypt.Crypto.Jasmin.LowCTReflect.emitP384EcdsaRust)
  , ("CatCrypt.Crypto.Jasmin.P384DhkemReflect",
      CatCrypt.Crypto.Jasmin.LowCTReflect.emitP384DhkemRust) ]

end CatCrypt.EmitArtifacts.P384Rust

/-- Run the P-384 Rust emitters, reporting each. -/
def main : IO Unit := do
  for (name, act) in CatCrypt.EmitArtifacts.P384Rust.emitters do
    IO.println s!"emitting {name}"
    act
  IO.println s!"emit-p384-rust: {CatCrypt.EmitArtifacts.P384Rust.emitters.length} emitters ran"
