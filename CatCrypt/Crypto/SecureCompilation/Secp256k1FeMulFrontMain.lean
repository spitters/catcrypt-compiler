/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront

/-!
# Owned producer entry point for the front-generated secp256k1 field multiply

Split out of `Secp256k1FeMulFront` so the emit-logic module carries no root
`main` and can be imported without dragging a
`main` into importers. Run with `lake exe secp256k1femulfront` (native — the
front-generated `Com` renders too slowly through the `lean --run` interpreter).
-/

@[expose] public section

def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront.emit
    "bench/secp256k1_femul_front_compare/gen_com/secp256k1_femul.s"
