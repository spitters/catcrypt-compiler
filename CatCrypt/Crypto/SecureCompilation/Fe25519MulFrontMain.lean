/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Fe25519MulFront

/-!
# Owned producer entry point for the front-generated Curve25519 field multiply

Split out of `Fe25519MulFront` so the emit-logic module carries no root `main`
and can be imported without dragging a `main` into importers. Run with
`lake exe fe25519mulfront` (native — the front-generated `Com` renders too slowly
through the `lean --run` interpreter).
-/

@[expose] public section

def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.Fe25519MulFront.emit
    "bench/x25519_fieldmul_compare/gen_com/fe25519_mul_front.s"
