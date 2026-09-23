/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontEmit

/-!
# Owned producer entry point for the front-generated secp256k1 point ops

Writes the two front-generated owned `.s` kernels (`secp256k1_jac_dbl`,
`secp256k1_jac_add`). Native compilation is required: the composed
`jacDblFrontCom`/`jacAddFrontCom` are ~6000-node `Com`s, beyond the
`lean --run` interpreter's practical reach. Run with
`lake exe secp256k1pointop`.

The producer is `Secp256k1PointOpFrontEmit.emitProven`, which carries
`denote = spec` by proof. `Secp256k1PointOpFront.emit` writes the same kernels
with no in-Lean check.
-/

@[expose] public section

def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontEmit.emitProven
    "bench/secp256k1_pointop_front_compare/gen_com/secp256k1_pointop.s"
