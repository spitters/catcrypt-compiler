/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront

/-!
# Owned producer entry point for the front-generated secp256k1 point ops

Runs the native whole-op `denote = jacDbl/jacAddSpec` self-check over the KAT
battery and, only if all vectors pass, writes the two front-generated owned `.s`
kernels (`secp256k1_jac_dbl`, `secp256k1_jac_add`). Native compilation is
required: the composed `jacDblFrontCom`/`jacAddFrontCom` are ~6000-node `Com`s,
beyond the `lean --run` interpreter's practical reach. Run with
`lake exe secp256k1pointop`.
-/

def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront.emit
    "bench/secp256k1_pointop_front_compare/gen_com/secp256k1_pointop.s"
