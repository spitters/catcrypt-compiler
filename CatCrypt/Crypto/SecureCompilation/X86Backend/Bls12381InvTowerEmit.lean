/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12MulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12MulKernel
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp2MulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp2MulKernel
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381FinalExp
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381FinalExp

/-!
# The BLS12-381 inverse-tower bench artifacts

The `bench/bls12381_fp2inv_compare` harness links one directory holding the whole
inverse tower — `fp2_inv → fp6_inv → fp12_inv` — together with every `Fp12`,
`Fp6`, `Fp2` and `Fp` leaf those inverses call. The renders themselves live with
their kernels (`Bls12381Fp6Fp12MulKernel`, `Bls12381Fp2MulKernel`,
`Bls12381FinalExp`), whose own emit drivers write the `bls12381_fp2_compare` and
`bls12381_fp6_compare` directories; this module collects the eighteen leaves into
the single directory the inverse-tower harness links.

The `Fp` Montgomery-multiply leaf (`bls12381_mont_mul_x86_from_lean.s`) is linked
read-only from `bench/bls12381_fieldmul_compare/gen_com/` and is not written here.

## Main definitions

* `genDir`: the harness directory
* `towerLeaves`: the eighteen `(file name, render)` pairs
* `emitMain`: the writer, run at elaboration
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381InvTowerEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp6Fp12MulKernel
  (fp2InvAsm fp6InvAsm fp12InvAsm fp12ConvCycAsm fp12MulAsm
   fp6MulAsm fp6ArtAsm fp6SubAsm fp6AddAsm fp2AddAsm fp2SubAsm fp2NorAsm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp2MulKernel
  (fp2MulAsm fp2SqrAsm fpAddAsm fpSubAsm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381FinalExp
  (fp12InvCycAsm fp12FrbAsm)

/-! ## 1. The artifact set -/

/-- The directory the inverse-tower harness links, relative to the repository
    root. -/
def genDir : String := "bench/bls12381_fp2inv_compare/gen"

/-- The eighteen leaves of the inverse tower, paired with the file name each is
    written to. -/
def towerLeaves : List (String × String) :=
  [ ("bls12381_fp12_conv_cyc_x86_from_lean.s", fp12ConvCycAsm),
    ("bls12381_fp12_mul_x86_from_lean.s",      fp12MulAsm),
    ("bls12381_fp12_inv_cyc_x86_from_lean.s",  fp12InvCycAsm),
    ("bls12381_fp12_frb_x86_from_lean.s",      fp12FrbAsm),
    ("bls12381_fp12_inv_x86_from_lean.s",      fp12InvAsm),
    ("bls12381_fp6_inv_x86_from_lean.s",       fp6InvAsm),
    ("bls12381_fp2_inv_x86_from_lean.s",       fp2InvAsm),
    ("bls12381_fp6_mul_x86_from_lean.s",       fp6MulAsm),
    ("bls12381_fp6_mul_art_x86_from_lean.s",   fp6ArtAsm),
    ("bls12381_fp6_sub_x86_from_lean.s",       fp6SubAsm),
    ("bls12381_fp6_add_x86_from_lean.s",       fp6AddAsm),
    ("bls12381_fp2_mul_x86_from_lean.s",       fp2MulAsm),
    ("bls12381_fp2_sqr_x86_from_lean.s",       fp2SqrAsm),
    ("bls12381_fp2_add_x86_from_lean.s",       fp2AddAsm),
    ("bls12381_fp2_sub_x86_from_lean.s",       fp2SubAsm),
    ("bls12381_fp2_mul_nor_x86_from_lean.s",   fp2NorAsm),
    ("bls12381_fp_add_x86_from_lean.s",        fpAddAsm),
    ("bls12381_fp_sub_x86_from_lean.s",        fpSubAsm) ]

/-! ## 2. Artifact writer

The literal paths below are the ones the harness links:
`bench/bls12381_fp2inv_compare/gen/bls12381_fp2_inv_x86_from_lean.s` and its
seventeen siblings. -/

/-- Write the eighteen inverse-tower leaves into the harness directory. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll genDir
  for (name, body) in towerLeaves do
    IO.FS.writeFile (genDir ++ "/" ++ name) body
  IO.println s!"WROTE {towerLeaves.length} .s into {genDir} (owned x86 backend, no jasminc)"

/-! ## 3. Artifact generation at elaboration

The renders are written while this module elaborates, so `lake` owns the
dependency between the kernels and the bench artifacts. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381InvTowerEmit
