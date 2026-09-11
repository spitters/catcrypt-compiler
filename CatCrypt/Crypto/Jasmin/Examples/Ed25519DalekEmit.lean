/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LowCTToMLIR
public import CatCrypt.Crypto.Jasmin.LowCTToMLIR
public meta import CatCrypt.Crypto.Jasmin.Examples.Ed25519AddChainsDSL
public import CatCrypt.Crypto.Jasmin.Examples.Ed25519AddChainsDSL
public meta import CatCrypt.Crypto.Jasmin.Examples.BenchOut
public import CatCrypt.Crypto.Jasmin.Examples.BenchOut

/-!
# Ed25519 dalek primitives: mixed-add, compress, decompress — MLIR emit

Drives the Phase-2 extensions of the dalek-pipeline plan:
- `edwards_madd_*` (projective + affine Niels-form table entry)
- `edwards_compress_{y,sign}` (uses `fp_inv`, `fp_is_neg`)
- `edwards_decompress_{X,T}` (uses `fp_sqrt_ratio_i`, `fp_cmov`)

Each reified pure-Lean function becomes one `func.func` in the emitted
MLIR. Externs include the extended fp surface:
- existing: `fp_add`, `fp_sub`, `fp_mul`, `fp_sqr`, `fp_opp`, `fp_mul_a24`
- new (Phase 1.2): `fp_inv`, `fp_invsqrt`, `fp_sqrt_ratio_i`, `fp_cmov`,
  `fp_is_neg`, `fp_is_zero`, `fp_sq2`, `fp_sq4`, `fp_sq8`.

Output target is `$CATCRYPT_BENCH/src/ed25519_{madd,compress,decompress}.mlir`,
with the benchmark / cross-check C wrappers in `bench_ed25519_*.c`.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.Examples.Ed25519DalekEmit

open CatCrypt.Crypto.Jasmin.LowCT

open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Jasmin.LowCTToMLIR
open CatCrypt.Crypto.Jasmin.Examples.Ed25519AddChainsDSL

/-! ## 1. Extern list — full Ed25519 / Ristretto surface. -/

def ed25519ExternsFull : List (String × Nat × TowerType × TowerType) :=
  [ ("fp_add",          2, .TFp25519,  .TFp25519)
  , ("fp_sub",          2, .TFp25519,  .TFp25519)
  , ("fp_mul",          2, .TFp25519,  .TFp25519)
  , ("fp_sqr",          1, .TFp25519,  .TFp25519)
  , ("fp_opp",          1, .TFp25519,  .TFp25519)
  , ("fp_mul_a24",      1, .TFp25519,  .TFp25519)
  , ("fp_sq2",          1, .TFp25519,  .TFp25519)
  , ("fp_sq4",          1, .TFp25519,  .TFp25519)
  , ("fp_sq8",          1, .TFp25519,  .TFp25519)
  , ("fp_inv",          1, .TFp25519,  .TFp25519)
  , ("fp_invsqrt",      1, .TFp25519,  .TFp25519)
  , ("fp_sqrt_ratio_i", 2, .TFp25519,  .TFp25519)
  , ("fp_cmov",         3, .TFp25519,  .TFp25519)
  , ("fp_is_neg",       1, .TFp25519,  .TFp25519)
  , ("fp_is_zero",      1, .TFp25519,  .TFp25519)
  , ("scalar_add",      2, .TFpL25519, .TFpL25519)
  , ("scalar_sub",      2, .TFpL25519, .TFpL25519)
  , ("scalar_mul",      2, .TFpL25519, .TFpL25519)
  , ("scalar_neg",      1, .TFpL25519, .TFpL25519)
  , ("scalar_inv",      1, .TFpL25519, .TFpL25519) ]

def emitReifiedFp (name : String) (rf : ReifiedFunc) : String :=
  emitFunc name rf.args rf.retName .TFp25519 rf.body

def emitReifiedFpL (name : String) (rf : ReifiedFunc) : String :=
  emitFunc name rf.args rf.retName .TFpL25519 rf.body

/-! ## 2. Mixed-add module (projective + affine Niels) -/

def ed25519MaddMLIR : String :=
  emitExterns ed25519ExternsFull ++ "\n" ++
  emitReifiedFp "ed25519_madd_x3" edwardsMaddX3Reified ++ "\n\n" ++
  emitReifiedFp "ed25519_madd_y3" edwardsMaddY3Reified ++ "\n\n" ++
  emitReifiedFp "ed25519_madd_t3" edwardsMaddT3Reified ++ "\n\n" ++
  emitReifiedFp "ed25519_madd_z3" edwardsMaddZ3Reified

#eval BenchOut.writeBench
  "ed25519_madd.mlir"
  ed25519MaddMLIR

/-! ## 3. Compress / decompress -/

def ed25519CompressMLIR : String :=
  emitExterns ed25519ExternsFull ++ "\n" ++
  emitReifiedFp "ed25519_compress_y"    edwardsCompressYReified ++ "\n\n" ++
  emitReifiedFp "ed25519_compress_sign" edwardsCompressSignReified

def ed25519DecompressMLIR : String :=
  emitExterns ed25519ExternsFull ++ "\n" ++
  emitReifiedFp "ed25519_decompress_x" edwardsDecompressXReified ++ "\n\n" ++
  emitReifiedFp "ed25519_decompress_t" edwardsDecompressTReified

#eval BenchOut.writeBench
  "ed25519_compress.mlir"
  ed25519CompressMLIR

#eval BenchOut.writeBench
  "ed25519_decompress.mlir"
  ed25519DecompressMLIR

/-! ## 4. Scalar arithmetic (sign-step `s = r + h·a mod L`) -/

def ed25519ScalarMLIR : String :=
  emitExterns ed25519ExternsFull ++ "\n" ++
  emitReifiedFpL "ed25519_scalar_s" ed25519ScalarSReified

#eval BenchOut.writeBench
  "ed25519_scalar.mlir"
  ed25519ScalarMLIR

/-! ## 4b. Curve25519 base-field addition chains (Track F2 reification)

`fp_inv` (254-sqr + 11-mul Fermat chain) and `fp_invsqrt`
(`z^(2^252 - 3)` Tonelli-Shanks tail) are reified from
`Ed25519AddChainsDSL` and emitted as `func.func`s here. Other modules
keep importing them via the extern declaration in `ed25519ExternsFull`,
and the LLVM linker resolves the call to the emitted body once
`ed25519_addchains.mlir` is also in the link line.

This shrinks the trusted base by removing the only hand-written-C
addition chain in the Ed25519 binary (`dalek_shim.c::fe_invert`). Math
correctness on the Lean side is `Ed25519Spec.lean`'s `interp_fp_inv`
(via Mathlib's Fermat); the chain-arithmetic axiom
`interp_fp_inv_pow` now points at the reified Lean chain rather than
the C source. -/

/-- Externs minus the chains we ourselves provide (avoids duplicate decl
    in the addchains module). -/
def ed25519AddChainExterns : List (String × Nat × TowerType × TowerType) :=
  ed25519ExternsFull.filter (fun (n, _, _, _) =>
    n ≠ "fp_inv" ∧ n ≠ "fp_invsqrt")

def ed25519AddChainsMLIR : String :=
  emitExterns ed25519AddChainExterns ++ "\n" ++
  emitFunc "fp_inv"     [("z", .TFp25519)] "out" .TFp25519 fpInvChain ++ "\n\n" ++
  emitFunc "fp_invsqrt" [("z", .TFp25519)] "out" .TFp25519 fpPowP58Chain

#eval BenchOut.writeBench
  "ed25519_addchains.mlir"
  ed25519AddChainsMLIR

/-! ## 5. Ristretto255 compress / decompress -/

def ristrettoMLIR : String :=
  emitExterns ed25519ExternsFull ++ "\n" ++
  emitReifiedFp "ristretto_compress_s"   ristrettoCompressSReified   ++ "\n\n" ++
  emitReifiedFp "ristretto_decompress_x" ristrettoDecompressXReified ++ "\n\n" ++
  emitReifiedFp "ristretto_decompress_y" ristrettoDecompressYReified ++ "\n\n" ++
  emitReifiedFp "ristretto_decompress_t" ristrettoDecompressTReified

#eval BenchOut.writeBench
  "ristretto255.mlir"
  ristrettoMLIR

end CatCrypt.Crypto.Jasmin.Examples.Ed25519DalekEmit
