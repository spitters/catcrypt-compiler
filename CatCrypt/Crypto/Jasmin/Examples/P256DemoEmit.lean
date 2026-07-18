/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTReflect
import CatCrypt.Crypto.Jasmin.LowCTToMLIR

/-!
# P-256 demonstration: same pipeline, different curve

A small NIST P-256 example showing the pipeline is curve-agnostic.
Same authoring shape as `X25519ReflectEmit`, but over `FpP256`
(saturated 4×u64 Montgomery) instead of `Fp25519` (unsaturated 5×u64
radix-51).

Demonstrates that adding a new curve to the pipeline is mechanical:
1. Add `TowerType` variant + `byteSize`/`encodeTy` cases (done in
   `LowCT.lean` and `LowCTToCryptoSSA.lean`).
2. Add reifier axioms (done in `LowCTReflect.lean §1.5`).
3. Generate the shim via `gen_fiat_shim.py p256_64.c` (already in
   `build/shims/p256_shim.{c,h}`).
4. Author a reified Lean function over the new opaque type.
5. Emit MLIR via `LowCTToMLIR.emitFunc` or `emitFuncOutParam`.

This file does steps 4 + 5; the C-side bench harness wiring is left
as a follow-up (the shim is auto-generated and ready).
-/

namespace CatCrypt.Crypto.Jasmin.Examples.P256DemoEmit

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Jasmin.LowCTToMLIR

/-! ## P-256 demo functions (reified pure Lean)

A "halfstep-shape" over the P-256 field: same 5-op shape as X25519's
`halfstep` (add, sub, sqr, sqr, mul), just on P-256 instead. Validates
that `LowCTReflect`'s knownOps registry correctly tags arguments
and result with `TowerType.TFpP256` → `memref<4xi64>`. -/

noncomputable def p256_halfstep (x y : FpP256) : FpP256 :=
  let a  := fp256_add x y
  let b  := fp256_sub x y
  let aa := fp256_sqr a
  let bb := fp256_sqr b
  fp256_mul aa bb

/-- A small Weierstrass-style step exercising more ops: computes
    `(x² + a)·y - x³` on P-256. Standard ECC field arithmetic shape. -/
noncomputable def p256_weierstrass_step (x y a : FpP256) : FpP256 :=
  let x2  := fp256_sqr x
  let x2a := fp256_add x2 a
  let lhs := fp256_mul x2a y
  let x3  := fp256_mul x2 x
  fp256_sub lhs x3

/-- Reified forms — `ReifiedFunc` bundles args/body/retName ready for
    `emitFunc`. -/
def p256HalfstepReified : ReifiedFunc := reifyLowCT% p256_halfstep
def p256WeierstrassReified : ReifiedFunc := reifyLowCT% p256_weierstrass_step

/-! ## MLIR emission (pool-ABI, matching the existing X25519 examples) -/

def p256Externs : List (String × Nat × TowerType × TowerType) :=
  [ ("fp256_add", 2, .TFpP256, .TFpP256)
  , ("fp256_sub", 2, .TFpP256, .TFpP256)
  , ("fp256_mul", 2, .TFpP256, .TFpP256)
  , ("fp256_sqr", 1, .TFpP256, .TFpP256)
  , ("fp256_opp", 1, .TFpP256, .TFpP256) ]

def p256DemoMLIR : String :=
  emitExterns p256Externs ++ "\n" ++
  emitFunc "p256_halfstep_demo"
    p256HalfstepReified.args
    p256HalfstepReified.retName
    .TFpP256
    p256HalfstepReified.body ++
  "\n\n" ++
  emitFunc "p256_weierstrass_step_demo"
    p256WeierstrassReified.args
    p256WeierstrassReified.retName
    .TFpP256
    p256WeierstrassReified.body

-- Emit MLIR to the catcrypt-bench source tree if it exists; otherwise skip
-- silently so the file builds in environments without that sibling repo.
#eval (do
  let path : System.FilePath :=
    "bench/p256_demo.mlir"
  if ← System.FilePath.pathExists path.parent.get! then
    IO.FS.writeFile path p256DemoMLIR
  : IO Unit)

end CatCrypt.Crypto.Jasmin.Examples.P256DemoEmit
