/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTReflect
import CatCrypt.Crypto.Jasmin.LowCTToMLIR

/-!
# X25519 half-step + fullstep emitted via the Lean→LowCT reifier

This file takes the `ReifiedFunc` values produced by
`LowCTReflect`'s `reifyLowCT%` elaborator (walking pure Lean
functions over opaque `Fp25519`) and runs them through the direct
`LowCTToMLIR` emitter. Output drops into
`catcrypt-bench/src/x25519_*_reflect.mlir`.

Writes three files:
- `x25519_halfstep_reflect.mlir` — Lean-native halfstep reified.
- `x25519_fullstep_reflect.mlir` — four Lean-native step functions.
- (Compared against hand-VIR and DSL variants via `bench_reflect.c`.)
-/

namespace CatCrypt.Crypto.Jasmin.Examples.X25519ReflectEmit

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Jasmin.LowCTToMLIR

/-- Helper: write a string to `path`, but skip silently if the parent
directory is missing (e.g. CI environments without the sibling
`catcrypt-bench` source tree). -/
private def maybeWrite (path : String) (content : String) : IO Unit := do
  let p : System.FilePath := path
  if ← System.FilePath.pathExists p.parent.get! then
    IO.FS.writeFile path content

/-! ## 1. Externs (same as DSL path) -/

def x25519Externs : List (String × Nat × TowerType × TowerType) :=
  [ ("fp_add",     2, .TFp25519, .TFp25519)
  , ("fp_sub",     2, .TFp25519, .TFp25519)
  , ("fp_mul",     2, .TFp25519, .TFp25519)
  , ("fp_sqr",     1, .TFp25519, .TFp25519)
  , ("fp_mul_a24", 1, .TFp25519, .TFp25519) ]

/-! ## 2. Halfstep from the reified Lean function -/

def halfstepMLIR : String :=
  emitModule "x25519_halfstep_reflect"
    halfstepReified.args
    halfstepReified.retName
    .TFp25519
    halfstepReified.body
    x25519Externs

/-! ## 3. Four full-step functions from the reified Lean code -/

private def emitReified (name : String) (rf : ReifiedFunc) : String :=
  emitFunc name rf.args rf.retName .TFp25519 rf.body

def fullstepMLIR : String :=
  emitExterns x25519Externs ++ "\n" ++
  emitReified "x25519_step_x2_reflect" fullstepX2Reified ++ "\n\n" ++
  emitReified "x25519_step_z2_reflect" fullstepZ2Reified ++ "\n\n" ++
  emitReified "x25519_step_x3_reflect" fullstepX3Reified ++ "\n\n" ++
  emitReified "x25519_step_z3_reflect" fullstepZ3Reified

/-! ## 4. Emit at elaboration -/

#eval maybeWrite
  "bench/x25519_halfstep_reflect.mlir"
  halfstepMLIR

#eval maybeWrite
  "bench/x25519_fullstep_reflect.mlir"
  fullstepMLIR

/-! ## 5. Ed25519 Edwards point-add (4 outputs) from reified pure Lean -/

/-- Extended externs including `fp_opp` for doubling. -/
def x25519ExternsFull : List (String × Nat × TowerType × TowerType) :=
  x25519Externs ++ [("fp_opp", 1, .TFp25519, .TFp25519)]

def ed25519AddMLIR : String :=
  emitExterns x25519ExternsFull ++ "\n" ++
  emitReified "ed25519_add_x3" edwardsAddX3Reified ++ "\n\n" ++
  emitReified "ed25519_add_y3" edwardsAddY3Reified ++ "\n\n" ++
  emitReified "ed25519_add_t3" edwardsAddT3Reified ++ "\n\n" ++
  emitReified "ed25519_add_z3" edwardsAddZ3Reified

def ed25519DblMLIR : String :=
  emitExterns x25519ExternsFull ++ "\n" ++
  emitReified "ed25519_dbl_x3" edwardsDblX3Reified ++ "\n\n" ++
  emitReified "ed25519_dbl_y3" edwardsDblY3Reified ++ "\n\n" ++
  emitReified "ed25519_dbl_t3" edwardsDblT3Reified ++ "\n\n" ++
  emitReified "ed25519_dbl_z3" edwardsDblZ3Reified

#eval maybeWrite
  "bench/ed25519_add.mlir"
  ed25519AddMLIR

#eval maybeWrite
  "bench/ed25519_dbl.mlir"
  ed25519DblMLIR

/-! ## 6. Out-param variant — fiat-crypto-direct, no shim pool

Calls `fiat_25519_add`/`fiat_25519_sub`/`fiat_25519_carry_mul`/
`fiat_25519_carry_square`/`fiat_25519_opp`/`fiat_25519_carry_scmul_121666`
directly with out-param convention. Links against `curve25519_64.c`
directly (no fiat_shim.c pool indirection).

Expected speedup: ~3× (measured hand-C inlined is 47 μs vs pool-based
MLIR at 145 μs). -/

/-- Remap each `RCall` leaf name from our pool-ABI name to the fiat-crypto
    direct symbol. We walk the LowCT tree replacing call names. -/
partial def remapLeafs (c : LowCT) : LowCT :=
  let remap (s : String) : String :=
    match s with
    | "fp_add"     => "fiat_25519_add"
    | "fp_sub"     => "fiat_25519_sub"
    | "fp_mul"     => "fiat_25519_carry_mul"
    | "fp_sqr"     => "fiat_25519_carry_square"
    | "fp_opp"     => "fiat_25519_opp"
    | "fp_mul_a24" => "fiat_25519_carry_scmul_121666"
    | other        => other
  match c with
  | .RSkip              => .RSkip
  | .RSeq a b           => .RSeq (remapLeafs a) (remapLeafs b)
  | .RCall f d args     => .RCall (remap f) d args
  | .RLetZero x t body  => .RLetZero x t (remapLeafs body)
  | .RLetU64Zero x body => .RLetU64Zero x (remapLeafs body)
  | other               => other

/-- Externs for the direct-fiat out-param ABI. -/
def fiatDirectExterns : List (String × Nat × TowerType × TowerType) :=
  [ ("fiat_25519_add",             2, .TFp25519, .TFp25519)
  , ("fiat_25519_sub",             2, .TFp25519, .TFp25519)
  , ("fiat_25519_carry_mul",       2, .TFp25519, .TFp25519)
  , ("fiat_25519_carry_square",    1, .TFp25519, .TFp25519)
  , ("fiat_25519_opp",             1, .TFp25519, .TFp25519)
  , ("fiat_25519_carry_scmul_121666", 1, .TFp25519, .TFp25519) ]

private def emitReifiedOutParam (name : String) (rf : ReifiedFunc) : String :=
  emitFuncOutParam name rf.args rf.retName .TFp25519 (remapLeafs rf.body)

def ed25519AddMLIRv : String :=
  emitExternsOutParam fiatDirectExterns ++ "\n" ++
  emitReifiedOutParam "ed25519_add_x3_v" edwardsAddX3Reified ++ "\n\n" ++
  emitReifiedOutParam "ed25519_add_y3_v" edwardsAddY3Reified ++ "\n\n" ++
  emitReifiedOutParam "ed25519_add_t3_v" edwardsAddT3Reified ++ "\n\n" ++
  emitReifiedOutParam "ed25519_add_z3_v" edwardsAddZ3Reified

def ed25519DblMLIRv : String :=
  emitExternsOutParam fiatDirectExterns ++ "\n" ++
  emitReifiedOutParam "ed25519_dbl_x3_v" edwardsDblX3Reified ++ "\n\n" ++
  emitReifiedOutParam "ed25519_dbl_y3_v" edwardsDblY3Reified ++ "\n\n" ++
  emitReifiedOutParam "ed25519_dbl_t3_v" edwardsDblT3Reified ++ "\n\n" ++
  emitReifiedOutParam "ed25519_dbl_z3_v" edwardsDblZ3Reified

#eval maybeWrite
  "bench/ed25519_add_v.mlir" ed25519AddMLIRv

#eval maybeWrite
  "bench/ed25519_dbl_v.mlir" ed25519DblMLIRv

end CatCrypt.Crypto.Jasmin.Examples.X25519ReflectEmit
