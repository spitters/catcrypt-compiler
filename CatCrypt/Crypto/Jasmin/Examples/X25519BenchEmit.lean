/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTToMLIR
import CatCrypt.Crypto.Jasmin.LowCTDSL

/-!
# X25519 half-step + fullstep emitted via the DSL

Mirrors the existing `catcrypt-bench/src/x25519_{halfstep,fullstep}.mlir`
files — same signatures, same external leaves — but authored in the
LowCT DSL and emitted through the direct `LowCT → MLIR` printer.

The output MLIR is intended to drop into `catcrypt-bench/src/` and
flow through the same `mlir-opt-20 → mlir-translate-20 → clang`
pipeline as the hand-authored version, so runtime numbers are a fair
apples-to-apples comparison.

## Usage

```
#eval IO.FS.writeFile
  "bench/x25519_halfstep_dsl.mlir"
  halfstepMLIR
```
-/

namespace CatCrypt.Crypto.Jasmin.Examples.X25519BenchEmit

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTDSL
open CatCrypt.Crypto.Jasmin.LowCTDSL.Rcm
open CatCrypt.Crypto.Jasmin.LowCTToMLIR
open TowerType

/-! ## Half-step

Single Montgomery-ladder body producing x2' = AA · BB, where
AA = (x2+z2)², BB = (x2-z2)². Five field operations: add, sub, sqr, sqr, mul. -/

/-- DSL authoring of the half-step body. Inputs `x2` and `z2` are
    expected to be function arguments; we just emit the compute steps. -/
def halfstepBody : LowCT := Rcm.run do
  rc_call "fp_add" (loc "A" TFp25519) [loc "x2" TFp25519, loc "z2" TFp25519]
  rc_call "fp_sub" (loc "B" TFp25519) [loc "x2" TFp25519, loc "z2" TFp25519]
  rc_call "fp_sqr" (loc "AA" TFp25519) [loc "A" TFp25519]
  rc_call "fp_sqr" (loc "BB" TFp25519) [loc "B" TFp25519]
  rc_call "fp_mul" (loc "x2p" TFp25519) [loc "AA" TFp25519, loc "BB" TFp25519]

/-- MLIR externs common to X25519 Montgomery-form field ops. -/
def x25519Externs : List (String × Nat × TowerType × TowerType) :=
  [ ("fp_add",     2, .TFp25519, .TFp25519)
  , ("fp_sub",     2, .TFp25519, .TFp25519)
  , ("fp_mul",     2, .TFp25519, .TFp25519)
  , ("fp_sqr",     1, .TFp25519, .TFp25519)
  , ("fp_mul_a24", 1, .TFp25519, .TFp25519) ]

/-- Half-step MLIR module. Signature matches `x25519_halfstep.mlir`:
    `(memref<5xi64>, memref<5xi64>) -> memref<5xi64>`. -/
def halfstepMLIR : String :=
  emitModule
    "x25519_halfstep_dsl"
    [("x2", .TFp25519), ("z2", .TFp25519)]
    "x2p" .TFp25519
    halfstepBody
    x25519Externs

/-! ## Full-step: four separate outputs (matching the hand-written bench)

**Important**: because VIR has single-return (one `func.func` per output),
each of the four step functions re-does any shared work. `func.call` is a
side-effecting op to LLVM, so CSE across `func.func`s does not dedup
the field ops — each function literally runs its own computation. We
therefore only compute what each output *needs*, not a shared prelude.
-/

/-- Compute x2' = (x2+z2)² · (x2-z2)². Needs: A, B, AA, BB, AA*BB. -/
def fullstep_x2 : LowCT := Rcm.run do
  rc_call "fp_add" (loc "A"  TFp25519) [loc "x2" TFp25519, loc "z2" TFp25519]
  rc_call "fp_sub" (loc "B"  TFp25519) [loc "x2" TFp25519, loc "z2" TFp25519]
  rc_call "fp_sqr" (loc "AA" TFp25519) [loc "A" TFp25519]
  rc_call "fp_sqr" (loc "BB" TFp25519) [loc "B" TFp25519]
  rc_call "fp_mul" (loc "x2p" TFp25519) [loc "AA" TFp25519, loc "BB" TFp25519]

/-- Compute z2' = E · (BB + 121666·E). Needs: A, B, AA, BB, E, a24·E, inn, z2p.  -/
def fullstep_z2 : LowCT := Rcm.run do
  rc_call "fp_add" (loc "A"  TFp25519) [loc "x2" TFp25519, loc "z2" TFp25519]
  rc_call "fp_sub" (loc "B"  TFp25519) [loc "x2" TFp25519, loc "z2" TFp25519]
  rc_call "fp_sqr" (loc "AA" TFp25519) [loc "A" TFp25519]
  rc_call "fp_sqr" (loc "BB" TFp25519) [loc "B" TFp25519]
  rc_call "fp_sub" (loc "E"  TFp25519) [loc "AA" TFp25519, loc "BB" TFp25519]
  rc_call "fp_mul_a24" (loc "a24E" TFp25519) [loc "E" TFp25519]
  rc_call "fp_add" (loc "inn" TFp25519) [loc "BB" TFp25519, loc "a24E" TFp25519]
  rc_call "fp_mul" (loc "z2p" TFp25519) [loc "E" TFp25519, loc "inn" TFp25519]

/-- Compute x3' = (DA+CB)². Needs: A, B, C, D, DA, CB, DA+CB, squared. -/
def fullstep_x3 : LowCT := Rcm.run do
  rc_call "fp_add" (loc "A" TFp25519) [loc "x2" TFp25519, loc "z2" TFp25519]
  rc_call "fp_sub" (loc "B" TFp25519) [loc "x2" TFp25519, loc "z2" TFp25519]
  rc_call "fp_add" (loc "C" TFp25519) [loc "x3" TFp25519, loc "z3" TFp25519]
  rc_call "fp_sub" (loc "D" TFp25519) [loc "x3" TFp25519, loc "z3" TFp25519]
  rc_call "fp_mul" (loc "DA" TFp25519) [loc "D" TFp25519, loc "A" TFp25519]
  rc_call "fp_mul" (loc "CB" TFp25519) [loc "C" TFp25519, loc "B" TFp25519]
  rc_call "fp_add" (loc "DApCB" TFp25519) [loc "DA" TFp25519, loc "CB" TFp25519]
  rc_call "fp_sqr" (loc "x3p" TFp25519) [loc "DApCB" TFp25519]

/-- Compute z3' = x1 · (DA-CB)². -/
def fullstep_z3 : LowCT := Rcm.run do
  rc_call "fp_add" (loc "A" TFp25519) [loc "x2" TFp25519, loc "z2" TFp25519]
  rc_call "fp_sub" (loc "B" TFp25519) [loc "x2" TFp25519, loc "z2" TFp25519]
  rc_call "fp_add" (loc "C" TFp25519) [loc "x3" TFp25519, loc "z3" TFp25519]
  rc_call "fp_sub" (loc "D" TFp25519) [loc "x3" TFp25519, loc "z3" TFp25519]
  rc_call "fp_mul" (loc "DA" TFp25519) [loc "D" TFp25519, loc "A" TFp25519]
  rc_call "fp_mul" (loc "CB" TFp25519) [loc "C" TFp25519, loc "B" TFp25519]
  rc_call "fp_sub" (loc "DAmCB" TFp25519) [loc "DA" TFp25519, loc "CB" TFp25519]
  rc_call "fp_sqr" (loc "DAmCB2" TFp25519) [loc "DAmCB" TFp25519]
  rc_call "fp_mul" (loc "z3p" TFp25519) [loc "x1" TFp25519, loc "DAmCB2" TFp25519]

/-- All four full-step function entries, concatenated. The `%arg0..4`
    convention mirrors the hand-authored `x25519_fullstep.mlir`:
    `arg0=x1, arg1=x2, arg2=z2, arg3=x3, arg4=z3`. -/
def fullstepFuncs : String :=
  let argList : List (String × TowerType) :=
    [("x1", .TFp25519), ("x2", .TFp25519), ("z2", .TFp25519),
     ("x3", .TFp25519), ("z3", .TFp25519)]
  emitFunc "x25519_step_x2_dsl" argList "x2p" .TFp25519 fullstep_x2 ++ "\n\n" ++
  emitFunc "x25519_step_z2_dsl" argList "z2p" .TFp25519 fullstep_z2 ++ "\n\n" ++
  emitFunc "x25519_step_x3_dsl" argList "x3p" .TFp25519 fullstep_x3 ++ "\n\n" ++
  emitFunc "x25519_step_z3_dsl" argList "z3p" .TFp25519 fullstep_z3

/-- Full-step MLIR module. -/
def fullstepMLIR : String :=
  emitExterns x25519Externs ++ "\n" ++ fullstepFuncs

/-! ## Emission entry points -/

/-- Write the half-step MLIR to `catcrypt-bench/src/`. -/
def writeHalfstepMLIR (path : String) : IO Unit :=
  IO.FS.writeFile path halfstepMLIR

/-- Write the full-step MLIR to `catcrypt-bench/src/`. -/
def writeFullstepMLIR (path : String) : IO Unit :=
  IO.FS.writeFile path fullstepMLIR

-- Emit at elaboration time, but skip silently if the catcrypt-bench
-- source tree is not present (e.g. CI environments without the sibling repo).
private def maybeWrite (path : String) (write : String → IO Unit) : IO Unit := do
  let p : System.FilePath := path
  if ← System.FilePath.pathExists p.parent.get! then
    write path

#eval maybeWrite
  "bench/x25519_halfstep_dsl.mlir"
  writeHalfstepMLIR
#eval maybeWrite
  "bench/x25519_fullstep_dsl.mlir"
  writeFullstepMLIR

end CatCrypt.Crypto.Jasmin.Examples.X25519BenchEmit
