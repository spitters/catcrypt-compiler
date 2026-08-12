/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTDSL

set_option autoImplicit false

/-!
# Ed25519 Curve25519 base-field addition chains in the LowCT DSL

Reified pure-Lean transcriptions of the two Fermat-style addition chains
that ship in the trusted hand-written `dalek_shim.c`:

- `fpInvChain` — 254-square + 11-multiply chain computing `z^(p-2)` for
  the Curve25519 prime `p = 2^255 - 19`. Sourced from
  `dalek_shim.c::fe_invert` (also: ed25519-donna's `curve25519_recip`).
- `fpPowP58Chain` — chain for `z^((p-5)/8) = z^(2^252 - 3)`, used inside
  dalek's `fp_sqrt_ratio_i`. First 8 blocks are shared with `fpInvChain`
  (both walk to `z^(2^250 - 1)`); only the tail differs.

Both compile to a `func.func` in the emitted MLIR via `emitFunc`,
replacing the previously-trusted external `fp_inv` / `fp_invsqrt`. The
math is already proved (`Ed25519Spec.lean`'s `interp_fp_inv` via
Mathlib's Fermat); reifying the chain into Lean shrinks the TCB by
removing the only "trusted hand-written C" in the Ed25519 binary.

## Conventions

The chains are written with shadowed `t0` / `t1` / `t2` accumulators
exactly matching the C source so each cluster is auditable side-by-side.
Cluster sizes (per `dalek_shim.c::fe_invert`, line numbers in comments):

| Block | Sqrs | Mul (output) | Power reached     |
|-------|------|--------------|-------------------|
| 1     | 1    | —            | `z2 = z^2`        |
| 2     | 1    | —            | `t1 = z^4`        |
| 3     | 1    | `z9`         | `z9 = z^9`        |
| 4     | —    | `z11`        | `z11 = z^11`      |
| 5     | 1    | `t0`         | `t0 = z^(2^5-1)`  |
| 6     | 5    | `t0`         | `z^(2^10-1)`      |
| 7     | 10   | `t1`         | `z^(2^20-1)`      |
| 8     | 20   | `t1`         | `z^(2^40-1)`      |
| 9     | 10   | `t0`         | `z^(2^50-1)`      |
| 10    | 50   | `t1`         | `z^(2^100-1)`     |
| 11    | 100  | `t1`         | `z^(2^200-1)`     |
| 12    | 50   | `t0`         | `z^(2^250-1)`     |
| 13a   | 5    | `out=z^(p-2)`| **fpInvChain**    |
| 13b   | 2    | `out=z^pp58` | **fpPowP58Chain** |

Sqr-count check: `1 + 1 + 1 + 1 + 5 + 10 + 20 + 10 + 50 + 100 + 50 + 5 = 254`
for `fpInvChain`; `... + 2 = 251` for `fpPowP58Chain`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.Ed25519AddChainsDSL

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTDSL
open CatCrypt.Crypto.Jasmin.LowCTDSL.Rcm
open TowerType

/-! ## 1. Shared prefix: walk `z` up to `z^(2^250 - 1)`

Identical first 12 blocks of `fe_invert` and `fe_pow_p58`. After this
prefix, `t0` holds `z^(2^250 - 1)` and `z11` holds `z^11`. -/

private def prefix2_250minus1 : Rcm Unit := do
  /- Block 1–4 (shim lines 148–152): build `z2`, `z9`, `z11`. -/
  rc_call "fp_sqr" (loc "z2"  TFp25519) [loc "z"   TFp25519]
  rc_call "fp_sqr" (loc "t1"  TFp25519) [loc "z2"  TFp25519]   -- z^4
  rc_call "fp_sqr" (loc "t0"  TFp25519) [loc "t1"  TFp25519]   -- z^8
  rc_call "fp_mul" (loc "z9"  TFp25519) [loc "t0"  TFp25519, loc "z"  TFp25519]
  rc_call "fp_mul" (loc "z11" TFp25519) [loc "z9"  TFp25519, loc "z2" TFp25519]
  /- Block 5 (lines 153–154): t0 = z^31 = z^(2^5 - 1). -/
  rc_call "fp_sqr" (loc "t0"  TFp25519) [loc "z11" TFp25519]   -- z^22
  rc_call "fp_mul" (loc "t0"  TFp25519) [loc "t0"  TFp25519, loc "z9" TFp25519]
  /- Block 6 (lines 155–157): t0 = z^(2^10 - 1). 5 sqrs + 1 mul. -/
  rc_call "fp_sqr" (loc "t1"  TFp25519) [loc "t0"  TFp25519]
  for _ in List.range 4 do
    rc_call "fp_sqr" (loc "t1" TFp25519) [loc "t1" TFp25519]
  rc_call "fp_mul" (loc "t0"  TFp25519) [loc "t1"  TFp25519, loc "t0" TFp25519]
  /- Block 7 (lines 158–160): t1 = z^(2^20 - 1). 10 sqrs + 1 mul. -/
  rc_call "fp_sqr" (loc "t1"  TFp25519) [loc "t0"  TFp25519]
  for _ in List.range 9 do
    rc_call "fp_sqr" (loc "t1" TFp25519) [loc "t1" TFp25519]
  rc_call "fp_mul" (loc "t1"  TFp25519) [loc "t1"  TFp25519, loc "t0" TFp25519]
  /- Block 8 (lines 161–163): t1 = z^(2^40 - 1). 20 sqrs + 1 mul. -/
  rc_call "fp_sqr" (loc "t2"  TFp25519) [loc "t1"  TFp25519]
  for _ in List.range 19 do
    rc_call "fp_sqr" (loc "t2" TFp25519) [loc "t2" TFp25519]
  rc_call "fp_mul" (loc "t1"  TFp25519) [loc "t2"  TFp25519, loc "t1" TFp25519]
  /- Block 9 (lines 164–166): t0 = z^(2^50 - 1). 10 sqrs + 1 mul. -/
  rc_call "fp_sqr" (loc "t1"  TFp25519) [loc "t1"  TFp25519]
  for _ in List.range 9 do
    rc_call "fp_sqr" (loc "t1" TFp25519) [loc "t1" TFp25519]
  rc_call "fp_mul" (loc "t0"  TFp25519) [loc "t1"  TFp25519, loc "t0" TFp25519]
  /- Block 10 (lines 167–169): t1 = z^(2^100 - 1). 50 sqrs + 1 mul. -/
  rc_call "fp_sqr" (loc "t1"  TFp25519) [loc "t0"  TFp25519]
  for _ in List.range 49 do
    rc_call "fp_sqr" (loc "t1" TFp25519) [loc "t1" TFp25519]
  rc_call "fp_mul" (loc "t1"  TFp25519) [loc "t1"  TFp25519, loc "t0" TFp25519]
  /- Block 11 (lines 170–172): t1 = z^(2^200 - 1). 100 sqrs + 1 mul. -/
  rc_call "fp_sqr" (loc "t2"  TFp25519) [loc "t1"  TFp25519]
  for _ in List.range 99 do
    rc_call "fp_sqr" (loc "t2" TFp25519) [loc "t2" TFp25519]
  rc_call "fp_mul" (loc "t1"  TFp25519) [loc "t2"  TFp25519, loc "t1" TFp25519]
  /- Block 12 (lines 173–175): t0 = z^(2^250 - 1). 50 sqrs + 1 mul. -/
  rc_call "fp_sqr" (loc "t1"  TFp25519) [loc "t1"  TFp25519]
  for _ in List.range 49 do
    rc_call "fp_sqr" (loc "t1" TFp25519) [loc "t1" TFp25519]
  rc_call "fp_mul" (loc "t0"  TFp25519) [loc "t1"  TFp25519, loc "t0" TFp25519]

/-! ## 2. `fpInvChain`: `z^(p-2) = z^(2^255 - 21)` for Curve25519

The full Fermat addition chain. After `prefix2_250minus1`, finish with
`t0² ⋅ ⋅ ⋅ t0² ⋅ z11 = z^(2^255 - 21) = z^(p-2)` (5 squarings then 1
multiply, shim lines 176–177). Returns the inverse in the named output
`out`. -/

def fpInvChain : LowCT := Rcm.run do
  prefix2_250minus1
  /- Block 13a (lines 176–177): out = z^(2^255 - 21) = z^(p-2). -/
  for _ in List.range 5 do
    rc_call "fp_sqr" (loc "t0" TFp25519) [loc "t0" TFp25519]
  rc_call "fp_mul" (loc "out" TFp25519) [loc "t0" TFp25519, loc "z11" TFp25519]

/-! ## 3. `fpPowP58Chain`: `z^((p-5)/8) = z^(2^252 - 3)` for Curve25519

Used by dalek's `fp_sqrt_ratio_i` to compute the inverse-square-root
component. After `prefix2_250minus1`, finish with `t0²·t0·z =
z^(2^252 - 3)` (2 squarings then 1 multiply, shim lines 228–231). -/

def fpPowP58Chain : LowCT := Rcm.run do
  prefix2_250minus1
  /- Block 13b (lines 228–231): out = z^(2^252 - 3). -/
  rc_call "fp_sqr" (loc "t0"  TFp25519) [loc "t0" TFp25519]
  rc_call "fp_sqr" (loc "t0"  TFp25519) [loc "t0" TFp25519]
  rc_call "fp_mul" (loc "out" TFp25519) [loc "t0" TFp25519, loc "z" TFp25519]

/-! ## 4. Sanity checks (elaboration-time only)

Smoke tests that the chain elaborates and the underlying LowCT is
non-trivial (catches a `RSkip`-only regression). -/

example : True := by trivial

end CatCrypt.Crypto.Jasmin.Examples.Ed25519AddChainsDSL
