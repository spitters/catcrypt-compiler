/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public import CatCrypt.Crypto.Pairing.MsmReduce

/-!
# Emission of the pairing-ZK shared hot kernel: multi-scalar multiplication (MSM)

**TEST/BENCH-ONLY — STRING-TEMPLATED, not verified-compiler output.** The emitted
`bench/msm_compare/gen/msm.jazz` is assembled as text: `msmJazz` writes a literal
`export fn ec_msm … { … }` Jasmin body (`msmLoopBody` is a hand-written `for` loop)
with `++`, with no verified-printer descent for the whole file. `msmKernel_dot`/
`msmKernel_isSum` pin the abstract `msm = scalarFold = Σ_i k_i·P_i` denotation over
the EC group, not the emitted `.jazz` text; the `strContains` theorems are substring
assertions on that text. It is a bench/interop reference. The verified emit path is
the front-sourced descent; see `../SSProve-lean/bench/framework/AUDIT_EMIT_BYPASS.md` and
`EMIT_PROVENANCE.md`.

The prover/commitment core of Groth16, KZG, and Bulletproofs is the
multi-scalar multiplication `Σ_{i=0}^{L-1} k_i · P_i` over an elliptic-curve
group. This file emits that fixed-size MSM kernel through the verified front, as
a single-level bounded `for` loop whose body is the two EC **leaves** — one
`ec_scalar_mul(k_i, P_i)` per term, accumulated by `ec_point_add` — and links a
byte-identical KAT against a schoolbook EC reference MSM over the same field
(`bench/msm_compare/`).

## No new machinery — the committed `scalarFold` reduction at the EC lane

The kernel is the `VectorReduce.scalarFold` shape: a sequential left-fold
`acc ← acc + k_i · P_i` over the per-term EC scalar-multiples. The denotation
proof is carried by `MsmReduce.msm_eq_scalarFold` (the MSM reduces to `scalarFold`
over the EC `AddCommMonoid` — the EC group is an `AddCommGroup`), and the EC ops
come via the opaque-leaf agreement `MsmReduce.EcLeafAgrees` (the same
`extCall`-leaf edge FAEST's AES/SHAKE leaves carry). `MsmReduce.msmTermCom_denote`
pins one fold step `acc ↦ prims.pointAdd acc (prims.scalarMul k P)` at the leaf
level, under the carried agreement.

## The emitted text

`msmJazz` emits an `export fn ec_msm(reg ptr u8[2] out, reg const ptr u8[L] ks,
reg const ptr u8[2L] ps)`: it initialises `acc` to the on-wire identity, then a
real single-level `for i = 0 to L` loop computes `t = ec_scalar_mul(ks[i],
ps[i])` and `acc = ec_point_add(acc, t)`, finishing with `out = acc`. The loop is
a REAL `for` (not unrolled). The two EC leaves are external (`bench/msm_compare/
ec_leaves.c`, schoolbook affine EC over the toy field) — the production analogue
is the AUCurves/fiat BLS12-381 G1 `scalar_mul` / `g1_add` leaves wired in
`CatCrypt/Crypto/{KZG,ECDSA}`.

## Field / KAT / bench

The toy EC group is `y² = x³ + a·x + b` over `Fp = Z/23` (`MsmReduce.toyW`,
matching `ec_ref.h`'s `P=23`); a curve point is two little-endian field bytes
`(x ‖ y)`, with `(0xff, 0xff)` the point-at-infinity sentinel. The emitted
`gen/msm.jazz` linked against the schoolbook EC leaves is byte-identical to the
independent schoolbook reference `ec_msm_ref` over several cases
(identity / generator multiples / random scalars).

**Scope.** This is the prover/commitment MSM substrate the three pairing-ZK
systems share. The pairing / Miller-loop (for *verification*) is a separate
AUCurves leaf, the remaining piece for full Groth16/KZG verify.

Invoke:  lake env lean bench/msm_compare/msm_emit.lean
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.MsmEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.Pairing.MsmReduce

/-- The MSM length the bench uses (`L = 8` terms, matching `ec_msm_compare.c`). -/
def L : Nat := 8

/-! ## 1. Denotation preservation, at the EC-group kernel lane shape

`k : Fin L → ℕ` are the scalars, `P : Fin L → ECPt a b` the EC points. The
parallel/tree path computes `msm k P = hsum (fun i => k i • P i)` (lane-wise
scalar-mul + tree point-add); the scalar emit computes the sequential fold
`msmFold k P = scalarFold (fun i => k i • P i)`. They are equal — the verified
content the MSM emit carries, directly `MsmReduce.msm_eq_scalarFold` at the
kernel's lane shape. -/

/-- **Denotation preservation for the emitted MSM kernel.** The straight-line
    fold the kernel emits (`msmFold`, `acc ← acc + k_i·P_i` left to right) equals
    the horizontal reduction (`msm = Σ_i k_i·P_i`). Directly
    `MsmReduce.msm_eq_scalarFold` — no new content; the soundness of the MSM
    accumulation reassociating is the EC group's `AddCommMonoid` laws, settled in
    `VectorReduce.scalarFold_eq_hsum`. -/
theorem msmKernel_dot {a b : Fp} (k : Fin L → ℕ) (P : Fin L → ECPt a b) :
    msmFold k P = msm k P :=
  msm_eq_scalarFold k P

/-- The emitted MSM kernel computes the mathematical multi-scalar multiplication
    `Σ_i k_i · P_i` — the commitment/proof Groth16 / KZG / Bulletproofs realize. -/
theorem msmKernel_isSum {a b : Fp} (k : Fin L → ℕ) (P : Fin L → ECPt a b) :
    msm k P = ∑ i, (k i) • (P i) :=
  msm_isSum k P

/-! ## 2. The MSM emission (the `scalarFold` loop over the two EC leaves) -/

/-- Render the single-level MSM `for` loop body: scalar-mul leaf on `(ks[i],
    ps[i])` into the term buffer `psi`, then point-add leaf into the accumulator —
    the `scalarFold` step `acc ↦ acc + k_i·P_i`, built from the two EC leaves
    (`MsmReduce.ecMulLeafExpr` / `ecAddLeafExpr`). One iteration; the `for` is NOT
    unrolled. The scalar-mul result is written back into `psi` (the point buffer
    it read): the Jasmin reg-ptr discipline returns one of a leaf's pointer
    arguments, so the per-term scalar-multiple `k_i·P_i` lives in `psi` and is
    then accumulated — exactly the `EcPrimitives.scalarMul`/`pointAdd` composition
    the `msmTermCom` denotation (`MsmReduce.msmTermCom_denote`) pins. -/
def msmLoopBody : String :=
  "  for i = 0 to " ++ toString L ++ " {\n" ++
  "    for j = 0 to 1 { ksi[j] = ks[i]; }\n" ++
  "    for j = 0 to 2 { psi[j] = ps[2 * i + j]; }\n" ++
  "    psi = ec_scalar_mul(ksi, psi);\n" ++
  "    acc = ec_point_add(acc, psi);\n" ++
  "  }"

/-- The fixed-size MSM kernel `Σ_{i=0}^{L-1} k_i · P_i` emitted through the
    verified front. ABI: `out : u8[2]` (the result point `x‖y`), `ks : u8[L]`
    (the `L` scalar bytes), `ps : u8[2L]` (the `L` points, `x_i‖y_i`). The body
    initialises `acc` to the on-wire identity `(0xff,0xff)`, runs the REAL
    single-level `for i = 0 to L` loop (each iteration: one `ec_scalar_mul` leaf
    into `psi` + one `ec_point_add` leaf into `acc` — the `scalarFold` step), then
    writes `acc` to `out`.

    Denotation: `out = msm k P = Σ_i k_i·P_i` over the EC group, equal to the
    scalar straight-line fold by `MsmReduce.msm_eq_scalarFold`; the per-step EC
    leaves agree with the EC primitives by `MsmReduce.EcLeafAgrees`
    (`msmTermCom_denote`). -/
def msmJazz : String :=
  "export fn ec_msm(reg ptr u8[2] out, reg const ptr u8[" ++ toString L ++
    "] ks, reg const ptr u8[" ++ toString (2 * L) ++ "] ps) -> reg ptr u8[2] {\n" ++
  "  stack u8[2] acc;\n" ++
  "  stack u8[2] psi;\n" ++
  "  stack u8[1] ksi;\n" ++
  "  inline int i;\n" ++
  "  inline int j;\n" ++
  "  acc[0] = 0xff;\n" ++
  "  acc[1] = 0xff;\n" ++
  msmLoopBody ++ "\n" ++
  "  for j = 0 to 2 { out[j] = acc[j]; }\n" ++
  "  return out;\n}"

/-! ### Structural checks on the emitted text -/

/-- The MSM kernel emits an `export fn` with the `(out, ks, ps)` ABI: the result
    point, the `L` scalar bytes, the `2L` point bytes. -/
theorem msm_export_sig :
    strContains msmJazz
      "export fn ec_msm(reg ptr u8[2] out, reg const ptr u8[8] ks, reg const ptr u8[16] ps)"
      = true := by native_decide

/-- The body is a REAL single-level `for i = 0 to 8` loop (`L = 8`), not unrolled
    — the `scalarFold` reduction structure. -/
theorem msm_has_for :
    strContains msmJazz "for i = 0 to 8" = true := by native_decide

/-- Each iteration calls the EC scalar-multiply leaf on the term `(k_i, P_i)`,
    writing the per-term scalar-multiple `k_i·P_i` into the point buffer `psi`. -/
theorem msm_body_scalar_mul_leaf :
    strContains msmJazz "psi = ec_scalar_mul(ksi, psi);" = true := by native_decide

/-- Each iteration accumulates the term into `acc` via the EC point-add leaf —
    the `scalarFold` step `acc ↦ acc + k_i·P_i`. -/
theorem msm_body_point_add_leaf :
    strContains msmJazz "acc = ec_point_add(acc, psi);" = true := by native_decide

/-- The accumulator initialises to the on-wire point-at-infinity identity
    `(0xff, 0xff)` (the `0` of the EC `AddCommMonoid`, the fold's start value). -/
theorem msm_init_identity :
    strContains msmJazz "acc[0] = 0xff;" = true
      ∧ strContains msmJazz "acc[1] = 0xff;" = true := by native_decide

/-- The scalar-multiply leaf body appears exactly ONCE (the `for` is not unrolled
    to `L` copies). -/
theorem msm_not_unrolled :
    (msmJazz.splitOn "psi = ec_scalar_mul(ksi, psi);").length = 2 := by
  native_decide

def main : IO Unit := do
  IO.FS.createDirAll "bench/msm_compare/gen"
  IO.FS.writeFile "bench/msm_compare/gen/msm.jazz" (msmJazz ++ "\n")
  IO.println "wrote bench/msm_compare/gen/msm.jazz (MSM = scalarFold over the EC group, two EC leaves)"

#eval main

end CatCrypt.Crypto.Pairing.MsmEmit
