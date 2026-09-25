/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LeafSig
public import CatCrypt.Crypto.Jasmin.LeafSig
public meta import CatCrypt.Crypto.Vale.LeafLeakage
public import CatCrypt.Crypto.Vale.LeafLeakage


@[expose] public section
set_option autoImplicit false

/-!
# secp256k1 scalar-multiplication leaves (libsecp256k1 wNAF ecmult)

This module declares libsecp256k1's constant-time wNAF / signed-digit
scalar-multiplication routines as opaque verified-CT leaves for
CatCrypt's verified front, following the established extCall pattern
(`Jasmin.LowCT` `RCall`) used for the HACL\*/Vale Curve25519,
ChaCha20-Vec256, SHA-256, SHA-512, GHASH-CLMUL, AES-GCM and the
AUCurves BY/safegcd-secp256k1 inversion leaves.

## Why scalar-mult and not (only) inversion

The wave-1 secp256k1 adoption took *field inversion* (BY/safegcd,
`CatCrypt/Crypto/Vale/SafegcdSecp256k1.lean`) at ≈0.85× vs
libsecp256k1 — a leaf win, but the macro impact on **Bitcoin ECDSA
signature verification** is ≈1%, because verify is
**scalar-multiplication-bound**, not inversion-bound:

* A single ECDSA verify is dominated by the double-scalar
  multiplication `u1·G + u2·Q` (≈50–100 Kcyc on modern x86),
  computed by libsecp256k1's `secp256k1_ecmult` (Straus / wNAF with
  the precomputed generator table `secp256k1_pre_g`).
* Field inversion (`secp256k1_fe_inv`, ≈4 Kcyc) appears only when
  normalising the result point's Z-coordinate — a small constant.

To move the needle on Bitcoin verify chains the leaf adoption must
happen at the **scalar-multiplication boundary**. This module declares
that boundary:

* `secp256k1_ecmult_const` — single-scalar `k·P` (constant-time;
  ECDH / `tweak` paths).
* `secp256k1_ecmult` — double-scalar `u1·G + u2·Q` (the ECDSA verify
  hot path).

## Trust baseline — this is *trust narrowing*, NOT verified-from-scratch

**No verified-CT secp256k1 scalar-multiplication exists in AUCurves.**
AUCurves' only secp256k1 code is *field* arithmetic
(`secp256k1-safe-rust/src/lib.rs`: fiat-crypto field ops + the
Bernstein–Yang `fp_inv`). Its verified-CT scalar-multiplication work
(X25519, the Straus 2-MSM ed25519 verify body in
`src/Bedrock/End2End/Ed25519/Straus2MSMBody.v`) is exclusively for the
**Curve25519 / Edwards** family — there is no secp256k1 `ecmult`
bedrock2 / fiat extraction.

Therefore this leaf adopts **libsecp256k1's own wNAF ecmult**
(`src/ecmult_const_impl.h`, `src/ecmult_impl.h`) as the trust
baseline. The trust delta is a **trust narrowing**: we replace a
hand-emitted scalar-mult (which we have not proved) with the
production, heavily-reviewed Bitcoin reference whose constant-time
discipline is the de-facto standard for the curve. This is weaker than
the BY/safegcd-secp256k1 inversion leaf, which cites an AUCurves
machine-checked convergence certificate. We do **not** overstate the
trust delta: the denotation axioms below are *specifications matched
against libsecp256k1*, not consequences of a CatCrypt/AUCurves
machine-checked proof.

## CT discipline (the constant-time claim)

libsecp256k1's `ecmult_const` uses a fixed signed-digit / GLV ladder
with no secret-dependent branches or memory indices (the table lookup
`secp256k1_ecmult_const_table_get_ge` is a constant-time conditional
sweep over the precomputed window). `secp256k1_ecmult` (the verify
path) is *not* claimed constant-time by libsecp256k1 in general —
verify operates on public inputs (`u1`, `u2`, `Q` are all public in
ECDSA verification), so CT is not required there. We record the CT
prop only for the single-scalar `ecmult_const` (the secret-scalar
path) and explicitly mark `ecmult` (double-scalar verify) as a
public-input routine.

## Leaf C signatures (the shim, exposed by the bench's staticlib)

```c
/* single-scalar k·P, P given as 64-byte (x,y) BE affine, k as 32-byte
   BE scalar; out is 64-byte (x,y) BE affine. CT in k. */
extern void secp256k1_ecmult_const_leaf(uint8_t out64[64],
                                        const uint8_t p64[64],
                                        const uint8_t k32[32]);

/* double-scalar u1·G + u2·Q (the ECDSA verify step), G = SEC2
   generator (implicit), Q as 64-byte BE affine, u1/u2 as 32-byte BE
   scalars; out is 64-byte BE affine. Public inputs. */
extern void secp256k1_ecmult_double_leaf(uint8_t out64[64],
                                         const uint8_t u1_32[32],
                                         const uint8_t u2_32[32],
                                         const uint8_t q64[64]);
```

Both wrap the file-static libsecp256k1 routines (the shim links the
amalgamation `secp256k1.c` + `precomputed_ecmult.c`).
-/

namespace CatCrypt.Crypto.Vale.Secp256k1Ecmult

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Opaque surface types

A secp256k1 scalar (32-byte big-endian, reduced mod the group order
`n`) and a secp256k1 affine point (64 bytes: x ‖ y, each 32-byte
big-endian). Opaque — the concrete leaves at link time are
libsecp256k1's `secp256k1_ecmult_const` / `secp256k1_ecmult`. -/

opaque Secp256k1Scalar.Impl : NonemptyType.{0}
/-- A secp256k1 scalar (32-byte big-endian, reduced mod the group
    order `n = 2^256 − 432420386565659656852420866394968145599`).
    Opaque. -/
def Secp256k1Scalar : Type := Secp256k1Scalar.Impl.type
instance : Nonempty Secp256k1Scalar := Secp256k1Scalar.Impl.property
/-- An inhabitant. -/
noncomputable opaque Secp256k1Scalar.default : Secp256k1Scalar
noncomputable instance : Inhabited Secp256k1Scalar :=
  ⟨Secp256k1Scalar.default⟩

opaque Secp256k1Point.Impl : NonemptyType.{0}
/-- A secp256k1 affine point (64 bytes: x ‖ y, each 32-byte
    big-endian), or the point at infinity (encoded as all-zero by the
    shim). Opaque. -/
def Secp256k1Point : Type := Secp256k1Point.Impl.type
instance : Nonempty Secp256k1Point := Secp256k1Point.Impl.property
/-- An inhabitant. -/
noncomputable opaque Secp256k1Point.default : Secp256k1Point
noncomputable instance : Inhabited Secp256k1Point :=
  ⟨Secp256k1Point.default⟩

/-! ## §2. Scalar-mult leaf axioms (the trust delta)

These are the denotation + CT axioms we add to CatCrypt's axiom budget
when we permit the libsecp256k1 scalar-mult leaves. Unlike the
BY/safegcd inversion leaf, these are *specifications matched against
libsecp256k1's reviewed implementation*, not consequences of a
machine-checked certificate (no verified-CT secp256k1 scalar-mult
exists upstream — see the module docstring). -/

/-- **Single-scalar denotation axiom**: the libsecp256k1
    `secp256k1_ecmult_const` leaf computes `k · P` on the secp256k1
    curve (`y² = x³ + 7` over `F_p`, `p = 2^256 − 2^32 − 977`), with
    `k` reduced mod the group order `n`. Matched against
    libsecp256k1's reviewed signed-digit / GLV ladder
    (`src/ecmult_const_impl.h`). -/
noncomputable opaque Secp256k1Ecmult_const_denote
    (k : Secp256k1Scalar) (P : Secp256k1Point) : Secp256k1Point

/-- **Double-scalar denotation axiom**: the libsecp256k1
    `secp256k1_ecmult` leaf computes `u1 · G + u2 · Q`, where `G` is
    the fixed SEC2 generator (consumed via the static precomputed
    table `secp256k1_pre_g`) and `Q` is the public key point. This is
    the ECDSA signature-verification step. Matched against
    libsecp256k1's Straus / wNAF implementation
    (`src/ecmult_impl.h`). -/
noncomputable opaque Secp256k1Ecmult_double_denote
    (u1 u2 : Secp256k1Scalar) (Q : Secp256k1Point) : Secp256k1Point

/-- **Constant-time axiom (single-scalar only)**: the libsecp256k1
    `secp256k1_ecmult_const` leaf is constant-time in the secret
    scalar `k`. Sourced from the libsecp256k1 CT discipline: a fixed
    signed-digit ladder over a precomputed window, with constant-time
    conditional table sweeps (`secp256k1_ecmult_const_table_get_ge`)
    and no secret-dependent branches or memory indices. This is the
    same discipline libsecp256k1 documents for its ECDH path.

    NOTE: `Secp256k1Ecmult_double_denote` (the verify double-scalar
    path) is **not** marked constant-time — ECDSA verification
    operates on entirely public inputs (`u1`, `u2`, `Q`), so CT is not
    a requirement there, and libsecp256k1's `secp256k1_ecmult` makes
    no CT claim. -/
noncomputable opaque Secp256k1Ecmult_const_leak
    (P : Secp256k1Point) (k : Secp256k1Scalar) : LeafLeak

/-- **Constant-time axiom (single-scalar only)**: at each fixed base point
    `P`, the leakage trace of the `secp256k1_ecmult_const` leaf is the same at
    every scalar `k`. The point is the public parameter; the scalar is the
    secret one. The companion `Secp256k1Ecmult_double_denote` leaf is
    variable-time and carries no such axiom. `ValeCoqAxioms.lean` records that
    no upstream proof of this was located. -/
axiom Secp256k1Ecmult_const_CT (P : Secp256k1Point) :
    SecretIndependent (Secp256k1Ecmult_const_leak P)

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `Vale/SafegcdSecp256k1.lean` pattern: registering each
leaf so the verified front accepts the corresponding `RCall` as a
well-formed extCall.

* `secp256k1_ecmult_const_leaf`  — arity 2 (`k`, `P`).
* `secp256k1_ecmult_double_leaf` — arity 3 (`u1`, `u2`, `Q`).

The `towerType` records the *result* packing: a 64-byte affine point
(`TBytes 64`). -/

/-- Register `Secp256k1Ecmult_const_denote` → leaf
    `secp256k1_ecmult_const_leaf`. -/
@[rust_cmd_pattern]
def secp256k1EcmultConstPattern : LowCTPattern where
  name      := "secp256k1_ecmult_const_leaf"
  fnHead    := ``Secp256k1Ecmult_const_denote
  arity     := 2
  towerType := .TBytes 64   -- 64-byte affine point (x ‖ y)

/-- Register `Secp256k1Ecmult_double_denote` → leaf
    `secp256k1_ecmult_double_leaf`. -/
@[rust_cmd_pattern]
def secp256k1EcmultDoublePattern : LowCTPattern where
  name      := "secp256k1_ecmult_double_leaf"
  fnHead    := ``Secp256k1Ecmult_double_denote
  arity     := 3
  towerType := .TBytes 64   -- 64-byte affine point (x ‖ y)

/-! ## §4. Tower-type abbreviations -/

/-- Tower type of a secp256k1 scalar (`TBytes 32`, 32-byte BE). -/
def secp256k1ScalarTowerType : TowerType := .TBytes 32

/-- Tower type of a secp256k1 affine point (`TBytes 64`, x ‖ y). -/
def secp256k1PointTowerType : TowerType := .TBytes 64

/-! ## §5. `LeafSig` entries

Both leaves are non-aliasing at the SSA level: `out` is distinct from
all inputs in the shim signatures. We declare `destAliasOk := []`. -/

/-- Per-leaf signature for `secp256k1_ecmult_const_leaf`. -/
def secp256k1EcmultConstLeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "secp256k1_ecmult_const_leaf"
  destAliasOk := []

/-- Per-leaf signature for `secp256k1_ecmult_double_leaf`. -/
def secp256k1EcmultDoubleLeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "secp256k1_ecmult_double_leaf"
  destAliasOk := []

/-! ## §6. Pure-Lean wrappers — the specs -/

/-- Single-scalar `k · P` via the libsecp256k1 `ecmult_const` leaf. -/
noncomputable def secp256k1EcmultConstLean
    (k : Secp256k1Scalar) (P : Secp256k1Point) : Secp256k1Point :=
  Secp256k1Ecmult_const_denote k P

/-- Double-scalar `u1 · G + u2 · Q` (the ECDSA verify step) via the
    libsecp256k1 `ecmult` leaf. -/
noncomputable def secp256k1EcmultDoubleLean
    (u1 u2 : Secp256k1Scalar) (Q : Secp256k1Point) : Secp256k1Point :=
  Secp256k1Ecmult_double_denote u1 u2 Q

/-! ## §7. Hand-built `LowCT` bodies (front-end input)

Following the `Vale/SafegcdSecp256k1.lean` pattern: the front-end
`reifyLowCT%` macro reads `knownOps` only, so we hand-build the
single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `secp256k1EcmultConstLean`. Shape:
    `RSeq RSkip (RCall "secp256k1_ecmult_const_leaf" __result [k, P])`. -/
def secp256k1EcmultConstBody : LowCT :=
  let k_l      := loc "k"        secp256k1ScalarTowerType
  let p_l      := loc "P"        secp256k1PointTowerType
  let result_l := loc "__result" secp256k1PointTowerType
  .RSeq .RSkip
    (.RCall "secp256k1_ecmult_const_leaf"
            result_l [k_l, p_l])

/-- The `LowCT` body for `secp256k1EcmultDoubleLean`. Shape:
    `RSeq RSkip (RCall "secp256k1_ecmult_double_leaf"
                       __result [u1, u2, Q])`. -/
def secp256k1EcmultDoubleBody : LowCT :=
  let u1_l     := loc "u1"       secp256k1ScalarTowerType
  let u2_l     := loc "u2"       secp256k1ScalarTowerType
  let q_l      := loc "Q"        secp256k1PointTowerType
  let result_l := loc "__result" secp256k1PointTowerType
  .RSeq .RSkip
    (.RCall "secp256k1_ecmult_double_leaf"
            result_l [u1_l, u2_l, q_l])

/-- `ReifiedFunc` bundle for the single-scalar `ecmult_const` leaf. -/
def secp256k1EcmultConstReified : ReifiedFunc :=
  { args    := [("k", secp256k1ScalarTowerType),
                ("P", secp256k1PointTowerType)]
    body    := secp256k1EcmultConstBody
    retName := "__result" }

/-- `ReifiedFunc` bundle for the double-scalar `ecmult` (verify) leaf. -/
def secp256k1EcmultDoubleReified : ReifiedFunc :=
  { args    := [("u1", secp256k1ScalarTowerType),
                ("u2", secp256k1ScalarTowerType),
                ("Q",  secp256k1PointTowerType)]
    body    := secp256k1EcmultDoubleBody
    retName := "__result" }

/-! ## §8. Inspection -/

#eval secp256k1EcmultConstReified.args.map Prod.fst   -- [k, P]
#eval secp256k1EcmultDoubleReified.args.map Prod.fst  -- [u1, u2, Q]
#eval secp256k1EcmultDoubleReified.args.length        -- 3
#eval secp256k1EcmultDoubleReified.retName            -- __result

end CatCrypt.Crypto.Vale.Secp256k1Ecmult
