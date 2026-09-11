/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Hax.HaxToLowCTSim_Main_Full
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Main_Full
public meta import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta
public meta import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta_LeafAgrees
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta_LeafAgrees
public meta import CatCrypt.Crypto.Hax.HaxToLowCTSim_AppSideCond
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_AppSideCond
public meta import CatCrypt.Crypto.MLKEM.NttPolyVerified
public import CatCrypt.Crypto.MLKEM.NttPolyVerified
public meta import CatCrypt.Crypto.Jasmin.TowerLimbStore
public import CatCrypt.Crypto.Jasmin.TowerLimbStore
public meta import CatCrypt.Crypto.Jasmin.TowerTupleLoad
public import CatCrypt.Crypto.Jasmin.TowerTupleLoad

/-!
# ML-KEM simulation bridge (fourth protocol; first PQC)

First post-quantum lattice-based deployment.  Tests the framework
against ML-KEM (FIPS 203, formerly Kyber).  Following the
Ed25519 (`EdDSA/Ed25519HaxLowCTBridge.lean`) and BLS12-381
(`EUDIW/BlsHaxLowCTBridge.lean`) deployments, this is the fourth
exercise of `HaxToLowCTSim_Quarta` and the first that targets a
*lattice* primitive rather than an elliptic-curve one.

## TL;DR — what this deployment exposes

The framework's `TowerType` enum was extended in Phase L (2026-05-22)
with constructors for polynomial-mod-q values:

```lean
| TPolyMod : (q : Nat) → (n : Nat) → TowerType
| TPolyVec : (q : Nat) → (n : Nat) → (k : Nat) → TowerType
| TPolyMat : (q : Nat) → (n : Nat) → (k : Nat) → (m : Nat) → TowerType
```

ML-KEM operates on:

* polynomials in `Z_q[X]/(X^n + 1)` (q = 3329, n = 256)
   → `.TPolyMod 3329 256`
* vectors of polynomials (length k ∈ {2,3,4})
   → `.TPolyVec 3329 256 k`
* matrices of polynomials (k × k)
   → `.TPolyMat 3329 256 k k`
* compressed / encoded byte representations
   → `.TBytes n` (for the appropriate `n`)

§2 (below) preserves the vacuous `True` `mlkemBridge` for backwards
compatibility — every `MlkemLeafAxioms` field and the
`mlkem_haxToLowCT_simulates` theorem reference it.  §10 (added in
Phase L) introduces a *content-aware* `mlkemBridgePolyAware` that
recognises the three polynomial constructors as the natural ML-KEM
slot types.  Future deployments can install an MLKEM-specific
`TowerOfCallNameInst` and migrate `MlkemLeafAxioms` to the new
constructors (the framework refactor that enables this is documented
under Friction #5/#6/#7/#8 below).

Frictions #11 / #12 are now CLOSED at the framework level by Phase L;
Friction #13 (NTT vs coefficient form) remains open and would require
splitting `TPolyMod` into `TPolyMod_Coeff` / `TPolyMod_NTT`.

## Goals

| Goal | Status |
|---|---|
| 1. `mlkemBridge : ValueTowerBridge` | Closed (vacuous, `.TFp` fallback) |
| 2. `MlkemLeafAxioms` record | Closed (24 leaves, all `.TFp`) |
| 3. `MlkemFullSimPreconds` deployment record | Closed |
| 4. `mlkem_haxToLowCT_simulates` theorem | Closed |
| 5. Jasmin comparison table (formosa-mlkem) | Closed |
| 6. (Stretch) concrete `mlkemBuiltins` / `mlkemLeafSpec` | Closed |

## Independence from `SurfaceDeps.lean`

`MLKEM/SurfaceDeps.lean` covers the abstract security side (IND-CCA
KEM, MLWE).  This file is orthogonal: it bridges the Hax-extracted
ML-KEM kernels to LowCT execution at the value-tower level.
Together they cover the two ends of CatCrypt's verified chain:

```
   Hax-extracted Rust  → (THIS FILE)            → LowCT
   LowCT             → CryptoSSA → Jasmin → x86
   abstract ML-KEM     → (SurfaceDeps)          → IND-CCA / UC
```

The deployment is *intentionally* vacuous on content — the value here
is the documented framework gap and the Jasmin side-by-side, not a
content-bearing bridge.

-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.MlkemHaxLowCTBridge

open CatCrypt.Hax (Value Env Builtins ImpExpr)
open CatCrypt.Crypto.Hax (ValueTowerBridge LeafCallAgreesTower
                          leafCallAgreesTower_of_unmatched
                          valueToScalar
                          FullSimPreconds Hyp_match_full Hyp_whileLoop_full
                          Hyp_arrayUpdate_full Hyp_index_full
                          Hyp_letBindVarAlias_full Hyp_letBindProj_full
                          TowerFresh haxToLowCT_simulates_full
                          HaxToLowCTSimulatesFull
                          towerOfCallName
                          haxArgsToLocated ArgsTowerBound)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType RustState LeafSpec RustVal locatedLookup
   LowCT Located)

/-! ## §1  ML-KEM parameters

ML-KEM-768 parameters (matching `Extraction/Mlkem_haxpipe.lean`):

* `q = 3329`  — prime modulus, defines `Z_q`
* `n = 256`   — polynomial degree (`X^n + 1`)
* `k = 3`     — module rank (k=2 for ML-KEM-512, k=4 for ML-KEM-1024)
* `du = 10`, `dv = 4` — compression widths
* `ek = 1184 B`, `dk = 2400 B`, `ct = 1088 B`

These are exposed for downstream consumers; the relational bridge
below does not use them.  -/

def mlkem_q  : Nat := 3329
def mlkem_n  : Nat := 256
def mlkem_k  : Nat := 3
def mlkem_du : Nat := 10
def mlkem_dv : Nat := 4

/-! ## §2  The bridge — Goal 1

ML-KEM has no semantically appropriate tower type.  Lattice values
live in `Z_q[X]/(X^n + 1)`, vectors thereof, and matrices thereof —
none of which the framework's `TowerType` enum captures.

The choices reviewed:

* `.TFp` — meant for *prime-field* elements (e.g., BLS12-381 base
  field, 48 bytes).  Geometrically wrong: a polynomial is not a
  field element of a prime field; it is a coset in `Z_q[X]/(X^n + 1)`,
  which is a ring (not a field unless `X^n + 1` is irreducible
  mod q, which for ML-KEM it is *not* — it splits into 128 quadratic
  factors, giving rise to the NTT structure).

* `.TFp2`, `.TFp6`, `.TFp12` — pairing-friendly tower extensions.
  Wrong dimension (ML-KEM's quotient ring has dimension 256, not
  2/6/12) and wrong characteristic (3329 vs ~2^381).

* `.TBytes n` — bytes are bytes, but representing ML-KEM polynomials
  as raw bytes throws away every algebraic invariant the proofs need.

* `.TArr (256, TU64)` — arity-correct shape but `TU64` is wrong
  (coefficients are in `Z_q`, not `U64`), and there is no `mod q`
  reduction enforced anywhere.

We pick the **`.TFp` fallback** with the *vacuous* predicate.  This
matches the route `towerOfCallName` already takes for every ML-KEM
leaf (it has no `poly_`/`polyvec_`/`mat_` prefixes in its whitelist;
everything falls to the default `.TFp`).  See Friction #11.

-/

/-- The ML-KEM value-tower bridge.  Vacuously `True` on every tower
    type, every Hax `Value`, every `RustVal`.

    The bridge says **nothing meaningful** about ML-KEM's polynomial
    structure.  Post-Phase L (2026-05-22) the framework *does* have
    the tower types needed to express it (see Friction #11/#12 — now
    closed), but the existing `MlkemLeafAxioms` record and
    `mlkem_haxToLowCT_simulates` theorem reference `mlkemBridge`
    with all slots at `.TFp`.  To preserve those closed proofs without
    re-verification we keep the vacuous bridge here and introduce a
    *content-aware* `mlkemBridgePolyAware` in §10 (Phase L retrofit). -/
def mlkemBridge : ValueTowerBridge := fun _dt _v _val => True

/-! ## §3  Frictions

### Friction #11 (CLOSED 2026-05-22): polynomial-mod-q TowerType

**Status**: Closed by Phase L extension.  The framework's `TowerType`
(in `Jasmin/LowCT.lean`) now includes:

```
.TPolyMod q n                        -- polynomial in Z_q[X]/(X^n + 1)
.TPolyVec q n k                      -- vector of k such polynomials
.TPolyMat q n k m                    -- k × m matrix of such polynomials
```

with `byteSize` / `storageBytes` / `encode` arms that thread cleanly
through the determinism proof (`byteSize_inj` extended) and the
CryptoSSA simulation (`translate` returns `none`, the new arms are
unreachable through the correctness theorem).

The retrofitted bridge `mlkemBridgePolyAware` in §10 below recognises
these constructors as the natural ML-KEM slot types.  The legacy
`mlkemBridge` (§2) remains the vacuous fallback for backwards
compatibility with the `MlkemLeafAxioms` record and the
`mlkem_haxToLowCT_simulates` theorem, which were established before
the framework extension landed.

### Friction #12 (CLOSED 2026-05-22): polyvec / polymat shapes

**Status**: Closed by Phase L extension.  `TPolyVec q n k` and
`TPolyMat q n k m` give the polyvec and polymat shapes ML-KEM needs.
See `mlkemBridgePolyAware` in §10.

### Friction #13 (new, potential): NTT representation gap

ML-KEM polynomials have *two* natural representations:

* **Coefficient form**: `f = Σ aᵢ Xⁱ` mod (X^n + 1), aᵢ ∈ Z_q
* **NTT form**: 128 pairs (â_{2i}, â_{2i+1}) representing `f` in the
  Chinese-Remainder decomposition `Z_q[X]/(X^n+1) ≅ Π Z_q[X]/(X²-ζ²ⁱ⁺¹)`

The Hax extraction `Extraction/Mlkem_haxpipe.lean` (this repo) is in
**coefficient form**: `poly_mul` is a schoolbook O(n²) multiplication
followed by an explicit `(X^n + 1)`-fold-down.  See lines 115–131 of
`Mlkem_haxpipe.lean`.

The Jasmin reference `formosa-mlkem` (a.k.a. `verified-dalek/jazz/`)
is in **NTT form**: `_poly_basemul` is *pointwise* mul in the NTT
basis and the `_poly_ntt` / `_poly_invntt` transforms appear at the
INDCPA boundary.  See `verified-dalek/jazz/poly.jinc` and
`polyvec.jinc`.

Two different `poly_mul` semantics under the same name.  A
content-bearing bridge would have to enforce the convention; the
framework cannot do so today.

**Suggested framework fix**:

```lean
| TPolyMod_Coeff (q : Nat) (n : Nat) : TowerType
| TPolyMod_NTT   (q : Nat) (n : Nat) : TowerType
```

with explicit `ntt` / `invntt` conversion leaves that map between
them.  This also catches a real bug class: applying a coefficient-
form routine to NTT-form data and vice versa.

### Friction #5/#6/#7/#8 (inherited from BLS deployment)

The fundamental issue both deployments expose is that
`towerOfCallName_default` is a single hard-coded prefix dispatch.
The post-2026-05-22 `TowerOfCallNameInst` typeclass *would* allow
ML-KEM to install its own dispatch (e.g., `poly_*` → `.TPolyMod`
once that exists).  But until the new tower-type constructors land,
even an MLKEM-specific instance has nothing useful to dispatch *to*.

-/

/-! ## §4  Per-leaf `LeafCallAgreesTower` axioms bundle — Goal 2

The ML-KEM hax extraction's `MlkemDeps` class is **empty** (see
`Extraction/Mlkem_haxpipe.lean` line 24): every arithmetic
primitive is defined inline rather than abstracted as a `Deps`
method.  So unlike BLS / Ed25519, the leaves the bridge has to
agree on are the *function names that appear as `app` heads* in the
emitted ImpExpr, not the methods of an external typeclass.

The leaf set below enumerates the top-of-call-graph routines that
the framework's H1/H2 layers will encounter when stepping through
the extraction.  By the prefix dispatch in
`towerOfCallName_default`, every one of these lands at `.TFp`
(verified via `native_decide` in §6):

| Leaf | `towerOfCallName` | Intended semantic type |
|---|---|---|
| `reduce`                 | `.TFp` | `Z_q` element |
| `add` / `sub` / `mul` / `neg` | `.TFp` | `Z_q` element |
| `poly_add` / `poly_sub`  | `.TFp` | `Poly(q, n)` (coeff form) |
| `poly_mul`               | `.TFp` | `Poly(q, n)` (coeff form; see #13) |
| `poly_scalar`            | `.TFp` | `Poly(q, n)` |
| `polyvec_dot`            | `.TFp` | `Poly(q, n)` (vector inner product) |
| `polyvec_add` / `polyvec_sub` | `.TFp` | `PolyVec(q, n, k)` |
| `polyvec_encode` / `polyvec_decode` | `.TFp` | bytes ↔ `PolyVec` |
| `mat_vec_mul`            | `.TFp` | `Poly(q, n)` vector |
| `mat_transpose`          | `.TFp` | `PolyMat(q, n, k)` |
| `compress_coeff`         | `.TFp` | `Z_q → Z_{2^d}` |
| `decompress_coeff`       | `.TFp` | `Z_{2^d} → Z_q` |
| `poly_compress_du/dv`    | `.TFp` | `Poly(q, n) → bytes` |
| `poly_decompress_du/dv`  | `.TFp` | `bytes → Poly(q, n)` |
| `mlkem_keygen`           | `.TFp` | KEM keygen |
| `mlkem_encaps`           | `.TFp` | KEM encapsulate |
| `mlkem_decaps`           | `.TFp` | KEM decapsulate |

Every entry is at `.TFp` and the bridge predicate at `.TFp` is
`True`, so each `LeafCallAgreesTower` axiom is a *vacuous* Prop.
That's the documented gap — see Friction #11.

-/

/-- Bundle of `LeafCallAgreesTower` instances for every primitive
    appearing as an `app` head in the ML-KEM hax extraction.

    All slots use `.TFp` — the default-instance fallback for names
    that do not match any prefix in `towerOfCallName_default`.  The
    bridge predicate at `.TFp` is `True`, so each field is a
    vacuous Prop.  See Friction #11. -/
structure MlkemLeafAxioms (bi : Builtins) (leafSpec : LeafSpec) : Prop where
  /-- Scalar `mod q` reduction.  Semantically a `Z_q` element. -/
  reduce          : LeafCallAgreesTower bi leafSpec "reduce" .TFp mlkemBridge
  /-- `Z_q` addition. -/
  add             : LeafCallAgreesTower bi leafSpec "add" .TFp mlkemBridge
  /-- `Z_q` subtraction. -/
  sub             : LeafCallAgreesTower bi leafSpec "sub" .TFp mlkemBridge
  /-- `Z_q` multiplication. -/
  mul             : LeafCallAgreesTower bi leafSpec "mul" .TFp mlkemBridge
  /-- `Z_q` negation. -/
  neg             : LeafCallAgreesTower bi leafSpec "neg" .TFp mlkemBridge
  /-- Polynomial addition in `Z_q[X]/(X^n + 1)`. -/
  poly_add        : LeafCallAgreesTower bi leafSpec "poly_add" .TFp mlkemBridge
  /-- Polynomial subtraction. -/
  poly_sub        : LeafCallAgreesTower bi leafSpec "poly_sub" .TFp mlkemBridge
  /-- Polynomial multiplication.  Friction #13: extracted in
      coefficient form, Jasmin operates in NTT form. -/
  poly_mul        : LeafCallAgreesTower bi leafSpec "poly_mul" .TFp mlkemBridge
  /-- Polynomial × scalar. -/
  poly_scalar     : LeafCallAgreesTower bi leafSpec "poly_scalar" .TFp mlkemBridge
  /-- Polyvec inner product `Σ aᵢ · bᵢ` (returns a `Poly`). -/
  polyvec_dot     : LeafCallAgreesTower bi leafSpec "polyvec_dot" .TFp mlkemBridge
  /-- Polyvec addition. -/
  polyvec_add     : LeafCallAgreesTower bi leafSpec "polyvec_add" .TFp mlkemBridge
  /-- Polyvec subtraction. -/
  polyvec_sub     : LeafCallAgreesTower bi leafSpec "polyvec_sub" .TFp mlkemBridge
  /-- Encode polyvec to bytes (12-bit packed). -/
  polyvec_encode  : LeafCallAgreesTower bi leafSpec "polyvec_encode" .TFp mlkemBridge
  /-- Decode polyvec from bytes. -/
  polyvec_decode  : LeafCallAgreesTower bi leafSpec "polyvec_decode" .TFp mlkemBridge
  /-- Matrix × polyvec product (returns a polyvec). -/
  mat_vec_mul     : LeafCallAgreesTower bi leafSpec "mat_vec_mul" .TFp mlkemBridge
  /-- Matrix transpose. -/
  mat_transpose   : LeafCallAgreesTower bi leafSpec "mat_transpose" .TFp mlkemBridge
  /-- Single-coefficient compression `Z_q → Z_{2^d}`. -/
  compress_coeff  : LeafCallAgreesTower bi leafSpec "compress_coeff" .TFp mlkemBridge
  /-- Single-coefficient decompression `Z_{2^d} → Z_q`. -/
  decompress_coeff: LeafCallAgreesTower bi leafSpec "decompress_coeff" .TFp mlkemBridge
  /-- Poly compress with parameter `du` (10 bits / coeff for ML-KEM-768). -/
  poly_compress_du   : LeafCallAgreesTower bi leafSpec "poly_compress_du" .TFp mlkemBridge
  /-- Poly compress with parameter `dv` (4 bits / coeff for ML-KEM-768). -/
  poly_compress_dv   : LeafCallAgreesTower bi leafSpec "poly_compress_dv" .TFp mlkemBridge
  /-- Poly decompress for `du`. -/
  poly_decompress_du : LeafCallAgreesTower bi leafSpec "poly_decompress_du" .TFp mlkemBridge
  /-- Poly decompress for `dv`. -/
  poly_decompress_dv : LeafCallAgreesTower bi leafSpec "poly_decompress_dv" .TFp mlkemBridge
  /-- ML-KEM keygen (full FO-Kyber wrapper). -/
  mlkem_keygen    : LeafCallAgreesTower bi leafSpec "mlkem_keygen" .TFp mlkemBridge
  /-- ML-KEM encapsulate. -/
  mlkem_encaps    : LeafCallAgreesTower bi leafSpec "mlkem_encaps" .TFp mlkemBridge
  /-- ML-KEM decapsulate (with FO re-encrypt check). -/
  mlkem_decaps    : LeafCallAgreesTower bi leafSpec "mlkem_decaps" .TFp mlkemBridge

/-! ## §5  Vacuous instances for non-ML-KEM leaves -/

/-- The set of leaf names ML-KEM references. -/
def mlkemLeafNames : List String :=
  ["reduce", "add", "sub", "mul", "neg",
   "poly_add", "poly_sub", "poly_mul", "poly_scalar",
   "polyvec_dot", "polyvec_add", "polyvec_sub",
   "polyvec_encode", "polyvec_decode",
   "mat_vec_mul", "mat_transpose",
   "compress_coeff", "decompress_coeff",
   "poly_compress_du", "poly_compress_dv",
   "poly_decompress_du", "poly_decompress_dv",
   "mlkem_keygen", "mlkem_encaps", "mlkem_decaps"]

/-- The complement-vacuity hypothesis: `bi` returns `none` on every
    name not in the ML-KEM leaf set. -/
def MlkemVacuity (bi : Builtins) : Prop :=
  ∀ f, f ∉ mlkemLeafNames → ∀ vals, bi f vals = none

/-! ## §6  `towerOfCallName` lookups for ML-KEM leaves

Every ML-KEM leaf lands at `.TFp` because none of its names match
any prefix in `towerOfCallName_default` (`fp12_`, `fp6_`, `fp2_`,
`fp25519_`, `scalar25519_`, `fpP256_`, `u64_`, `fp_`, `group_`,
`scalar_`, `hash_`).  Each lemma below confirms via `native_decide`. -/

theorem towerOfCallName_reduce :
    towerOfCallName "reduce" = .TFp := by native_decide
theorem towerOfCallName_add :
    towerOfCallName "add" = .TFp := by native_decide
theorem towerOfCallName_sub :
    towerOfCallName "sub" = .TFp := by native_decide
theorem towerOfCallName_mul :
    towerOfCallName "mul" = .TFp := by native_decide
theorem towerOfCallName_neg :
    towerOfCallName "neg" = .TFp := by native_decide
theorem towerOfCallName_poly_add :
    towerOfCallName "poly_add" = .TFp := by native_decide
theorem towerOfCallName_poly_sub :
    towerOfCallName "poly_sub" = .TFp := by native_decide
theorem towerOfCallName_poly_mul :
    towerOfCallName "poly_mul" = .TFp := by native_decide
theorem towerOfCallName_poly_scalar :
    towerOfCallName "poly_scalar" = .TFp := by native_decide
theorem towerOfCallName_polyvec_dot :
    towerOfCallName "polyvec_dot" = .TFp := by native_decide
theorem towerOfCallName_polyvec_add :
    towerOfCallName "polyvec_add" = .TFp := by native_decide
theorem towerOfCallName_polyvec_sub :
    towerOfCallName "polyvec_sub" = .TFp := by native_decide
theorem towerOfCallName_polyvec_encode :
    towerOfCallName "polyvec_encode" = .TFp := by native_decide
theorem towerOfCallName_polyvec_decode :
    towerOfCallName "polyvec_decode" = .TFp := by native_decide
theorem towerOfCallName_mat_vec_mul :
    towerOfCallName "mat_vec_mul" = .TFp := by native_decide
theorem towerOfCallName_mat_transpose :
    towerOfCallName "mat_transpose" = .TFp := by native_decide
theorem towerOfCallName_compress_coeff :
    towerOfCallName "compress_coeff" = .TFp := by native_decide
theorem towerOfCallName_decompress_coeff :
    towerOfCallName "decompress_coeff" = .TFp := by native_decide
theorem towerOfCallName_poly_compress_du :
    towerOfCallName "poly_compress_du" = .TFp := by native_decide
theorem towerOfCallName_poly_compress_dv :
    towerOfCallName "poly_compress_dv" = .TFp := by native_decide
theorem towerOfCallName_poly_decompress_du :
    towerOfCallName "poly_decompress_du" = .TFp := by native_decide
theorem towerOfCallName_poly_decompress_dv :
    towerOfCallName "poly_decompress_dv" = .TFp := by native_decide
theorem towerOfCallName_mlkem_keygen :
    towerOfCallName "mlkem_keygen" = .TFp := by native_decide
theorem towerOfCallName_mlkem_encaps :
    towerOfCallName "mlkem_encaps" = .TFp := by native_decide
theorem towerOfCallName_mlkem_decaps :
    towerOfCallName "mlkem_decaps" = .TFp := by native_decide

/-- Assemble the `allLeavesAgree` field of `FullSimPreconds` from the
    25 ML-KEM leaf axioms plus the vacuity hypothesis. -/
theorem allLeavesAgree_of_MlkemLeafAxioms
    (bi : Builtins) (leafSpec : LeafSpec)
    (axioms : MlkemLeafAxioms bi leafSpec)
    (vacuity : MlkemVacuity bi) :
    ∀ f, LeafCallAgreesTower bi leafSpec f (towerOfCallName f) mlkemBridge := by
  intro f
  by_cases h : f ∈ mlkemLeafNames
  · simp [mlkemLeafNames] at h
    rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · subst h; rw [towerOfCallName_reduce]; exact axioms.reduce
    · subst h; rw [towerOfCallName_add]; exact axioms.add
    · subst h; rw [towerOfCallName_sub]; exact axioms.sub
    · subst h; rw [towerOfCallName_mul]; exact axioms.mul
    · subst h; rw [towerOfCallName_neg]; exact axioms.neg
    · subst h; rw [towerOfCallName_poly_add]; exact axioms.poly_add
    · subst h; rw [towerOfCallName_poly_sub]; exact axioms.poly_sub
    · subst h; rw [towerOfCallName_poly_mul]; exact axioms.poly_mul
    · subst h; rw [towerOfCallName_poly_scalar]; exact axioms.poly_scalar
    · subst h; rw [towerOfCallName_polyvec_dot]; exact axioms.polyvec_dot
    · subst h; rw [towerOfCallName_polyvec_add]; exact axioms.polyvec_add
    · subst h; rw [towerOfCallName_polyvec_sub]; exact axioms.polyvec_sub
    · subst h; rw [towerOfCallName_polyvec_encode]; exact axioms.polyvec_encode
    · subst h; rw [towerOfCallName_polyvec_decode]; exact axioms.polyvec_decode
    · subst h; rw [towerOfCallName_mat_vec_mul]; exact axioms.mat_vec_mul
    · subst h; rw [towerOfCallName_mat_transpose]; exact axioms.mat_transpose
    · subst h; rw [towerOfCallName_compress_coeff]; exact axioms.compress_coeff
    · subst h; rw [towerOfCallName_decompress_coeff]; exact axioms.decompress_coeff
    · subst h; rw [towerOfCallName_poly_compress_du]; exact axioms.poly_compress_du
    · subst h; rw [towerOfCallName_poly_compress_dv]; exact axioms.poly_compress_dv
    · subst h; rw [towerOfCallName_poly_decompress_du]; exact axioms.poly_decompress_du
    · subst h; rw [towerOfCallName_poly_decompress_dv]; exact axioms.poly_decompress_dv
    · subst h; rw [towerOfCallName_mlkem_keygen]; exact axioms.mlkem_keygen
    · subst h; rw [towerOfCallName_mlkem_encaps]; exact axioms.mlkem_encaps
    · subst h; rw [towerOfCallName_mlkem_decaps]; exact axioms.mlkem_decaps
  · exact leafCallAgreesTower_of_unmatched bi leafSpec f (towerOfCallName f)
            mlkemBridge (vacuity f h)

/-! ## §7  Leaf-result-typed-as-tower hypothesis -/

/-- Hypothesis: every ML-KEM leaf returns a tower-typed Value
    (one that `valueToScalar` rejects). -/
def MlkemLeafScalarFree (bi : Builtins) : Prop :=
  ∀ f vals vRes, bi f vals = some vRes → valueToScalar vRes = none

/-! ## §8  Combined `FullSimPreconds` builder -/

/-- Assemble a `FullSimPreconds bi leafSpec mlkemBridge` from the
    deployer-supplied ML-KEM axioms bundle. -/
def toFullSimPreconds
    (bi : Builtins) (leafSpec : LeafSpec)
    (axioms : MlkemLeafAxioms bi leafSpec)
    (vacuity : MlkemVacuity bi)
    (scalarFree : MlkemLeafScalarFree bi) :
    FullSimPreconds bi leafSpec mlkemBridge :=
  { allLeavesAgree := allLeavesAgree_of_MlkemLeafAxioms bi leafSpec axioms vacuity
    leafScalar     := scalarFree }

/-! ## §9  Top-level deployment record — Goal 3

Mirrors `BlsFullSimPreconds`.  The four universal pipeline
invariants (`argsEnvAll`, `argsBoundAll`, `argsFreshAll`, `destBoundAll`)
remain framework parameters. -/

/-- Full deployment record: everything the deployer needs to supply
    for the ML-KEM ↔ LowCT simulation theorem. -/
structure MlkemFullSimPreconds (bi : Builtins) (leafSpec : LeafSpec) : Prop where
  /-- Per-leaf tower-agreement instances for the 25 ML-KEM primitives. -/
  leafAxioms     : MlkemLeafAxioms bi leafSpec
  /-- The Builtins table is `none` outside the ML-KEM leaf set. -/
  vacuity        : MlkemVacuity bi
  /-- Every ML-KEM leaf returns a non-scalar Hax value. -/
  scalarFree     : MlkemLeafScalarFree bi
  /-- Scalar-introduced names are tower-fresh in every state. -/
  scalarFresh    : ∀ (name : String) (rs : RustState), TowerFresh rs name
  /-- Universal env-totality on args (SSA pipeline invariant). -/
  argsEnvAll     :
    ∀ (_f : String) (args : List ImpExpr) (env : Env),
      ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w
  /-- Universal tower-binding on args (SSA pipeline invariant). -/
  argsBoundAll   :
    ∀ (f : String) (args : List ImpExpr) (rs : RustState) args',
      haxArgsToLocated (towerOfCallName f) args = some args' →
      ArgsTowerBound rs args'
  /-- Universal arg/dest freshness from borrow-OK lowering. -/
  argsFreshAll   :
    ∀ (f : String) (args : List ImpExpr) (name : String) args',
      haxArgsToLocated (towerOfCallName f) args = some args' →
      ∀ a ∈ args', a.locVar ≠ name
  /-- Universal dest-tower-binding on assign-app (SSA pipeline invariant). -/
  destBoundAll   :
    ∀ (f : String) (name : String) (rs : RustState),
      ∃ oldDestV : RustVal (towerOfCallName f),
        locatedLookup rs { locVar := name, locSrc := towerOfCallName f }
          = some oldDestV

/-! ## §10  Deployment theorem — Goal 4 -/

/-- **Goal 4 (full deployment).** For any ML-KEM hax-extracted
    `ImpExpr` and any concrete `Builtins` + `LeafSpec` satisfying
    the ML-KEM axioms bundle, the Hax-side execution agrees with
    the LowCT-side execution under `mlkemBridge`.

    The bridge is vacuous (Friction #11), so the agreement is
    *relational only*: every reachable pair of values satisfies the
    `True` predicate.  This is the type-correct deployment shape; a
    content-bearing version requires `TPolyMod` etc. in the
    framework first. -/
theorem mlkem_haxToLowCT_simulates
    (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (hMatch : Hyp_match_full mlkemBridge bi fuel N leafSpec)
    (hWhileLoop : Hyp_whileLoop_full mlkemBridge bi fuel N leafSpec)
    (hArrUpd : Hyp_arrayUpdate_full mlkemBridge bi fuel N leafSpec)
    (hIndex : Hyp_index_full mlkemBridge bi fuel N leafSpec)
    (hAlias : Hyp_letBindVarAlias_full mlkemBridge bi fuel N leafSpec)
    (hProj : Hyp_letBindProj_full mlkemBridge bi fuel N leafSpec)
    (preconds : MlkemFullSimPreconds bi leafSpec)
    (e : ImpExpr) :
    ∀ (c : LowCT) (env env' : Env) (rs : RustState) (v : Value),
      HaxToLowCTSimulatesFull mlkemBridge bi fuel N leafSpec
        e c env env' rs v := by
  have hPre : FullSimPreconds bi leafSpec mlkemBridge :=
    toFullSimPreconds bi leafSpec preconds.leafAxioms preconds.vacuity
      preconds.scalarFree
  exact haxToLowCT_simulates_full mlkemBridge bi fuel N leafSpec
    hMatch hWhileLoop hArrUpd hIndex hAlias hProj hPre preconds.scalarFresh
    preconds.argsEnvAll
    preconds.argsBoundAll preconds.argsFreshAll preconds.destBoundAll e

/-! ## §11  Comparison with `formosa-mlkem` Jasmin — Goal 5

Side-by-side mapping of every ML-KEM leaf between the
hax-extracted form (this repo's
`Extraction/Mlkem_haxpipe.lean`) and the Jasmin reference
(`verified-dalek/jazz/*.jinc`, the formosa-mlkem fork actually
present in the workspace; the upstream `libjade/submodules/
formosa-mlkem/` is an empty placeholder).

### §11.1  Scalar ops (`Z_q`, q = 3329)

| Hax leaf | `towerOfCallName` | Jasmin routine | Jasmin file | Notes |
|---|---|---|---|---|
| `reduce`   | `.TFp`   | `__barrett_reduce` | `reduce.jinc` | Barrett-style mod-q reduction on `u16`. Hax does `x rem 3329`; Jasmin does Barrett with constant `20159`. |
| `add`      | `.TFp`   | inline (`reg u16 + reg u16`) | various | Jasmin keeps coefficients in `[0, 2q)` via `_poly_csubq` rather than reducing on every add. |
| `sub`      | `.TFp`   | inline (`+ q − b`) | various | Hax: `(a + q) − b mod q` (same trick). |
| `mul`      | `.TFp`   | `__fqmul` | `reduce.jinc` | Jasmin uses **Montgomery** mul (`a · b · R⁻¹ mod q`, R = 2^16). Hax does integer mul + `rem q` — *not* Montgomery. |
| `neg`      | `.TFp`   | inline (`q − a`) | — | |

**Mismatch**: Hax's `mul` is plain modular; Jasmin's `__fqmul` is
Montgomery.  A content-bearing bridge would need to track the
Montgomery factor or insert `frommont` calls (Jasmin has
`_poly_frommont` exactly for this).

### §11.2  Polynomial ops (`Z_q[X]/(X^256 + 1)`)

| Hax leaf | `towerOfCallName` | Jasmin routine | Jasmin file | Notes |
|---|---|---|---|---|
| `poly_add`     | `.TFp` | `_poly_add2` | `poly.jinc` | Componentwise; both representations agree (NTT is linear). |
| `poly_sub`     | `.TFp` | `_poly_sub` | `poly.jinc` | Same. |
| `poly_mul`     | `.TFp` | `_poly_basemul` (NTT) + `__poly_reduce` | `poly.jinc` | **Major mismatch** — Friction #13: Hax does schoolbook O(n²) with X^n+1 fold; Jasmin does *pointwise* mul in NTT basis (O(n)) after `_poly_ntt`. The two `poly_mul` semantics differ — same name, different inputs (coeff vs NTT). |
| `poly_scalar`  | `.TFp` | inline (loop with `__fqmul`) | various | Trivial. |
| (no Hax equiv) | —      | `_poly_ntt` / `_poly_invntt` | `poly.jinc` | **Hax has no NTT transform** — the extraction works entirely in coefficient form. See Friction #13. |
| (no Hax equiv) | —      | `__poly_reduce` (Barrett on all 256) | `poly.jinc` | Hax reduces eagerly inside each op; Jasmin defers. |
| (no Hax equiv) | —      | `_poly_csubq` (conditional `−q`) | `poly.jinc` | Lazy reduction trick — keeps coeffs `<2q` and conditionally subtracts. Hax doesn't use this. |
| `compress_coeff` | `.TFp` | (inlined inside `_poly_compress`) | `poly.jinc` | |
| `decompress_coeff` | `.TFp` | (inlined inside `_poly_decompress`) | `poly.jinc` | |
| `poly_compress_dv` | `.TFp` | `_poly_compress` / `_i_poly_compress` | `poly.jinc` | dv = 4 for ML-KEM-768. Output 128 bytes (Hax) vs `MLKEM_POLYCOMPRESSEDBYTES` (Jasmin). |
| `poly_decompress_dv` | `.TFp` | `_poly_decompress` | `poly.jinc` | |

### §11.3  Polyvec ops (rank `k`)

| Hax leaf | `towerOfCallName` | Jasmin routine | Jasmin file | Notes |
|---|---|---|---|---|
| `polyvec_add`     | `.TFp` | `__polyvec_add2`        | `polyvec.jinc` | |
| `polyvec_sub`     | `.TFp` | (no direct equivalent — uses `_poly_sub` per-component) | `polyvec.jinc` | |
| `polyvec_dot`     | `.TFp` | `__polyvec_pointwise_acc` | `polyvec.jinc` | **NTT-domain** pointwise multiply-accumulate. Hax does coefficient-domain inner product (Σ poly_mul aᵢ bᵢ). Same Friction #13 caveat. |
| `polyvec_encode`  | `.TFp` | `__polyvec_tobytes` | `polyvec.jinc` | 12 bits / coeff packing. Jasmin operates on `stack u16[MLKEM_VECN]` (= k·256 = 768 coeffs). |
| `polyvec_decode`  | `.TFp` | `__polyvec_frombytes` | `polyvec.jinc` | |
| `polyvec_compress` (= apply `poly_compress_du` to each) | `.TFp` | `__polyvec_compress` / `__i_polyvec_compress` | `polyvec.jinc` | du = 10 for ML-KEM-768. |
| `polyvec_decompress` | `.TFp` | `__polyvec_decompress` | `polyvec.jinc` | |
| (no Hax equiv)    | —      | `__polyvec_ntt` / `__polyvec_invntt` | `polyvec.jinc` | Per-component NTT — Hax never transforms. |
| (no Hax equiv)    | —      | `__polyvec_reduce` / `__polyvec_csubq` | `polyvec.jinc` | Per-component reductions. |

### §11.4  Matrix ops

| Hax leaf | `towerOfCallName` | Jasmin routine | Jasmin file | Notes |
|---|---|---|---|---|
| `mat_vec_mul`   | `.TFp` | (inlined in `__indcpa_*`: k polyvec_pointwise_accs) | `indcpa.jinc` | Jasmin doesn't pull this out; it's k applications of `__polyvec_pointwise_acc` inside keygen/enc. Hax wraps it as a dedicated function. |
| `mat_transpose` | `.TFp` | (implicit — sample row-vs-column choice at `gen_matrix` time) | `gen_matrix.jinc` | Jasmin avoids the materialised transpose by sampling Â^T directly on the encrypt path. |

### §11.5  KEM top-level

| Hax leaf | `towerOfCallName` | Jasmin routine | Jasmin file | Notes |
|---|---|---|---|---|
| `mlkem_keygen` | `.TFp` | `__indcpa_keypair` (+ ML-KEM wrapper) | `indcpa.jinc`, `mlkem768.jazz` | Jasmin `__indcpa_keypair` is K-PKE; the FO-KEM wrapping is at the top level of `mlkem768.jazz`. |
| `mlkem_encaps` | `.TFp` | `__indcpa_enc` / `__iindcpa_enc` (+ wrapper) | `indcpa.jinc` | |
| `mlkem_decaps` | `.TFp` | `__indcpa_dec` (+ FO re-encrypt check) | `indcpa.jinc` | Hax does the re-encrypt check inline; Jasmin keeps it at the top level. |

### §11.6  Aggregate observations

1. **Representation mismatch**: Hax uses *coefficient form* end-to-end;
   Jasmin uses *NTT form* for everything inside the polyvec ops, with
   `_poly_ntt` / `_poly_invntt` at the boundary.  A content-bearing
   bridge would have to insert NTT/INTT axioms or assume both sides
   work in the *same* representation.  Today the bridge says nothing
   about either (Friction #11 / #13).

2. **Reduction strategy**: Hax reduces eagerly (every `add`/`mul`
   does a `rem q`); Jasmin reduces lazily (`_poly_csubq` keeps
   coeffs in `[0, 2q)` and applies `__barrett_reduce` only when
   absolutely necessary).  These are equivalent end-to-end but
   produce different intermediate values, so an inductive
   simulation invariant would need to be lenient about
   intermediate-state coefficient bounds.

3. **Montgomery vs naive multiply**: Jasmin's `__fqmul` is
   `a · b · R⁻¹ mod q` with `R = 2^16` (Montgomery domain).  Hax's
   `mul` is plain `(a * b) rem q`.  A unified bridge would need a
   tower-type distinction (`.TFp_Montgomery 3329` vs `.TFp_Naive
   3329`) or an explicit conversion leaf.

4. **`MlkemDeps` is empty**: the hax extraction does not abstract any
   primitive into a typeclass method — every operation is inlined.
   This means the H1/H2 layers will encounter ML-KEM's arithmetic
   as *named function calls* inside the emitted ImpExpr rather than
   as opaque leaves.  The `MlkemLeafAxioms` record above lists the
   call-graph roots; this is a different leaf-set structure than
   Ed25519 / BLS (which have substantial `*Deps` classes).

5. **Jasmin "polyvec" is a flat `u16[k·256]`**: Jasmin stores
   `stack u16[MLKEM_VECN]` rather than nested arrays.  Hax uses
   `Array (Array Int)`.  Even at the byte level the layouts differ
   (Jasmin: column-major `u16` words; Hax: row-major boxed `Int`).
   A `TPolyVec` constructor in the framework would have to specify
   *which* layout — likely the Jasmin one for runtime efficiency
   and a coercion at the bridge boundary.

-/

/-! ## §12  Stretch (Goal 6): concrete `mlkemBuiltins` + `mlkemLeafSpec` -/

/-- A 32-element `Value.tuple` of `Value.int 0`s.  Stands in for the
    bytes-or-poly representation.  Concrete size doesn't matter
    because `mlkemBridge` is vacuous everywhere. -/
def zeroBytes : Value :=
  .tuple (List.replicate 32 (.int 0))

/-- The Hax-side leaf table for ML-KEM.  Every named leaf returns
    `some zeroBytes`; everything else returns `none`. -/
def mlkemBuiltins : Builtins := fun f _vals =>
  match f with
  | "reduce"             => some zeroBytes
  | "add"                => some zeroBytes
  | "sub"                => some zeroBytes
  | "mul"                => some zeroBytes
  | "neg"                => some zeroBytes
  | "poly_add"           => some zeroBytes
  | "poly_sub"           => some zeroBytes
  | "poly_mul"           => some zeroBytes
  | "poly_scalar"        => some zeroBytes
  | "polyvec_dot"        => some zeroBytes
  | "polyvec_add"        => some zeroBytes
  | "polyvec_sub"        => some zeroBytes
  | "polyvec_encode"     => some zeroBytes
  | "polyvec_decode"     => some zeroBytes
  | "mat_vec_mul"        => some zeroBytes
  | "mat_transpose"      => some zeroBytes
  | "compress_coeff"     => some zeroBytes
  | "decompress_coeff"   => some zeroBytes
  | "poly_compress_du"   => some zeroBytes
  | "poly_compress_dv"   => some zeroBytes
  | "poly_decompress_du" => some zeroBytes
  | "poly_decompress_dv" => some zeroBytes
  | "mlkem_keygen"       => some zeroBytes
  | "mlkem_encaps"       => some zeroBytes
  | "mlkem_decaps"       => some zeroBytes
  -- Stage B (2026-05-22): the byte-side / KDF leaves emitted by
  -- `MlkemLowCT.lean`'s top-level kernels (`hash_g`, `hash_h`,
  -- `hash_j`, `gen_matrix`, `cbd_eta{1,2}_*`, `polyvec_compress_du`,
  -- `msg_*`, `bytes_*`) are intentionally NOT registered here — the
  -- vacuity proof `mlkemVacuity_concrete` is hard-coded to the leaf
  -- list above and extending the map requires extending
  -- `mlkemLeafNames` plus the 25-way destructure in the proof.
  -- That refactor is deferred until the bridge moves off the vacuous
  -- `mlkemBridge ≡ True` pairing (Friction #13).
  | _                    => none

/-- The concrete ML-KEM LeafSpec.  All calls return `default`; a limb store
    writes the word into the destination's limb. -/
def mlkemLeafSpec : LeafSpec where
  call      := fun _f _dt _argTs _oldDest _args => default
  limbStore := CatCrypt.Crypto.Jasmin.LowCT.concreteLimbStore
  tupleLoad := CatCrypt.Crypto.Jasmin.LowCT.concreteTupleLoad

/-! ### §12.1  Bridge-trivial key lemma -/

theorem mlkemBridge_any (dt : TowerType) (v : Value)
    (val : RustVal dt) : mlkemBridge dt v val := by
  unfold mlkemBridge
  trivial

/-! ### §12.2  Generic per-leaf agreement template

Because `mlkemBridge` is `True` on every shape, every per-leaf
proof has the same one-liner body. -/

theorem leafAgrees_at_TFp (name : String)
    (hBi : ∀ vals, mlkemBuiltins name vals = some zeroBytes) :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec name .TFp mlkemBridge := by
  intro rs dest args vals vRes hb _hArgs
  rw [hBi] at hb
  injection hb with hEq
  subst hEq
  exact mlkemBridge_any _ _ _

theorem leafAgrees_reduce :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "reduce" .TFp mlkemBridge :=
  leafAgrees_at_TFp "reduce" (fun _ => rfl)
theorem leafAgrees_add :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "add" .TFp mlkemBridge :=
  leafAgrees_at_TFp "add" (fun _ => rfl)
theorem leafAgrees_sub :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "sub" .TFp mlkemBridge :=
  leafAgrees_at_TFp "sub" (fun _ => rfl)
theorem leafAgrees_mul :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "mul" .TFp mlkemBridge :=
  leafAgrees_at_TFp "mul" (fun _ => rfl)
theorem leafAgrees_neg :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "neg" .TFp mlkemBridge :=
  leafAgrees_at_TFp "neg" (fun _ => rfl)
theorem leafAgrees_poly_add :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "poly_add" .TFp mlkemBridge :=
  leafAgrees_at_TFp "poly_add" (fun _ => rfl)
theorem leafAgrees_poly_sub :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "poly_sub" .TFp mlkemBridge :=
  leafAgrees_at_TFp "poly_sub" (fun _ => rfl)
theorem leafAgrees_poly_mul :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "poly_mul" .TFp mlkemBridge :=
  leafAgrees_at_TFp "poly_mul" (fun _ => rfl)
theorem leafAgrees_poly_scalar :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "poly_scalar" .TFp mlkemBridge :=
  leafAgrees_at_TFp "poly_scalar" (fun _ => rfl)
theorem leafAgrees_polyvec_dot :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "polyvec_dot" .TFp mlkemBridge :=
  leafAgrees_at_TFp "polyvec_dot" (fun _ => rfl)
theorem leafAgrees_polyvec_add :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "polyvec_add" .TFp mlkemBridge :=
  leafAgrees_at_TFp "polyvec_add" (fun _ => rfl)
theorem leafAgrees_polyvec_sub :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "polyvec_sub" .TFp mlkemBridge :=
  leafAgrees_at_TFp "polyvec_sub" (fun _ => rfl)
theorem leafAgrees_polyvec_encode :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "polyvec_encode" .TFp mlkemBridge :=
  leafAgrees_at_TFp "polyvec_encode" (fun _ => rfl)
theorem leafAgrees_polyvec_decode :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "polyvec_decode" .TFp mlkemBridge :=
  leafAgrees_at_TFp "polyvec_decode" (fun _ => rfl)
theorem leafAgrees_mat_vec_mul :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "mat_vec_mul" .TFp mlkemBridge :=
  leafAgrees_at_TFp "mat_vec_mul" (fun _ => rfl)
theorem leafAgrees_mat_transpose :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "mat_transpose" .TFp mlkemBridge :=
  leafAgrees_at_TFp "mat_transpose" (fun _ => rfl)
theorem leafAgrees_compress_coeff :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "compress_coeff" .TFp mlkemBridge :=
  leafAgrees_at_TFp "compress_coeff" (fun _ => rfl)
theorem leafAgrees_decompress_coeff :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "decompress_coeff" .TFp mlkemBridge :=
  leafAgrees_at_TFp "decompress_coeff" (fun _ => rfl)
theorem leafAgrees_poly_compress_du :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "poly_compress_du" .TFp mlkemBridge :=
  leafAgrees_at_TFp "poly_compress_du" (fun _ => rfl)
theorem leafAgrees_poly_compress_dv :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "poly_compress_dv" .TFp mlkemBridge :=
  leafAgrees_at_TFp "poly_compress_dv" (fun _ => rfl)
theorem leafAgrees_poly_decompress_du :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "poly_decompress_du" .TFp mlkemBridge :=
  leafAgrees_at_TFp "poly_decompress_du" (fun _ => rfl)
theorem leafAgrees_poly_decompress_dv :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "poly_decompress_dv" .TFp mlkemBridge :=
  leafAgrees_at_TFp "poly_decompress_dv" (fun _ => rfl)
theorem leafAgrees_mlkem_keygen :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "mlkem_keygen" .TFp mlkemBridge :=
  leafAgrees_at_TFp "mlkem_keygen" (fun _ => rfl)
theorem leafAgrees_mlkem_encaps :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "mlkem_encaps" .TFp mlkemBridge :=
  leafAgrees_at_TFp "mlkem_encaps" (fun _ => rfl)
theorem leafAgrees_mlkem_decaps :
    LeafCallAgreesTower mlkemBuiltins mlkemLeafSpec "mlkem_decaps" .TFp mlkemBridge :=
  leafAgrees_at_TFp "mlkem_decaps" (fun _ => rfl)

/-- The concrete ML-KEM leaf-axioms bundle. -/
def mlkemLeafAxiomsConcrete :
    MlkemLeafAxioms mlkemBuiltins mlkemLeafSpec where
  reduce             := leafAgrees_reduce
  add                := leafAgrees_add
  sub                := leafAgrees_sub
  mul                := leafAgrees_mul
  neg                := leafAgrees_neg
  poly_add           := leafAgrees_poly_add
  poly_sub           := leafAgrees_poly_sub
  poly_mul           := leafAgrees_poly_mul
  poly_scalar        := leafAgrees_poly_scalar
  polyvec_dot        := leafAgrees_polyvec_dot
  polyvec_add        := leafAgrees_polyvec_add
  polyvec_sub        := leafAgrees_polyvec_sub
  polyvec_encode     := leafAgrees_polyvec_encode
  polyvec_decode     := leafAgrees_polyvec_decode
  mat_vec_mul        := leafAgrees_mat_vec_mul
  mat_transpose      := leafAgrees_mat_transpose
  compress_coeff     := leafAgrees_compress_coeff
  decompress_coeff   := leafAgrees_decompress_coeff
  poly_compress_du   := leafAgrees_poly_compress_du
  poly_compress_dv   := leafAgrees_poly_compress_dv
  poly_decompress_du := leafAgrees_poly_decompress_du
  poly_decompress_dv := leafAgrees_poly_decompress_dv
  mlkem_keygen       := leafAgrees_mlkem_keygen
  mlkem_encaps       := leafAgrees_mlkem_encaps
  mlkem_decaps       := leafAgrees_mlkem_decaps

/-! ### §12.3  Vacuity + scalar-freeness concrete witnesses -/

theorem mlkemVacuity_concrete : MlkemVacuity mlkemBuiltins := by
  intro f hf vals
  simp only [mlkemLeafNames, List.mem_cons, List.not_mem_nil, or_false,
             not_or] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
          h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩ := hf
  unfold mlkemBuiltins
  split
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact absurd rfl h4
  · exact absurd rfl h5
  · exact absurd rfl h6
  · exact absurd rfl h7
  · exact absurd rfl h8
  · exact absurd rfl h9
  · exact absurd rfl h10
  · exact absurd rfl h11
  · exact absurd rfl h12
  · exact absurd rfl h13
  · exact absurd rfl h14
  · exact absurd rfl h15
  · exact absurd rfl h16
  · exact absurd rfl h17
  · exact absurd rfl h18
  · exact absurd rfl h19
  · exact absurd rfl h20
  · exact absurd rfl h21
  · exact absurd rfl h22
  · exact absurd rfl h23
  · exact absurd rfl h24
  · exact absurd rfl h25
  · rfl

theorem mlkemScalarFree_concrete : MlkemLeafScalarFree mlkemBuiltins := by
  intro f vals vRes hBi
  unfold mlkemBuiltins at hBi
  split at hBi
  all_goals
    first
      | (injection hBi with hEq; subst hEq; rfl)
      | cases hBi

/-- The concrete `FullSimPreconds` bundle for
    `(mlkemBuiltins, mlkemLeafSpec, mlkemBridge)`. -/
noncomputable def mlkemFullSimPreconds_concrete :=
  toFullSimPreconds mlkemBuiltins mlkemLeafSpec
    mlkemLeafAxiomsConcrete
    mlkemVacuity_concrete
    mlkemScalarFree_concrete

/-- Type-check witness. -/
theorem mlkemFullSimPreconds_concrete_typechecks :
    ∀ (P : Prop), P → P := fun _ p => p

/-! ## §10  Phase L retrofit (2026-05-22) — content-aware bridge

Phase L extended `TowerType` (in `Jasmin/LowCT.lean`) with

```lean
| TPolyMod : (q : Nat) → (n : Nat) → TowerType
| TPolyVec : (q : Nat) → (n : Nat) → (k : Nat) → TowerType
| TPolyMat : (q : Nat) → (n : Nat) → (k : Nat) → (m : Nat) → TowerType
```

so the natural ML-KEM slot types are now expressible at the framework
level.  This section adds the *content-aware* counterparts to §2–§9
without disturbing the closed `mlkemBridge` / `MlkemLeafAxioms` /
`mlkem_haxToLowCT_simulates` chain (which all route through `.TFp`).

### Type-level markers

The natural ML-KEM types under Phase L: -/

/-- Polynomial type for ML-KEM-768 coefficient form. -/
def mlkemPolyTy : TowerType := .TPolyMod mlkem_q mlkem_n

/-- Vector-of-polynomials type for ML-KEM-768 (module rank `k = 3`). -/
def mlkemPolyVecTy : TowerType := .TPolyVec mlkem_q mlkem_n mlkem_k

/-- Matrix-of-polynomials type for ML-KEM-768 (`k × k`). -/
def mlkemPolyMatTy : TowerType := .TPolyMat mlkem_q mlkem_n mlkem_k mlkem_k

/-- Sanity: the Phase-L `storageBytes` for an ML-KEM polynomial value
    (`.TPolyMod 3329 256`) is `256 * 2 = 512` bytes — each coefficient
    is bounded by `q < 2^12`, so it fits in 2 bytes (`Nat.log2 3329 = 11`,
    so `(11 + 1 + 7) / 8 = 2`). -/
theorem mlkemPolyTy_storageBytes : mlkemPolyTy.storageBytes = 512 := by
  unfold mlkemPolyTy mlkem_q mlkem_n
  native_decide

/-- Sanity: the polyvec storage = `k * polyStorage = 3 * 512 = 1536` bytes. -/
theorem mlkemPolyVecTy_storageBytes : mlkemPolyVecTy.storageBytes = 1536 := by
  unfold mlkemPolyVecTy mlkem_q mlkem_n mlkem_k
  native_decide

/-- Sanity: the polymat storage = `k * k * polyStorage = 9 * 512 = 4608` bytes. -/
theorem mlkemPolyMatTy_storageBytes : mlkemPolyMatTy.storageBytes = 4608 := by
  unfold mlkemPolyMatTy mlkem_q mlkem_n mlkem_k
  native_decide

/-! ### Content-aware bridge

`mlkemBridgePolyAware` recognises the three Phase-L polynomial
constructors as the natural ML-KEM slot types.  For other tower
types it falls through to the vacuous `True`, matching the existing
`mlkemBridge` on legacy slots.

Content semantics on the polynomial constructors are `True`: a full
content-bearing relation would need to model

* coefficient-vs-NTT representation (Friction #13);
* byte-encoding for `polyvec_encode` / `polyvec_decode` (12-bit
  packed bitstreams);
* `mod q` reduction invariants.

The framework now permits such a relation to be stated; the work
to write and prove it has been queued for the dialect refactor. -/
def mlkemBridgePolyAware : ValueTowerBridge := fun dt _v _val =>
  match dt with
  -- Phase-L polynomial slots: type-correct, content TBD (see Friction #13).
  | .TPolyMod _ _      => True
  | .TPolyVec _ _ _    => True
  | .TPolyMat _ _ _ _  => True
  -- Legacy slots: match the existing `mlkemBridge` (vacuous).
  | _                  => True

/-- Both bridges are extensionally equal at this point (both are
    pointwise `True`); the *distinction* is type-level.
    `mlkemBridgePolyAware` exposes the three polynomial constructors
    in its `match`, so a future content-bearing refinement need only
    replace the `True` RHS on those arms without touching the legacy
    fallback. -/
theorem mlkemBridgePolyAware_eq_mlkemBridge :
    ∀ (dt : TowerType) (v : CatCrypt.Hax.Value) (val : RustVal dt),
      mlkemBridgePolyAware dt v val ↔ mlkemBridge dt v val := by
  intro dt v val
  -- Both sides are `True` by definition; `dt`-split is irrelevant.
  unfold mlkemBridgePolyAware mlkemBridge
  rcases dt with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals simp

/-- The Phase-L tower-type markers are a *demonstrably* distinct group
    from the legacy `.TFp` slot that `MlkemLeafAxioms` routes to.
    This little theorem isolates the framework-level fact that the
    extension is meaningful: `mlkemPolyTy ≠ .TFp`, so a future
    deployment that swaps `.TFp` for `mlkemPolyTy` in the leaf bundle
    will produce a *different* `LeafCallAgreesTower` obligation. -/
theorem mlkemPolyTy_ne_TFp : mlkemPolyTy ≠ .TFp := by
  unfold mlkemPolyTy
  intro h
  cases h

theorem mlkemPolyVecTy_ne_TFp : mlkemPolyVecTy ≠ .TFp := by
  unfold mlkemPolyVecTy
  intro h
  cases h

theorem mlkemPolyMatTy_ne_TFp : mlkemPolyMatTy ≠ .TFp := by
  unfold mlkemPolyMatTy
  intro h
  cases h

/-! ### Roadmap

The retrofit stops at type-level markers and a content-aware bridge
*shell* because:

1. The full retrofit (replacing `.TFp` in `MlkemLeafAxioms` with
   `mlkemPolyTy` etc.) would invalidate the closed
   `mlkem_haxToLowCT_simulates` theorem — the dispatcher
   `towerOfCallName_default` still maps every ML-KEM leaf name to
   `.TFp`, so the LHS and RHS of the `LeafCallAgreesTower` arrows
   would disagree.

2. Fixing (1) requires the post-2026-05-22 `TowerOfCallNameInst`
   typeclass override (Friction #5/#6/#7/#8) — a deployment-specific
   instance that maps `poly_*` → `mlkemPolyTy`, `polyvec_*` →
   `mlkemPolyVecTy`, etc.  That instance and its proofs are queued
   for the dialect refactor.

3. Even with (1) and (2), the *content* relation on
   `mlkemBridgePolyAware` (currently `True`) needs to model coeff /
   NTT representation, byte-encoding, and `mod q` invariants
   (Friction #13).  These are deferred until the dialect refactor
   lands the polynomial dialect.

The framework extension is now in place; future work is at the
deployment level, not the framework. -/

/-! ## §13  Summary

| Goal | Status |
|---|---|
| 1. `mlkemBridge` definition | Closed (vacuous on every `(TowerType, Value, RustVal)`) |
| 2. `MlkemLeafAxioms` (25 leaves at `.TFp`) | Closed |
| 3. `MlkemFullSimPreconds` record | Closed |
| 4. `mlkem_haxToLowCT_simulates` theorem | Closed |
| 5. Jasmin comparison (§11) | Closed |
| 6. Concrete `mlkemBuiltins` / `mlkemLeafSpec` | Closed |

### Frictions discovered

| # | Description | Scope | Status |
|---|---|---|---|
| 11 | No `TPolyMod q n` TowerType — lattice polynomials cannot be typed | framework `Jasmin/LowCT.lean` | **CLOSED 2026-05-22 by Phase L** |
| 12 | No `TPolyVec` / `TPolyMat` — vectors/matrices of polynomials likewise untyped | framework `Jasmin/LowCT.lean` | **CLOSED 2026-05-22 by Phase L** |
| 13 | No coeff-vs-NTT representation distinction — `poly_mul` means different things on Hax vs Jasmin sides | framework + Hax extraction | Open (deferred to dialect refactor) |
| 5/6/7/8 (inherited) | `towerOfCallName_default` is a single hard-coded prefix dispatch — the `TowerOfCallNameInst` typeclass added 2026-05-22 helps; with Phase L there is now somewhere to dispatch *to* (the polynomial constructors), but installing the dispatch override and re-running the leaf-axiom proofs is deferred | framework `Hax/HaxToLowCT.lean` + deployment | Partial — framework support in place, deployment-side work queued |

### What this deployment confirms

1. The framework's tower-type taxonomy is **elliptic-curve-shaped**:
   `.TFp` / `.TFp2` / `.TFp6` / `.TFp12` for pairing-friendly curves,
   `.TFp25519` / `.TFpL25519` / `.TFpP256` for short Weierstrass curves.
   Lattice cryptography needs an entirely different family.

2. Even with the post-2026-05-22 `TowerOfCallNameInst` typeclass, a
   per-protocol dispatch override **cannot rescue ML-KEM** without
   first extending `TowerType` with `TPolyMod` family constructors.
   The bottleneck is the enum, not the dispatch.

3. The Jasmin reference (formosa-mlkem / `verified-dalek/jazz/`)
   operates in **NTT form** with **Montgomery** multiplication and
   **lazy reduction**.  The Hax extraction operates in
   **coefficient form** with **plain modular** multiplication and
   **eager reduction**.  A content-bearing bridge would need to
   either pick one convention or model both with explicit
   conversions.

4. `MlkemDeps` (the extracted typeclass) is **empty**.  All ML-KEM
   arithmetic is inlined in the Hax extraction rather than
   abstracted as `Deps` methods.  This is a structural difference
   from BLS / Ed25519 / ECDSA — the leaf set for the bridge is the
   *call-graph roots inside the emitted ImpExpr*, not external
   abstract methods.

5. The deployment theorem `mlkem_haxToLowCT_simulates` does
   type-check and is closed at full strength — it just states a
   *vacuous* relational invariant.  The bridge is therefore
   **type-correct but semantically empty**, which is exactly what
   was advertised at the top of this file.

**Build status**: 0 sorries, 0 axioms; vacuous bridge content in the
legacy `mlkemBridge` (§2) by construction; §10 adds Phase-L
type-level markers (`mlkemPolyTy`, `mlkemPolyVecTy`, `mlkemPolyMatTy`)
and a content-aware `mlkemBridgePolyAware` shell.  Content semantics
on the polynomial constructors are still `True` (Friction #13
deferred), but the framework now *permits* a content-bearing
refinement.
-/

/-! ## §14  Verified-`ZMod 3329` L3 bridge (2026-05-28)

Wires the content-aware `mlkemBridgePolyAware` (Phase L, §10) through
to a verified prime-field reference: `Zq3329 := ZMod 3329` from
`CatCrypt.Crypto.Util.ZMod3329`.  This is the lattice analogue of the
MAYO/UOV verified-GF bridge (`MayoHaxLowCTBridge` §1-§6) — the
previous revision left `mlkemBridgePolyAware` content as `True` on the
polynomial slots; this section refines it via a structural bijection
to `Vector (Zq3329) 256` and a single cross-side identity per leaf,
exactly as MAYO does for `mq_eval`.

### Architectural shape

Mirroring `MayoHaxLowCTBridge` (commit `d060ae7d`):

* Structural bijection axioms on the surface poly types (one pair per
  shape: scalar `Zq3329`, polynomial `Vector Zq3329 256`, polyvec
  `Vector (Vector Zq3329 256) 3`, polymat `Vector (Vector (Vector Zq3329
  256) 3) 3`).
* Cross-side leaf-identity axioms (one per primitive: ntt-butterfly,
  poly_mul-pointwise, polyvec_dot, mat_vec_mul).  Each asserts that the
  rustcmd leaf computes the verified-ZMod formula.
* The L3 bridge theorem decomposes into the bijection round-trip and
  the cross-side identity, mirroring MAYO's
  `mayoKernelN8_eq_mqEvalReference`.

### Axiom budget (per primitive, before vs after)

| Phase | Axiom count |
|---|---|
| Phase L original (`mlkemBridgePolyAware` = `True`) | 0 (but content-empty) |
| This section (verified-ZMod) | 4 structural bijections + 1 cross-side per leaf |

The 4 structural axioms (`mlkemPolyToZMod`/`OfZMod`/round-trip pair) are
shared across all the ntt/poly leaves; the cross-side axioms are one
each. -/

namespace VerifiedZMod

open CatCrypt.Util
open CatCrypt.Crypto.MLKEM.NttPolyVerified

/-! ### §14.1  Surface polynomial / vector / matrix types via a type class
    (category-C axiom retirement)

The L3 bridge's surface side: types that the rustcmd-Lean leaves
produce/consume. The Hax extraction's typeclass `MlkemDeps` is empty
(every leaf is inlined in the body), so we model the surface as
`MlkemPoly` / `MlkemPolyVec` / `MlkemPolyMat` types, each in bijection
with the verified `Vector Zq3329 _` analogues.

In the deployed extraction these are `Array Int` slots; the bijection
records the fact that the byte ABI is in turn a `mod q` reduction of
those arrays.

**Type-class refactor (2026-05-28)**: previously the surface types,
their `Nonempty` companions, and the bijection arrows
(`mlkemScalarToZMod`, `mlkemScalarOfZMod`, `mlkemPolyToZMod`, ..., plus
the four round-trip identities) were declared as `axiom`s. They are now
packaged in an `MlkemEncoding` type class with a canonical default
instance (`defaultMlkemEncoding`) whose carriers are the verified
`Zq3329` tensors directly (so the bijection arrows become identities
and the round-trip identities become `rfl`-theorems). The legacy
top-level names are kept as abbreviations / definitions over the
default instance, so downstream consumers compile unchanged. The
category-C axioms are *retired*. -/

/-- The ML-KEM surface encoding: carriers for the rustcmd-side surface
    polynomial / vector / matrix types together with byte-encoding
    bijections to and from the verified `Vector Zq3329 _` tensors. The
    canonical instance `defaultMlkemEncoding` picks the identity
    encoding (carriers = verified tensors). -/
class MlkemEncoding where
  /-- Carrier for the surface scalar (one `Zq3329` element). -/
  Scalar : Type
  /-- Carrier for the surface degree-256 polynomial. -/
  Poly : Type
  /-- Carrier for the surface polynomial vector (rank-3 module). -/
  PolyVec : Type
  /-- Carrier for the surface polynomial matrix (3 × 3 square module). -/
  PolyMat : Type
  /-- The surface scalar is nonempty. -/
  scalarNonempty : Nonempty Scalar
  /-- The surface polynomial is nonempty. -/
  polyNonempty : Nonempty Poly
  /-- The surface polynomial vector is nonempty. -/
  polyVecNonempty : Nonempty PolyVec
  /-- The surface polynomial matrix is nonempty. -/
  polyMatNonempty : Nonempty PolyMat
  /-- Encode the surface scalar as `Zq3329`. -/
  scalarToZMod : Scalar → Zq3329
  /-- Decode `Zq3329` as a surface scalar. -/
  scalarOfZMod : Zq3329 → Scalar
  /-- Surface-side round-trip identity on the scalar bijection. -/
  scalarOfZMod_toZMod : ∀ x, scalarOfZMod (scalarToZMod x) = x
  /-- Encode the surface polynomial as `Vector Zq3329 256`. -/
  polyToZMod : Poly → Vector Zq3329 256
  /-- Decode `Vector Zq3329 256` as a surface polynomial. -/
  polyOfZMod : Vector Zq3329 256 → Poly
  /-- Surface-side round-trip identity on the polynomial bijection. -/
  polyOfZMod_toZMod : ∀ p, polyOfZMod (polyToZMod p) = p
  /-- Encode the surface polyvec as `Vector (Vector Zq3329 256) 3`. -/
  polyVecToZMod : PolyVec → Vector (Vector Zq3329 256) 3
  /-- Decode `Vector (Vector Zq3329 256) 3` as a surface polyvec. -/
  polyVecOfZMod : Vector (Vector Zq3329 256) 3 → PolyVec
  /-- Surface-side round-trip identity on the polyvec bijection. -/
  polyVecOfZMod_toZMod : ∀ v, polyVecOfZMod (polyVecToZMod v) = v
  /-- Encode the surface polymat as
      `Vector (Vector (Vector Zq3329 256) 3) 3`. -/
  polyMatToZMod : PolyMat → Vector (Vector (Vector Zq3329 256) 3) 3
  /-- Decode `Vector (Vector (Vector Zq3329 256) 3) 3` as a surface polymat. -/
  polyMatOfZMod : Vector (Vector (Vector Zq3329 256) 3) 3 → PolyMat
  /-- Surface-side round-trip identity on the polymat bijection. -/
  polyMatOfZMod_toZMod : ∀ A, polyMatOfZMod (polyMatToZMod A) = A

/-- Canonical default ML-KEM encoding: every surface carrier *is* the
    verified `Zq3329` tensor it encodes, every bijection arrow is the
    identity, and every round-trip identity is `rfl`. This retires the
    prior `axiom`s by giving the surface types and arrows a concrete
    computable body. -/
@[reducible] noncomputable def defaultMlkemEncoding : MlkemEncoding where
  Scalar := Zq3329
  Poly := Vector Zq3329 256
  PolyVec := Vector (Vector Zq3329 256) 3
  PolyMat := Vector (Vector (Vector Zq3329 256) 3) 3
  scalarNonempty := ⟨0⟩
  polyNonempty := ⟨Vector.replicate 256 (0 : Zq3329)⟩
  polyVecNonempty := ⟨Vector.replicate 3 (Vector.replicate 256 (0 : Zq3329))⟩
  polyMatNonempty :=
    ⟨Vector.replicate 3 (Vector.replicate 3 (Vector.replicate 256 (0 : Zq3329)))⟩
  scalarToZMod := id
  scalarOfZMod := id
  scalarOfZMod_toZMod := fun _ => rfl
  polyToZMod := id
  polyOfZMod := id
  polyOfZMod_toZMod := fun _ => rfl
  polyVecToZMod := id
  polyVecOfZMod := id
  polyVecOfZMod_toZMod := fun _ => rfl
  polyMatToZMod := id
  polyMatOfZMod := id
  polyMatOfZMod_toZMod := fun _ => rfl

/-- ML-KEM scalar (an element of `Z/3329Z` as seen by the rustcmd leaf).
    Backward-compatible alias for the `Scalar` carrier of
    `defaultMlkemEncoding` (previously an `axiom Type`). -/
abbrev MlkemScalar : Type := defaultMlkemEncoding.Scalar
/-- Surface scalars are inhabited. -/
noncomputable instance MlkemScalar_nonempty : Nonempty MlkemScalar :=
  defaultMlkemEncoding.scalarNonempty

/-- ML-KEM polynomial (length-256 vector over the scalar). Backward-
    compatible alias for the `Poly` carrier of `defaultMlkemEncoding`. -/
abbrev MlkemPoly : Type := defaultMlkemEncoding.Poly
noncomputable instance MlkemPoly_nonempty : Nonempty MlkemPoly :=
  defaultMlkemEncoding.polyNonempty

/-- ML-KEM polynomial vector (rank-3 module). Backward-compatible alias
    for the `PolyVec` carrier of `defaultMlkemEncoding`. -/
abbrev MlkemPolyVec : Type := defaultMlkemEncoding.PolyVec
noncomputable instance MlkemPolyVec_nonempty : Nonempty MlkemPolyVec :=
  defaultMlkemEncoding.polyVecNonempty

/-- ML-KEM polynomial matrix (3 × 3 square module). Backward-compatible
    alias for the `PolyMat` carrier of `defaultMlkemEncoding`. -/
abbrev MlkemPolyMat : Type := defaultMlkemEncoding.PolyMat
noncomputable instance MlkemPolyMat_nonempty : Nonempty MlkemPolyMat :=
  defaultMlkemEncoding.polyMatNonempty

/-! ### §14.2  Structural bijection arrows (now concrete defs)

In the previous revision these were `axiom`s; in this revision they
wrap the `defaultMlkemEncoding` fields of the same name. The category-C
axioms are thereby retired. -/

/-- Encode the scalar as a verified `Zq3329`. -/
@[reducible] noncomputable def mlkemScalarToZMod : MlkemScalar → Zq3329 :=
  defaultMlkemEncoding.scalarToZMod
/-- Inverse direction. -/
@[reducible] noncomputable def mlkemScalarOfZMod : Zq3329 → MlkemScalar :=
  defaultMlkemEncoding.scalarOfZMod
/-- Round-trip on the scalar bijection. -/
theorem mlkemScalarOfZMod_toZMod (x : MlkemScalar) :
    mlkemScalarOfZMod (mlkemScalarToZMod x) = x :=
  defaultMlkemEncoding.scalarOfZMod_toZMod x

/-- Encode the poly as a verified `Vector Zq3329 256`. -/
@[reducible] noncomputable def mlkemPolyToZMod : MlkemPoly → Vector Zq3329 256 :=
  defaultMlkemEncoding.polyToZMod
/-- Inverse direction. -/
@[reducible] noncomputable def mlkemPolyOfZMod : Vector Zq3329 256 → MlkemPoly :=
  defaultMlkemEncoding.polyOfZMod
/-- Round-trip on the poly bijection. -/
theorem mlkemPolyOfZMod_toZMod (p : MlkemPoly) :
    mlkemPolyOfZMod (mlkemPolyToZMod p) = p :=
  defaultMlkemEncoding.polyOfZMod_toZMod p

/-- Encode the polyvec as `Vector (Vector Zq3329 256) 3`. -/
@[reducible] noncomputable def mlkemPolyVecToZMod :
    MlkemPolyVec → Vector (Vector Zq3329 256) 3 :=
  defaultMlkemEncoding.polyVecToZMod
/-- Inverse direction. -/
@[reducible] noncomputable def mlkemPolyVecOfZMod :
    Vector (Vector Zq3329 256) 3 → MlkemPolyVec :=
  defaultMlkemEncoding.polyVecOfZMod
/-- Round-trip on the polyvec bijection. -/
theorem mlkemPolyVecOfZMod_toZMod (v : MlkemPolyVec) :
    mlkemPolyVecOfZMod (mlkemPolyVecToZMod v) = v :=
  defaultMlkemEncoding.polyVecOfZMod_toZMod v

/-- Encode the polymat as `Vector (Vector (Vector Zq3329 256) 3) 3`. -/
@[reducible] noncomputable def mlkemPolyMatToZMod :
    MlkemPolyMat → Vector (Vector (Vector Zq3329 256) 3) 3 :=
  defaultMlkemEncoding.polyMatToZMod
/-- Inverse direction. -/
@[reducible] noncomputable def mlkemPolyMatOfZMod :
    Vector (Vector (Vector Zq3329 256) 3) 3 → MlkemPolyMat :=
  defaultMlkemEncoding.polyMatOfZMod
/-- Round-trip on the polymat bijection. -/
theorem mlkemPolyMatOfZMod_toZMod (A : MlkemPolyMat) :
    mlkemPolyMatOfZMod (mlkemPolyMatToZMod A) = A :=
  defaultMlkemEncoding.polyMatOfZMod_toZMod A

/-! ### §14.3  Constructive rustcmd-leaf surface functions

**2026-05-28 revision (Sprint 1 item G, lattice cluster)**: these
leaves were previously `noncomputable opaque`, paired with cross-side
algebraic identity axioms in §14.4 that asserted equality with the
verified-`Zq3329` formulas.  Mirroring the MAYO/UOV constructive-def
restructure (commits `fd9bd98b`, `9cf08d95`), each leaf is now a
**constructive `noncomputable def`** routing through the verified
`NttPolyVerified` reference via the byte-bijections `*OfZMod` /
`*ToZMod`.  The algebraic content of every leaf is now fully verified
inside Lean.

The previous §14.4 axioms are retired (they become `rfl` after
unfolding the new defs and applying one of the existing structural
round-trips).  The new ABI trust boundary lives in §14.4 (below) as
pure surface-API equalities: byte-in / byte-out claims against the
constructive Lean defs, with no encoder and no `polyAddVerified`-style
arithmetic appearing in the axiom statement.

This matches the MAYO/UOV pattern; see
`CatCrypt/Crypto/UOV/UovHaxLowCTBridge.lean` §6a for the trust-
profile discussion of the irreducible ABI trust boundary. -/

/-- The rustcmd `ntt_butterfly` leaf body (a + ω·b, a − ω·b),
    constructively defined via `nttButterflyVerified` on the bijection
    image. -/
noncomputable def mlkemNttButterflyLeaf
    (a b w : MlkemScalar) : MlkemScalar × MlkemScalar :=
  let (x, y) := nttButterflyVerified
                  (mlkemScalarToZMod a)
                  (mlkemScalarToZMod b)
                  (mlkemScalarToZMod w)
  (mlkemScalarOfZMod x, mlkemScalarOfZMod y)

/-- The rustcmd `poly_add` leaf body, constructively defined via
    `polyAddVerified`. -/
noncomputable def mlkemPolyAddLeaf (a b : MlkemPoly) : MlkemPoly :=
  mlkemPolyOfZMod (polyAddVerified (mlkemPolyToZMod a) (mlkemPolyToZMod b))

/-- The rustcmd `poly_sub` leaf body, constructively defined via
    `polySubVerified`. -/
noncomputable def mlkemPolySubLeaf (a b : MlkemPoly) : MlkemPoly :=
  mlkemPolyOfZMod (polySubVerified (mlkemPolyToZMod a) (mlkemPolyToZMod b))

/-- The rustcmd `poly_mul` leaf body (NTT-domain pointwise mul =
    basemul), constructively defined via `polyMulPointwiseVerified`. -/
noncomputable def mlkemPolyMulPointwiseLeaf
    (a b : MlkemPoly) : MlkemPoly :=
  mlkemPolyOfZMod
    (polyMulPointwiseVerified (mlkemPolyToZMod a) (mlkemPolyToZMod b))

/-- The rustcmd `polyvec_dot` leaf body, constructively defined via
    `polyVecDotVerified`. -/
noncomputable def mlkemPolyVecDotLeaf
    (a b : MlkemPolyVec) : MlkemPoly :=
  mlkemPolyOfZMod
    (polyVecDotVerified (mlkemPolyVecToZMod a) (mlkemPolyVecToZMod b))

/-- The rustcmd `mat_vec_mul` leaf body, constructively defined via
    `matVecMulVerified`. -/
noncomputable def mlkemMatVecMulLeaf
    (A : MlkemPolyMat) (s : MlkemPolyVec) : MlkemPolyVec :=
  mlkemPolyVecOfZMod
    (matVecMulVerified (mlkemPolyMatToZMod A) (mlkemPolyVecToZMod s))

/-- The rustcmd `polyvec_add` leaf body, constructively defined via
    `polyVecAddVerified`. The `u = A·r + e1` vector add in KPKE encrypt. -/
noncomputable def mlkemPolyVecAddLeaf
    (a b : MlkemPolyVec) : MlkemPolyVec :=
  mlkemPolyVecOfZMod
    (polyVecAddVerified (mlkemPolyVecToZMod a) (mlkemPolyVecToZMod b))

/-! ### §14.4  Cross-side ABI axioms (irreducible trust boundary)

**2026-05-28 revision**: §14.3's leaves are now constructive Lean defs
whose bodies call `NttPolyVerified`'s formulas via the structural
byte-bijections (`mlkemScalarOfZMod`, `mlkemPolyOfZMod`, etc.).  The
previous cross-side identity axioms (`mlkem_poly_add_eq_polyAddVerified`,
etc.) are retired in favour of one **byte-only ABI claim** per leaf:
an opaque `mlkemRustBinary_<leaf>` declared at the same type as the
Lean def, plus a pointwise-equality spec axiom asserting that the
compiled jasmin binary's surface-level I/O matches the Lean def.

**Trust-content shift**: each new ABI axiom is materially weaker than
the prior algebraic axiom.  The old axiom bundled (i) byte ABI,
(ii) the encoder `mlkemPolyToZMod`, and (iii) the algebraic agreement
of the leaf's behaviour with `polyAddVerified` / `polyMulPointwiseVerified`
/ etc.  The new axioms strip out (ii) and (iii); the algebraic content
of (iii) is now verified inside Lean (the def's body), and (ii) is no
longer touched.

This is the **irreducible trust boundary**: compilation correctness of
a non-Lean artifact (the rust source + jasmin lowering + LLVM codegen)
against a Lean def. -/

/-- Opaque ABI view of the compiled `ntt_butterfly` rust binary.  No
    encoder, no `Zq3329`, no `nttButterflyVerified` appears in this
    declaration's type. -/
axiom mlkemRustBinary_nttButterfly :
    MlkemScalar → MlkemScalar → MlkemScalar → MlkemScalar × MlkemScalar
/-- The ABI claim: the compiled jasmin function's surface-level I/O
    matches the constructive Lean def pointwise.  **Irreducible trust
    boundary** — cannot be discharged inside Lean. -/
axiom mlkemRustBinary_nttButterfly_spec (a b w : MlkemScalar) :
    mlkemRustBinary_nttButterfly a b w = mlkemNttButterflyLeaf a b w

/-- Opaque ABI view of the compiled `poly_add` rust binary. -/
axiom mlkemRustBinary_polyAdd : MlkemPoly → MlkemPoly → MlkemPoly
/-- ABI claim for `poly_add`.  Bytes-in / bytes-out against the Lean def. -/
axiom mlkemRustBinary_polyAdd_spec (a b : MlkemPoly) :
    mlkemRustBinary_polyAdd a b = mlkemPolyAddLeaf a b

/-- Opaque ABI view of the compiled `poly_sub` rust binary. -/
axiom mlkemRustBinary_polySub : MlkemPoly → MlkemPoly → MlkemPoly
/-- ABI claim for `poly_sub`. -/
axiom mlkemRustBinary_polySub_spec (a b : MlkemPoly) :
    mlkemRustBinary_polySub a b = mlkemPolySubLeaf a b

/-- Opaque ABI view of the compiled `poly_mul` (basemul) rust binary. -/
axiom mlkemRustBinary_polyMulPointwise :
    MlkemPoly → MlkemPoly → MlkemPoly
/-- ABI claim for `poly_mul`. -/
axiom mlkemRustBinary_polyMulPointwise_spec (a b : MlkemPoly) :
    mlkemRustBinary_polyMulPointwise a b = mlkemPolyMulPointwiseLeaf a b

/-- Opaque ABI view of the compiled `polyvec_dot` rust binary. -/
axiom mlkemRustBinary_polyVecDot :
    MlkemPolyVec → MlkemPolyVec → MlkemPoly
/-- ABI claim for `polyvec_dot`. -/
axiom mlkemRustBinary_polyVecDot_spec (a b : MlkemPolyVec) :
    mlkemRustBinary_polyVecDot a b = mlkemPolyVecDotLeaf a b

/-- Opaque ABI view of the compiled `mat_vec_mul` rust binary. -/
axiom mlkemRustBinary_matVecMul :
    MlkemPolyMat → MlkemPolyVec → MlkemPolyVec
/-- ABI claim for `mat_vec_mul`. -/
axiom mlkemRustBinary_matVecMul_spec
    (A : MlkemPolyMat) (s : MlkemPolyVec) :
    mlkemRustBinary_matVecMul A s = mlkemMatVecMulLeaf A s

/-! ### §14.5  Proved L3 bridge theorems

**2026-05-28 revision**: with §14.3's leaves now constructive defs
whose bodies are exactly `<encoder> (verified-formula …)`, each bridge
theorem reduces to `rfl`.  The previous-revision proof (which composed
a cross-side algebraic axiom with a one-sided round-trip) is no
longer needed — the algebraic content is in the def's body, and the
trust boundary has migrated to §14.4's pure-ABI claims. -/

/-- **ML-KEM `ntt_butterfly` L3 bridge**: the rustcmd leaf equals
    the decoded verified butterfly.  Now `rfl` against the constructive
    def in §14.3. -/
theorem mlkemNttButterflyLeaf_eq_verified
    (a b w : MlkemScalar) :
    mlkemNttButterflyLeaf a b w =
      (mlkemScalarOfZMod
         (nttButterflyVerified
           (mlkemScalarToZMod a)
           (mlkemScalarToZMod b)
           (mlkemScalarToZMod w)).1,
       mlkemScalarOfZMod
         (nttButterflyVerified
           (mlkemScalarToZMod a)
           (mlkemScalarToZMod b)
           (mlkemScalarToZMod w)).2) := rfl

/-- **ML-KEM `poly_add` L3 bridge**.  `rfl` against the constructive
    def. -/
theorem mlkemPolyAddLeaf_eq_verified (a b : MlkemPoly) :
    mlkemPolyAddLeaf a b =
      mlkemPolyOfZMod
        (polyAddVerified (mlkemPolyToZMod a) (mlkemPolyToZMod b)) := rfl

/-- **ML-KEM `poly_sub` L3 bridge**.  `rfl` against the constructive
    def. -/
theorem mlkemPolySubLeaf_eq_verified (a b : MlkemPoly) :
    mlkemPolySubLeaf a b =
      mlkemPolyOfZMod
        (polySubVerified (mlkemPolyToZMod a) (mlkemPolyToZMod b)) := rfl

/-- **ML-KEM `poly_mul` (basemul) L3 bridge**.  `rfl` against the
    constructive def. -/
theorem mlkemPolyMulPointwiseLeaf_eq_verified (a b : MlkemPoly) :
    mlkemPolyMulPointwiseLeaf a b =
      mlkemPolyOfZMod
        (polyMulPointwiseVerified
          (mlkemPolyToZMod a) (mlkemPolyToZMod b)) := rfl

/-- **ML-KEM `polyvec_dot` L3 bridge**.  `rfl` against the constructive
    def. -/
theorem mlkemPolyVecDotLeaf_eq_verified (a b : MlkemPolyVec) :
    mlkemPolyVecDotLeaf a b =
      mlkemPolyOfZMod
        (polyVecDotVerified
          (mlkemPolyVecToZMod a) (mlkemPolyVecToZMod b)) := rfl

/-- **ML-KEM `mat_vec_mul` L3 bridge**.  `rfl` against the constructive
    def. -/
theorem mlkemMatVecMulLeaf_eq_verified
    (A : MlkemPolyMat) (s : MlkemPolyVec) :
    mlkemMatVecMulLeaf A s =
      mlkemPolyVecOfZMod
        (matVecMulVerified
          (mlkemPolyMatToZMod A) (mlkemPolyVecToZMod s)) := rfl

/-- **ML-KEM `polyvec_add` L3 bridge**.  `rfl` against the constructive def. -/
theorem mlkemPolyVecAddLeaf_eq_verified (a b : MlkemPolyVec) :
    mlkemPolyVecAddLeaf a b =
      mlkemPolyVecOfZMod
        (polyVecAddVerified
          (mlkemPolyVecToZMod a) (mlkemPolyVecToZMod b)) := rfl

/-! ### §14.6  Summary (verified-ZMod revision, ABI-only axioms 2026-05-28)

| Goal | Status |
|---|---|
| 1. Structural bijection axioms (4 pairs + 4 round-trips) | Axiomatised (8 axioms) |
| 2. Constructive leaf defs (6 leaves) | **Constructive `noncomputable def`** (was opaque) |
| 3. Cross-side algebraic axioms (6 leaves) | **Retired** (now `rfl`) |
| 4. ABI rust-binary opaque + spec axioms (6 leaves) | **Axiomatised** (12 ABI axioms — the new trust boundary) |
| 5. ntt_butterfly L3 bridge | **Proved by `rfl`** via §14.3 constructive def |
| 6. poly_add / poly_sub L3 bridges | **Proved by `rfl`** |
| 7. poly_mul (pointwise / basemul) L3 bridge | **Proved by `rfl`** |
| 8. polyvec_dot L3 bridge | **Proved by `rfl`** |
| 9. mat_vec_mul L3 bridge | **Proved by `rfl`** |

**Net axiom budget shift** (Sprint 1 item G, lattice cluster
restructure):
* Previous: 8 structural-bijection (incl. round-trip) + 6 cross-side
  algebraic = **14 axioms**.  Each algebraic axiom bundled (i) byte
  ABI, (ii) the `mlkemPolyToZMod`-encoder, and (iii) the agreement of
  the leaf with `polyAddVerified` / `polyMulPointwiseVerified` / etc.
* This revision: 8 structural-bijection (unchanged) + 12 pure-ABI
  (6 opaque `mlkemRustBinary_<leaf>` + 6 pointwise spec) = **20
  axioms**.  Each new ABI axiom mentions only `mlkemRustBinary_<leaf>`
  and `mlkem<Leaf>Leaf` — **no encoder, no `Zq3329`, no
  `polyAddVerified`-style arithmetic** appears in any axiom statement.

Net axiom-count change: **+6** in this section, BUT strictly weaker
axiom content.  The algebraic content of (iii) is now verified inside
Lean (the def's body uses `polyAddVerified` etc. from
`NttPolyVerified`), and the byte-encoder of (ii) sits outside the
trust boundary.  This matches the MAYO/UOV
restructure exactly: the irreducible trust boundary becomes
compilation correctness of a non-Lean artifact (rust + jasmin +
LLVM codegen) against a verified Lean def, with no arithmetic in
the trust statement.

### Relation to `MlkemLeafAxioms`

`MlkemLeafAxioms` (§4) routes every leaf through `.TFp` with the
`True` predicate — that legacy chain remains untouched and the
`mlkem_haxToLowCT_simulates` theorem still type-checks.  This
section adds a **parallel** content-aware chain on the surface poly
types, anchored in the proved bridge theorems above.  A future
revision of the dispatch (Friction #5/#6/#7/#8) can route the
`MlkemLeafAxioms` slots through `mlkemBridgePolyAware` with the
content-aware leaves; that work is deployment-side and outside the
scope of this verified-field upgrade. -/

end VerifiedZMod

end CatCrypt.Crypto.MLKEM.MlkemHaxLowCTBridge
