/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.Jasmin.LowCT
public meta import CatCrypt.Crypto.Jasmin.LowCTDSL
public import CatCrypt.Crypto.Jasmin.LowCTDSL
public meta import CatCrypt.Crypto.Jasmin.LowCTBorrowCheck
public import CatCrypt.Crypto.Jasmin.LowCTBorrowCheck
public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# ML-KEM-768 — spec-faithful LowCT implementation

Hand-authored LowCT kernels for ML-KEM-768 primitives, using the
Phase L `TPolyMod 3329 256` / `TPolyVec 3329 256 3` /
`TPolyMat 3329 256 3 3` constructors (extended in `Jasmin/LowCT.lean`,
2026-05-22).

This file unblocks the empirical baseline benchmark vs formosa-mlkem:
once the kernels are written, the existing `LowCTToJasmin` →
`JasminEmit` pipeline can produce `.s` files that go through the
same Jasmin compiler as formosa's source.

## Scope

* Leaf primitives (poly / polyvec / polymat ops): full set
* Compress / decompress: full set (single-coeff + poly-level du/dv)
* Byte-side / KDF leaves (G/H/J, gen_matrix, CBD samplers, polyvec
  compress/decompress, message encode/decode, byte concat / slice /
  cmov): full set, modelled as opaque leaf calls.  Rejection sampling
  inside `gen_matrix` is bytes-side and stays opaque (probabilistic).
* Higher-level keygen / encaps / decaps: full set (Stage B,
  2026-05-22) — composed as `do`-blocks that wire seed →
  matrix/secret/error → K-PKE arithmetic → output serialization,
  with FO transform plumbing for encaps/decaps.

## Naming

Variable names in the leaf wrappers are passed as `String`s — these
become Jasmin stack slots after the `LowCTToJasmin` lowering pass.
The destination is always the first argument, mirroring the in-place
mutation discipline of the underlying Jasmin reference code.

## Independence from `MlkemHaxLowCTBridge.lean`

The bridge file (Goal 1-4 there) is the *relational* side: it pairs
Hax-extracted ImpExpr with LowCT at the vacuous-`True` predicate
level.  This file is the *concrete* side: actual LowCT terms
authored over the typed Phase-L slots that the benchmarking pipeline
consumes.  The two are orthogonal — content-bearing simulation would
require a richer `mlkemBridgePolyAware`, deferred per Friction #13
(NTT vs coefficient form) in the bridge file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.MlkemLowCT

open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT Located borrowOk)
open CatCrypt.Crypto.Jasmin.LowCTDSL
open CatCrypt.Crypto.Jasmin.LowCTDSL.Rcm
-- Coefficient-form ML-KEM surface axioms + `reifyLowCT%` (Part 3 kernel
-- migration: the kpke arithmetic cores are reified pure-Lean references).
open CatCrypt.Crypto.Jasmin.LowCTReflect
  (MlPoly MlVec MlMat mlk_mat_vec_mul_c mlk_polyvec_add_c mlk_polyvec_dot_c
   mlk_poly_sub_c mlk_poly_add)

/-! ## §1 Parameters and tower-type aliases (Goal 1)

ML-KEM-768 parameters from FIPS 203:

* `q = 3329`  — prime modulus, `Z_q` is the coefficient field.
* `n = 256`   — polynomial degree (working in `Z_q[X]/(X^n + 1)`).
* `k = 3`     — module rank for ML-KEM-768 (=2 for -512, =4 for -1024).

The Phase-L `TPolyMod / TPolyVec / TPolyMat` constructors lift these
into the tower type system, so any LowCT term over MLKEM data has
type-level information about coefficient bounds and arity.
-/

/-- ML-KEM-768 polynomial type: 256 coefficients mod q = 3329. -/
abbrev MlkemPolyTy : TowerType := .TPolyMod 3329 256

/-- ML-KEM-768 polyvec type: k = 3 polynomials. -/
abbrev MlkemPolyVecTy : TowerType := .TPolyVec 3329 256 3

/-- ML-KEM-768 matrix type: 3 × 3 polynomials. -/
abbrev MlkemPolyMatTy : TowerType := .TPolyMat 3329 256 3 3

/-- The modulus `q`. -/
def mlkem_q : Nat := 3329

/-- Coefficient count `n`. -/
def mlkem_n : Nat := 256

/-- Module rank `k`. -/
def mlkem_k : Nat := 3

/-- Compression bit-width for ciphertext-`u` polyvec (10 bits / coeff). -/
def mlkem_du : Nat := 10

/-- Compression bit-width for ciphertext-`v` polynomial (4 bits / coeff). -/
def mlkem_dv : Nat := 4

/-! ## §2 Leaf-call primitive wrappers (Goal 2)

Each primitive becomes a thin wrapper producing a `LowCT` term.
The names mirror the Hax extraction's call-graph roots
(see `MlkemHaxLowCTBridge.lean` §11 for the Jasmin reference
mapping).  By convention `dst` is the destination (mutated) and
arguments are passed in source order.

`borrowOk` is verified at the end of this section.
-/

/-! ### §2.1 Scalar `Z_q` ops (coefficient-level) -/

/-- Scalar Barrett-style reduction: `dst = a mod q`.
    Hax extraction does `x rem 3329`; formosa-mlkem uses Barrett with
    constant `20159`.  Same semantics, different schedule. -/
def reduce (dst a : String) : LowCT :=
  .RCall "reduce"
    { locVar := dst, locSrc := .TFp }
    [{ locVar := a, locSrc := .TFp }]

/-- `Z_q` addition: `dst = (a + b) mod q`. -/
def add (dst a b : String) : LowCT :=
  .RCall "add"
    { locVar := dst, locSrc := .TFp }
    [{ locVar := a, locSrc := .TFp }, { locVar := b, locSrc := .TFp }]

/-- `Z_q` subtraction: `dst = (a + q − b) mod q`. -/
def sub (dst a b : String) : LowCT :=
  .RCall "sub"
    { locVar := dst, locSrc := .TFp }
    [{ locVar := a, locSrc := .TFp }, { locVar := b, locSrc := .TFp }]

/-- `Z_q` multiplication: `dst = (a * b) mod q`.
    Friction note: Hax uses plain modular mul; formosa uses
    Montgomery (`a · b · R⁻¹ mod q`, R = 2^16).  Same name, different
    domain — see Bridge §11.1. -/
def mul (dst a b : String) : LowCT :=
  .RCall "mul"
    { locVar := dst, locSrc := .TFp }
    [{ locVar := a, locSrc := .TFp }, { locVar := b, locSrc := .TFp }]

/-- `Z_q` negation: `dst = (q − a) mod q`. -/
def neg (dst a : String) : LowCT :=
  .RCall "neg"
    { locVar := dst, locSrc := .TFp }
    [{ locVar := a, locSrc := .TFp }]

/-! ### §2.2 Polynomial ops in `Z_q[X]/(X^n + 1)`

These operate on `TPolyMod 3329 256`-typed slots.  After Phase L
the type system tracks the dimension and coefficient bound, so
e.g. `poly_add a b` is statically prevented from mixing a polyvec
slot with a polynomial slot. -/

/-- Polynomial addition: `dst = a + b` (componentwise mod q). -/
def poly_add (dst a b : String) : LowCT :=
  .RCall "poly_add"
    { locVar := dst, locSrc := MlkemPolyTy }
    [{ locVar := a, locSrc := MlkemPolyTy },
     { locVar := b, locSrc := MlkemPolyTy }]

/-- Polynomial subtraction: `dst = a − b` (componentwise mod q). -/
def poly_sub (dst a b : String) : LowCT :=
  .RCall "poly_sub"
    { locVar := dst, locSrc := MlkemPolyTy }
    [{ locVar := a, locSrc := MlkemPolyTy },
     { locVar := b, locSrc := MlkemPolyTy }]

/-- Polynomial multiplication: `dst = a · b` in `Z_q[X]/(X^n + 1)`.
    Hax extraction: schoolbook O(n²) plus `(X^n + 1)`-fold-down.
    formosa-mlkem: pointwise mul in the NTT basis (after
    `_poly_ntt`).  This is Friction #13 in the bridge file. -/
def poly_mul (dst a b : String) : LowCT :=
  .RCall "poly_mul"
    { locVar := dst, locSrc := MlkemPolyTy }
    [{ locVar := a, locSrc := MlkemPolyTy },
     { locVar := b, locSrc := MlkemPolyTy }]

/-- Polynomial × scalar: `dst[i] = c · f[i] mod q`. -/
def poly_scalar (dst c f : String) : LowCT :=
  .RCall "poly_scalar"
    { locVar := dst, locSrc := MlkemPolyTy }
    [{ locVar := c, locSrc := .TFp },
     { locVar := f, locSrc := MlkemPolyTy }]

/-! ### §2.3 PolyVec ops (rank `k = 3`) -/

/-- Polyvec addition: `dst[i] = a[i] + b[i]` for each polynomial slot. -/
def polyvec_add (dst a b : String) : LowCT :=
  .RCall "polyvec_add"
    { locVar := dst, locSrc := MlkemPolyVecTy }
    [{ locVar := a, locSrc := MlkemPolyVecTy },
     { locVar := b, locSrc := MlkemPolyVecTy }]

/-- Polyvec subtraction: `dst[i] = a[i] − b[i]` componentwise. -/
def polyvec_sub (dst a b : String) : LowCT :=
  .RCall "polyvec_sub"
    { locVar := dst, locSrc := MlkemPolyVecTy }
    [{ locVar := a, locSrc := MlkemPolyVecTy },
     { locVar := b, locSrc := MlkemPolyVecTy }]

/-- Polyvec inner product: `dst = Σᵢ aᵢ · bᵢ` (returns a polynomial).
    Hax does coefficient-form inner-product via `poly_mul` + `poly_add`;
    formosa does NTT-domain pointwise multiply-accumulate
    (`__polyvec_pointwise_acc`). -/
def polyvec_dot (dst a b : String) : LowCT :=
  .RCall "polyvec_dot"
    { locVar := dst, locSrc := MlkemPolyTy }
    [{ locVar := a, locSrc := MlkemPolyVecTy },
     { locVar := b, locSrc := MlkemPolyVecTy }]

/-! ### §2.4 Matrix ops (`k × k = 3 × 3`) -/

/-- Matrix × polyvec product: `dst[i] = polyvec_dot(A[i], s)`. -/
def mat_vec_mul (dst a s : String) : LowCT :=
  .RCall "mat_vec_mul"
    { locVar := dst, locSrc := MlkemPolyVecTy }
    [{ locVar := a, locSrc := MlkemPolyMatTy },
     { locVar := s, locSrc := MlkemPolyVecTy }]

/-- Matrix transpose: `dst[i][j] = a[j][i]`.  formosa avoids
    materialising this by sampling Â^T directly at `gen_matrix` time;
    Hax produces an explicit transpose function. -/
def mat_transpose (dst a : String) : LowCT :=
  .RCall "mat_transpose"
    { locVar := dst, locSrc := MlkemPolyMatTy }
    [{ locVar := a, locSrc := MlkemPolyMatTy }]

/-! ### §2.5 Compression / decompression

Per FIPS 203 §4.2.1:

```
Compress_d(x)   = ⌊(2^d / q) · x⌋ mod 2^d
Decompress_d(y) = ⌊(q / 2^d) · y⌉
```

The parameter `d` is encoded in the function name (`du` = 10 for the
ciphertext-u polyvec, `dv` = 4 for the ciphertext-v polynomial) so
the caller doesn't pass it as a runtime arg.  Single-coefficient
versions take a `Z_q` element; polynomial versions operate on a
whole `TPolyMod` slot. -/

/-- Single-coefficient compression `Z_q → Z_{2^d}`.
    `d` is the second arg (a `u64`-typed scalar). -/
def compress_coeff (dst x d : String) : LowCT :=
  .RCall "compress_coeff"
    { locVar := dst, locSrc := .TFp }
    [{ locVar := x, locSrc := .TFp },
     { locVar := d, locSrc := .TU64 }]

/-- Single-coefficient decompression `Z_{2^d} → Z_q`. -/
def decompress_coeff (dst y d : String) : LowCT :=
  .RCall "decompress_coeff"
    { locVar := dst, locSrc := .TFp }
    [{ locVar := y, locSrc := .TFp },
     { locVar := d, locSrc := .TU64 }]

/-- Compress a polynomial with `du = 10` bits / coeff.  Output is a
    `TBytes (n·du/8) = TBytes 320`-typed byte slot (320 bytes per poly).
    The Hax extraction produces a flat `Array UInt8`. -/
def poly_compress_du (dst src : String) : LowCT :=
  .RCall "poly_compress_du"
    { locVar := dst, locSrc := .TBytes 320 }
    [{ locVar := src, locSrc := MlkemPolyTy }]

/-- Compress a polynomial with `dv = 4` bits / coeff.  Output: 128 bytes
    per polynomial. -/
def poly_compress_dv (dst src : String) : LowCT :=
  .RCall "poly_compress_dv"
    { locVar := dst, locSrc := .TBytes 128 }
    [{ locVar := src, locSrc := MlkemPolyTy }]

/-- Decompress bytes into a polynomial under `du = 10`. -/
def poly_decompress_du (dst src : String) : LowCT :=
  .RCall "poly_decompress_du"
    { locVar := dst, locSrc := MlkemPolyTy }
    [{ locVar := src, locSrc := .TBytes 320 }]

/-- Decompress bytes into a polynomial under `dv = 4`. -/
def poly_decompress_dv (dst src : String) : LowCT :=
  .RCall "poly_decompress_dv"
    { locVar := dst, locSrc := MlkemPolyTy }
    [{ locVar := src, locSrc := .TBytes 128 }]

/-! ### §2.6 Encode / decode (12-bit packing)

These are the lossless `polyvec ↔ bytes` codecs that produce
`PUBLICKEYBYTES = k·n·12/8 = 1152` bytes for k = 3. -/

/-- Encode a polyvec to bytes (12 bits / coefficient).
    Output: `k * n * 12 / 8 = 3 * 256 * 12 / 8 = 1152` bytes. -/
def polyvec_encode (dst src : String) : LowCT :=
  .RCall "polyvec_encode"
    { locVar := dst, locSrc := .TBytes 1152 }
    [{ locVar := src, locSrc := MlkemPolyVecTy }]

/-- Decode bytes to a polyvec (inverse of `polyvec_encode`). -/
def polyvec_decode (dst src : String) : LowCT :=
  .RCall "polyvec_decode"
    { locVar := dst, locSrc := MlkemPolyVecTy }
    [{ locVar := src, locSrc := .TBytes 1152 }]

/-! ## §3 Higher-level kernel (Goal 3) — DSL smoke test

A trivially-composable kernel that simply invokes `poly_mul` from
inside an `Rcm` `do`-block.  The purpose is to verify the DSL elaborates
cleanly against the new `TPolyMod` tower types — historically the DSL
was exercised only with `TFp` / `TFp25519` / `TBytes` slots. -/

/-- `c = a * b` for two ML-KEM polynomials.  DSL-style. -/
def poly_mul_kernel (a b c : String) : LowCT := rustcmd| do
  rc_call "poly_mul" (loc c MlkemPolyTy) [loc a MlkemPolyTy, loc b MlkemPolyTy]

/-- A small straight-line composition: `c = a*b ; d = c + a` (mixing
    `poly_mul` and `poly_add` through fresh slots).  Demonstrates the
    DSL chains primitives without manual `RSeq` plumbing. -/
def poly_madd_kernel (a b c d : String) : LowCT := rustcmd| do
  rc_call "poly_mul" (loc c MlkemPolyTy) [loc a MlkemPolyTy, loc b MlkemPolyTy]
  rc_call "poly_add" (loc d MlkemPolyTy) [loc c MlkemPolyTy, loc a MlkemPolyTy]

/-- Polyvec inner product `acc = <s, e>` via the dedicated leaf.  Used as
    the inner kernel of `mat_vec_mul`'s row-by-row composition. -/
def polyvec_dot_kernel (s e acc : String) : LowCT := rustcmd| do
  rc_call "polyvec_dot" (loc acc MlkemPolyTy)
    [loc s MlkemPolyVecTy, loc e MlkemPolyVecTy]

/-! ## §4 `borrowOk` smoke checks (Goal 4)

Each primitive must pass the static borrow check — i.e. its
destination base-variable name does not appear in its argument list.
These are `#guard` checks; the failure mode is a compile-time error
at definition time (immediate feedback during authoring). -/

#guard borrowOk (reduce "r" "a")
#guard borrowOk (add "c" "a" "b")
#guard borrowOk (sub "c" "a" "b")
#guard borrowOk (mul "c" "a" "b")
#guard borrowOk (neg "r" "a")

#guard borrowOk (poly_add "c" "a" "b")
#guard borrowOk (poly_sub "c" "a" "b")
#guard borrowOk (poly_mul "c" "a" "b")
#guard borrowOk (poly_scalar "r" "c" "f")

#guard borrowOk (polyvec_add "c" "a" "b")
#guard borrowOk (polyvec_sub "c" "a" "b")
#guard borrowOk (polyvec_dot "r" "a" "b")

#guard borrowOk (mat_vec_mul "r" "A" "s")
#guard borrowOk (mat_transpose "r" "A")

#guard borrowOk (compress_coeff "y" "x" "d")
#guard borrowOk (decompress_coeff "x" "y" "d")
#guard borrowOk (poly_compress_du "b" "p")
#guard borrowOk (poly_compress_dv "b" "p")
#guard borrowOk (poly_decompress_du "p" "b")
#guard borrowOk (poly_decompress_dv "p" "b")
#guard borrowOk (polyvec_encode "b" "v")
#guard borrowOk (polyvec_decode "v" "b")

#guard borrowOk (poly_mul_kernel "a" "b" "c")
#guard borrowOk (poly_madd_kernel "a" "b" "c" "d")
#guard borrowOk (polyvec_dot_kernel "s" "e" "acc")

-- The borrow checker correctly rejects an aliased destination —
-- `poly_add "a" "a" "b"` writes to `a` while reading it, which is
-- a borrow violation.
#guard borrowOk (poly_add "a" "a" "b") == false

/-! ## §5 (Stretch) Goal 5 — a keygen-shaped composition

A simplified ML-KEM-768 K-PKE keygen body using the primitives above.
This *skips rejection sampling* (the `gen_matrix` / `cbd_eta` byte-side
ingredients are deferred to a later pass — they're not LowCT-friendly
because they're probabilistic and operate on raw byte streams).

Inputs (assumed already in scope, populated by the caller):
* `A`           : `MlkemPolyMatTy`  — public matrix (sampled from seed)
* `s`           : `MlkemPolyVecTy`  — secret vector (CBD sampled)
* `e`           : `MlkemPolyVecTy`  — error vector (CBD sampled)

Outputs (written by this kernel):
* `t`           : `MlkemPolyVecTy`  — `t = A·s + e` (the public key)

Algorithm (FIPS 203, K-PKE.KeyGen, lines 6–8):
```
t ← A · s
t ← t + e
```

The full ML-KEM keygen then concatenates `(seedA ‖ encode(t))` for the
public key and `encode(s)` for the secret key — those bytes-side
operations are appended by the wrapping `keygen` function.

**Authored as a pure Lean reference function and relationally compiled
(reified) by `reifyLowCT%`** rather than hand-written `RCall` plumbing:
the coefficient-form `mat_vec_mul` / `polyvec_add` leaves and their
heterogeneous tower-typed arguments (`A : MlMat`, `s e : MlVec`) are
recovered from the Lean binder types by the reifier. -/
noncomputable def kpkeKeygenComputeTRef (A : MlMat) (s e : MlVec) : MlVec :=
  let Asmul := mlk_mat_vec_mul_c A s
  let t     := mlk_polyvec_add_c Asmul e
  t

/-- K-PKE keygen arithmetic core, the reified `kpkeKeygenComputeTRef`. -/
def kpke_keygen_compute_t : LowCT :=
  (reifyLowCT% kpkeKeygenComputeTRef).body

/-- K-PKE encrypt inner kernel (skipping randomness derivation /
    decompression of the public key, which are byte-side operations).

    Inputs:
    * `At`  : `MlkemPolyMatTy`  — transposed public matrix
    * `t`   : `MlkemPolyVecTy`  — decoded public key
    * `r`   : `MlkemPolyVecTy`  — encryption randomness (CBD sampled)
    * `e1`  : `MlkemPolyVecTy`  — error vector 1
    * `e2`  : `MlkemPolyTy`     — error polynomial
    * `mu`  : `MlkemPolyTy`     — decompressed message poly

    Outputs:
    * `u`   : `MlkemPolyVecTy`  — `u = A^T · r + e1`
    * `v`   : `MlkemPolyTy`     — `v = <t, r> + e2 + mu`

    Per FIPS 203, K-PKE.Encrypt, lines 16–19.

    **Authored as a pure-Lean reference returning the tuple `(u, v)` and
    relationally compiled by `reifyLowCTMulti%`** — the first multi-output
    kernel migrated to relational-compilation style.  The two outputs `u`
    (a polyvec) and `v` (a poly) are recovered as named `&mut` slots from
    the tuple components; their heterogeneous tower types and those of
    the per-argument leaves are threaded from the Lean binder types. -/
noncomputable def kpkeEncryptComputeUvRef
    (At : MlMat) (t r e1 : MlVec) (e2 mu : MlPoly) : MlVec × MlPoly :=
  let AtR  := mlk_mat_vec_mul_c At r
  let u    := mlk_polyvec_add_c AtR e1
  let tr   := mlk_polyvec_dot_c t r
  let tre2 := mlk_poly_add tr e2
  let v    := mlk_poly_add tre2 mu
  (u, v)

/-- K-PKE encrypt arithmetic core, the reified `kpkeEncryptComputeUvRef`.
    `outNames = ["u", "v"]`. -/
def kpke_encrypt_compute_uv : LowCT :=
  (reifyLowCTMulti% kpkeEncryptComputeUvRef).body

/-- K-PKE decrypt inner kernel.

    Inputs:
    * `s`  : `MlkemPolyVecTy`  — secret key (decoded)
    * `u`  : `MlkemPolyVecTy`  — first ciphertext component (decompressed)
    * `v`  : `MlkemPolyTy`     — second ciphertext component (decompressed)

    Outputs:
    * `mu` : `MlkemPolyTy`     — `mu = v − <s, u>` (then compress to bits)

    Per FIPS 203, K-PKE.Decrypt, line 4.

    **Authored as a pure Lean reference function and reified by
    `reifyLowCT%`.**  The `polyvec_dot : MlVec → MlVec → MlPoly` leaf is
    the heterogeneous case: its two `MlVec` arguments and its `MlPoly`
    result carry distinct tower types, threaded per-argument by the
    reifier. -/
noncomputable def kpkeDecryptComputeMuRef (s u : MlVec) (v : MlPoly) : MlPoly :=
  let sU := mlk_polyvec_dot_c s u
  let mu := mlk_poly_sub_c v sU
  mu

/-- K-PKE decrypt arithmetic core, the reified `kpkeDecryptComputeMuRef`. -/
def kpke_decrypt_compute_mu : LowCT :=
  (reifyLowCT% kpkeDecryptComputeMuRef).body

/-! `borrowOk` smoke checks for the stretch kernels. -/

#guard borrowOk kpke_keygen_compute_t
#guard borrowOk kpke_encrypt_compute_uv
#guard borrowOk kpke_decrypt_compute_mu

/-! ## §6 Byte-side / KDF primitive wrappers (Stage B, 2026-05-22)

These leaves model the *opaque* byte-side ingredients of ML-KEM-768
that the FIPS 203 spec invokes but that aren't pure tower-typed
polynomial arithmetic: SHA-3 hashes (G/H/J), the SHAKE-128
expansion + rejection sampler (`gen_matrix`), the CBD samplers, and
the byte-level encode/decode + concat/slice/cmov used to assemble
the public/secret-key / ciphertext wire formats.

They are wrappers, not definitions: each is an `RCall` to a leaf
name that downstream layers (`MlkemHaxLowCTBridge.mlkemBuiltins`,
the Jasmin/MLIR lowering passes, the LeafSpec axiomatisation) bind
to a concrete implementation.  The wrappers here only fix the
tower-typed slot signature.

ML-KEM-768 wire-format constants (FIPS 203 §6):

* `MLKEM_PKBYTES   = 1184` = 1152 (encode(t)) + 32 (ρ)
* `MLKEM_SKBYTES   = 2400` = 1152 (encode(s)) + 1184 (pk) + 32 (H(pk)) + 32 (z)
* `MLKEM_CTBYTES   = 1088` = 960 (compress_du(u) = 3·320) + 128 (compress_dv(v))
* `MLKEM_SSBYTES   = 32`
-/

/-- ML-KEM-768 public-key size in bytes (FIPS 203 §6). -/
def mlkem_pk_bytes : Nat := 1184

/-- ML-KEM-768 secret-key size in bytes (FIPS 203 §6). -/
def mlkem_sk_bytes : Nat := 2400

/-- ML-KEM-768 ciphertext size in bytes (FIPS 203 §6). -/
def mlkem_ct_bytes : Nat := 1088

/-- ML-KEM-768 shared-secret size in bytes (= 32 for all parameter sets). -/
def mlkem_ss_bytes : Nat := 32

/-! ### §6.1  Hash leaves (FIPS 203 §4.1) -/

/-- G : SHA3-512 ; produces 64 bytes.  Used as `G(d ‖ k)` in keygen
    (split into ρ ‖ σ) and `G(m ‖ H(ek))` in encaps (split into
    K ‖ r).  `inLen` is the caller-side input size; ML-KEM uses 33 in
    keygen (32-byte seed + 1-byte param) and 64 in encaps. -/
def hash_g (dst src : String) (inLen : Nat) : LowCT :=
  .RCall "hash_g"
    { locVar := dst, locSrc := .TBytes 64 }
    [{ locVar := src, locSrc := .TBytes inLen }]

/-- H : SHA3-256 ; produces 32 bytes.  Used as `H(ek)` in keygen
    (binding the public key into the secret-key wire format) and
    again on the encaps side. -/
def hash_h (dst src : String) (inLen : Nat) : LowCT :=
  .RCall "hash_h"
    { locVar := dst, locSrc := .TBytes 32 }
    [{ locVar := src, locSrc := .TBytes inLen }]

/-- J : SHAKE-256-32 ; produces 32 bytes.  Used in decaps for the
    implicit-rejection branch `K = J(z ‖ c)`.  `inLen = 32 + 1088 = 1120`. -/
def hash_j (dst src : String) (inLen : Nat) : LowCT :=
  .RCall "hash_j"
    { locVar := dst, locSrc := .TBytes 32 }
    [{ locVar := src, locSrc := .TBytes inLen }]

/-! ### §6.2  Public-matrix + CBD samplers (FIPS 203 §4.2.2 / §4.2.3)

`gen_matrix` is SHAKE-128 expansion + rejection sampling per
`(i, j)` pair.  The rejection sampler is the only probabilistic
component of the spec but it operates entirely on the byte stream
(produces a bounded but unbounded-in-the-worst-case number of
SHAKE-128 squeezes); per the file docstring §"Scope" we model it
as an opaque leaf — the only `LowCT`-visible effect is the
typed `MlkemPolyMatTy` slot it writes.

`cbd_eta1` / `cbd_eta2` are pure byte-stream samplers (CBD2 for
both, since ML-KEM-768 uses η₁ = η₂ = 2).  We expose two variants
for the two output shapes used by the spec (poly vs polyvec). -/

/-- Sample the public matrix `Â ∈ (Z_q^{n×n}[X]/(X^n+1))^{k×k}` from a
    32-byte seed ρ using SHAKE-128 + rejection sampling. -/
def gen_matrix (dst rho : String) : LowCT :=
  .RCall "gen_matrix"
    { locVar := dst, locSrc := MlkemPolyMatTy }
    [{ locVar := rho, locSrc := .TBytes 32 }]

/-- Sample a polyvec from a 32-byte seed σ + 1-byte nonce, using CBD₂
    (`η₁ = 2` for ML-KEM-768).  The `nonce` argument is a `u64` slot
    that the leaf reads as a single byte (low 8 bits).  Used for both
    the secret vector `s` (nonce 0..k-1) and the error vector `e`
    (nonce k..2k-1) in keygen, and for `r` (nonce 0..k-1) in encaps. -/
def cbd_eta1_polyvec (dst sigma nonce : String) : LowCT :=
  .RCall "cbd_eta1_polyvec"
    { locVar := dst, locSrc := MlkemPolyVecTy }
    [{ locVar := sigma, locSrc := .TBytes 32 },
     { locVar := nonce, locSrc := .TU64 }]

/-- Sample a polyvec from a 32-byte seed using CBD₂ (`η₂ = 2`).  Used
    for the encryption error vector `e₁` (nonce k..2k-1) in encaps. -/
def cbd_eta2_polyvec (dst sigma nonce : String) : LowCT :=
  .RCall "cbd_eta2_polyvec"
    { locVar := dst, locSrc := MlkemPolyVecTy }
    [{ locVar := sigma, locSrc := .TBytes 32 },
     { locVar := nonce, locSrc := .TU64 }]

/-- Sample a single polynomial from a 32-byte seed using CBD₂.  Used
    for the encryption error polynomial `e₂` (nonce 2k) in encaps. -/
def cbd_eta2_poly (dst sigma nonce : String) : LowCT :=
  .RCall "cbd_eta2_poly"
    { locVar := dst, locSrc := MlkemPolyTy }
    [{ locVar := sigma, locSrc := .TBytes 32 },
     { locVar := nonce, locSrc := .TU64 }]

/-! ### §6.3  Polyvec compress / decompress (FIPS 203 §4.2.1)

These mirror the per-poly `poly_compress_d*` leaves at the polyvec
level.  For ML-KEM-768 the polyvec ciphertext component `u` is
compressed at `du = 10`, producing `k · n · du / 8 = 3·256·10/8 =
960` bytes. -/

/-- Compress a polyvec at `du = 10` bits / coefficient.
    Output size: `k · n · du / 8 = 960` bytes. -/
def polyvec_compress_du (dst src : String) : LowCT :=
  .RCall "polyvec_compress_du"
    { locVar := dst, locSrc := .TBytes 960 }
    [{ locVar := src, locSrc := MlkemPolyVecTy }]

/-- Decompress a 960-byte buffer to a polyvec under `du = 10`. -/
def polyvec_decompress_du (dst src : String) : LowCT :=
  .RCall "polyvec_decompress_du"
    { locVar := dst, locSrc := MlkemPolyVecTy }
    [{ locVar := src, locSrc := .TBytes 960 }]

/-! ### §6.4  Message encode / decode (FIPS 203 §4.2.1 with d = 1)

The plaintext message `m` is a 32-byte buffer; on the encrypt side
it is `Decompress_1`-lifted to a polynomial `μ` (each bit → a
coefficient in `{0, ⌈q/2⌉}`), and on the decrypt side `μ'` is
`Compress_1`-rounded back to 32 bytes (each coefficient → 1 bit). -/

/-- `μ = Decompress_1(m)` — bit-by-bit lift of a 32-byte message to a
    `MlkemPolyTy` polynomial.  Equivalent to `poly_decompress` with
    `d = 1`; given its own leaf because the spec calls it out
    separately and the byte/poly layout is fixed. -/
def msg_decode (dst src : String) : LowCT :=
  .RCall "msg_decode"
    { locVar := dst, locSrc := MlkemPolyTy }
    [{ locVar := src, locSrc := .TBytes 32 }]

/-- `m = Compress_1(μ)` — bit-by-bit projection of a `MlkemPolyTy`
    polynomial back to 32 bytes.  Used at the tail of decaps to
    recover the message before the re-encrypt check. -/
def msg_encode (dst src : String) : LowCT :=
  .RCall "msg_encode"
    { locVar := dst, locSrc := .TBytes 32 }
    [{ locVar := src, locSrc := MlkemPolyTy }]

/-! ### §6.5  Byte concat / slice / cmov

The wire formats of `ek`, `dk`, and `c` are byte-level concatenations
of fixed-size pieces; we model assembly with `bytes_concat_{2,3,4}`
and disassembly with `bytes_slice`.  `bytes_cmov` is the
constant-time conditional move used at the tail of decaps to select
between `K'` (re-encrypt success) and `J(z ‖ c)` (implicit rejection)
without branching on the comparison result. -/

/-- Concatenate two byte buffers into a fresh buffer of size `m + n`.  -/
def bytes_concat_2 (dst a b : String) (m n : Nat) : LowCT :=
  .RCall "bytes_concat_2"
    { locVar := dst, locSrc := .TBytes (m + n) }
    [{ locVar := a, locSrc := .TBytes m },
     { locVar := b, locSrc := .TBytes n }]

/-- Concatenate three byte buffers into a fresh buffer of size `m + n + p`. -/
def bytes_concat_3 (dst a b c : String) (m n p : Nat) : LowCT :=
  .RCall "bytes_concat_3"
    { locVar := dst, locSrc := .TBytes (m + n + p) }
    [{ locVar := a, locSrc := .TBytes m },
     { locVar := b, locSrc := .TBytes n },
     { locVar := c, locSrc := .TBytes p }]

/-- Concatenate four byte buffers into a fresh buffer of size `m + n + p + r`. -/
def bytes_concat_4 (dst a b c d : String) (m n p r : Nat) : LowCT :=
  .RCall "bytes_concat_4"
    { locVar := dst, locSrc := .TBytes (m + n + p + r) }
    [{ locVar := a, locSrc := .TBytes m },
     { locVar := b, locSrc := .TBytes n },
     { locVar := c, locSrc := .TBytes p },
     { locVar := d, locSrc := .TBytes r }]

/-- Slice a sub-buffer of size `len` out of `src` starting at byte
    offset `off`.  `off` and `len` are encoded as `u64` scalar slots.
    The leaf's runtime semantics is bounds-checked memcopy; the
    wrapper does not propagate the source size into the destination
    tower type — the caller is responsible for matching `len` to the
    expected slice length (typically a compile-time constant). -/
def bytes_slice (dst src off : String) (len : Nat) : LowCT :=
  .RCall "bytes_slice"
    { locVar := dst, locSrc := .TBytes len }
    [{ locVar := src, locSrc := .TBytes 0 },  -- size erased at the leaf boundary
     { locVar := off, locSrc := .TU64 }]

/-- Constant-time conditional move: if `cond` (a `u64` slot) is zero,
    `dst := a`; otherwise `dst := b`.  No branch on `cond`'s value at
    the implementation level — Jasmin lowers this to a `cmov`
    instruction sequence.  Both `a` and `b` must have size `n`. -/
def bytes_cmov (dst cond a b : String) (n : Nat) : LowCT :=
  .RCall "bytes_cmov"
    { locVar := dst, locSrc := .TBytes n }
    [{ locVar := cond, locSrc := .TU64 },
     { locVar := a, locSrc := .TBytes n },
     { locVar := b, locSrc := .TBytes n }]

/-- Constant-time equality of two byte buffers: returns `0` if equal,
    nonzero otherwise (matches the convention of `bytes_cmov`'s `cond`
    argument).  Output is a `u64` slot. -/
def bytes_neq (dst a b : String) (n : Nat) : LowCT :=
  .RCall "bytes_neq"
    { locVar := dst, locSrc := .TU64 }
    [{ locVar := a, locSrc := .TBytes n },
     { locVar := b, locSrc := .TBytes n }]

/-! ### §6.6  `borrowOk` smoke checks for byte-side leaves -/

#guard borrowOk (hash_g "g" "src" 33)
#guard borrowOk (hash_h "h" "src" 1184)
#guard borrowOk (hash_j "j" "src" 1120)
#guard borrowOk (gen_matrix "A" "rho")
#guard borrowOk (cbd_eta1_polyvec "s" "sigma" "n")
#guard borrowOk (cbd_eta2_polyvec "e1" "sigma" "n")
#guard borrowOk (cbd_eta2_poly "e2" "sigma" "n")
#guard borrowOk (polyvec_compress_du "b" "v")
#guard borrowOk (polyvec_decompress_du "v" "b")
#guard borrowOk (msg_decode "mu" "m")
#guard borrowOk (msg_encode "m" "mu")
#guard borrowOk (bytes_concat_2 "d" "a" "b" 32 32)
#guard borrowOk (bytes_concat_3 "d" "a" "b" "c" 32 32 32)
#guard borrowOk (bytes_concat_4 "d" "a" "b" "c" "e" 32 32 32 32)
#guard borrowOk (bytes_slice "d" "s" "off" 32)
#guard borrowOk (bytes_cmov "d" "c" "a" "b" 32)
#guard borrowOk (bytes_neq "d" "a" "b" 32)

/-! ## §7 Top-level ML-KEM-768 kernels (Stage B, 2026-05-22)

The three FIPS 203 algorithms `KeyGen` / `Encaps` / `Decaps`, hand
ported as `LowCT` `do`-blocks.  Each composes the §2/§6 leaves +
the §5 K-PKE arithmetic sub-kernels into a single straight-line term.

### Convention

* Inputs and outputs are passed as **variable names already in scope
  in the calling context** — the kernels do not bind their input
  slots (the caller does).  Output slots are bound via `rc_let`
  at the top of each kernel.
* Internal intermediate slots are bound via `rc_let` at point of
  first use.  Names are scoped to the kernel; collisions across
  kernels are fine because each kernel is its own `do`-block.

### What is and isn't here

These kernels are **structurally** spec-faithful — every FIPS 203
line maps to a `LowCT` step in the obvious way.  Content-bearing
correctness (e.g. "this `do`-block denotes the same key-pair
distribution as `formosa-mlkem`'s `__indcpa_keypair`") still depends
on the leaf-level semantics, which lives behind the `LeafSpec.call`
oracle and remains an open Friction (#13: NTT vs coefficient form;
#11: representation mismatch).

The FO transform (`KeyGen` binds `H(pk)` into `sk`; `Decaps` does
the re-encrypt check + implicit rejection) is **inlined** — there's
no separate K-PKE-vs-K-EM split at the `LowCT` level.

The same `do`-block convention exposes both kernels and sub-kernels
to the optimizer pipeline.  After Stage D the emitted Jasmin can be
diffed against `formosa-mlkem` line by line.
-/

/-! ### §7.1  `mlkem_keygen_kernel` (FIPS 203 §6.2)

Inputs (caller-supplied slots):

* `d` : `TBytes 32` — random seed (KeyGen randomness)
* `z` : `TBytes 32` — implicit-rejection seed (bound into `sk`)

Outputs:

* `ek` : `TBytes 1184` — public key (encapsulation key)
* `dk` : `TBytes 2400` — secret key (decapsulation key)

Algorithm:

```
(ρ, σ) ← G(d ‖ k=3)          -- 64 bytes split into 32+32
Â ← gen_matrix(ρ)             -- 3×3 polymat (NTT-style; opaque here)
s ← cbd_eta1_polyvec(σ, 0)    -- secret vector
e ← cbd_eta1_polyvec(σ, k)    -- error vector
t ← Â · s + e                  -- public-key vector (cf. K-PKE.KeyGen)
ek_t ← polyvec_encode(t)      -- 1152 bytes
ek ← ek_t ‖ ρ                 -- 1184 bytes
hpk ← H(ek)                   -- 32 bytes
dk_s ← polyvec_encode(s)      -- 1152 bytes
dk ← dk_s ‖ ek ‖ hpk ‖ z      -- 2400 bytes
```
-/
def mlkem_keygen_kernel : LowCT := rustcmd| do
  -- Hash the seed into ρ ‖ σ.  We feed `d` directly (33-byte form
  -- with the parameter byte is the spec convention; the leaf-side
  -- implementation appends the byte internally).
  rc_let "g_out" (.TBytes 64)
  rc_call "hash_g" (loc "g_out" (.TBytes 64))
    [loc "d" (.TBytes 33)]
  rc_let "rho" (.TBytes 32)
  rc_let "sigma" (.TBytes 32)
  rc_letU64 "rho_off"; rc_set "rho_off" 0
  rc_letU64 "sig_off"; rc_set "sig_off" 32
  rc_call "bytes_slice" (loc "rho" (.TBytes 32))
    [loc "g_out" (.TBytes 0), loc "rho_off" .TU64]
  rc_call "bytes_slice" (loc "sigma" (.TBytes 32))
    [loc "g_out" (.TBytes 0), loc "sig_off" .TU64]
  -- Sample the public matrix and the secret/error vectors.
  rc_let "A" MlkemPolyMatTy
  rc_call "gen_matrix" (loc "A" MlkemPolyMatTy) [loc "rho" (.TBytes 32)]
  rc_letU64 "n_s"; rc_set "n_s" 0
  rc_letU64 "n_e"; rc_set "n_e" 3  -- k = 3
  rc_let "s" MlkemPolyVecTy
  rc_let "e" MlkemPolyVecTy
  rc_call "cbd_eta1_polyvec" (loc "s" MlkemPolyVecTy)
    [loc "sigma" (.TBytes 32), loc "n_s" .TU64]
  rc_call "cbd_eta1_polyvec" (loc "e" MlkemPolyVecTy)
    [loc "sigma" (.TBytes 32), loc "n_e" .TU64]
  -- K-PKE arithmetic: t = A·s + e.
  rc_let "Asmul" MlkemPolyVecTy
  rc_call "mat_vec_mul" (loc "Asmul" MlkemPolyVecTy)
    [loc "A" MlkemPolyMatTy, loc "s" MlkemPolyVecTy]
  rc_let "t" MlkemPolyVecTy
  rc_call "polyvec_add" (loc "t" MlkemPolyVecTy)
    [loc "Asmul" MlkemPolyVecTy, loc "e" MlkemPolyVecTy]
  -- Serialize the public key: ek = encode(t) ‖ ρ.
  rc_let "ek_t" (.TBytes 1152)
  rc_call "polyvec_encode" (loc "ek_t" (.TBytes 1152))
    [loc "t" MlkemPolyVecTy]
  rc_let "ek" (.TBytes 1184)
  rc_call "bytes_concat_2" (loc "ek" (.TBytes 1184))
    [loc "ek_t" (.TBytes 1152), loc "rho" (.TBytes 32)]
  -- Hash the public key for binding into the secret key.
  rc_let "hpk" (.TBytes 32)
  rc_call "hash_h" (loc "hpk" (.TBytes 32)) [loc "ek" (.TBytes 1184)]
  -- Serialize the secret key: dk = encode(s) ‖ ek ‖ H(ek) ‖ z.
  rc_let "dk_s" (.TBytes 1152)
  rc_call "polyvec_encode" (loc "dk_s" (.TBytes 1152))
    [loc "s" MlkemPolyVecTy]
  rc_call "bytes_concat_4" (loc "dk" (.TBytes 2400))
    [loc "dk_s" (.TBytes 1152), loc "ek" (.TBytes 1184),
     loc "hpk" (.TBytes 32), loc "z" (.TBytes 32)]

/-! ### §7.2  `mlkem_encaps_kernel` (FIPS 203 §6.3)

Inputs:

* `ek` : `TBytes 1184` — public key
* `m`  : `TBytes 32`   — message (random in honest use)

Outputs:

* `c` : `TBytes 1088` — ciphertext
* `K` : `TBytes 32`   — shared secret

Algorithm:

```
hpk ← H(ek)                   -- 32 bytes
(K, r) ← G(m ‖ hpk)           -- 64 bytes split into 32+32
ρ ← ek[1152..]                -- 32 bytes (last component of ek)
t ← polyvec_decode(ek[..1152])
Â ← gen_matrix(ρ)
r' ← cbd_eta1_polyvec(r, 0)
e1 ← cbd_eta2_polyvec(r, k)
e2 ← cbd_eta2_poly(r, 2k)
μ ← msg_decode(m)
u ← Âᵀ · r' + e1
v ← <t, r'> + e2 + μ
c1 ← polyvec_compress_du(u)   -- 960 bytes
c2 ← poly_compress_dv(v)      -- 128 bytes
c ← c1 ‖ c2                   -- 1088 bytes
```
-/
def mlkem_encaps_kernel : LowCT := rustcmd| do
  -- Derive (K, r) from G(m ‖ H(ek)).
  rc_let "hpk_enc" (.TBytes 32)
  rc_call "hash_h" (loc "hpk_enc" (.TBytes 32)) [loc "ek" (.TBytes 1184)]
  rc_let "g_in" (.TBytes 64)
  rc_call "bytes_concat_2" (loc "g_in" (.TBytes 64))
    [loc "m" (.TBytes 32), loc "hpk_enc" (.TBytes 32)]
  rc_let "g_out" (.TBytes 64)
  rc_call "hash_g" (loc "g_out" (.TBytes 64)) [loc "g_in" (.TBytes 64)]
  rc_letU64 "k_off"; rc_set "k_off" 0
  rc_letU64 "r_off"; rc_set "r_off" 32
  rc_call "bytes_slice" (loc "K" (.TBytes 32))
    [loc "g_out" (.TBytes 0), loc "k_off" .TU64]
  rc_let "r" (.TBytes 32)
  rc_call "bytes_slice" (loc "r" (.TBytes 32))
    [loc "g_out" (.TBytes 0), loc "r_off" .TU64]
  -- Decode the public key: (encode(t), ρ) = ek.
  rc_letU64 "t_off"; rc_set "t_off" 0
  rc_letU64 "rho_off2"; rc_set "rho_off2" 1152
  rc_let "ek_t" (.TBytes 1152)
  rc_let "rho2" (.TBytes 32)
  rc_call "bytes_slice" (loc "ek_t" (.TBytes 1152))
    [loc "ek" (.TBytes 0), loc "t_off" .TU64]
  rc_call "bytes_slice" (loc "rho2" (.TBytes 32))
    [loc "ek" (.TBytes 0), loc "rho_off2" .TU64]
  rc_let "t" MlkemPolyVecTy
  rc_call "polyvec_decode" (loc "t" MlkemPolyVecTy) [loc "ek_t" (.TBytes 1152)]
  -- Sample the public matrix.  Note: FIPS 203 uses Â (NTT form)
  -- directly here without an explicit transpose because gen_matrix
  -- samples the rows in transposed order; for the coefficient-form
  -- analogue we materialise Â^T explicitly via mat_transpose.
  rc_let "Ahat" MlkemPolyMatTy
  rc_call "gen_matrix" (loc "Ahat" MlkemPolyMatTy) [loc "rho2" (.TBytes 32)]
  rc_let "At" MlkemPolyMatTy
  rc_call "mat_transpose" (loc "At" MlkemPolyMatTy) [loc "Ahat" MlkemPolyMatTy]
  -- Sample r', e1, e2.
  rc_letU64 "n_r"; rc_set "n_r" 0
  rc_letU64 "n_e1"; rc_set "n_e1" 3
  rc_letU64 "n_e2"; rc_set "n_e2" 6
  rc_let "r_vec" MlkemPolyVecTy
  rc_let "e1" MlkemPolyVecTy
  rc_let "e2" MlkemPolyTy
  rc_call "cbd_eta1_polyvec" (loc "r_vec" MlkemPolyVecTy)
    [loc "r" (.TBytes 32), loc "n_r" .TU64]
  rc_call "cbd_eta2_polyvec" (loc "e1" MlkemPolyVecTy)
    [loc "r" (.TBytes 32), loc "n_e1" .TU64]
  rc_call "cbd_eta2_poly" (loc "e2" MlkemPolyTy)
    [loc "r" (.TBytes 32), loc "n_e2" .TU64]
  -- Decompress the message: μ = Decompress_1(m).
  rc_let "mu" MlkemPolyTy
  rc_call "msg_decode" (loc "mu" MlkemPolyTy) [loc "m" (.TBytes 32)]
  -- Compute u = A^T · r' + e1.
  rc_let "AtR" MlkemPolyVecTy
  rc_call "mat_vec_mul" (loc "AtR" MlkemPolyVecTy)
    [loc "At" MlkemPolyMatTy, loc "r_vec" MlkemPolyVecTy]
  rc_let "u" MlkemPolyVecTy
  rc_call "polyvec_add" (loc "u" MlkemPolyVecTy)
    [loc "AtR" MlkemPolyVecTy, loc "e1" MlkemPolyVecTy]
  -- Compute v = <t, r'> + e2 + μ.
  rc_let "tr" MlkemPolyTy
  rc_call "polyvec_dot" (loc "tr" MlkemPolyTy)
    [loc "t" MlkemPolyVecTy, loc "r_vec" MlkemPolyVecTy]
  rc_let "tre2" MlkemPolyTy
  rc_call "poly_add" (loc "tre2" MlkemPolyTy)
    [loc "tr" MlkemPolyTy, loc "e2" MlkemPolyTy]
  rc_let "v" MlkemPolyTy
  rc_call "poly_add" (loc "v" MlkemPolyTy)
    [loc "tre2" MlkemPolyTy, loc "mu" MlkemPolyTy]
  -- Serialize the ciphertext: c = compress_du(u) ‖ compress_dv(v).
  rc_let "c1" (.TBytes 960)
  rc_call "polyvec_compress_du" (loc "c1" (.TBytes 960)) [loc "u" MlkemPolyVecTy]
  rc_let "c2" (.TBytes 128)
  rc_call "poly_compress_dv" (loc "c2" (.TBytes 128)) [loc "v" MlkemPolyTy]
  rc_call "bytes_concat_2" (loc "c" (.TBytes 1088))
    [loc "c1" (.TBytes 960), loc "c2" (.TBytes 128)]

/-! ### §7.3  `mlkem_decaps_kernel` (FIPS 203 §6.4)

Inputs:

* `dk` : `TBytes 2400` — secret key
* `c`  : `TBytes 1088` — ciphertext

Outputs:

* `K` : `TBytes 32` — shared secret

Algorithm (with implicit rejection):

```
s ← polyvec_decode(dk[..1152])
ek ← dk[1152..2336]                  -- 1184 bytes
hpk ← dk[2336..2368]                 -- 32 bytes
z ← dk[2368..]                       -- 32 bytes
u ← polyvec_decompress_du(c[..960])
v ← poly_decompress_dv(c[960..])
μ' ← v − <s, u>
m' ← msg_encode(μ')
(K', _r') ← G(m' ‖ hpk)              -- 64 bytes, split
-- Re-encrypt: derive c' from (ek, m') as in encaps; compare.
c' ← Encaps_inner(ek, m')            -- 1088 bytes
Krej ← J(z ‖ c)                      -- 32 bytes
neq ← (c ≠? c')                       -- u64 (0 if equal)
K ← bytes_cmov(neq, K', Krej)
```

For the re-encrypt step we *inline* the body of `mlkem_encaps_kernel`
under the local variable name prefix `re_*` (so the slots don't
collide with the caller's `K` output of the re-encrypt branch).
This keeps decaps a single straight-line `do`-block. -/
def mlkem_decaps_kernel : LowCT := rustcmd| do
  -- Disassemble dk = (encode(s) ‖ ek ‖ H(ek) ‖ z).
  rc_letU64 "s_off"; rc_set "s_off" 0
  rc_letU64 "ek_off"; rc_set "ek_off" 1152
  rc_letU64 "hpk_off"; rc_set "hpk_off" 2336
  rc_letU64 "z_off"; rc_set "z_off" 2368
  rc_let "dk_s" (.TBytes 1152)
  rc_let "ek" (.TBytes 1184)
  rc_let "hpk" (.TBytes 32)
  rc_let "z" (.TBytes 32)
  rc_call "bytes_slice" (loc "dk_s" (.TBytes 1152))
    [loc "dk" (.TBytes 0), loc "s_off" .TU64]
  rc_call "bytes_slice" (loc "ek" (.TBytes 1184))
    [loc "dk" (.TBytes 0), loc "ek_off" .TU64]
  rc_call "bytes_slice" (loc "hpk" (.TBytes 32))
    [loc "dk" (.TBytes 0), loc "hpk_off" .TU64]
  rc_call "bytes_slice" (loc "z" (.TBytes 32))
    [loc "dk" (.TBytes 0), loc "z_off" .TU64]
  rc_let "s" MlkemPolyVecTy
  rc_call "polyvec_decode" (loc "s" MlkemPolyVecTy) [loc "dk_s" (.TBytes 1152)]
  -- Disassemble c = (compress_du(u) ‖ compress_dv(v)).
  rc_letU64 "c1_off"; rc_set "c1_off" 0
  rc_letU64 "c2_off"; rc_set "c2_off" 960
  rc_let "c1" (.TBytes 960)
  rc_let "c2" (.TBytes 128)
  rc_call "bytes_slice" (loc "c1" (.TBytes 960))
    [loc "c" (.TBytes 0), loc "c1_off" .TU64]
  rc_call "bytes_slice" (loc "c2" (.TBytes 128))
    [loc "c" (.TBytes 0), loc "c2_off" .TU64]
  rc_let "u" MlkemPolyVecTy
  rc_let "v" MlkemPolyTy
  rc_call "polyvec_decompress_du" (loc "u" MlkemPolyVecTy) [loc "c1" (.TBytes 960)]
  rc_call "poly_decompress_dv" (loc "v" MlkemPolyTy) [loc "c2" (.TBytes 128)]
  -- Recover the message: μ' = v − <s, u> ; m' = Compress_1(μ').
  rc_let "sU" MlkemPolyTy
  rc_call "polyvec_dot" (loc "sU" MlkemPolyTy)
    [loc "s" MlkemPolyVecTy, loc "u" MlkemPolyVecTy]
  rc_let "muPrime" MlkemPolyTy
  rc_call "poly_sub" (loc "muPrime" MlkemPolyTy)
    [loc "v" MlkemPolyTy, loc "sU" MlkemPolyTy]
  rc_let "mPrime" (.TBytes 32)
  rc_call "msg_encode" (loc "mPrime" (.TBytes 32)) [loc "muPrime" MlkemPolyTy]
  -- Re-derive (K', r') from G(m' ‖ H(ek)).  `hpk` was already
  -- decoded; we don't re-hash ek.
  rc_let "g_in" (.TBytes 64)
  rc_call "bytes_concat_2" (loc "g_in" (.TBytes 64))
    [loc "mPrime" (.TBytes 32), loc "hpk" (.TBytes 32)]
  rc_let "g_out" (.TBytes 64)
  rc_call "hash_g" (loc "g_out" (.TBytes 64)) [loc "g_in" (.TBytes 64)]
  rc_letU64 "kp_off"; rc_set "kp_off" 0
  rc_letU64 "rp_off"; rc_set "rp_off" 32
  rc_let "Kprime" (.TBytes 32)
  rc_call "bytes_slice" (loc "Kprime" (.TBytes 32))
    [loc "g_out" (.TBytes 0), loc "kp_off" .TU64]
  rc_let "rPrime" (.TBytes 32)
  rc_call "bytes_slice" (loc "rPrime" (.TBytes 32))
    [loc "g_out" (.TBytes 0), loc "rp_off" .TU64]
  -- Re-encrypt with (ek, m') under r' to produce c'.  We inline the
  -- encaps polynomial arithmetic to keep decaps as one straight-line
  -- `do`-block; intermediates are prefixed `re_*`.
  rc_letU64 "re_t_off"; rc_set "re_t_off" 0
  rc_letU64 "re_rho_off"; rc_set "re_rho_off" 1152
  rc_let "re_ek_t" (.TBytes 1152)
  rc_let "re_rho" (.TBytes 32)
  rc_call "bytes_slice" (loc "re_ek_t" (.TBytes 1152))
    [loc "ek" (.TBytes 0), loc "re_t_off" .TU64]
  rc_call "bytes_slice" (loc "re_rho" (.TBytes 32))
    [loc "ek" (.TBytes 0), loc "re_rho_off" .TU64]
  rc_let "re_t" MlkemPolyVecTy
  rc_call "polyvec_decode" (loc "re_t" MlkemPolyVecTy) [loc "re_ek_t" (.TBytes 1152)]
  rc_let "re_Ahat" MlkemPolyMatTy
  rc_call "gen_matrix" (loc "re_Ahat" MlkemPolyMatTy) [loc "re_rho" (.TBytes 32)]
  rc_let "re_At" MlkemPolyMatTy
  rc_call "mat_transpose" (loc "re_At" MlkemPolyMatTy) [loc "re_Ahat" MlkemPolyMatTy]
  rc_letU64 "re_n_r"; rc_set "re_n_r" 0
  rc_letU64 "re_n_e1"; rc_set "re_n_e1" 3
  rc_letU64 "re_n_e2"; rc_set "re_n_e2" 6
  rc_let "re_r_vec" MlkemPolyVecTy
  rc_let "re_e1" MlkemPolyVecTy
  rc_let "re_e2" MlkemPolyTy
  rc_call "cbd_eta1_polyvec" (loc "re_r_vec" MlkemPolyVecTy)
    [loc "rPrime" (.TBytes 32), loc "re_n_r" .TU64]
  rc_call "cbd_eta2_polyvec" (loc "re_e1" MlkemPolyVecTy)
    [loc "rPrime" (.TBytes 32), loc "re_n_e1" .TU64]
  rc_call "cbd_eta2_poly" (loc "re_e2" MlkemPolyTy)
    [loc "rPrime" (.TBytes 32), loc "re_n_e2" .TU64]
  rc_let "re_mu" MlkemPolyTy
  rc_call "msg_decode" (loc "re_mu" MlkemPolyTy) [loc "mPrime" (.TBytes 32)]
  rc_let "re_AtR" MlkemPolyVecTy
  rc_call "mat_vec_mul" (loc "re_AtR" MlkemPolyVecTy)
    [loc "re_At" MlkemPolyMatTy, loc "re_r_vec" MlkemPolyVecTy]
  rc_let "re_u" MlkemPolyVecTy
  rc_call "polyvec_add" (loc "re_u" MlkemPolyVecTy)
    [loc "re_AtR" MlkemPolyVecTy, loc "re_e1" MlkemPolyVecTy]
  rc_let "re_tr" MlkemPolyTy
  rc_call "polyvec_dot" (loc "re_tr" MlkemPolyTy)
    [loc "re_t" MlkemPolyVecTy, loc "re_r_vec" MlkemPolyVecTy]
  rc_let "re_tre2" MlkemPolyTy
  rc_call "poly_add" (loc "re_tre2" MlkemPolyTy)
    [loc "re_tr" MlkemPolyTy, loc "re_e2" MlkemPolyTy]
  rc_let "re_v" MlkemPolyTy
  rc_call "poly_add" (loc "re_v" MlkemPolyTy)
    [loc "re_tre2" MlkemPolyTy, loc "re_mu" MlkemPolyTy]
  rc_let "re_c1" (.TBytes 960)
  rc_call "polyvec_compress_du" (loc "re_c1" (.TBytes 960))
    [loc "re_u" MlkemPolyVecTy]
  rc_let "re_c2" (.TBytes 128)
  rc_call "poly_compress_dv" (loc "re_c2" (.TBytes 128))
    [loc "re_v" MlkemPolyTy]
  rc_let "cPrime" (.TBytes 1088)
  rc_call "bytes_concat_2" (loc "cPrime" (.TBytes 1088))
    [loc "re_c1" (.TBytes 960), loc "re_c2" (.TBytes 128)]
  -- Constant-time compare + conditional move.
  rc_let "neq" .TU64
  rc_call "bytes_neq" (loc "neq" .TU64)
    [loc "c" (.TBytes 1088), loc "cPrime" (.TBytes 1088)]
  -- Implicit-rejection branch: Krej = J(z ‖ c).
  rc_let "rej_in" (.TBytes 1120)
  rc_call "bytes_concat_2" (loc "rej_in" (.TBytes 1120))
    [loc "z" (.TBytes 32), loc "c" (.TBytes 1088)]
  rc_let "Krej" (.TBytes 32)
  rc_call "hash_j" (loc "Krej" (.TBytes 32)) [loc "rej_in" (.TBytes 1120)]
  -- Select K' on equal, Krej on differ.
  rc_call "bytes_cmov" (loc "K" (.TBytes 32))
    [loc "neq" .TU64, loc "Kprime" (.TBytes 32), loc "Krej" (.TBytes 32)]

/-! ### §7.4  `borrowOk` smoke checks for top-level kernels

These confirm the kernels pass the static borrow check.  The
intermediate `re_*` slot naming in decaps is what keeps it green —
without the prefix, slots like `r_vec` / `e1` / `u` / `v` would
collide between the outer "split-c" use and the inner "re-encrypt"
use of the same names. -/

#guard borrowOk mlkem_keygen_kernel
#guard borrowOk mlkem_encaps_kernel
#guard borrowOk mlkem_decaps_kernel

/-! ## §8 Spec-faithfulness notes

The primitive set above lines up 1:1 with the call-graph roots of the
Hax extraction (`Extraction/Mlkem_haxpipe.lean`).  The leaf semantics
are *not* defined here — they live behind the `LeafSpec.call` oracle
(see `MlkemHaxLowCTBridge.lean` §12 for the concrete-but-vacuous
witness, and the Friction #13 note for the NTT-vs-coefficient gap).

The LowCT terms in this file are spec-faithful in the *structural*
sense: every leaf appears in the correct location with the correct
tower-typed slots and the correct argument order.  Content-bearing
correctness (e.g. "the Hax `poly_mul` definition equals the formosa
`__polyvec_pointwise_acc` after NTT") is the bridge file's job — and
remains an open Friction.

Per-protocol mapping (matches `MlkemHaxLowCTBridge.lean` §11):

| LowCT primitive       | Hax extraction          | formosa-mlkem routine          |
|-------------------------|-------------------------|-------------------------------|
| `reduce`                | `reduce`                | `__barrett_reduce`             |
| `add` / `sub` / `mul`   | `add` / `sub` / `mul`   | inline / `__fqmul` (Montgomery) |
| `neg`                   | `neg`                   | inline                         |
| `poly_add` / `poly_sub` | `poly_add` / `poly_sub` | `_poly_add2` / `_poly_sub`     |
| `poly_mul`              | `poly_mul` (coeff form) | `_poly_basemul` (NTT form)     |
| `poly_scalar`           | `poly_scalar`           | inline                         |
| `polyvec_dot`           | `polyvec_dot`           | `__polyvec_pointwise_acc` (NTT) |
| `polyvec_add/sub`       | `polyvec_add/sub`       | `__polyvec_add2` / inline      |
| `mat_vec_mul`           | `mat_vec_mul`           | (inlined into `__indcpa_*`)    |
| `mat_transpose`         | `mat_transpose`         | (implicit; sampled directly)   |
| `compress_coeff`        | `compress_coeff`        | (inlined)                      |
| `decompress_coeff`      | `decompress_coeff`      | (inlined)                      |
| `poly_compress_d{u,v}`  | `poly_compress_d{u,v}`  | `_poly_compress*`              |
| `poly_decompress_d{u,v}`| `poly_decompress_d{u,v}`| `_poly_decompress*`            |
| `polyvec_encode/decode` | `polyvec_encode/decode` | `__polyvec_tobytes/frombytes`  |

-/

end CatCrypt.Crypto.MLKEM.MlkemLowCT
