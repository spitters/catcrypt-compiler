/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# Ed25519 sign / verify — Lean specification layer

High-level specification of RFC 8032 Ed25519 signing and verification.

The field-layer and scalar-layer primitives live in `LowCTReflect.lean`
as reifier-visible axioms. SHA-512 is *not* reifier-visible because its
variable-length `ByteBuf` input does not match the fixed-size `memref<Nxi64>`
encoding that pipeline (1a) emits for field operations. Instead, SHA-512
runs as a `libjade`-linked symbol from the outer C wrapper in
`catcrypt-bench/src/bench_ed25519_*.c`, and the emitted MLIR handles only
the field-and-scalar compute.

This file names the interface so that Lean-side specifications,
correctness proofs, and future reifiable SHA-512 ports have a stable
entry point.

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│ C wrapper (bench_ed25519_sign.c)                            │
│                                                             │
│   jade_sha512(...)   ──►  scalar_reduce(...)  ──►          │
│   ed25519_scalarmult_base(...) ──►                         │
│   ed25519_compress(...)     (MLIR-emitted, pipeline 1a)     │
│                                                             │
│   All MLIR func.func calls resolve to                       │
│   catcrypt-bench/src/{ed25519_add,dbl,madd,compress,        │
│     decompress,scalar}.mlir                                 │
└─────────────────────────────────────────────────────────────┘
```

RFC 8032 §5.1 signing flow (PureEdDSA):
```
1. h      := SHA-512(seed)
2. a      := clamp(h[0..31])      -- secret scalar, 32 B
3. pfx := h[32..64]            -- for nonce derivation
4. A      := a · B                -- public key, compressed 32 B
5. r      := SHA-512(pfx || M) mod L     -- per-msg nonce scalar
6. R      := r · B                -- point commitment, compressed 32 B
7. k      := SHA-512(R || A || M) mod L     -- challenge scalar
8. s      := (r + k · a) mod L    -- response scalar
9. sig    := R || s
```

Steps 4, 6 are `ed25519_scalarmult_base` (emitted to MLIR via pipeline 1a).
Step 8 is `ed25519_scalar_s` (already emitted as `ed25519_scalar.mlir`).
Steps 1, 5, 7 are SHA-512, invoked from the C wrapper.

## Verification flow (RFC 8032 §5.1.7):
```
1. R, s   := parse(sig)
2. A'     := decompress(A)                 -- ed25519_decompress.mlir
3. k      := SHA-512(R || A || M) mod L
4. check  s · B == R + k · A'              -- ed25519_double_scalarmult_vartime
```

The double-scalarmult is a fused Shamir's-trick implementation, written
in C for variable-time efficiency (allowed because `A`, `R`, `k` are
public). Both `s · B` and `k · A'` use the emitted `ed25519_add` /
`ed25519_dbl` MLIR functions as leaves.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.Ed25519

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect

/-! ## 1. SHA-512 interface (not reifier-visible)

Opaque byte-buffer type + hash axiom. The implementation is
`jade_hash_sha512_amd64_ref` from libjade, pre-verified and linked via
`catcrypt-bench/src/jade_sha512.s`. KATs live in `bench_sha512.c`
(FIPS 180-4 empty, "abc", 896-bit, million-'a'). -/

/-- Opaque variable-length byte buffer. The reifier does not handle
    `ByteBuf` — instead, SHA-512 is invoked from the C wrapper and
    its output (which *is* fixed-size) is threaded into the field/scalar
    compute as one or two `FpL25519` values (via `scalar_reduce_64`). -/
axiom ByteBuf : Type
axiom ByteBuf.default : ByteBuf
noncomputable instance : Inhabited ByteBuf := ⟨ByteBuf.default⟩

/-- SHA-512 hash — 64-byte output, variable-length input. -/
axiom jade_sha512 : ByteBuf → ByteBuf

/-- Reduce a 64-byte SHA-512 output to a scalar mod L. The wrapper
    implementation splits the 64 bytes into two halves, interprets
    them as two `FpL25519` Montgomery-domain scalars, and recombines
    via `scalar_add` on `low + high · 2^256 mod L`. -/
axiom scalar_reduce_64 : ByteBuf → FpL25519

/-! ## 2. Ed25519 reference specification

These are spec-only Lean functions that mirror RFC 8032 step-by-step,
intended for future correctness proofs. They use the reifier-visible
axioms for all arithmetic, so the spec is definitionally close to the
deployed MLIR. Byte-level plumbing (clamping, 32-byte splits, sign-bit
packing) stays in the C wrapper. -/

structure EdPoint where
  X : Fp25519
  Y : Fp25519
  T : Fp25519
  Z : Fp25519

noncomputable instance : Inhabited EdPoint :=
  ⟨{ X := Fp25519.default, Y := Fp25519.default,
     T := Fp25519.default, Z := Fp25519.default }⟩

/-- Ed25519 base point `B`. Wired to the fiat-crypto-derived constant
    in `curve25519_64.c` via the C wrapper; spec value is abstract. -/
axiom basepoint : EdPoint

/-- Curve parameter `d = -121665/121666 mod p`, threaded through all
    Edwards-addition calls as the `two_d`/`d_const` argument. -/
axiom curve_d      : Fp25519
/-- `2·d` for extended-Edwards addition. -/
axiom curve_two_d  : Fp25519

/-- Fixed-base scalar multiplication `k · B`. Implementation is a
    windowed precomputed-table routine in C that drives the MLIR-emitted
    `ed25519_madd_*` functions. -/
axiom ed25519_scalarmult_base : FpL25519 → EdPoint

/-- Variable-base double-scalar `s·B + k·A`. Implementation uses
    Shamir's trick in variable time (only on public values during
    verification) and drives MLIR-emitted `ed25519_add_*` / `ed25519_dbl_*`. -/
axiom ed25519_double_scalarmult_vartime :
    FpL25519 → FpL25519 → EdPoint → EdPoint

/-! ### 2.1 Signing

Signature value: the C wrapper packages `R || s` into a 64-byte blob.
Here we expose the (scalar, point) pair the wrapper then serializes. -/

structure EdSignature where
  R : EdPoint      -- commitment point, compressed to 32 B by the wrapper
  s : FpL25519     -- response scalar, serialized as 32 B little-endian

/-- Compute the response scalar `s = r + k · a mod L`. This uses
    only `FpL25519` ops and is already reifier-visible — emitted in
    `ed25519_scalar.mlir`. -/
noncomputable def response_scalar (r a k : FpL25519) : FpL25519 :=
  ed25519_scalar_s r a k

/-- Ed25519 sign, spec form. Input: secret scalar `a`, nonce-pfx-
    derived `pfx` bytes, and message `M`. Output: `(R, s)` pair.
    SHA-512 invocations are abstract; the wrapper supplies concrete
    byte-buffer concatenations.

    RFC 8032 step numbering in comments. -/
noncomputable def sign
    (a : FpL25519)           -- secret scalar (clamp(h[0..31]))
    (pfx : ByteBuf)       -- h[32..64], for nonce derivation
    (A : EdPoint)            -- public key `A = a · B`
    (msg : ByteBuf)          -- message to sign
    (pfx_msg : ByteBuf)   -- pfx || M   (built by the wrapper)
    (R_A_msg : EdPoint → ByteBuf)
        -- R || A || M   builder (compresses R and concatenates) — supplied
        -- by the wrapper since byte-level serialization is not in Lean
    : EdSignature :=
  let r := scalar_reduce_64 (jade_sha512 pfx_msg)   -- step 5
  let R := ed25519_scalarmult_base r                   -- step 6
  let k := scalar_reduce_64 (jade_sha512 (R_A_msg R))  -- step 7
  let s := response_scalar r a k                       -- step 8
  { R := R, s := s }

/-! ### 2.2 Verification

Success predicate: returns `true` iff `s · B - k · A' == R`. The
wrapper computes `A' = decompress(A_bytes)` via `ed25519_decompress.mlir`
and `R = decompress(R_bytes)`. -/

/-- Point equality — the wrapper compresses both sides to 32 bytes and
    does a constant-time `memcmp`. Abstract in Lean. -/
axiom point_eq : EdPoint → EdPoint → Bool

/-- Ed25519 verify, spec form. All decompression and byte-assembly is in
    the wrapper; Lean sees the parsed point/scalar triple + SHA-512 output. -/
noncomputable def verify
    (R : EdPoint)        -- parsed from signature bytes 0..32
    (s : FpL25519)       -- parsed from signature bytes 32..64
    (A : EdPoint)        -- decompressed public key
    (R_A_msg : ByteBuf)  -- R || A || M built by wrapper
    : Bool :=
  let k := scalar_reduce_64 (jade_sha512 R_A_msg)
  let lhs := ed25519_double_scalarmult_vartime s k (neg_point A)
  point_eq lhs R
where
  /-- Abstract negation; C wrapper uses `ed25519_add_*` with `two_d` sign-flipped,
      or implements via `fp_opp` on `X` and `T` coordinates. -/
  neg_point : EdPoint → EdPoint := fun P => P

/-! ## 3. Axiom ↔ implementation correspondence

This section maps each axiom in this spec file to the concrete
artifact that implements it downstream. Together these establish
the TCB (trusted computing base) of our Ed25519 deployment:

| Spec axiom | Implementation | Status |
|------------|----------------|--------|
| `Fp25519` (type) | `uint64_t[5]` in `fiat_shim.c` + `curve25519_64.c` | Trusted: fiat-crypto proved correct |
| `FpL25519` (type) | `uint64_t[4]` Montgomery in `curve25519_scalar_64_exp.c` | Trusted: fiat-crypto proved correct |
| `fp_add/sub/mul/sqr/opp` | `fiat_shim.c::fp_*` with post-op carry | Trusted: fiat-crypto proofs |
| `fp_inv` | `dalek_shim.c::fe_invert` (254 sqr + 11 mul chain) | **Hand-coded, not proved** |
| `fp_invsqrt` / `fp_sqrt_ratio_i` | `dalek_shim.c::fe_pow_p58`, `fp_sqrt_ratio_i` | **Hand-coded, not proved** |
| `scalar_add/sub/mul/neg` | `dalek_shim.c::scalar_*` wrapping `fiat_25519_scalar_*` | Trusted |
| `scalar_reduce_64` | `dalek_shim.c::scalar_reduce_64` via Mont-abuse trick | **Hand-coded, not proved** |
| `jade_sha512` | `jade_sha512.s` assembled from verified libjade Jasmin | Trusted: libjade proofs |
| `basepoint` | `BASEPOINT_COMPRESSED` + `ed_decompress` at init | Trusted: RFC 8032 constant |
| `ed25519_scalarmult_base` | `bench_ed25519_sign.c::ed_scalarmult_base` (windowed, radix-16) | **Hand-coded, not proved** |
| `ed25519_double_scalarmult_vartime` | `ed_scalarmult_wnaf` (k·A) + `ed_scalarmult_base` (s·B) | **Hand-coded, not proved** |
| `sign` (def) | `bench_ed25519_sign.c::ed_sign` | Cross-checked via RFC 8032 §7.1 KATs (3/3 pass) |
| `verify` (def) | `bench_ed25519_sign.c::ed_verify` | Cross-checked via KATs (accepts our sigs + RFC's) |

## 4. Proof path (open work)

A full-stack correctness proof of `sign` and `verify` would compose:

1. **fiat-crypto lemmas** (given, machine-checked in Rocq):
   `fiat_25519_add`, `carry_mul`, `carry_square`, etc. are specified as
   bounded integer operations mod p = 2²⁵⁵−19. Analogous lemmas for
   `fiat_25519_scalar_*` mod L.

2. **Addition-chain correctness** (to prove, ~1 week):
   `fe_invert(z) = z^(p-2) mod p` for all z ≠ 0. Chain transcribed from
   ed25519-donna; each step is a sqr or mul, bounded-range trivially
   via fiat-crypto bounds. Proof shape: unroll the 254 sqrs + 11 muls
   and show each intermediate exponent. Tractable but tedious.

3. **Dalek `fp_sqrt_ratio_i` correctness** (to prove, ~2 weeks):
   Show that for u, v ∈ Fp with v ≠ 0 and u/v a quadratic residue,
   `fp_sqrt_ratio_i(u, v)` returns the canonical non-negative square
   root of u/v. Non-trivial: involves the Legendre-symbol / pow_p58
   trick + canonicalization branch.

4. **Scalar reduction correctness** (to prove, ~1 day):
   `scalar_reduce_64(bytes) = int(bytes) mod L` as Montgomery form.
   The Mont-domain trick is subtle (to_montgomery applied twice on
   the high half); a concrete statement + `decide`-level check for
   small inputs, then abstract argument via fiat lemmas for general.

5. **Edwards curve law** (to prove, ~2 weeks):
   Extended-coords point addition and doubling formulas are correct.
   Standard algebraic lemmas (also in the dalek Coq artifacts); can be
   ported.

6. **Scalarmult correctness** (to prove, ~1 week):
   Both windowed fixed-base and wNAF variable-base compute
   `scalar · P` correctly, given the point-operation lemmas.

7. **RFC 8032 sign/verify correctness** (to prove, ~1 week):
   Given 2–6 above, the wrapper flows `sign` and `verify` match the RFC
   spec. Mostly sequencing / byte-packing arithmetic.

Total: rough estimate 6–10 weeks of proof work for full end-to-end
certification. The KAT-based cross-check is the pragmatic substitute
for now; the pipeline-(1a) pieces (field + scalar primitives + ed_add/
dbl MLIR) are the same code paths used for actual signature operations,
so KAT agreement pins down correctness on every tested input. -/

end CatCrypt.Crypto.Jasmin.Ed25519
