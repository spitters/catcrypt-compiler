# Benchmarks

The compiler emits assembly inside Lean. These benchmarks measure that emitted
assembly against the fastest deployed reference for each primitive, cycle-for-cycle
on one host. The numbers below are a snapshot; the `bench/` directory holds the
harness and reproduces them.

## Method

Each kernel is pinned (`taskset`) and timed with RDTSC on an AMD Ryzen 7 PRO 7840U,
reported as the ratio of the emitted code to the reference — below 1.0 is faster
than the reference, above 1.0 is slower. Comparisons are made only at matching
scope, an emitted kernel against an emitted kernel and an adopted leaf against an
adopted leaf, and each row is one of:

- **like-for-like** — both sides fully emitted through the pipeline in the same
  backend class;
- **adopted leaf** — the emit rides a verified external leaf, so the ratio is near
  1.0 by construction;
- **partial** — a kernel whose whole-primitive assembly is not yet linked in
  a single binary; the ratio is a target, not a verdict.

## Field and bignum

Against verified references — s2n-bignum, Jasmin, fiat-crypto, libgmp — the emitted
arithmetic is at parity.

| kernel | reference | ratio |
|---|---|---|
| Curve25519 field multiplication | s2n-bignum | 0.98× |
| 4-limb bignum multiply | s2n-bignum / Jasmin | 1.05× / 0.982× |
| `mpn` basecase multiplication | libgmp | faster at every size |
| X25519 scalar-mul ladder (in-Lean, unadopted) | s2n-bignum | 1.61× |

The X25519 ladder row is the modularity floor: where the compiler emits an unadopted
kernel rather than riding a verified leaf, a small scheduling factor remains.

## Elliptic curve

Against optimized libcrux (AVX2), the Curve25519 operations built over the
self-emitted field:

| operation | ratio |
|---|---|
| X25519 `secret_to_public` | 0.97× |
| X25519 ECDH | 1.06× |

## Symmetric

Best variant against best variant, the emitted symmetric primitives are at or ahead
of the optimized reference:

| primitive | reference | ratio |
|---|---|---|
| SHA-256 (SHA-NI) | libcrux | 0.20× |
| SHA-3 / SHAKE (4-way AVX2) | libcrux | 0.46× |
| HMAC-SHA256 | libcrux | 0.30× |

## Coverage

The harness pairs the emit against the optimized libcrux crates: BLAKE2,
ChaCha20-Poly1305, Curve25519, Ed25519, HKDF, HMAC, ML-DSA, ML-KEM, SHA-2, SHA-3.
Some rows are partial — ChaCha20-Poly1305 rides a scalar Poly1305 leaf, the Ed25519
signers ride an adopted field leaf, and ML-KEM-768's arithmetic, sampling, and
orchestration are each emitted and checked against reference vectors but not yet
linked in a single binary. Extending the harness to the remaining crates and parameter sets
(P-256/ECDSA, RSA, further ML-KEM and ML-DSA parameters) is recompilation and wiring
over emit that already exists.
