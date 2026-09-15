# Benchmarks

Cycle counts on one host (AMD Ryzen 7 PRO 7840U, `taskset`-pinned, `rdtsc`),
each behind a byte-identical known-answer test. A ratio is our cycles divided by
the reference's; below 1.00 we are faster. Every row of the first three tables
compares against the fastest production implementation at the same instruction
tier, named in the reference column. Figures are from the development scoreboard
of 2026-08-11, reconciled with the artifact-tied record of 2026-08-26 on
2026-09-15. The full record, with tiers, harness commands, corrections and
shipped artifacts, is [bench/SCOREBOARD.md](bench/SCOREBOARD.md); the kernel
inventory is [CAPABILITIES.md](CAPABILITIES.md).

## Ahead of or at production, same tier

| kernel or primitive | reference (tier) | ratio |
|---|---|---:|
| SHA-512, 4-way | HACL\* `Vec256` (AVX2) | 0.38 |
| SDitH GF(251) syndrome | sdith-ref (scalar) | 0.57 |
| ML-KEM-768 encaps | libcrux (AVX2) | 0.58 |
| SHA-256, 8-way | HACL\* `Vec256` (AVX2) | 0.68 |
| ML-KEM-768 decaps | libcrux (AVX2) | 0.68 |
| SNOVA GF(16) multiply | SNOVA upstream (GFNI) | 0.85 |
| secp256k1 field multiply | s2n-bignum (ADX) | 0.94 |
| X25519, base point | libcrux (scalar ADX) | 0.97 |
| ChaCha20-Poly1305, 114 B | HACL\* `Simd128` (SSE) | 0.99 |
| AES-128-CTR | AES-NI reference | 1.00 |
| QR-UOV GF(127) matvec | QR-UOV reference (scalar) | 1.00 |
| Curve25519 field multiply | s2n-bignum (ADX) | 1.05 |
| X25519, variable base | libcrux (scalar ADX) | 1.06 |
| HMAC-SHA256 | HACL\* (scalar) | 1.06 |

Owned x86 backend against `jasminc` on the same nine emitted programs: 0.75.

## Behind production, same tier

| kernel or primitive | reference (tier) | ratio |
|---|---|---:|
| MQOM GF(251) MQ-eval | mqom-ref (scalar) | 1.18 |
| NTRU-HRSS ring multiply | ntruhrss701 reference (scalar) | 1.22 |
| HKDF-SHA256 | HACL\* (scalar) | 1.25 |
| ML-KEM-768 encaps | formosa (AVX2, hand-written) | 1.87 |
| FAEST-128s sign | faest-ref (scalar) | 2.1 |
| ML-KEM-768 decaps | formosa (AVX2, hand-written) | 2.33 |
| SHA-256, long messages | HACL\* (scalar) | 2.98 |
| SHA-512, long messages | HACL\* (scalar) | 3.35 |
| SHAKE128, long messages | HACL\* (scalar) | 3.82 |
| SLH-DSA-128s sign | liboqs (scalar SHA-2) | 6.9 |

The scalar SHA-2 and Keccak gap is register allocation in the owned backend
(the same kernels through `gcc -O3` run 6.7× and 8.6× faster than our
scalar emit). The ML-KEM gap against formosa is the by-value leaf interface,
which keeps the 768-coefficient vectors in memory between leaves.

## Ahead of production through an instruction-set extension it does not use

Not same-tier: the production code is scalar and ours uses the extension.

| kernel or primitive | ours | reference | ratio |
|---|---|---|---:|
| ML-KEM-768 NTT | AVX2 | PQClean (scalar) | 0.04 |
| ML-DSA-65 NTT | AVX2 | PQClean (scalar) | 0.11 |
| SHA-256 block compression | SHA-NI | HACL\* (scalar) | 0.20 |
| SHA-512, 4-way | AVX2 | libcrux (scalar) | 0.37 |
| Keccak-f1600, 4-way | AVX2 | HACL\* (scalar) | 0.38 |
| SLH-DSA-128s sign | SHA-NI leaf | liboqs (scalar SHA-2) | 0.56 |
| X25519, base point | scalar ADX | curve25519-dalek (AVX2) | 0.85 |
| X25519, variable base | scalar ADX | curve25519-dalek (AVX2) | 0.93 |

The last two rows are the opposite case: our scalar ladder is faster than the
production AVX2 one.
