# Benchmarks

The figures are transcribed from the CatCrypt benchmark record; the timing harnesses
and the reference builds that produced them are not part of this package. "Owned" code
is code that CatCrypt's own backend emits from the Jasmin dialect, as opposed to output
of Jasmin's compiler `jasminc`.

Cycle counts are from one host (AMD Ryzen 7 PRO 7840U, `taskset`-pinned, `rdtsc`),
each behind a byte-identical known-answer test. A ratio is our cycles divided by
the reference's; below 1.00 we are faster. The first two tables compare against
the fastest production implementation at the same instruction tier, named in the
reference column. [bench/SCOREBOARD.md](bench/SCOREBOARD.md) is the full record,
with tiers, harness commands and shipped artifacts; [CAPABILITIES.md](CAPABILITIES.md)
is the kernel inventory.

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

The owned x86 backend against `jasminc` on the same nine emitted programs: 0.75.

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

## P-384 ECDSA and DHKEM, emitted Rust orchestration

These rows are not in the tables above, because they are wall-clock medians of
whole operations rather than cycle counts, and in most of them the arithmetic
under the emitted orchestration is not ours. The compiler emits the call
sequence as Rust (`lake exe emit-p384-rust`); the leaves are the AUCurves
`p384-safe-rust` group law over the fiat-crypto Rust field or the CryptOpt
assembly field (`aucurves`), or AWS s2n-bignum assembly (`s2n`, where no byte
below the orchestration is ours). A ratio is ours over theirs in the same
process, on the same host, pinned. The full tables, dates, machine load and
commands are in
[bench/p384_ecdsa_rust/PERF.md](bench/p384_ecdsa_rust/PERF.md); the crate and
its tiering are described in
[bench/p384_ecdsa_rust/README.md](bench/p384_ecdsa_rust/README.md).

| operation | ours | reference | tier | ratio |
|---|---|---|---|---:|
| ECDSA sign | `aucurves`, fiat-crypto Rust field | RustCrypto `p384` 0.13.1 | same tier | 0.16 |
| ECDSA verify | `aucurves`, fiat-crypto Rust field | RustCrypto `p384` 0.13.1 | same tier | 0.49 |
| ECDSA verify | `aucurves`, CryptOpt field | Graviola 0.4.1 (s2n-bignum) | same tier | 1.54 |
| ECDSA sign | `s2n` | Graviola 0.4.1 (s2n-bignum) | same arithmetic; Graviola's column includes hashing and nonce derivation | 0.20 – 0.21 |
| ECDSA verify | `s2n` | Graviola 0.4.1 (s2n-bignum) | same arithmetic | 0.59 – 0.65 |
| ECDSA sign, nonce supplied | `s2n` | AWS-LC 5.9.0 | same tier | 0.41 |
| ECDSA verify | `s2n` | AWS-LC 5.9.0 | same tier | 0.88 |
| DHKEM encap, emitted | `s2n` | AWS-LC 5.9.0, reconstruction | same tier | 0.86 |
| DHKEM decap, emitted | `s2n` | AWS-LC 5.9.0, reconstruction | same tier | 0.98 |
| P-384 field multiply, cycles | emitted `p384_montmul_proven` | s2n-bignum `bignum_montmul_p384` (ADX) | same tier | 2.58 |

The ECDSA rows against RustCrypto and Graviola are from 2026-09-16, the AWS-LC
rows from a loaded machine on the same date, the DHKEM rows from the emitted
kernels on 2026-09-17, and the field-multiply row is invariant-TSC minima.
The emitted P-384 field multiply is not used under any of the whole-operation
rows.
