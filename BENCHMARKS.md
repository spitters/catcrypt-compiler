# Benchmarks

These rows are timed on one host, an AMD Ryzen 7 PRO 7840U (Zen 4), with the process pinned to one core and a
load average near 2, on 2026-11-05. A ratio is ours over the reference, so a ratio below 1 means our code is
faster. Each row is one run of its harness, and the harness checks the object against the reference on test
vectors before timing it. The objects of the first two tables date from June to September 2026, before the
current back half `compileRegion`. Their harnesses are in the development repository, which is not public.

## Generated kernels

The verified front generates these objects from a Lean program. Cycles per operation.

| kernel | ours | reference | reference cycles | ratio |
|---|---:|---|---:|---:|
| SDitH syndrome and Reed-Solomon evaluation, GF(251) | 132 | SDitH production, Barrett | 231 | 0.57 |
| SDitH syndrome, GF(251) | 117.2 | SDitH production, Barrett | 111.0 | 1.06 |
| UOV dot product, GF(256) | 192.5 | pqov production `gf256_mul` | 106.4 | 1.81 |
| SNOVA ring, GF(16) | 356.7 | SNOVA production, multiplication table | 57.6 | 6.19 |
| MQOM MQ evaluation, GF(251), n = 8 | 646.5 | schoolbook C | 377.3 | 1.71 |
| FrodoKEM matrix multiply, 16 × 16 | 465.0 | HACL\* `matrix_mul`, C at `-O2 -mavx2` | 53.2 | 8.73 |

## Field multiplication

These objects are intermediate programs written by hand in Lean, which our compiler prints.

| field | ours | reference | reference figure | ratio |
|---|---:|---|---:|---:|
| secp256k1 | 26.6 cycles | s2n-bignum `bignum_mul_p256k1` | 27.0 cycles | 0.98 |
| Curve25519 | 30.0 cycles | s2n-bignum `bignum_mul_p25519` | 27.4 cycles | 1.09 |
| BLS12-381 | 32.6 ns | blst `mulx_mont_384` | 30.2 ns | 1.08 |
| BN254 | 15.4 ns | fiat-crypto C | 30.2 ns | 0.51 |
| P-384 | 266.5 cycles | s2n-bignum `bignum_montmul_p384` | 102.3 cycles | 2.60 |

## P-384 ECDSA and DHKEM

The compiler emits the call sequence of each operation as Rust ([`bench/p384_ecdsa_rust`](bench/p384_ecdsa_rust/README.md)).
The arithmetic below that sequence is linked: the AUCurves group law over the fiat-crypto Rust field or the
CryptOpt assembly field, or AWS s2n-bignum assembly. The figures are medians of whole operations in one process;
a reference's figure varies by about 3 % between runs. `PERF.md` beside the crate holds the method and the full
tables of an earlier run.

| operation | ours, arithmetic | ours | reference | reference figure | ratio |
|---|---|---:|---|---:|---:|
| ECDSA sign | fiat-crypto | 75.9 µs | RustCrypto `p384` | 475.9 µs | 0.16 |
| ECDSA verify | fiat-crypto | 427.9 µs | RustCrypto `p384` | 873.8 µs | 0.49 |
| ECDSA verify | CryptOpt | 315.4 µs | Graviola | 201.4 µs | 1.57 |
| ECDSA sign, nonce supplied | s2n-bignum | 23.9 µs | AWS-LC | 62.8 µs | 0.38 |
| ECDSA verify | s2n-bignum | 124.3 µs | AWS-LC | 141.4 µs | 0.88 |
| DHKEM encapsulation | s2n-bignum | 124.5 µs | AWS-LC, reconstructed | 143.2 µs | 0.87 |
| DHKEM decapsulation | s2n-bignum | 103.3 µs | AWS-LC, reconstructed | 104.2 µs | 0.99 |

## Comparison with `jasminc`

`jasminOfA` prints the program `compileA` compiles, and `jasminOfA_same_program` states that the two come from
one structured program. Three modules in the tree have such a text and a layout.

| program | `compileA` | `jasminc` | ratio |
|---|---:|---:|---:|
| `maj` | 7.22 ticks | 6.70 ticks | 1.08 |
| `fri_fold_fixed_bb` | 868 bytes | register allocation refused | none |
| `mpn_mul_1` | declined under its layout | not compared | none |

The `maj` figures are the median of three runs. `compileA` saves every callee-saved register on entry; the
`jasminc` code saves none.
