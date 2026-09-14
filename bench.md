# Benchmarks

The figures below were measured in the CatCrypt development repository on one host
(AMD Ryzen 7 PRO 7840U, RDTSC cycle counts, `taskset`-pinned). The timing harnesses,
the reference builds and the raw results are in that repository, which is private.
No ratio on this page can be reproduced from this package: the package ships
neither a harness nor the reference implementations, and for most rows it does not
ship the measured object either (column "artifact"). The figures are reported for
orientation only.

A ratio is our kernel's time divided by the reference's time: below 1.0 is faster,
above 1.0 is slower. "Owned x86 backend" is this package's own lowering and assembly
printer, as distinct from Jasmin's compiler `jasminc`. "Artifact" names the file under `bench/` for the row, or states that
none is shipped; [bench/PROVENANCE.md](bench/PROVENANCE.md)
describes every shipped `.s` file and the declaration that writes it.

## Field and bignum

| kernel | reference | ratio | artifact |
|---|---|---|---|
| Curve25519 field multiply, 4×64 limbs (`fe25519_mul_x86_from_lean`, owned x86 backend) | s2n-bignum `bignum_mul_p25519` | 0.98× | none; `x25519_fieldmul_compare/gen/fe25519_mul_proven.s` is a different render and was not timed |
| `bignum_mul_4_8`, 4×4 → 8 limbs (owned x86 backend) | s2n-bignum `bignum_mul_4_8` | 1.05× | none |
| `mpn_mul_basecase`, n = 16 to 128 limbs (emitted Jasmin compiled by `jasminc`) | libgmp | 0.79–0.90× | none |
| owned x86 backend against `jasminc` on the same emitted programs, 9 kernels | `jasminc` | 0.749× (geometric mean) | none |

## Symmetric

| primitive | reference | ratio | artifact |
|---|---|---|---|
| SHA-256 compression (owned x86 backend) | HACL\* `Hacl_Hash_SHA2`, scalar, long messages, cycles per byte | 2.98× | none; `sha2_linear_compare/sha256_owned_body.s` is a body-only render without prologue or return |
| SHA-256 compression (emitted) | a C implementation built with `gcc -O3`, checked to give output identical to the emitted kernel | 6.65× | none |
| SHA-512 compression (emitted, owned register allocation) | HACL\* `Hacl_Hash_SHA2`, scalar | 5.1–5.7× | none; `sha2_linear_compare/sha512_owned_body.s` is a body-only render without prologue or return |
| HMAC-SHA256, amortised over precomputed pad states (emitted SHA-256 compression) | HACL\* scalar SHA-2 | 1.06× | `hmac_compare/gen/sha256_compress.s` and `hmac_compare/gen/hmac_xor_pad.s` ship; the package does not record that they are the timed object files |

Keccak-f1600 has no current measurement against a reference. A render that predates
the current register allocator measured 2.55–3.82× slower per byte than HACL\*
`Hacl_Hash_SHA3`. `keccak_linear_compare/keccak_owned.s` ships without a record of
which render it is.

## Elliptic curve and pairing

| operation | reference | ratio | artifact |
|---|---|---|---|
| X25519 scalar-multiplication ladder (emitted from Lean, no external field leaf) | s2n-bignum | 1.857×, from an automatically parsed timing table with no audit of the comparison | none |
| BN254 Montgomery field multiply (owned x86 backend) | libgmp | 0.493×, from the same automatically parsed table; the reference's instruction-set tier is not recorded | `bn254_fieldmul_compare/gen_com/bn254_mont_mul_x86_from_lean.s` ships; the package does not record that it is the timed object file |

BLS12-377 has no ratio. Its orchestration is emitted by the owned backend, and the
field and pairing arithmetic are external calls into the AUCurves bedrock2 routines
(`bls12_377_compare/gen_com/bls12_377_orch_owned.s`).

## Proof-system hashing

| primitive | reference | ratio | artifact |
|---|---|---|---|
| Poseidon2 BabyBear width-16 permutation (AVX2 emit, lowered by `jasminc`) | Plonky3 v0.5.3, AVX2 backend | 1.30× | none |
