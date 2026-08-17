# Benchmark artifact provenance

Each `.s` under `bench/` is the emitted (or partly emitted) assembly for one
`bench.md` row, kept as the compiler produced it. This file records, per artifact,
which symbols are owned-emit (verified-compiler output) versus `call <leaf>` (a
linked external verified leaf), and the development-scoreboard line the row's ratio
is cited from. The timing harness itself is not shipped in this package.

| artifact | class | provenance | ratio source |
|---|---|---|---|
| `sha2_linear_compare/sha256_owned_body.s` | owned-emit | `sha256_compress_body`, whole compression, no external call | `bench/scoreboard/RESULTS.md:72` (HACL\* scalar ~6.6× faster — emit is behind) |
| `sha2_linear_compare/sha512_owned_body.s` | owned-emit | `sha512_compress_body`, whole compression, no external call | `bench/sha2_linear_compare/README.md:160-176` (HACL\* scalar ~5.1–5.7× faster) |
| `keccak_linear_compare/keccak_owned.s` | owned-emit | `keccak_f1600`, no external call | `bench/scoreboard/RESULTS.md:358` (no same-tier win; verified scheduler ~1.01×) |
| `x25519_fieldmul_compare/gen/fe25519_mul_proven.s` | owned-emit | `fe25519_mul_proven`, owned x86 backend, no external call | `bench/x25519_fieldmul_compare/README.md:65-66` (s2n `bignum_mul_p25519` = 0.98×, parity) |
| `hmac_compare/gen/sha256_compress.s` + `hmac_xor_pad.s` | adopted-leaf | HMAC glue over the owned resident `sha256_compress`; ipad/opad midstates plumbed | `bench/scoreboard/RESULTS.md:209` (HACL\* scalar = 1.06×, ours slightly slower) |
| `bn254_fieldmul_compare/gen_com/bn254_mont_mul_x86_from_lean.s` | owned-emit | `bn254_mont_mul`, owned x86 backend, no external call | `bench/RESULTS.md:59` (auto-parsed 0.493× vs libgmp scalar; **tier unconfirmed, uncurated**) |
| `bls12_377_compare/gen_com/bls12_377_orch_owned.s` | adopted-leaf | orchestration owned-emit (`bls377_field_add/sub/mul/square/inv`, `.globl`); the field/pairing arithmetic is `call bls377_{add,sub,mul,square,inv,pairing,Fp12_mul}` resolved at link into the AUCurves verified bedrock2 tower — **not emitted here** | `bench/RESULTS.md:219,270` (no committed ratio) |

Owned-emit (self-contained verified-compiler output): SHA-256/512 compress,
Keccak-f1600, `fe25519_mul`, BN254 mont-mul. Adopted-leaf (owned glue over a linked
verified leaf): HMAC, BLS12-377 orchestration.
