# Benchmark artifact provenance

The files below are the assembly artifacts tracked under `bench/`. None carries a
header comment; this table records, for each, the declaration or program that
writes it, whether it calls external symbols, and how it relates to
[bench.md](../bench.md). The timing harnesses are not part of this package, so no
artifact here comes with a way to time it.

| artifact | written by | external calls | bench.md row |
|---|---|---|---|
| `sha2_linear_compare/sha256_owned_body.s` | `lake exe sha256linear` (`VIR/Sha256LinearMain.lean`, its `<base>_owned_body.s` output): the function body without prologue, epilogue or return, the assembler baseline for the byte encoder | none | SHA-256; not the timed function |
| `sha2_linear_compare/sha512_owned_body.s` | `lake exe sha256linear sha512`, the same output for SHA-512 | none | SHA-512; not the timed function |
| `keccak_linear_compare/keccak_owned.s` | no module writes a file of this name; `lake exe keccaklinear` (`VIR/KeccakLinearMain.lean`) writes a render with the same symbol `keccak_f1600` to `bench/keccak_compare/gen/keccak_f1600_x86_from_lean.s` | none | Keccak-f1600; no current ratio |
| `x25519_fieldmul_compare/gen/fe25519_mul_proven.s` | `X86Backend.Fe25519MulProvenEmit.emitMain` | none | none; the Curve25519 row timed `fe25519_mul_x86_from_lean` |
| `hmac_compare/gen/sha256_compress.s` | no module writes a file of this name | none | HMAC-SHA256 |
| `hmac_compare/gen/hmac_xor_pad.s` | no module writes a file of this name; `VIR.HmacHkdfEmit.hmacXorPadJazz` is Jasmin source for a function of the same name | none | HMAC-SHA256 |
| `bn254_fieldmul_compare/gen_com/bn254_mont_mul_x86_from_lean.s` | `X86Backend.Bn254MontMulKernel.emitMain` | none | BN254 field multiply |
| `bls12_377_compare/gen_com/bls12_377_orch_owned.s` | `Pairing.Bls12_377Emit.emitMain` | the `bls377_*` field and pairing routines of AUCurves, resolved at link time | BLS12-377; no ratio |

Declaration names are relative to `CatCrypt.Crypto.SecureCompilation`, except
`Pairing.Bls12_377Emit`, which is relative to `CatCrypt.Crypto`; module paths are
relative to `CatCrypt/Crypto/SecureCompilation/`. No executable in `lakefile.lean`
calls the three `emitMain` declarations, and their modules do not run them during
elaboration.

`cryptopt/fiat_curve25519_carry_mul.asm` and
`cryptopt/fiat_curve25519_solinas_square.asm` are not benchmark artifacts. They are
CryptOpt-generated kernels from fiat-crypto, which `X86Backend/NasmParse.lean` reads
for the ascent proofs ([ASCENT.md](../ASCENT.md), "Hand-written assembly").
