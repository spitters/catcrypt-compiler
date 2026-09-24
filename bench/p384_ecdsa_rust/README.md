# `p384_ecdsa_rust`: leaf shims, tests and benchmarks for the emitted P-384 ECDSA and DHKEM source

kind: authored · authority: canonical for this directory · freshness: the file
tables go stale when the emitter or the leaf backends change; the measured
figures are in [PERF.md](PERF.md), each with its date

The CatCrypt compiler emits the orchestration of ECDSA-P-384 as Rust that
calls thirteen leaf functions. This crate supplies those leaves, a second
implementation to test the emitted code against, the FIPS 186-4 CAVP
vectors, the Wycheproof adversarial corpus, equivalence and interop tests
against RustCrypto and Graviola, and a wall-clock comparison with both.
Behind `--features production` it adds the C libraries production TLS
stacks run, OpenSSL 3.0, BoringSSL and AWS-LC, and Microsoft SymCrypt, to
the interop suite and the benchmark
([§ OpenSSL and BoringSSL](#openssl-and-boringssl-the-production-opponents),
[§ AWS-LC](#aws-lc-the-third-production-opponent),
[§ SymCrypt](#symcrypt-the-fourth-production-opponent)).

The leaves come in three backends, and the same emitted orchestration is
compiled over each: AUCurves `p384-safe-rust` with the fiat-crypto field,
the same with the CryptOpt assembly field, and, behind `--features s2n`,
AWS s2n-bignum assembly. Graviola's P-384 arithmetic is s2n-bignum, so the
third backend makes the comparison with Graviola one of orchestration alone.
[§ The three leaf backends](#the-three-leaf-backends) says what each
configuration is for, and
[PERF.md § Whole operation, three backends](PERF.md#whole-operation-three-backends)
holds the result.

The crate also carries DHKEM(P-384, HKDF-SHA384), RFC 9180 KEM id
`0x0011`, `Encap` and `Decap` only, over the same backends, with its own
reference and interop suite:
[§ DHKEM(P-384, HKDF-SHA384)](#dhkemp-384-hkdf-sha384).

All measurements, with host, load, commands and ratios, are in
[PERF.md](PERF.md). A ratio there is ours over theirs, measured in the same
process.

## What is where

The P-384 and s2n-bignum material spans three repositories:
catcrypt-compiler (this repository), the development tree SSProve-lean, and
the AUCurves tree at `../BLS/AUCurves`. A path of the form `../X` in prose is
relative to the root of this repository; commands run from this directory. Paths in
the table are relative to the root of
the repository named in the second column. The "proved" column states only what
the module docstring of the file states; "none" means the file carries no
theorem. Elsewhere in this document a code span of the form `checkout:path`
names a file of an external checkout or package (for example
`openssl-3.0.13:crypto/ec/ec_lib.c` or `graviola-0.4.1:src/mid/p384.rs`),
not a file of this repository.

| path | repository | what it is | what is proved |
|---|---|---|---|
| [`CatCrypt/Crypto/Jasmin/P384Reflect.lean`](../../CatCrypt/Crypto/Jasmin/P384Reflect.lean) | catcrypt-compiler | Lean front: P-384 surface types, the group-law leaf registrations, the MSM-term and two-term MSM kernels as `LowCT`, their Rust rendering (`emitP384Rust`) | structural only: each body lowers to a Jasmin command of the stated length with the stated leaf names; the leaves are axioms; no constant-time or security property |
| [`CatCrypt/Crypto/Jasmin/P384EcdsaReflect.lean`](../../CatCrypt/Crypto/Jasmin/P384EcdsaReflect.lean) | catcrypt-compiler | Lean front: ECDSA-P-384 verify and sign as call-only `LowCT` over the mod-`n` scalar leaves (`emitP384EcdsaRust`) | structural only: command counts (13 for verify, 10 for sign) and the leaf name of each command; no unforgeability or constant-time property |
| [`CatCrypt/Crypto/Jasmin/P384DhkemReflect.lean`](../../CatCrypt/Crypto/Jasmin/P384DhkemReflect.lean) | catcrypt-compiler | Lean front: DHKEM(P-384, HKDF-SHA384) `Encap` and `Decap` as call-only `LowCT` (`emitP384DhkemRust`) | structural only: the ordered leaf names of each lowered body; no IND-CCA, correctness or constant-time property |
| [`CatCrypt/EmitArtifacts/P384Rust.lean`](../../CatCrypt/EmitArtifacts/P384Rust.lean) | catcrypt-compiler | emit driver, `lake exe emit-p384-rust`, run from the repository root; writes `gen/` of this directory | none |
| [`gen/`](gen/PROVENANCE.md) | catcrypt-compiler | the emitted Rust: `p384_ecdsa_verify.rs`, `p384_ecdsa_sign.rs`, `p384_ecdsa_verify_msm.rs`, `p384_msm_term.rs`, `p384_dhkem_encap.rs`, `p384_dhkem_decap.rs`; never hand-edited | none; see the front modules |
| `src/generated.rs` | catcrypt-compiler | includes `gen/` once per backend; the hand-written fallback transcription | none |
| `src/leaves.rs`, `src/scalar.rs`, `src/lincomb.rs`, `src/sec1.rs`, `src/dhkem_kdf.rs` | catcrypt-compiler | leaf backend `aucurves`: shims over `p384-safe-rust`, fiat-crypto's scalar field and `safegcd-rs`, the interleaved two-term multiply, SEC1 and HKDF leaves | none; see [§ The leaves and their constant-time status](#the-leaves-and-their-constant-time-status) |
| `src/leaves_s2n.rs`, `src/s2n.rs`, `src/comb_s2n.rs`, `src/lincomb_s2n.rs` | catcrypt-compiler | leaf backend `s2n` (`--features s2n`): shims over the s2n-bignum archive, the fixed-base comb and the interleaved pass | none in this repository; s2n-bignum's routines carry HOL Light proofs upstream |
| `src/backend.rs` | catcrypt-compiler | the backend table the tests and the benchmark iterate | none |
| `src/reference.rs`, `src/dhkem_ref.rs` | catcrypt-compiler | independent reference ECDSA and DHKEM | none |
| `tests/`, `src/vectors.rs` | catcrypt-compiler | CAVP, Wycheproof, differential, leaf, scalar, s2n-backend, RustCrypto, Graviola, production and DHKEM suites ([§ Commands](#commands)) | none; test evidence |
| `src/rc.rs`, `src/grav.rs`, `src/ossl.rs`, `src/ossl_kem.rs`, `src/bssl.rs`, `src/awslc.rs`, `src/symcrypt.rs`, `src/hpke_rs.rs` | catcrypt-compiler | bridges to the opponents: RustCrypto `p384` 0.13.1, Graviola 0.4.1, OpenSSL, BoringSSL, AWS-LC, SymCrypt 103.13.0, hpke-rs 0.7.0 | none |
| `src/bin/bench.rs`, `src/bin/fieldbench.rs` | catcrypt-compiler | the ECDSA and DHKEM benchmark; the field-multiply comparison | none; results in [PERF.md](PERF.md) |
| [`bench/s2n_import`](../s2n_import/README.md) | catcrypt-compiler | the s2n-bignum importer (`import_s2n.sh`, `translate.awk`), re-emit and encode drivers, the framed known-answer test | none; the importer is untrusted |
| [`Ascent/Demos/S2nMontmulP384.lean`](../../CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontmulP384.lean), [`S2nMontsqrP384.lean`](../../CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontsqrP384.lean) | catcrypt-compiler, under `CatCrypt/Crypto/SecureCompilation/` | the imported `bignum_montmul_p384` (264 instructions) and `bignum_montsqr_p384` (230) as `List (JInstr 64)`, pinned to s2n-bignum commit `7bd7c8ca` | the block lengths |
| [`Ascent/Demos/S2nMontmulP384Proof.lean`](../../CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontmulP384Proof.lean) | catcrypt-compiler | correctness of the imported montmul block | `s2nMontmulP384_correct`: under `runBlock`, for `x · y ≤ 2^384 · p384`, the block stores `z < p384` with `z = x · y · (2^384)⁻¹` in `ZMod p384`; name-keyed memory, no aliasing between output and inputs |
| [`Ascent/Demos/S2nMontmulP384Bytes.lean`](../../CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontmulP384Bytes.lean) | catcrypt-compiler | the montmul block carried to the owned encoder's bytes | `s2nMontmulP384_decode`: the bytes decode to the block; `s2nMontmulP384Bytes_correct`: the decoded instructions compute the Montgomery product; decoder-to-processor agreement is not proved |
| [`Ascent/Demos/S2nMontmulP384Addr.lean`](../../CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontmulP384Addr.lean) | catcrypt-compiler | the montmul result over address memory | `s2nMontmulP384_correct_addr` with no hypothesis relating the three pointers (in-place and squaring instances included); `s2nMontsqrP384_sim_addr`: the montsqr block's address run agrees with its name-keyed run |
| [`Ascent/Demos/S2nMontmulP384Framed.lean`](../../CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontmulP384Framed.lean) | catcrypt-compiler | the montmul block inside the red-zone leaf frame, the source of `bignum_montmul_p384_framed` | `s2nMontmulP384FramedBytes_correct`: the decoded framed bytes compute the product and restore `%rsp` and the six callee-saved registers; the red zone not overlapping the caller's buffers is assumed |
| [`Ascent/AddrMem.lean`](../../CatCrypt/Crypto/SecureCompilation/Ascent/AddrMem.lean) | catcrypt-compiler | an address-memory machine for `JInstr 64` and the discipline checks | simulation of `runBlock` by `runBlockA` under the address discipline |
| [`X86Backend/LeafFrame.lean`](../../CatCrypt/Crypto/SecureCompilation/X86Backend/LeafFrame.lean) | catcrypt-compiler | the System V red-zone save/restore frame as `JInstr 64` | `runBlock_framed`, `corresJ_framed` for bodies satisfying `frameSafe` |
| [`X86Backend/EncodedBlockCorres.lean`](../../CatCrypt/Crypto/SecureCompilation/X86Backend/EncodedBlockCorres.lean) | catcrypt-compiler | `CorresJ` carried from a block to its encoded byte stream | `encodeJBlock_bytesCorresJ`, `encodeJBlock?_bytesCorresJ` |
| [`X86Backend/SailX86LeanUniversal.lean`](../../CatCrypt/Crypto/SecureCompilation/X86Backend/SailX86LeanUniversal.lean) | catcrypt-compiler | the owned instruction model compared with Sail-x86 and the Intel SDM for the instructions of the montmul block | `evalInstr` equal to, or refining, the transcribed Sail bodies (or SDM definitions) for every starting state, register name and operand value |
| `p384-safe-rust` | AUCurves | P-384 field and group in Rust: fiat-crypto field, RCB `a = -3` complete formulas, 4-bit window, `W = 5` comb; field chosen at build time (fiat, CryptOpt, s2n-bignum, encoded montmul) | outside this repository; see its README |
| `safegcd-rs` | AUCurves | Bernstein-Yang divstep inversion; `safegcd_p384` (field) and `safegcd_p384_order` (group order) | outside this repository; convergence certificates in Rocq under AUCurves |
| `fiat-crypto/fiat-rust` | AUCurves | fiat-crypto generated Rust, including `fiat-rust:src/p384_64.rs` and `fiat-rust:src/p384_scalar_64.rs` | outside this repository |

The two emitted field kernels that `fieldbench` links are untracked files of
this repository, written by `emitMainP384` in
`CatCrypt/Crypto/SecureCompilation/X86Backend/Curve6MontMulProvenEmit.lean` and
by `emitP384` in `CatCrypt/Crypto/SecureCompilation/X86Backend/P384FieldKernel.lean`
([§ Paths](#paths)):

    bench/p384_compare/gen/p384_montmul_proven.s
    bench/p384_fieldmul_compare/gen_com/p384_mul_x86_from_lean.s

## The emitted entry points

    p384_ecdsa_verify(e: &[u8;48], r: &[u8;48], s: &[u8;48],
                      Q: &[u8;144], ok: &mut u64)
    p384_ecdsa_sign(e: &[u8;48], d: &[u8;48], k: &[u8;48],
                    r: &mut [u8;48], s: &mut [u8;48], ok: &mut u64)
    p384_ecdsa_verify_msm(u1: &[u8;48], G: &[u8;144],
                          u2: &[u8;48], Q: &[u8;144],
                          __result: &mut [u8;144])
    p384_msm_term(k: &[u8;48], P: &[u8;144], __result: &mut [u8;144])

Neither `p384_ecdsa_verify` nor `p384_ecdsa_sign` takes `G`: multiples of
the generator go through `p384_scalar_mul_base`, which carries the base
point in its precomputed table, and through `p384_lincomb`, which carries
it in the interleaved pass. `p384_ecdsa_verify_msm`
and `p384_msm_term` are the two-term and one-term multi-scalar
multiplications and are still parametric in the points;
`tests/diff.rs::msm_matches_the_reference` exercises the two-term one, and
`p384_msm_term` is re-exported and otherwise unused here.

`p384_ecdsa_sign`'s `ok` is `in_range(r) AND in_range(s)`. `k` is an input,
so the kernel cannot retry: a caller that gets `ok = 0` resamples `k`. A
zero `k` drives `r` to zero and is reported the same way.

## Provenance of each component

| layer | source | ours? |
|---|---|---|
| ECDSA orchestration (`gen/*.rs`) | CatCrypt compiler emit | ours |
| leaf shims (`src/leaves.rs`) | this crate | ours (plumbing only, no arithmetic) |
| two-term multiply `u1*G + u2*Q` (`src/lincomb.rs`) | this crate | ours |
| mod-`n` reduction, addition, Fermat inverse (`src/scalar.rs`) | this crate | ours |
| group law (`g1_add`, `g1_double`, `g1_neg`, `g1_scalar_mul`, `g1_scalar_mul_base`) | AUCurves `p384-safe-rust`, Rocq-emitted RCB `a = -3` formulas, Qed borrow certificates | ours |
| `fp_inv`, the base-field inverse | Bernstein-Yang divstep port in AUCurves `safegcd-rs`, against the Rocq convergence certificate | ours |
| mod-`n` divstep inverse | the same port, instantiated at the group order in `safegcd-rs:src/safegcd_p384_order.rs` | ours |
| mod-`n` multiply, squaring, Montgomery conversions | fiat-crypto `fiat-rust:src/p384_scalar_64.rs` | external, machine-generated and machine-checked |
| base field | fiat-crypto `fiat-rust:src/p384_64.rs`, and optionally the CryptOpt assembly | external |
| reference sign and verify (`src/reference.rs`) | this crate | ours |
| RustCrypto `p384` 0.13.1 / `ecdsa` 0.16.9 | external | reference and benchmark baseline, never ours |
| Graviola 0.4.1 | external, s2n-bignum assembly | second reference and benchmark baseline, never ours |
| OpenSSL 3.0.13 `libcrypto.so.3` | external, system library | production opponent (`--features production`), never ours |
| BoringSSL at `956bac6e4db9` | external, `libcrypto.a` | production opponent (`--features production`), never ours |
| AWS-LC 5.9.0 at `f3798b6fe6a8` | external, `libcrypto.so` of the build tree `../bench_refs/aws-lc-build`, P-384 field in s2n-bignum assembly | production opponent, ECDSA and DHKEM reconstruction (`--features production`, skipped when absent), never ours |
| Microsoft SymCrypt 103.13.0 at `286762b` (MIT) | external, the shared module `libsymcrypt.so.103` of the CMake preset `Linux_AMD64_GCC_Release`, P-384 field in SymCrypt's own MULX assembly | production opponent, ECDSA and DHKEM reconstruction (`--features production`, skipped when absent), never ours |
| DHKEM orchestration (`gen/p384_dhkem_*.rs`) | CatCrypt compiler emit | ours |
| DHKEM leaves (`src/leaves.rs`, `src/leaves_s2n.rs`, `src/dhkem_kdf.rs`, `src/sec1.rs`) | this crate | ours (plumbing; HKDF is `hkdf` 0.12.4 / `hmac` 0.12.1 / `sha2` 0.10.9, external) |
| reference DHKEM (`src/dhkem_ref.rs`) | this crate over RustCrypto `p384` ECDH and `hkdf` | reference, not a kernel |
| hpke-rs 0.7.0 with `hpke-rs-rust-crypto` 0.7.0 | external | DHKEM production opponent, never ours |
| OpenSSL 3.6.0, Microsoft Defender's `libcrypto.so.3` | external, found on the machine | DHKEM native-API opponent (`--features production`), never ours |
| OpenSSL 4.1.0-dev, `../bench_refs/openssl-install/lib/libcrypto.so.4` | external, built from the `bench_refs/openssl` checkout (HEAD `83ef562`; that the install matches this HEAD was not checked) | the same role, selected with `P384_OPENSSL36_LIBCRYPTO`, never ours |

Every layer that differs between the two sides is ours. The field is the one
layer neither side owns and both sides share: RustCrypto's
`p384-0.13.1:src/arithmetic/field/p384_64.rs` and the field AUCurves calls are
the same fiat-crypto generated code, so in the pure-Rust configuration the
measurement isolates the group law, the scalar layer and the orchestration —
all three of them ours.

The CryptOpt assembly is the exception and is external, which is why the row
that links it is marked as not same-tier against RustCrypto. Against
Graviola the tiering is the other way round; the next section sets it out.

The crate is pure Rust when the CryptOpt assembly is not linked. AUCurves
links it only on x86-64 Linux with BMI2 and ADX and with `nasm` present, and
`P384_NO_CRYPTOPT=1` forces the fiat-crypto field leaves instead.
`p384::CRYPTOPT_ASM` reports which of the two a binary got, and the benchmark
prints it.

## The three leaf backends

`src/backend.rs` is the table the tests and the benchmark iterate. The
emitted sources in `gen/` are included once per backend (`src/generated.rs`),
so every backend runs character-for-character the same orchestration over a
different set of leaves.

| backend | leaves | field and group law | ours? |
|---|---|---|---|
| `aucurves`, pure Rust | `src/leaves.rs` | AUCurves `p384-safe-rust` RCB complete formulas over the fiat-crypto field | group law ours, field external |
| `aucurves`, assembly | `src/leaves.rs` | the same group law over the CryptOpt field | group law ours, field external |
| `s2n` | `src/leaves_s2n.rs` | AWS s2n-bignum `p384_montj*` and `bignum_*_p384` | **neither ours**; the orchestration above them is |

### The question each configuration answers

The `aucurves` configuration is the one where the group law is ours: the
Renes-Costello-Batina complete formulas AUCurves emits from Rocq, over a
field neither side owns. Its ratio against RustCrypto is the measurement of
our group law plus our orchestration against a production Rust
implementation.

The `s2n` configuration is the one where **nothing below the orchestration is
ours** — the field, the point operations and the scalar multiplication are
all AWS's assembly, machine-checked in HOL Light, external to us exactly as
fiat-crypto and CryptOpt are. Its ratio against Graviola is therefore the
measurement of orchestration alone: both sides run the same arithmetic, and
what differs is how the multiplications are organised above it.

Neither replaces the other, and both are kept. A win in the `s2n`
configuration does not measure our group law, and a win in the `aucurves`
configuration is against an opponent on different arithmetic.

### The two orchestration levers

Graviola's README states that its P-384 base-point and variable-point
multiplications both use a five-bit Booth window, "which leaves some P384
base point performance on the table", and its verification runs two separate
window multiplications. The `s2n` backend spends its orchestration exactly
there:

* `src/comb_s2n.rs` — a fixed-base comb for the generator. Seventy-seven
  five-bit windows, every multiple `d * 2^(5i) * G` precomputed in affine
  Montgomery coordinates, so the pass is seventy-seven `p384_montjmixadd`
  calls and **no doublings at all**, against the three hundred and
  eighty-four doublings a windowed variable-point multiplication performs.
  The table is 229 KB, built once on first use from the generator with a
  single Montgomery batch inversion.
* `src/lincomb_s2n.rs` — the interleaved two-term multiply, the same
  structure as `src/lincomb.rs` over the s2n-bignum point operations, with
  the generator's additions taking the mixed-addition path against a
  precomputed affine table and `Q`'s a per-call Jacobian one.

The comb's table lookup is a full linear scan of all thirty-one entries with
a mask select, and a zero digit adds a dummy entry whose result is
mask-selected away, so no branch and no address depends on the scalar. The
mixed addition is never handed equal or mutually inverse arguments, which it
does not serve: before window `i` the accumulator represents an integer
`m < 2^(5i)` and the addend one `a >= 2^(5i)`, so `m != a`, and `m + a` is a
partial sum of the digits of `k`, hence below `n`, so they are not mutually
inverse either. The module header carries the argument. The interleaved pass
has no such argument, so it detects the case instead and substitutes the
double.

### The Jacobian representation

**In the `s2n` backend the 144 bytes are a Jacobian triple, not a projective
one.** `src/leaves.rs` carries the homogeneous projective `(X : Y : Z)` of
the RCB formulas, where the affine point is `(X/Z, Y/Z)`.
`src/leaves_s2n.rs` carries the Jacobian `(X, Y, Z)` of `p384_montjadd`,
where it is `(X/Z^2, Y/Z^3)`. Both are `X || Y || Z` as three 48-byte
little-endian Montgomery field elements, so they are the same 144 bytes with
different meanings, and a point string is not portable between backends.

That is safe because the emitted kernel never inspects point bytes: it
receives `Q` from its caller, passes it between leaves, and reads a scalar
back out. The backend has to be internally consistent, and it has to agree
with the others at exactly two places, both checked directly in
`tests/s2n.rs`:

1. `p384_point_affine_x` yields the same canonical `x` for the same curve
   point, and zero for the identity —
   `affine_x_agrees_with_the_projective_backend`, twenty-four points plus
   the identity.
2. `p384_point_valid` has the same identity and validity semantics —
   `point_valid_agrees_with_the_projective_backend`, twenty-four valid keys,
   eight off-curve strings and the identity.

Everything outside the crate builds a point string through
`Backend::point_from_affine`, `Backend::identity` or `Backend::generator`,
never through `codec::point_bytes`.

### Tiering and ownership of the `s2n` configuration

s2n-bignum is AWS's, machine-checked in HOL Light, and external to us in
exactly the sense fiat-crypto and CryptOpt are. So this configuration is
**our orchestration over external verified assembly**, and against Graviola
it is the same-tier comparison, because both sides then run the same
arithmetic. It is not a claim about our compiler's code generation: no byte
under these leaves was emitted by us.

The archive is `x86/libs2nbignum.a` in the s2n-bignum checkout named by
`S2N_BIGNUM_DIR` ([§ Paths](#paths)). It is read, never modified, and linked
by `build.rs` behind the `s2n` feature. With the feature off the crate builds
and tests exactly as before.

## Graviola, the second opponent

Graviola 0.4.1 (`graviola::signing::ecdsa` over `curve::P384`) is the second
external implementation this crate is measured and cross-checked against.
`src/grav.rs` is the bridge, `tests/graviola.rs` the interop suite.

### Its arithmetic

Graviola's P-384 field, group and scalar arithmetic is hand-written x86-64
assembly imported from AWS's [s2n-bignum](https://github.com/awslabs/s2n-bignum)
and machine-checked in HOL Light: `bignum_montmul_p384`,
`bignum_montsqr_p384`, `bignum_inv_p384`, `p384_montjadd`,
`p384_montjdouble`, `bignum_point_select_p384`, under
`graviola-0.4.1/src/low/x86_64/`, each carrying the s2n-bignum copyright and
the "generated source, do not edit" header. Graviola's own README states it:
"All ECC field and scalar arithmetic are provided by s2n-bignum", and "P384
base and variable point multiplication both use a 5-bit exponent window with
Booth encoding".

So Graviola is not another fiat-crypto consumer. RustCrypto and this crate
share the same generated fiat-crypto Rust field; Graviola shares nothing with
either.

### Tiering

| our configuration | against Graviola | why |
|---|---|---|
| `s2n` backend | same tier **and same arithmetic** | the identical s2n-bignum routines on both sides; the difference is orchestration alone |
| `aucurves`, CryptOpt assembly field | same tier | assembly against assembly, but a different group law and a different field |
| `aucurves`, fiat-crypto field, pure Rust | not same tier | Rust against assembly; we expect to lose |

The pure-Rust rows against Graviola are reported with that label rather than
omitted. All three are in the tables of [PERF.md](PERF.md), and where we lose the row says
so.

### The signing-fairness problem

The two sides' signing APIs do not cover the same work, and the ratio must
not be read as though they did.

| side | hashes the message | reads the system RNG | derives the nonce | curve arithmetic |
|---|---|---|---|---|
| our emitted kernel | no, takes `e` | no | no, takes `k` | yes |
| RustCrypto `try_sign_prehashed` | no, takes `e` | no | no, takes `k` | yes |
| Graviola `sign::<Sha384>` | yes | yes, 16 bytes | yes, RFC 6979 HMAC_DRBG | yes |

Graviola's `rfc6979_sign_with_random` — the entry point that takes the
sixteen bytes as an argument — is private, so the DRBG cannot be bypassed
from outside the crate. Neither can the hash: `verify` and `sign` are generic
over a `Hash`, but `Hash::zeroed_block` returns
`graviola::high::hash::HashBlock`, a type that no public path names, so the
trait cannot be implemented downstream and no prehashed instantiation exists.

What is reported instead: Graviola's full `sign` as measured, with the three
components it performs and our kernel does not timed separately in the same
round-robin, so the arithmetic-only cost can be bounded. The SHA-384 and the
sixteen-byte RNG read are called directly. The DRBG is a reconstruction over
Graviola's own public `Hmac<Sha384>` following `graviola-0.4.1:src/high/hmac_drbg.rs`: four
invocations to seed `HmacDrbg::new(d, e, random)` and three to draw one
48-byte candidate through `RandomSource::fill`, seven HMAC-SHA-384
invocations in all. A rejected candidate would add three, which for P-384
happens with probability about 2^-194. What the reconstruction cannot cover
is whatever else `sign` does — the private-key encode, the zeroise, the
rejection test — so the difference is an *upper* bound on Graviola's
arithmetic-only signing cost, and the ratio computed against it is an upper
bound on our ratio.

Verification has no such problem: Graviola's `verify` takes no RNG and no
DRBG and differs from our kernel only by hashing the message. The benchmark
message is 25 bytes, one SHA-384 block, and the measurement in [PERF.md](PERF.md) puts the
hash at 0.1% of the verify row. Verification is therefore the headline
Graviola comparison.

### Interop

`tests/graviola.rs`, eight tests, all passing in both field configurations.
The marshalling: our `(r, s)` are two canonical little-endian 48-byte
integers and Graviola wants the fixed-length big-endian concatenation
`r || s`; our public key is the 144-byte projective form and Graviola wants
the 97-byte X9.62 uncompressed encoding `0x04 || X || Y`. `src/grav.rs`
carries both conversions, alongside `src/rc.rs`'s analogues.

| check | result |
|---|---|
| our emitted signature verifies under Graviola's `VerifyingKey` | 32/32 accepted, 32/32 with a flipped bit rejected |
| Graviola's signature verifies under `p384_ecdsa_verify` with `ok = 1` | 32/32 accepted, 32/32 tampered rejected |
| Graviola and this crate derive the same public key from `d` | 32/32 |
| CAVP `d` gives the published public key under Graviola | 15/15 |
| CAVP `k` gives `x(k*G) mod n` equal to the published `r` under Graviola | 15/15 |
| CAVP `(d, k)` signed by the emitted kernel, verified by Graviola | 15/15 |
| SHA-384 agrees between the `sha2` crate and Graviola | 32/32 |
| the HMAC_DRBG reconstruction yields a nonce in range | 16/16 |

Checks 1 and 2 run over a real message, with this crate's side taking
`e = SHA-384(message) mod n` from the `sha2` crate and Graviola hashing the
same message itself, so the two sides reach the same scalar through two
independent SHA-384 implementations.

The CAVP block is three checks rather than one because the vectors in
`src/vectors.rs` carry the digest `m` and not the message it came from, and
Graviola has no prehashed entry point. No `(m, r, s)` triple can be put
through its verify. What is reachable is its base-point multiplication, which
both published scalars go through: `d` must give the published `(Qx, Qy)`,
and `k` must give the published `r`. Signing each vector's `(d, k)` over a
real message and having Graviola verify that closes the loop over the same
key material — `r` is the vector's, since `r` depends only on `k`, while `s`
is this message's. **`m` and `s` are the two published fields Graviola cannot
be made to check**, and no vector was altered to make anything pass.

## OpenSSL and BoringSSL, the production opponents

`--features production` adds OpenSSL 3.0.13, the system `libcrypto.so.3`,
and BoringSSL, the static `libcrypto.a` of the checkout at
`../bench_refs/boringssl` (commit `956bac6e4db9`), as two more
opponents. `src/ossl.rs` and `src/bssl.rs` are the bridges, `tests/production.rs`
the interop suite; the benchmark gains an OpenSSL and a BoringSSL column. Off
by default: without the feature the crate builds and tests exactly as before
(80 tests without `s2n`, 94 with it). AWS-LC and SymCrypt, a third and a
fourth production opponent behind the same feature, have their own sections
below.

### Linkage

The two libraries export the same C names — 1 667 of the 3 394 global
symbols BoringSSL's archive defines are also defined by `libcrypto.so.3`,
`ECDSA_do_sign`, `EC_KEY_new_by_curve_name` and `BN_bin2bn` among them — so only one
of them can be linked by name into a binary. `build.rs` links BoringSSL's
archive statically (`static:-bundle`, search directory ahead of the system
one, which holds OpenSSL's own `libcrypto.a`); `src/ossl.rs` opens OpenSSL's
shared library with `dlopen(RTLD_NOW | RTLD_LOCAL | RTLD_DEEPBIND)` and takes
each function from that handle with `dlsym`. On the resulting test binary,
`ldd` lists no `libcrypto`, `nm` shows `bn_mul_mont_nohw`, `ECDSA_do_verify`
and `ECDSA_sign_with_nonce_and_leak_private_key_for_testing` as local text
symbols, and `nm -D` exports none of the libraries' names; at run time
`OpenSSL_version_num()` through the handle reports `0x300000d0`, which
BoringSSL's own `OpenSSL_version_num` does not return. Neither library is
built or modified here, and no C source is compiled: the bridges are
`extern "C"` declarations. No registry crate was added.

The BoringSSL build under `build-ct/` is `CMAKE_BUILD_TYPE=Release`
(`-O3 -DNDEBUG`), GCC 13, assembly enabled, not FIPS, and without
`CONSTANT_TIME_VALIDATION` (none of those options appears in its
`boringssl-build-ct:CMakeCache.txt`). OpenSSL is Ubuntu's `3.0.13-0ubuntu3.15` build.

### Their P-384 arithmetic

Neither library has P-384-specific arithmetic. Both run the generic
Montgomery EC method over a generic word-serial Montgomery multiply in
perlasm, which at six limbs takes the plain `MUL` loop and no MULX/ADX path.

**OpenSSL 3.0.13.** The source is not on this machine at that version (the
checkout in `bench_refs/openssl` is master, 4.1.0-dev, which has
`openssl:crypto/ec/ecp_nistp384.c`); the files below were read from the `openssl-3.0.13` tag
on GitHub.

| layer | 3.0.13 source |
|---|---|
| method | `openssl-3.0.13:crypto/ec/ec_curve.c`: the `NID_secp384r1` entry carries a method only under `S390X_EC_ASM`, so `ec_group_new_from_data` calls `EC_GROUP_new_curve_GFp`; `openssl-3.0.13:crypto/ec/ec_cvt.c` returns `EC_GFp_mont_method()` whenever `OPENSSL_BN_ASM_MONT` is defined. `openssl-3.0.13:crypto/ec/ecp_nistp384.c` does not exist in 3.0. The system library exports `EC_GFp_nistp224_method`, `_nistp256_` and `_nistp521_` and no P-384 method |
| field multiply | `ossl_ec_GFp_mont_field_mul` → `BN_mod_mul_montgomery` → `bn_mul_mont_fixed_top` (`openssl-3.0.13:crypto/bn/bn_mont.c`) → `bn_mul_mont` (`openssl-3.0.13:crypto/bn/asm/x86_64-mont.pl`), whose entry sends a limb count with `num & 3 != 0` to `.Lmul_enter`, the generic loop; `bn_mulx4x_mont` needs a multiple of four limbs, at least eight |
| points | `BIGNUM` Jacobian, `ossl_ec_GFp_simple_add` / `_dbl` (`openssl-3.0.13:crypto/ec/ecp_smpl.c`) |
| `k*G` in signing | `ossl_ec_scalar_mul_ladder` (`openssl-3.0.13:crypto/ec/ec_mult.c`), Montgomery ladder with coordinate blinding, no precomputed table |
| `u1*G + u2*Q` | `ossl_ec_wNAF_mul`, interleaved wNAF, window 4 at 384 bits (`EC_window_bits_for_scalar_size`) |
| scalar inverse | `ec_field_inverse_mod_ord` (`openssl-3.0.13:crypto/ec/ec_lib.c`): Fermat, `BN_mod_exp_mont` to `n - 2` |
| P-256, for contrast | `ecp_nistz256` x86-64 assembly (`ecp_nistz256-x86_64.pl`) |

**BoringSSL `956bac6e4db9`.**

| layer | source |
|---|---|
| method | `crypto/fipsmodule/ec/ec.cc.inc`, `EC_group_p384`: `out->meth = EC_GFp_mont_method()` |
| field multiply | `ec_felem_mul` (`felem.cc.inc`) → `bn_mod_mul_montgomery_small` → `bn_mul_mont_words` (`bn/montgomery.cc.inc`), which at six limbs fails `bn_mulx4x_mont_capable` and `bn_mul4x_mont_capable` (both need `num >= 8 && num % 4 == 0`) and calls `bn_mul_mont_nohw`, the generic loop of `bn/asm/x86_64-mont.pl` |
| points | C Jacobian formulas, `ec_GFp_mont_add` / `_dbl` (`ec_montgomery.cc.inc`) |
| `k*G` in signing | `ec_GFp_mont_mul_base` = `ec_GFp_mont_mul` on the generator (`simple_mul.cc.inc`): 5-bit fixed window, a 32-entry table built per call, constant-time select |
| `u1*G + u2*Q` | `ec_GFp_mont_mul_public_batch` (`wnaf.cc.inc`), interleaved wNAF, `EC_WNAF_WINDOW_BITS 4` |
| scalar inverse | `ec_simple_scalar_inv0_montgomery` → `bn_mod_inverse0_prime_mont_small` (`bn/exponentiation.cc.inc`): Fermat |

**BoringSSL's P-384 field is not fiat-crypto.** `third_party/fiat` at this
commit carries `boringssl:third_party/fiat/p256_64.h`, `p256_field_64.br.c.inc` and the Curve25519
files and nothing for P-384; the P-384 group is the generic Montgomery
method above. So neither production library is the same field as the
`aucurves` pure-Rust configuration.

### Tiering

| our configuration | against OpenSSL and BoringSSL | why |
|---|---|---|
| `aucurves`, fiat-crypto field, pure Rust | not same tier, against us | Rust field against an assembly Montgomery loop |
| `aucurves`, CryptOpt assembly field | same tier on the field (assembly against assembly), with a P-384-specialised multiply on our side and a generic one on theirs | group law ours (Rust) against theirs (C) |
| `s2n` | not same tier, in our favour | s2n-bignum's P-384-specialised MULX/ADX field and assembly point operations against a generic `MUL` loop under C |

### Signing fairness

| side | input | nonce | what is timed |
|---|---|---|---|
| our kernel | digest, `k` | supplied | the arithmetic, `(r, s)` written as bytes |
| BoringSSL, table column | digest, `k` | supplied | `ECDSA_sign_with_nonce_and_leak_private_key_for_testing`, then `ECDSA_SIG_get0` and `BN_bn2bin_padded` twice, `ECDSA_SIG_free` |
| OpenSSL, table column | digest, `k` | supplied, by reconstruction | `EC_POINT_mul(k*G)`, `EC_POINT_get_affine_coordinates`, `BN_nnmod`, `BN_mod_exp_mont(k, n-2)`, `ECDSA_do_sign_ex(kinv, r)`, extraction as for BoringSSL |
| BoringSSL, full-API row | digest | derived | `ECDSA_do_sign` |
| OpenSSL, full-API row | digest | derived | `ECDSA_do_sign` |

BoringSSL's nonce-supplied entry point is exported in this version
(`boringssl:include/openssl/ecdsa.h`, defined in `crypto/ecdsa/ecdsa_asn1.cc`) and
reaches the same `ecdsa_sign_impl` as `ECDSA_do_sign`; what it skips is
`ecdsa_sign_fixed`'s SHA-512 of the private key and digest and its
rejection-sampled DRBG draw. The self-test hook `ecdsa_sign_fixed` calls is
an inline no-op outside FIPS builds (`boringssl:crypto/internal.h`). That column is
like for like.

OpenSSL's `ECDSA_do_sign_ex` exists in 3.0.13, but with `kinv` and `r` given
`ossl_ecdsa_simple_sign_sig` (`openssl-3.0.13:crypto/ec/ecdsa_ossl.c`) skips
`ecdsa_sign_setup`, so it computes only `s = kinv (e + d r)` and timing it
alone would drop `k*G` and the inverse. The OpenSSL column therefore
rebuilds the rest of `ecdsa_sign_setup` from exported functions with the same
arguments the source passes — the scalar-only `EC_POINT_mul` that routes to
the ladder, `BN_nnmod`, and `BN_mod_exp_mont` with the group's own order and
`EC_GROUP_get_mont_data` — before calling `ECDSA_do_sign_ex`. It is a
reconstruction of the production sequence, not the production entry point:
it allocates its own `BN_CTX` where the source shares one. Interop check 3
below shows it produces the kernel's signature, and the full-API row bounds
it from the other side.

The nonce derivation each full API adds is timed on its own: OpenSSL's
`BN_generate_dsa_nonce`, called directly (two rounds of a 64-byte private-RNG
draw hashed with SHA-512, `openssl-3.0.13:crypto/bn/bn_rand.c`), and BoringSSL's pair
rebuilt from `SHA512` over the same 96 bytes and `BN_rand_range_ex(k, 1, n)`,
which runs the same `bn_rand_range_words` DRBG loop with zero additional
data. Neither is isolated inside the library's own call.

Verification needs no caveat: both columns are `ECDSA_do_verify` on the
digest and a pre-built `ECDSA_SIG`.

### Interop

`tests/production.rs`, ten of its twenty-three tests (six are AWS-LC's and
seven SymCrypt's, below), all passing on both leaf backends in both
AUCurves field configurations (`P384_NO_CRYPTOPT=1` and not). The
marshalling: our scalars are little-endian limbs, the libraries take
big-endian 48-byte strings (`rc::be_from_limbs`), a public key is set with
`EC_KEY_set_public_key_affine_coordinates`, and a signature is an
`ECDSA_SIG` built with `ECDSA_SIG_set0`.

| check | BoringSSL | OpenSSL |
|---|---|---|
| our kernel's signature verifies under `ECDSA_do_verify` (per backend) | 32/32, 32/32 flipped-bit rejected | 32/32, 32/32 flipped-bit rejected |
| the library's `ECDSA_do_sign` verifies under `p384_ecdsa_verify` with `ok = 1` (per backend) | 32/32, 32/32 `s + 1` rejected | 32/32, 32/32 `s + 1` rejected |
| nonce-supplied `(r, s)` byte-identical to the kernel's (per backend) | 32/32 | 32/32 |
| CAVP `(d, Q, k, m)` reproduces the published `(r, s)` | 15/15 | 15/15 |
| the published `(m, r, s)` verifies under the published `Q` | 15/15, 15/15 flipped-bit rejected | 15/15, 15/15 flipped-bit rejected |
| loaded library is 3.0.x | — | `OpenSSL 3.0.13 30 Jan 2024`, `0x300000d0` |
| `BN_generate_dsa_nonce` output below `n` | — | 16/16 |

Unlike Graviola, both libraries accept a prehashed digest and a supplied
nonce, so every published field of the CAVP vectors, `m` and `s` included,
is checked through both. No failure occurred and no vector was altered.

## AWS-LC, the third production opponent

`--features production` also brings in AWS-LC 5.9.0, the shared
`libcrypto.so` of the build tree `../bench_refs/aws-lc-build`, built
from the checkout `../bench_refs/aws-lc` at `f3798b6fe6a8`.
`src/awslc.rs` is the bridge. The library is loaded at run time, not at
build time, so the build does not need it: `awslc::available()` reports
whether it loaded, and each AWS-LC test prints a `SKIP:` line and passes
when it did not. `P384_AWSLC_LIBCRYPTO` overrides the path.

### Linkage of AWS-LC

AWS-LC is a BoringSSL fork and exports the same C names: of its 3 046
dynamic symbols, 2 223 are also defined by the BoringSSL archive linked here
and 2 113 by the system OpenSSL. `src/awslc.rs` therefore opens it as
`src/ossl.rs` opens OpenSSL, `dlopen(RTLD_NOW | RTLD_LOCAL | RTLD_DEEPBIND)`
by absolute path, and takes each function from that handle with `dlsym`;
`ldd` of the benchmark binary lists no `libcrypto`, and the library itself
depends only on `libc`. Its `OpenSSL_version(OPENSSL_VERSION)` reports
`AWS-LC 5.9.0` and `awslc_api_version_num()` 37, which neither of the other
two libraries exports.

The build is `CMAKE_BUILD_TYPE=Release` (`-O3 -DNDEBUG`), GCC 13.3.0,
assembly enabled, `BUILD_SHARED_LIBS=ON`; the `FIPS` option is not set in
its `aws-lc-build:CMakeCache.txt`, so `BORINGSSL_FIPS` is undefined and the lazy
self-test hooks are no-ops (`aws-lc:crypto/internal.h:1257`).

### Its P-384 arithmetic

Unlike BoringSSL and OpenSSL, AWS-LC has a dedicated P-384 method, and its
field is s2n-bignum assembly, the arithmetic of our `s2n` backend and of
Graviola. File:line references are to the checkout above. A file name given
without its full directory is in the `ec`, `ecdsa` or `bn` subdirectory of
`aws-lc:crypto/fipsmodule`.

| layer | source |
|---|---|
| method | `aws-lc:crypto/fipsmodule/ec/ec.c:129-146`, `EC_group_p384`: `out->meth = EC_GFp_nistp384_method()` unless `OPENSSL_SMALL` |
| field selection | `aws-lc:crypto/fipsmodule/ec/ec_nistp.h:20-25` defines `EC_NISTP_USE_S2N_BIGNUM` when `OPENSSL_NO_ASM` is unset, the OS is Linux or Apple, and on x86-64 `MY_ASSEMBLER_IS_TOO_OLD_FOR_ADX_AVX2` is unset (it is `OFF` in `aws-lc-build:CMakeCache.txt`) |
| field multiply, square | `aws-lc:crypto/fipsmodule/ec/p384.c:45-55` and `:288-302` map them to `bignum_montmul_p384_selector` / `bignum_montsqr_p384_selector`; `aws-lc:third_party/s2n-bignum/s2n-bignum_aws-lc.h:88-90` and `:112-120` call `bignum_montmul_p384` / `bignum_montsqr_p384` (MULX/ADX) when the CPU has BMI2 and ADX, and the `_alt` variants otherwise. The Ryzen 7840U has both, so the non-`_alt` routines run (inferred from the selector and `/proc/cpuinfo`, not traced) |
| point double | `aws-lc:p384.c:259`, `p384_montjdouble_selector`, s2n-bignum assembly |
| point add | `aws-lc:p384.c:275-284`, `ec_nistp_point_add` in C (`aws-lc:ec_nistp.c`) over the s2n-bignum field calls |
| variable-base multiply (ECDH) | `aws-lc:p384.c:464-484`: `p384_montjscalarmul_selector` (`:475`), s2n-bignum's `p384_montjscalarmul`, the routine of the same name that our "montjscalarmul on G" micro-benchmark calls from the vendored archive (the two s2n-bignum copies were not compared) |
| `k*G` in signing | `aws-lc:p384.c:491`, `ec_nistp_scalar_mul_base` (`aws-lc:ec_nistp.c:507-565`): a comb over the precomputed `p384_g_pre_comp` table with regular-wNAF digits, window 5 (`aws-lc:ec_nistp.c:308`) |
| `u1*G + u2*Q` in verification | `aws-lc:p384.c:513`, `ec_nistp_scalar_mul_public` (`aws-lc:ec_nistp.c:647-699`): textbook wNAF, `w = 5` for both scalars, the first sub-table of the precomputed table for `G` |
| scalar inverse | `aws-lc:crypto/fipsmodule/ec/scalar.c:128-133`, `bn_mod_inverse0_prime_mont_small` (`aws-lc:bn/exponentiation.c:756-762`): Fermat; the verifier's `ec_scalar_to_montgomery_inv_vartime` (`aws-lc:scalar.c:135`) uses the same routine |
| scalar multiply mod `n` | `bn_mod_mul_montgomery_small` (`aws-lc:bn/montgomery.c:491-506`) → `bn_mul_mont` (`:523-540`), which at six limbs fails `bn_mulx4x_mont_capable` and `bn_mul4x_mont_capable` (`aws-lc:bn/internal.h:305-313`, both need `num >= 8 && num % 4 == 0`) and calls `bn_mul_mont_nohw` |
| sign | `aws-lc:crypto/fipsmodule/ecdsa/ecdsa.c:157-221`, `ecdsa_sign_impl`; `ECDSA_sign_with_nonce_and_leak_private_key_for_testing` (`:251-258`) and `ECDSA_do_sign` (`:260-326`) both reach it |
| verify | `aws-lc:ecdsa.c:103-148`, `ec_point_mul_scalar_public` at `:137` |
| ECDH | `aws-lc:crypto/ecdh_extra/ecdh_extra.c:26-34` → `ECDH_compute_shared_secret` (`aws-lc:crypto/fipsmodule/ecdh/ecdh.c:28`), which copies the peer point into a fresh `EC_KEY` and runs `EC_KEY_check_fips` on it (`:58`) on every call, then `ec_point_mul_scalar` (`:64`) |

`nm` on the library lists `bignum_montmul_p384`, `bignum_montmul_p384_alt`,
`bignum_montinv_p384`, the `p384_montjscalarmul` loops and the
`ec_GFp_nistp384_*` functions as local text symbols, which agrees with the
`EC_NISTP_USE_S2N_BIGNUM` configuration. That the `p384_montjscalarmul`
and non-`_alt` field routines are the ones executed at run time is inferred
from the source and the CPU flags; it was not traced.

### Tiering

| our configuration | against AWS-LC | why |
|---|---|---|
| `aucurves`, fiat-crypto field, pure Rust | not same tier, against us | Rust field against s2n-bignum assembly |
| `aucurves`, CryptOpt assembly field | not same tier, against us | assembly field on both sides, but AWS-LC's point double and variable-base multiply are assembly as well, where our group law is Rust |
| `s2n` | **same tier** | the same s2n-bignum field routines on both sides; the difference is orchestration (our emitted sequence and our comb and interleaved pass in Rust against AWS-LC's C comb and wNAF) and AWS-LC's generic scalar arithmetic mod `n` |

### Signing fairness

AWS-LC is driven as BoringSSL is: the table column is
`ECDSA_sign_with_nonce_and_leak_private_key_for_testing`, which reaches
the production `ecdsa_sign_impl` with the kernel's nonce, then
`ECDSA_SIG_get0` and `BN_bn2bin_padded` twice and `ECDSA_SIG_free`; the
full-API row is `ECDSA_do_sign`. `ECDSA_do_sign` has BoringSSL's structure
(SHA-512 of the private key and digest as additional data, then
`ec_random_nonzero_scalar`), and its nonce-derivation arm is the same
rebuilt pair, `SHA512` and `BN_rand_range_ex(k, 1, n)`. Verification is
`ECDSA_do_verify` on a pre-built `ECDSA_SIG`. Setting the public key of a
signing key runs AWS-LC's pairwise consistency check (`ec_key_gen_pct`,
`aws-lc:crypto/fipsmodule/ec/ec_key.c:247`), which is key setup and not timed.

### Interop

`tests/production.rs`, six tests for AWS-LC: the four of the shared suite
(the same macro as for BoringSSL and OpenSSL), `awslc_is_aws_lc`, and
`awslc_nonce_parts_run`. All pass on both leaf backends with
`P384_NO_CRYPTOPT=1`; with `P384_AWSLC_LIBCRYPTO` pointing at a missing file
all six print `SKIP:` and pass.

| check | AWS-LC |
|---|---|
| our kernel's signature verifies under `ECDSA_do_verify` (per backend) | 32/32, 32/32 flipped-bit rejected |
| the library's `ECDSA_do_sign` verifies under `p384_ecdsa_verify` with `ok = 1` (per backend) | 32/32, 32/32 `s + 1` rejected |
| nonce-supplied `(r, s)` byte-identical to the kernel's (per backend) | 32/32 |
| CAVP `(d, Q, k, m)` reproduces the published `(r, s)` | 15/15 |
| the published `(m, r, s)` verifies under the published `Q` | 15/15, 15/15 flipped-bit rejected |
| loaded library | `AWS-LC 5.9.0`, `OpenSSL_version_num` `0x1010107f`, `awslc_api_version_num` 37 |
| nonce-derivation arm runs | 16/16 |

No ECDSA divergence was found. The DHKEM reconstruction has one; see
[§ Divergences of the opponents from RFC 9180](#divergences-of-the-opponents-from-rfc-9180).

## SymCrypt, the fourth production opponent

`--features production` also brings in Microsoft SymCrypt 103.13.0 (commit
`286762b`, MIT licence), the shared module `libsymcrypt.so.103` built in the
checkout `../bench_refs/symcrypt` with the CMake preset
`Linux_AMD64_GCC_Release`. `src/symcrypt.rs` is the bridge. As for AWS-LC,
the module is loaded at run time: `symcrypt::available()` reports whether it
loaded and accepted the API version, and each SymCrypt test prints a `SKIP:`
line and passes when it did not. `P384_SYMCRYPT_LIB` overrides the path.
File:line references in this section are to that checkout.

### Linkage of SymCrypt

SymCrypt's exported names carry the prefix `SymCrypt` and collide with
neither OpenSSL nor BoringSSL. The module is opened as the other run-time
libraries are, `dlopen(RTLD_NOW | RTLD_LOCAL | RTLD_DEEPBIND)` by absolute
path, with every function taken from the handle with `dlsym`, so the build
needs no SymCrypt file. The module exports 709 dynamic symbols and has no
`DT_NEEDED` entry; its undefined references (`malloc`, `getentropy`, the
`pthread_mutex_*` functions and a few others) resolve against the process.
Two exports are `const` pointer variables, `SymCryptEcurveParamsNistP384`
and `SymCryptHmacSha384Algorithm`; the bridge dereferences the address
`dlsym` returns.

The module's ELF constructor `SymCryptModuleMain`
(`symcrypt:modules/posix/common/module.c:12-71`) calls `SymCryptInit` and
`SymCryptRngInit`, and `SymCryptInit` is documented as unnecessary for the
shared object (`symcrypt:inc/symcrypt.h:505-510`). The bridge calls
`SymCryptModuleInitEx(103, 13)` (`symcrypt:modules/posix/common/module.c:79-87`),
the non-fatal form behind `SYMCRYPT_MODULE_INIT_EX()`, and treats a refusal
as absence. The module exports no version string; `symcrypt_is_103_13`
shows that it accepts 103.13 and refuses 103.14 and 104.0, so its version is
103.13.

The build is `CMAKE_BUILD_TYPE=RelWithDebInfo`, which is what the preset named
`Release` sets (`symcrypt:CMakePresets.json:69-78`; `-O2 -g -DNDEBUG`), GCC
13.3.0, `SYMCRYPT_USE_ASM=ON`, `SYMCRYPT_FIPS_BUILD=OFF`, stripped, with the
debug information in `module/generic/.debug/`.
`SYMCRYPT_MODULE_DO_FIPS_SELFTESTS` is 0
(`symcrypt:modules/symcrypt_modules_common.h:10-12`), so the constructor
runs no self-test. Importing a key without `SYMCRYPT_FLAG_KEY_NO_FIPS` runs
the ECDSA or ECDH self-test once per process
(`symcrypt:lib/eckey.c:547-566`); the benchmark imports its keys before any
timed call.

### SymCrypt's P-384 arithmetic

SymCrypt has its own P-384 field multiply in MULX assembly, with a
Montgomery reduction specialised to the form of `p`. Everything above the
field is generic C: Jacobian formulas, a fixed-window multiply without a
comb, and a group order handled by the generic multiply-then-divide table.

| layer | source |
|---|---|
| curve object | `SymCryptEcurveAllocate(SymCryptEcurveParamsNistP384, 0)`, once per process in the bridge; `a = -3` selects the type `SHORT_WEIERSTRASS_AM3` (`symcrypt:lib/ecurve.c:325-340`), whose dispatch entry is `symcrypt:lib/ec_dispatch.c:77-92` |
| field modulus type | built with `SYMCRYPT_FLAG_DATA_PUBLIC` and `100 * 384` expected operations (`symcrypt:lib/ecurve.c:13`, `:284-290`); `SymCryptFdefDecideModulusType` sets the Montgomery and NIST P-384 features (`symcrypt:lib/fdef_mod.c:300-319`), and the first selection entry (`symcrypt:lib/a_dispatch.c:81`) takes the `MULXP384` table when the CPU has BMI2 and ADX (`symcrypt:lib/sc_lib.h:314`) |
| field multiply, square | `SymCryptFdefModMulMontgomeryMulxP384Asm`, `SymCryptFdefModSquareMontgomeryMulxP384Asm` (`symcrypt:lib/sc_lib.h:2211-2222`, `symcrypt:lib/amd64/fdef_mulx.symcryptasm:1400-1693`): MULX/ADCX/ADOX products interleaved with Montgomery steps whose reduction uses `p = 2^384 - 2^128 - 2^96 + 2^32 - 1` (the comment at `:1452-1497`); the square enters the multiply (`:1687`) |
| field inverse | `SymCryptFdef369ModInvMontgomery` (`symcrypt:lib/fdef369_mod.c:201-231`) → `SymCryptFdefModInvGeneric` (`symcrypt:lib/fdef_mod.c:986`), a binary extended GCD on the input times a random factor (`:1075-1082`) unless the caller marks it public |
| group-order modulus type | built with 1 expected operation (`symcrypt:lib/ecurve.c:14`, `:399-405`), below the Montgomery threshold of 10 (`symcrypt:lib/fdef_mod.c:300-303`), so the last, generic selection entry (`symcrypt:lib/a_dispatch.c:101`, table `symcrypt:lib/sc_lib.h:2120-2131`) |
| scalar multiply mod `n` | `SymCryptFdefModMulGeneric` (`symcrypt:lib/fdef_mod.c:935-957`): `SymCryptFdefRawMul`, which calls `SymCryptFdefRawMulMulx` when the CPU has MULX (`symcrypt:lib/fdef_int.c:781-783`), then `SymCryptFdefRawDivMod` |
| scalar inverse | `SymCryptFdefModInvGeneric`, the same blinded binary GCD: signing passes the flag 0 for `k` (`symcrypt:lib/ec_dsa.c:311`), so `k` is blinded with a second RNG draw; verification marks `s` public (`:612`) |
| points | Jacobian C formulas, `SymCryptShortWeierstrassAdd` (`symcrypt:lib/ec_short_weierstrass.c:843`), `SymCryptShortWeierstrassDoubleSpecializedAm3` (`:499`) |
| `k*G` in signing and key import | `SymCryptEcpointScalarMulFixedWindow` (`symcrypt:lib/ec_mul.c:90-331`): signed fixed window, `w = 6` (`symcrypt:inc/symcrypt_internal.h:2926`, `symcrypt:lib/ecurve.c:446-447`), over the 16 odd multiples of `G` computed once at curve allocation (`symcrypt:lib/ecurve.c:481-499`), selected by masked copy; about 380 doublings per multiply |
| `k*P` in ECDH | the same routine, with the 16 odd multiples of `P` computed on each call |
| `u1*G + u2*Q` | `SymCryptEcpointMultiScalarMulWnafWithInterleaving` (`symcrypt:lib/ec_mul.c:339`), interleaved wNAF, `w = 6` |
| sign | `SymCryptEcDsaSign` (`symcrypt:lib/ec_dsa.c:408-436`) → `SymCryptEcDsaSignEx` with no nonce (`:146-403`): `SymCryptEcpointSetRandom` draws `k` in `[1, n - 1]` and computes `k*G` (`:286-290`, `symcrypt:lib/ec_mul.c:546-570`); one heap allocation of scratch space per call (`symcrypt:lib/ec_dsa.c:233`) |
| verify | `SymCryptEcDsaVerify` (`symcrypt:lib/ec_dsa.c:440-694`) |
| ECDH | `SymCryptEcDhSecretAgreement` (`symcrypt:lib/ec_dh.c:12-157`): checks that the peer point is not the identity, multiplies (`:115`), checks the result, returns `x`; the curve check is done at key import |
| key import | `SymCryptEckeySetValue` (`symcrypt:lib/eckey.c:261-577`): private key below `n` and non-zero (`:370-378`, `:440-444`), coordinates below `p` (`symcrypt:lib/ecpoint.c:645-660`), point on the curve (`symcrypt:lib/eckey.c:209-215`); with a private key and no public key, computes `d*G`; with both and without `SYMCRYPT_FLAG_KEY_NO_FIPS`, recomputes `d*G` and compares (`:486-529`) |
| RNG | `SymCryptRandom` (`symcrypt:modules/posix/common/rng.c`): AES-CTR DRBG behind a mutex, requests under 128 bytes served from a cache (`:176`) |

**Which routines run, traced.** The module is stripped, but its debug
file carries the build ID. With that file reachable through a build-ID
directory, gdb counted the calls of one test,
`symcrypt_suite::full_api_nonce_is_fresh` (one pairwise key import, two
signatures, two verifications, and the ECDSA self-test the first import
triggers):

| routine | calls |
|---|---|
| `SymCryptFdefModMulMontgomeryMulxP384Asm` | 17 397 |
| `SymCryptFdefModSquareMontgomeryMulxP384Asm` | 6 082 |
| `SymCryptFdefModMulMontgomeryMulx`, `SymCryptFdef369ModMulMontgomery`, `SymCryptFdefModMulMontgomery` | 0 |
| `SymCryptFdefModMulGeneric` | 22 |
| `SymCryptFdefRawMulMulx` | 22 |
| `SymCryptFdefModSquareGeneric` | 0 |
| `SymCryptEcpointScalarMulFixedWindow` | 4 |
| `SymCryptEcpointMultiScalarMulWnafWithInterleaving` | 3 |
| `SymCryptEcpointGenericSetRandom` | 2 |
| `SymCryptFdefModInvGeneric` | 12 |

So on this CPU the field is the P-384 MULX routine and the group order the
generic multiply-and-divide over `SymCryptFdefRawMulMulx`, as the source
predicts. The split of the four fixed-window calls (import, two signatures,
self-test) is read from the source, not traced. The reproduction, with
`$S` a scratch directory:

    mkdir -p $S/dbg/.build-id/d7
    ln -s "$PWD"/../../../bench_refs/symcrypt/build/cmake/Linux_AMD64_GCC_Release/module/generic/.debug/libsymcrypt.so.103.13.0 \
      $S/dbg/.build-id/d7/fcb5a95c00644e79cc8a8fedc07ce411d835ce.debug
    # a gdb script: set debug-file-directory $S/dbg; one `break` per routine,
    # each with `commands silent continue end`; run; info breakpoints
    gdb -batch -x count.gdb --args target/release/deps/production-<hash> \
      --exact symcrypt_suite::full_api_nonce_is_fresh --test-threads=1

### Tiering against SymCrypt

| our configuration | against SymCrypt | why |
|---|---|---|
| `aucurves`, fiat-crypto field, pure Rust | not same tier, against us | Rust field against a MULX assembly field |
| `aucurves`, encoded s2n-bignum montmul | same tier on the field multiply | a P-384 Montgomery multiply in assembly on both sides (ours: s2n-bignum's `bignum_montmul_p384`, bytes Lean-proved; theirs: `MulxP384Asm`); our square is a multiply, theirs a dedicated entry; group law Rust against C |
| `aucurves`, CryptOpt assembly field | same tier on the field | not measured against SymCrypt |
| `s2n` | not same tier, in our favour above the field | both fields are P-384-specialised MULX assembly; our point double and add are s2n-bignum assembly, SymCrypt's are C |

Our scalar arithmetic mod `n` (fiat-crypto Montgomery, divstep inverse)
differs from SymCrypt's (a product and a division per multiply, a blinded
binary GCD) on every row.

### Signing fairness with SymCrypt

`SymCryptEcDsaSignEx`, which accepts a nonce, is defined
(`symcrypt:lib/ec_dsa.c:146`) and exported by the static
`libsymcrypt_common.a`, but it is not in the shared module's export list
(`symcrypt:modules/posix/common/exports.ver`), and `nm -D` does not list it.
No other exported function takes `k`. Linking the static library instead
would be a different build of SymCrypt and was not done. So:

| side | input | nonce | what is timed |
|---|---|---|---|
| our kernel | digest, `k` | supplied | the arithmetic |
| SymCrypt, table column | digest | drawn by SymCrypt | `SymCryptEcDsaSign`, `r \|\| s` copied into two arrays |
| SymCrypt, full-API table | digest | drawn by SymCrypt | the same call, a second arm |
| SymCrypt, derivation row | — | — | one `SymCryptRandom` call for 48 bytes |

The `vs SC` sign ratio is therefore not like for like. SymCrypt's nonce
derivation is `SymCryptModSetRandom`: one 48-byte draw, a comparison with
`n - 1` and, rarely, a retry (`symcrypt:lib/fdef_mod.c:784-803`). The
derivation row times the draw alone, and "full API minus nonce derivation"
is an estimate of SymCrypt's nonce-supplied cost. The second 48-byte draw,
the blinding factor of the `k` inversion, stays in that estimate, because
`SymCryptEcDsaSignEx` with a supplied `k` draws it too. The signing key is
imported as the pair `(d, Q)` with the default validation, which recomputes
`d*G` at import, outside the timed arm. Verification is `SymCryptEcDsaVerify`
on the digest and a pre-built 96-byte `r || s`.

### Interop with SymCrypt

`tests/production.rs`, seven tests for SymCrypt: checks 1 and 2 of the shared
suite (the same macro as for the other three libraries), a CAVP test without
the signing half, and four SymCrypt-only tests. All pass on both leaf
backends with `P384_NO_CRYPTOPT=1`; with `P384_SYMCRYPT_LIB` naming a
missing file all seven print `SKIP:` and pass.

| check | SymCrypt |
|---|---|
| our kernel's signature verifies under `SymCryptEcDsaVerify` (per backend) | 32/32, 32/32 flipped-bit rejected |
| `SymCryptEcDsaSign`'s signature verifies under `p384_ecdsa_verify` with `ok = 1` (per backend) | 32/32, 32/32 `s + 1` rejected |
| nonce-supplied `(r, s)` byte-identical to the kernel's | not possible, no exported entry point |
| CAVP `(d, Q)` passes the pairwise import check; the published `(m, r, s)` verifies under `Q` | 15/15, 15/15, 15/15 flipped-bit rejected |
| CAVP: SymCrypt's own signature of `m` verifies under SymCrypt and under the kernel (both backends) | 15/15 |
| two signatures of one digest differ in `r` and both verify | yes |
| key import rejects an off-curve point, `x = p`, `y = p`, a mismatched pair, `d = 0`, `d = n` | 6/6 |
| module version | `SymCryptModuleInitEx` accepts 103.13, refuses 103.14 and 104.0 |
| RNG arm returns distinct outputs | 16/16 |

No ECDSA divergence was found. The CAVP check covers `d`, `Q`, `m`, `r` and
`s` on the verification side; `k` and the published signature cannot be
checked on the signing side. The DHKEM reconstruction rejects every invalid
input the kernels reject;
[§ Divergences of the opponents from RFC 9180](#divergences-of-the-opponents-from-rfc-9180)
records what SymCrypt accepts under its validation opt-out.

## Paths

The three path dependencies are relative and assume the AUCurves checkout is
at `../BLS/AUCurves`, the layout the sibling bench directories already
use:

    p384        -> ../../../BLS/AUCurves/p384-safe-rust   (features = ["extracted"])
    fiat-crypto -> ../../../BLS/AUCurves/fiat-crypto/fiat-rust
    safegcd     -> ../../../BLS/AUCurves/safegcd-rs

`features = ["extracted"]` is needed for `p384::wnaf::{point_to_bytes,
point_from_bytes}`, which fix the 144-byte point encoding. RustCrypto's
`p384` is imported under the name `p384_rc` because the path dependency already occupies
the name.

Further paths are read, never written, and are not cargo dependencies:

    s2n-bignum   -> $S2N_BIGNUM_DIR/x86/libs2nbignum.a
                    (feature `s2n`; S2N_BIGNUM_DIR is the s2n-bignum checkout,
                     default ../../../SSProve-lean/bench/reference_install/s2n-bignum)
    emitted montmul -> ../p384_compare/gen/p384_montmul_proven.s
    emitted solinas -> ../p384_fieldmul_compare/gen_com/p384_mul_x86_from_lean.s
                    (feature `emit-field`, the `fieldbench` binary only;
                     override with P384_EMIT_MONTMUL_S, P384_EMIT_SOLINAS_S)

    boringssl    -> ../../../bench_refs/boringssl/build-ct/libcrypto.a
                    (feature `production`, linked statically; override the
                     directory with BORINGSSL_LIB_DIR)
    openssl      -> /usr/lib/x86_64-linux-gnu/libcrypto.so.3
                    (feature `production`, opened with dlopen; override with
                     P384_OPENSSL_LIBCRYPTO at build or run time)
    openssl 3.6  -> /opt/microsoft/mdatp/lib/libcrypto.so.3
                    (feature `production`, DHKEM only, opened with dlopen at
                     run time and skipped when absent; override with
                     P384_OPENSSL36_LIBCRYPTO, e.g. with
                     ../../../bench_refs/openssl-install/lib/libcrypto.so.4)
    aws-lc       -> ../../../bench_refs/aws-lc-build/crypto/libcrypto.so
                    (feature `production`, ECDSA and DHKEM, opened with dlopen
                     at run time and skipped when absent; override with
                     P384_AWSLC_LIBCRYPTO)
    symcrypt     -> ../../../bench_refs/symcrypt/build/cmake/Linux_AMD64_GCC_Release/module/libsymcrypt.so.103
                    (feature `production`, ECDSA and DHKEM, opened with dlopen
                     at run time and skipped when absent or not version
                     103.13; override with P384_SYMCRYPT_LIB)

`S2N_BIGNUM_DIR` is the single setting for the s2n-bignum checkout: `build.rs`,
the `Makefile` of this directory (which also derives `S2N_FIELD` from it for
`make bench-dhkem`) and every script in `bench/s2n_import` read it. The default
names the checkout of the sibling SSProve-lean tree, the one s2n-bignum checkout
on the development machine; the build stops with the path it looked for when
`x86/libs2nbignum.a` is absent there. The checkout must be at the commit the
importer pins (`bench/s2n_import/kernels/bignum_montmul_p384.sh`) for
`make import` in `bench/s2n_import`; the archive is built in the checkout with
its own makefile.

The two `.s` files are untracked build output of their Lean emitters.
`build.rs` hands them to the linker of the `fieldbench` binary and never
regenerates them; regenerate them before recording a figure from them. Their
emitters are `emitMainP384` (module
`CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6MontMulProvenEmit`) and
`emitP384` (module `CatCrypt.Crypto.SecureCompilation.X86Backend.P384FieldKernel`),
both in this repository. The drivers that call them are in SSProve-lean and
write relative to the working directory, so run from the root of SSProve-lean (`../SSProve-lean`)
they write under that tree's `bench/`:

    lake env lean bench/sm2_compare/p384_montmul_proven_emit.lean
    lake exe emit-securecompilation3      # includes P384FieldKernel.emitP384

Copy the two files here afterwards, or point `P384_EMIT_MONTMUL_S` and
`P384_EMIT_SOLINAS_S` at them.

Graviola is a pinned registry dependency, `graviola = "=0.4.1"`, and is
declared under `[dependencies]` rather than `[dev-dependencies]` because the
benchmark is a `[[bin]]` target and would not see a dev-dependency. It and
its three transitive dependencies (`cfg-if`, `getrandom`, `libc`) are in this
machine's registry cache, so `--offline` resolves; it compiles in about three
seconds and needs no assembler, since the s2n-bignum routines are inline
assembly in Rust source.

## The ABI

| kind | encoding |
|---|---|
| scalar, digest | `[u8; 48]`, canonical integer in `[0, n)`, little-endian, not Montgomery |
| field element (output of `p384_point_affine_x`) | `[u8; 48]`, canonical integer in `[0, p)`, little-endian |
| point, `aucurves` backend | `[u8; 144]`, **projective** `X \|\| Y \|\| Z`, affine `(X/Z, Y/Z)`, 48 little-endian Montgomery bytes each — `p384::wnaf::point_to_bytes` |
| point, `s2n` backend | `[u8; 144]`, **Jacobian** `X \|\| Y \|\| Z`, affine `(X/Z^2, Y/Z^3)`, 48 little-endian Montgomery bytes each — `s2n::point_to_bytes` |
| flag | `u64`, 1 or 0 |

The scalar, field-element and flag encodings are shared by every backend;
the point encoding is not. See
[§ The Jacobian representation](#the-jacobian-representation).

Leaves take the destination first; the emitted entry points take inputs
first and outputs last, which is `ppRustFunction`'s order.

Published test vectors are big-endian; `codec::limbs_from_be_hex` and
`rc::be_from_limbs` are the conversions.

## The leaves and their constant-time status

Constant time here means the instruction trace and the memory addresses
touched do not depend on input values. It is a claim about the shim and the
function it calls, read off the code; nothing here was measured with a timing
harness.

| leaf | shim for | constant time |
|---|---|---|
| `p384_scalar_mul` | `g1_scalar_mul` (4-bit window, full table scan) | yes |
| `p384_scalar_mul_base` | `g1_scalar_mul_base` (5-bit fixed window, precomputed `G_TABLE`) | yes — each window scans all 31 entries with a limb-mask select |
| `p384_point_add` | `g1_add` (complete RCB `a = -3`) | yes |
| `p384_lincomb` | `crate::lincomb::lincomb`, one interleaved pass over width-5 non-adjacent digits of both scalars | **no** — the pass branches on the digits and indexes both tables by digit |
| `p384_scalar_inv` | `safegcd::safegcd_p384_order`, 15 outer iterations of 59 divsteps | yes — the divstep count is a compile-time constant and every step is a masked select |
| `p384_scalar_muln` | `fiat_p384_scalar_mul` with Montgomery conversions | yes |
| `p384_scalar_addn` | limb add with a mask-selected conditional subtraction | yes |
| `p384_scalar_reduce` | 384 rounds of double-and-add mod `n` | yes |
| `p384_point_affine_x` | `g1_to_affine` (Bernstein-Yang `fp_inv`) then `fiat_p384_from_montgomery` | **no** — `g1_to_affine` branches on `Z = 0` |
| `p384_scalar_is_eq` | byte-wise difference accumulation | yes |
| `p384_scalar_in_range` | `scalar::ct_lt_n` and `scalar::ct_is_zero` | yes |
| `p384_point_valid` | `fp_square` / `fp_mul` / `fp_add` on the projective curve equation | yes |
| `p384_flag_and` | a `u64` bitwise and | yes |

Two leaves are variable time, `p384_point_affine_x` and `p384_lincomb`, and
both run only on public verification data. Whether `R` is the identity is a
public fact about a verification input; `u1 = e * s^-1` and `u2 = r * s^-1`
are computed from the digest and the signature, which the verifier receives
in the clear. Neither leaf is reached by the signing sequence with a secret
argument: `p384_point_affine_x` is applied there to `k*G`, whose identity
status the `ok` flag already reports, and `p384_lincomb` is not in the
signing sequence at all. Secret scalars go through `p384_scalar_mul_base`
and `p384_scalar_mul`, which are constant time.

`p384_scalar_in_range` compares against `n`; it does not reduce, so a value
at or above `n` gives 0, and zero gives 0. `p384_point_valid` evaluates the
homogeneous curve equation `Y^2 Z = X^3 + a X Z^2 + b Z^3` on the decoded
projective coordinates and ands the result with `Z != 0`, which rejects the
identity and every other `Z = 0` encoding. It does not use the affine
`g1_is_on_curve_affine`, because reaching affine coordinates would need the
variable-time `g1_to_affine`; that is also why the check costs nine field
multiplications and squarings and no inversion. It reads the three
coordinates as canonical Montgomery values below `p`, which is what the
point ABI carries and what the fiat field operations require of their
inputs; a 144-byte string with a coordinate limb at or above `p` is outside
its domain.

## The scalar inverse

`p384_scalar_inv` is the Bernstein-Yang divstep inversion of
`safegcd::safegcd_p384_order`, which is `safegcd-rs`'s modulus-generic
`ModInfo<7>` core instantiated at the group order. It is the sibling of
`safegcd-rs:src/safegcd_p384.rs`, the base-field instance behind `fp_inv`: `n` and `p` are
both odd and both 384 bits wide, so both take 7×62-bit signed limbs and the
same 15 outer iterations of 59 divsteps. `ModInfo::outer_iters` requires
`ceil((9437*b + 1) / (4096*59))` for a b-bit modulus under the δ₀=1/2
encoding, which is 15 at `b = 384`, and `modinv_62` requires only that the
bottom limb be odd; `safegcd-rs:src/safegcd_p384_order.rs` asserts both, and its in-crate
KAT checks `x * x^-1 = 1 (mod n)` on the same inputs as the base-field one,
including `n - 1`.

The inverter's domain is `[0, n)`. `n > 2^383`, so any 384-bit value is
below `2n` and the leaf brings one into range with a single masked
conditional subtraction, which is also what keeps
`tests/leaves.rs::scalar_leaves_reduce_out_of_range_inputs` true of it.

The Fermat chain it replaced is still in the crate as `scalar::inv`: 383
squarings and 287 multiplications, left-to-right square-and-multiply over
`n - 2`, whose top bit is set and which has 288 set bits.
`tests/scalar.rs::inv_cost_constants_match_the_exponent` recomputes both
figures from `N_MINUS_2`, and `divstep_inverse_matches_fermat` checks that
the two agree on 200 random scalars and on `0`, `1`, `2`, `n - 2` and
`n - 1`. It is the differential reference for the leaf, and the measured
cost of both is in [PERF.md § The scalar inverse](PERF.md#the-scalar-inverse).

## The two-term multiply

`p384_lincomb` computes `u1*G + u2*Q` in one interleaved left-to-right pass:
the two terms share one accumulator, so the accumulator is doubled once per
bit position rather than once per term per bit position, and each term
contributes an addition only where its own digit is non-zero. The digits are
width-5 non-adjacent form, so a term's table is its eight odd multiples
`1P, 3P, ..., 15P` and a negative digit negates an entry.

A Cartesian joint table `i*G + j*Q` is the other way to index one
interleaved pass. It is not used, because at a window wide enough to matter
its build cost dominates: at 4 bits per window the cross terms alone are 225
additions, against the 14 the two non-adjacent tables cost together.

Field multiplications at 384 bits, counting `g1_double` at 13 and `g1_add`
at 14, and taking the non-adjacent form's mean digit density of `1/(W + 1)`:

| route | doublings | additions | field mul |
|---|---|---|---|
| `p384_scalar_mul_base(u1)`, `p384_scalar_mul(u2, Q)`, `p384_point_add` | 387 | 180 | 7551 |
| `p384_lincomb` | 386 | 142 | 7006 |

The interleaved pass also drops the constant-time table scans the two
multiplication leaves perform — 3827 entries between them, each a
three-coordinate masked select — which is the rest of the difference the
measurement in [PERF.md § The two-term multiply](PERF.md#the-two-term-multiply) shows.

## `gen/` and the fallback

`build.rs` collects every `gen/*.rs`, in sorted order, into one module that
has the leaf shims in scope, and sets `cfg(p384_emitted)`. With no such file
the crate uses the hand-written transcription in
`src/generated.rs::fallback`, which is the same three call sequences written
out by hand. `p384_ecdsa_rust::EMITTED` reports which path a binary took, and
`--features force-fallback` selects the transcription even when `gen/` is
populated, so the two can be compared.

`gen/` is written by `lake exe emit-p384-rust`, run from the root of this
repository (the executable and its module `CatCrypt/EmitArtifacts/P384Rust.lean`
are declared in this repository's `lakefile.lean`). It holds six files: the
ECDSA files `p384_ecdsa_verify.rs`, `p384_ecdsa_sign.rs`,
`p384_ecdsa_verify_msm.rs` and `p384_msm_term.rs`, and the two DHKEM files of
[§ DHKEM](#dhkemp-384-hkdf-sha384). The ECDSA call sequences agree with the
fallback transcription leaf call for leaf call: thirteen for verify, ten for
sign, three for the two-term MSM. Nothing under `gen/` is hand-edited; the
provenance note is `gen/PROVENANCE.md` rather than a README because the
emitter writes into that directory.

## Test vectors

**FIPS 186-4 CAVP, `[P-384,SHA-384]` SigGen, 15 vectors** — in
`src/vectors.rs`. NIST publishes them in `186-4ecdsatestvectors.zip:SigGen.txt` inside
`186-4ecdsatestvectors.zip`; the copy transcribed here is the one in the
RustCrypto `p384` 0.13.1 crate at `p384-0.13.1:src/test_vectors/ecdsa.rs`, which names
that source and whose `m` field is the SHA-384 prehash of the original `Msg`.
That crate is in this machine's cargo registry cache. Nothing was fetched
from the network and no vector was constructed here.

**CAVP SigVer is not on this machine.** No `.rsp` file for ECDSA P-384
verification was found in the sibling checkouts, the cargo home or the AUCurves tree. The
negative-verification corpus used instead is Google Wycheproof's
`wycheproof_testvectors:ecdsa_secp384r1_sha384_p1363_test.txt`, in BoringSSL's converted text form
at `../bench_refs/boringssl/third_party/wycheproof_testvectors`. It is
Wycheproof, not CAVP, and `tests/wycheproof.rs` says so. The vectors are not
vendored into this directory; point `WYCHEPROOF_DIR` at a checkout, and the
test reports a skip when the file is absent.

**The CAVP digests cannot be put through Graviola.** The transcription keeps
the prehash `m` and not the `Msg` it came from, and Graviola's ECDSA API
hashes the message itself with no prehashed alternative. `tests/graviola.rs`
cross-checks what is reachable — `d` against the published public key and `k`
against the published `r`, both through Graviola's base-point multiplication,
plus a fresh signature over each vector's key material — and leaves `m` and
`s` unchecked by that third implementation. They remain checked against
RustCrypto and against `src/reference.rs`.

## Inputs the emitted kernel rejects

The emitted verify checks `r` and `s` against `[1, n)`, validates `Q`, and
ands the three flags with the arithmetic relation; the emitted sign reports
an out-of-range `r` or `s` through `ok`. On the Wycheproof corpus and on
every differential input in `tests/`, the kernel accepts exactly the inputs
RustCrypto accepts.

It carries no explicit identity check on `R = u1*G + u2*Q` and needs none:
the identity gives `x(R) = 0`, which no `r` in `[1, n)` equals.

Four inputs used to separate the emitted verifier from RustCrypto. Each is
now asserted rejected in
`tests/rustcrypto.rs::historical_divergences_are_now_rejected`, together
with the fact that the ECDSA arithmetic relation still holds on it —
`reference::verify_core` is that relation without the checks, and its
holding is what made the old acceptance possible.

| | input | old kernel | now | rejected by |
|---|---|---|---|---|
| D1 | `e = 0`, `r = 0`, `s = 1` | accepted | rejects | `p384_scalar_in_range(r)` |
| D2 | `r = 0`, `s = 0`, any `e` | accepted | rejects | `p384_scalar_in_range` on both |
| D3 | `s` at or above `n`, equal mod `n` to a valid `s` | accepted | rejects | `p384_scalar_in_range(s)` |
| D4 | `Q` = the point at infinity, `s = 1`, `r = x(e*G) mod n` | accepted a forgery made without a private key | rejects | `p384_point_valid(Q)` |

D3 came from the leaves rather than from a missing check: the scalar leaves
take an out-of-range input mod `n`, so `s + n` verified wherever `s` did.
Wycheproof tcId 165 is that case end to end. The leaf behaviour behind it is
unchanged and is still pinned by
`tests/leaves.rs::scalar_leaves_reduce_out_of_range_inputs`; what changed is
that `p384_scalar_in_range` rejects the input before the reduction can
matter. For `r` the reduction never produced an acceptance anyway, because
the final comparison is against a value already reduced mod `n`. The test
builds the D3 signature with a small `s` by solving for the digest,
`e = s*k - r*d mod n`, so that `s + n` still fits in 384 bits and is a legal
48-byte input.

## Commands

Every command below with `--features s2n` needs `S2N_BIGNUM_DIR` to name a
built s2n-bignum checkout, or the default of [§ Paths](#paths) to exist. The
`Makefile` sets and exports the default.

    # every test, every backend, pure-Rust AUCurves field
    P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n -- --nocapture

    # the same with the CryptOpt assembly linked
    cargo test --offline --release --features s2n -- --nocapture

    # the two AUCurves backends alone, as the crate builds without the archive
    P384_NO_CRYPTOPT=1 cargo test --offline --release -- --nocapture

    # the CAVP vectors only
    P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n --test cavp -- --nocapture

    # the Wycheproof corpus only
    WYCHEPROOF_DIR=../../../bench_refs/boringssl/third_party/wycheproof_testvectors \
      P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n --test wycheproof -- --nocapture

    # the Graviola interop suite only
    P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n --test graviola -- --nocapture

    # the OpenSSL, BoringSSL, AWS-LC and SymCrypt interop suite
    P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n,production --test production -- --nocapture

    # the same with AWS-LC or SymCrypt from another build, or absent (their
    # tests then skip)
    P384_AWSLC_LIBCRYPTO=/path/to/libcrypto.so P384_SYMCRYPT_LIB=/path/to/libsymcrypt.so.103 \
      P384_NO_CRYPTOPT=1 \
      cargo test --offline --release --features s2n,production --test production -- --nocapture

    # the s2n backend's own suite: constants, comb, interleaved pass, and the
    # two representation agreement points
    P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n --test s2n -- --nocapture

    # the hand-written transcription instead of gen/
    P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n,force-fallback

    # benchmark, one process per AUCurves configuration; each prints the
    # scalar-inverse, base-point-multiply and two-term-multiply
    # micro-benchmarks before the whole-operation table
    BENCH_REPS=15 BENCH_ITERS=300 BENCH_MICRO_ITERS=4000 taskset -c 15 \
      cargo run --offline --release --quiet --features s2n --bin bench
    P384_NO_CRYPTOPT=1 BENCH_REPS=15 BENCH_ITERS=300 BENCH_MICRO_ITERS=4000 taskset -c 15 \
      cargo run --offline --release --quiet --features s2n --bin bench

    # the same with the OpenSSL, BoringSSL and (when present) AWS-LC and
    # SymCrypt columns
    BENCH_REPS=15 BENCH_ITERS=300 BENCH_MICRO_ITERS=4000 taskset -c 15 \
      cargo run --offline --release --quiet --features s2n,production --bin bench
    P384_NO_CRYPTOPT=1 BENCH_REPS=15 BENCH_ITERS=300 BENCH_MICRO_ITERS=4000 taskset -c 15 \
      cargo run --offline --release --quiet --features s2n,production --bin bench

    # the P-384 field multiply alone: our two emitted kernels against
    # s2n-bignum's, known-answer gate first
    P384_NO_CRYPTOPT=1 KAT_RANDOM=100000 FIELD_SAMPLES=301 FIELD_INNER=2000 taskset -c 15 \
      cargo run --offline --release --quiet --features s2n,emit-field --bin fieldbench

The `Makefile` wraps these as `test`, `test-asm`, `test-no-s2n`, `kat`,
`wycheproof`, `graviola`, `production`, `bench`, `bench-production` and
`field`, and the DHKEM commands of
[§ DHKEM, Commands](#commands-1) as `dhkem` and `bench-dhkem`. None of them
runs Lean. Recorded results and the conditions of each run are in
[PERF.md](PERF.md). `--offline` is required: the
registry cache holds the pinned RustCrypto and Graviola versions and the
network is not reliable here.

The suite is 94 tests with `--features s2n`: 5 CAVP, 13 differential against
`src/reference.rs`, 19 leaf, 6 against RustCrypto, 8 against Graviola, 14
s2n-backend, 13 scalar-field, the Wycheproof corpus, and 15 DHKEM
(`tests/dhkem.rs`). Every test that drives a kernel runs once per backend, so
the counts are test functions, not scored cases. Without the feature it is
80, the s2n file compiling to nothing. With `--features s2n,production` it is
124, the twenty-three of `tests/production.rs` (ten for OpenSSL and
BoringSSL, six for AWS-LC, seven for SymCrypt) and the seven of
`tests/dhkem_production.rs` added; those files compile to nothing without
`production`. The three counts, 80, 94 and 124, were rerun on 2026-09-17
after SymCrypt was added, with `P384_NO_CRYPTOPT=1` only, every test passing
and no compiler warning from this crate; the `s2n,production` run was
repeated with `P384_SYMCRYPT_LIB` naming a missing file, the SymCrypt
tests printing `SKIP:` and passing. Before SymCrypt was added the
`s2n,production` count was 116. Under `--features force-fallback` two fewer, because the two
ECDSA `built_against_the_emitted_sources` assertions are compiled out; the
DHKEM one checks the fallback instead. Before AWS-LC was added, all five
configurations were run on 2026-09-16 with every test passing, the
`s2n,production` one under each of the three AUCurves field configurations. The
`safegcd` crate's own suite is 18 tests, three of them the P-384 group-order
instance:

    cd ../../../BLS/AUCurves/safegcd-rs && cargo test --offline --release

## DHKEM(P-384, HKDF-SHA384)

RFC 9180 §4.1 with KEM id `0x0011`, `Encap` and `Decap` only: the KEM of
HPKE suite `(0x0011, 0x0002, *)` and of MLS ciphersuite 7.

### The entry points and the leaves

    p384_dhkem_encap(skE: &[u8;48], pkR: &[u8;97],
                     enc: &mut [u8;97], ss: &mut [u8;48], ok: &mut u64)
    p384_dhkem_decap(enc: &[u8;97], skR: &[u8;48], pkR: &[u8;97],
                     ss: &mut [u8;48], ok: &mut u64)

`Encap` is eleven leaf calls: `ok = in_range(skE) AND sec1_valid(pkR)`,
`enc = sec1_encode(skE*G)`, `ss = expand(extract(dh_x_be(skE*sec1_decode(pkR))),
enc || pkR)`. `Decap` is nine: `ok = sec1_valid(enc) AND in_range(skR)`, the
same derivation with `skR` and `enc`. `Decap` takes `pkR` rather than
recomputing it from `skR`, which saves a fixed-base multiply; the caller
supplies the key pair. `enc` and `ss` are written whatever `ok` is.

Seven leaves are new, on every backend:

| leaf | `aucurves` (`src/leaves.rs`) | `s2n` (`src/leaves_s2n.rs`) |
|---|---|---|
| `p384_sec1_decode(P, s)` | `fiat_p384_to_montgomery` on each coordinate, `Z = 1`, projective | `bignum_tomont_p384` on each, `Z = 1`, Jacobian |
| `p384_sec1_valid(f, s)` | prefix `0x04`, both coordinates `< p` (`src/sec1.rs`), and `p384_point_valid` of the decoded point | the same over the Jacobian `p384_point_valid` |
| `p384_sec1_encode(s, P)` | `fp_inv(Z)`, two `fp_mul`, masked to `0x04 \|\| 0^96` when `Z = 0` | `bignum_montinv_p384`, which returns 0 for 0, then `X/Z^2`, `Y/Z^3` |
| `p384_dh_x_be(d, P)` | as `sec1_encode`, `x` only, big-endian | `p384_point_affine_x`, byte-reversed |
| `p384_kem_context(c, enc, pkR)` | `enc \|\| pkR` | shared |
| `dhkem_p384_extract(prk, dh)` | `LabeledExtract("", "eae_prk", dh)`, `hkdf` 0.12.4 | shared |
| `dhkem_p384_expand(ss, prk, ctx)` | `LabeledExpand(prk, "shared_secret", ctx, 48)` | shared |

The last three are in `src/dhkem_kdf.rs` and re-exported by both leaf
modules. All seven are constant time in the sense of
[§ The leaves and their constant-time status](#the-leaves-and-their-constant-time-status):
`p384_sec1_encode` and `p384_dh_x_be` do not branch on `Z`, unlike
`p384_point_affine_x` in the `aucurves` backend.

There is no leaf that tests the DH output for the identity. P-384 has prime
order, so a scalar in `[1, n)` times a valid affine point is not the
identity, and the two validity flags are what exclude the other inputs.
`tests/dhkem.rs::boundary_private_keys_are_accepted` exercises `1` and
`n - 1`.

### Byte order of the private key

**The kernels take `skE` and `skR` as six little-endian limbs**, the scalar
ABI of the ECDSA kernels. RFC 9180 §7.1.2 serialises a P-384 private key as
48 big-endian bytes. The conversion is the caller's:
`dhkem_kdf::sk_le_from_be` and `sk_be_from_le`, a byte reversal. Every
reference, interop test and benchmark arm in this crate converts explicitly;
`enc` and `pkR` are SEC1 bytes and need no conversion.

### `gen/` and the fallback

`build.rs` sets `cfg(p384_dhkem_encap_emitted)` and
`cfg(p384_dhkem_decap_emitted)` when a `gen/*.rs` file defines the function,
and each entry point it does not define is taken from the transcription in
`src/generated.rs` (`dhkem_transcription!`), whose call order is the Lean
front's. `p384_ecdsa_rust::DHKEM_ENCAP_EMITTED` and `DHKEM_DECAP_EMITTED`
report the choice; `tests/dhkem.rs::built_against_the_emitted_sources_when_present`
checks it against the directory. Both files have been in `gen/` since
2026-09-17, when `lake exe emit-p384-rust` wrote them;
`P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n,production`
passes 116 tests on them, 124 since SymCrypt was added. The DHKEM tables of [PERF.md](PERF.md) marked
"transcription" predate that, and
[PERF.md § Emitted kernels](PERF.md#emitted-kernels) holds the run on the
emitted sources.

### Reference and opponents

What exists on this machine, established from the source in the registry
cache and the checkouts, not assumed:

| implementation | P-384 DHKEM? | used here as |
|---|---|---|
| `src/dhkem_ref.rs` | — | independent reference: RustCrypto `p384` 0.13.1 `ecdh::diffie_hellman` and `hkdf` 0.12.4 streaming, no leaf shared |
| hpke-rs 0.7.0, `hpke-rs-rust-crypto` 0.7.0 | **yes**: the `DhKemP384` arms of `dh`, `secret_to_public`, `kem_key_gen` in `hpke-rs-rust-crypto-0.7.0:src/lib.rs`, over RustCrypto `p384` 0.13 and `hkdf` 0.13 | native API (`Hpke::setup_sender` / `setup_receiver`), and a reconstruction over its provider trait (`src/hpke_rs.rs`) |
| hpke-rs 0.7.0, `hpke-rs-libcrux` 0.7.0 | only through RustCrypto `p384` **0.14.0-rc.8** behind `rustcrypto-p-curves` (`hpke-rs-libcrux-0.7.0:src/lib.rs`, lines 15-19 and 75-84); `libcrux-ecdh` 0.0.8 itself has no P-384 (`libcrux-ecdh-0.0.8:src/ecdh.rs`: `derive` returns `UnknownAlgorithm`) | not used: `p384` 0.14.0-rc.8 is not in the registry cache |
| Graviola 0.4.1 | ECDH yes (`key_agreement::p384`, `graviola-0.4.1:src/mid/p384.rs`), HMAC yes, no HKDF, no HPKE | reconstruction (`src/grav.rs`) |
| BoringSSL `956bac6e4db9` | its HPKE has KEMs `0x0010`, `0x0020`, X-Wing and ML-KEM only (`boringssl:include/openssl/hpke.h`) | reconstruction from `EC_POINT_*`, `ECDH_compute_key`, `HKDF_extract`/`HKDF_expand` (`src/bssl.rs`) |
| OpenSSL 3.0.13 (system) | no HPKE (no `OSSL_HPKE_*` export) and no DHKEM operation; both arrived in 3.2 | reconstruction from `EVP_PKEY_derive` and `EVP_KDF "HKDF"` (`src/ossl_kem.rs`) |
| OpenSSL 3.6.0, `/opt/microsoft/mdatp/lib/libcrypto.so.3` | **yes**: `EVP_PKEY_encapsulate` / `EVP_PKEY_decapsulate` with `operation = "DHKEM"` (the layer under `OSSL_HPKE_encap`) | native API, and the same reconstruction |
| OpenSSL 4.1.0-dev, `bench_refs/openssl-install/lib/libcrypto.so.4` | **yes**, the same operation | the same two roles, when `P384_OPENSSL36_LIBCRYPTO` names it |
| AWS-LC 5.9.0 at `f3798b6fe6a8` | its HPKE has KEMs X25519 (`0x0020`) and ML-KEM only (`aws-lc:include/openssl/hpke.h:41-44`); no P-384 KEM | reconstruction from `EC_POINT_*`, `ECDH_compute_key`, `HKDF_extract`/`HKDF_expand`, in the shape of the BoringSSL one (`src/awslc.rs`) |
| SymCrypt 103.13.0 at `286762b` | no HPKE; ECDH (`SymCryptEcDhSecretAgreement`) and HKDF (`SymCryptHkdf`) are exported | reconstruction from `SymCryptEckeySetValue`, `SymCryptEckeyGetValue`, `SymCryptEcDhSecretAgreement` and `SymCryptHkdf` over `SymCryptHmacSha384Algorithm` (`src/symcrypt.rs`) |

The OpenSSL 3.6.0 library is the copy Microsoft Defender for Endpoint ships,
used as found and loaded with `dlopen` (override with
`P384_OPENSSL36_LIBCRYPTO`; the tests skip it when absent). Its build
configuration is not published. It exports no `EC_GFp_nistp*_method`, which
3.x exports exactly when `enable-ec_nistp_64_gcc_128` is set, so secp384r1
gets no dedicated method (`openssl:crypto/ec/ec_curve.c`) and runs the generic
`EC_GFp_mont_method`; it carries the CRYPTOGAMS `x86_64-mont` code. That is
an inference from its exports and strings.

The OpenSSL 4.1.0-dev library in `bench_refs/openssl-install` was built
from the `bench_refs/openssl` checkout; its `configdata.pm` lists
`no-ec_nistp_64_gcc_128`, under which `openssl:crypto/ec/ec_curve.c:2722-2730`
gives secp384r1 no method, and `nm` finds no `nistp384` symbol in it, so it
too runs the generic `EC_GFp_mont_method` (the `x86_64-mont` path is
inferred, not traced). `OpenSSL_version_num()` reports `0x40100000`; the
tests and the benchmark label it `openssl 4.1` from that number.

AWS-LC's P-384 is described in
[§ AWS-LC](#aws-lc-the-third-production-opponent): a dedicated method over
s2n-bignum assembly. `ECDH_compute_key` copies the peer point into a fresh
`EC_KEY` and runs `EC_KEY_check_fips` on it on every call, and that cost is
inside its DHKEM rows.

SymCrypt's P-384 is described in
[§ SymCrypt](#symcrypt-the-fourth-production-opponent). Its key objects take
points as the 96-byte `X || Y` string, so the reconstruction checks the SEC1
prefix itself and accepts only `0x04`. `Encap` imports `skE` alone with
`SYMCRYPT_FLAG_ECKEY_ECDH` and the default validation, which computes
`skE*G`; `SymCryptEckeyGetValue` returns that point as `enc`. `Decap`
imports `(skR, pkR)` with `SYMCRYPT_FLAG_KEY_NO_FIPS` added, under which the
range check on `skR` and the curve check on `pkR` still run but `skR*G` is
not recomputed (`symcrypt:lib/eckey.c:486-488`), matching the kernel's
`Decap`, which takes `pkR` as given. The peer point (`pkR` in `Encap`, `enc`
in `Decap`) is imported with the default validation on every call.
`SymCryptHkdf` computes `HKDF-Expand(HKDF-Extract(salt, ikm), info, L)` in
one call, so `ExtractAndExpand` is one call with an empty salt and the
labelled `ikm` and `info` of RFC 9180 §4; the crate's own KDF is not used.

**Test vectors.** No official DHKEM(P-384) vectors are on this machine. The
CFRG test-vector file in `../libcrux/tests/hpke_test_vectors.json`
holds KEM ids `0x0010`, `0x0012`, `0x0020` and `0x0021` only, the same four
RFC 9180 Appendix A covers; BoringSSL's HPKE vectors cover its own KEMs; the
hpke-rs 0.7.0 package ships no test data. The evidence is agreement across
the implementations above, bit for bit where the interface admits it.

### Tests

`tests/dhkem.rs`, 15 tests, every backend:

* our `Encap` with a supplied `skE` equals the reference's `(enc, ss)` bit for
  bit, and the backends equal each other;
* reference `Encap` → our `Decap`, our `Encap` → reference `Decap` (which
  recomputes `pkR` as the RFC does);
* hpke-rs: `setup_sender` with its ephemeral randomness fixed by
  `Hpke::seed`; our `Encap` with `skE = DeriveKeyPair(ikm)` gives hpke-rs's
  `enc`, and a shared secret whose base-mode key schedule exports the same
  bytes as hpke-rs's context (the shared secret itself is not public in
  hpke-rs); each side decapsulates the other's `enc`; hpke-rs's
  `DeriveKeyPair` equals the reference's;
* Graviola reconstruction: `Encap` bit for bit, `Decap` both ways;
* rejection: 17 invalid `enc` strings (prefixes `0x00`, `0x02`, `0x03`,
  `0x05`, `0x06`, `0x07`, `0x14`, `0xff`; the all-zero identity string;
  `0x04 || 0^96`; a flipped `y` bit; `x + 1`; `x = p`; `y = p`;
  `x = 2^384 - 1`; `y = 2^384 - 1`; and `x = p` for the curve point
  `(0, sqrt b)`, a non-canonical encoding of a valid point) give `ok = 0` in
  `Decap` and `sec1_valid = 0`; the same strings as `pkR` give `ok = 0` in
  `Encap`; private keys `0`, `n`, `n + 1`, `2^384 - 1` give `ok = 0` in both;
  the identity point encodes to `0x04 || 0^96` and a zero DH value.

`tests/dhkem_production.rs`, 7 tests under `--features production`:
BoringSSL, OpenSSL 3.0, OpenSSL 3.2+, AWS-LC and SymCrypt reconstructions
agree bit for bit with our `Encap` (16 cases per backend) and interoperate
both ways;
the OpenSSL 3.2+ native DHKEM
with `ikme` gives the same `(enc, ss)` as our `Encap` with
`skE = DeriveKeyPair(ikme)`, and decapsulates ours; the invalid strings above
(plus prefix `0x07` and `x = p` for `(0, sqrt b)`) and out-of-range keys are
checked on every C side, each side declaring which of the divergences below
it has; `awslc_accepts_the_hybrid_encoding` pins AWS-LC's, and
`symcrypt_minimal_validation_opt_out` pins what SymCrypt accepts under its
validation opt-out. The AWS-LC and SymCrypt cases print `SKIP:` and pass
when their library is absent. The six tests that predate SymCrypt pass with
the OpenSSL 3.2+ side set to Defender's 3.6.0 and, separately, to the
4.1.0-dev build; the seven were run on 2026-09-17 with the 3.6.0 default.

### Divergences of the opponents from RFC 9180

Our kernels reject every invalid input above. Five opponents accept some
(Graviola, the three OpenSSL builds and the AWS-LC reconstruction),
and each divergence is pinned by a test rather than skipped:

1. **Graviola 0.4.1 accepts a coordinate `>= p`** when it reduces to a curve
   point. `AffineMontPoint::from_x962_uncompressed`
   (`graviola-0.4.1:src/mid/p384.rs`, lines 249-273) converts both
   coordinates to the Montgomery domain, which reduces them mod `p`, and
   checks only the curve equation. `x = p` with `y = sqrt(b)` is accepted as
   `(0, sqrt b)` (`tests/dhkem.rs::graviola_accepts_a_non_canonical_x_coordinate`).
   RustCrypto, hpke-rs, BoringSSL, AWS-LC, SymCrypt and every OpenSSL
   reject it.
2. **OpenSSL 3.0.13, 3.6.0 and 4.1.0-dev accept the X9.62 hybrid
   encoding**, prefix
   `0x06` or `0x07` whose low bit matches the parity of `y`, both on key
   import and in the native DHKEM `Decap` (`openssl:crypto/ec/ecp_oct.c` admits
   `POINT_CONVERSION_HYBRID`; `openssl:providers/implementations/kem/ec_kem.c` parses `enc` through
   `EC_KEY_oct2key`). RFC 9180 §7.1.1 specifies the uncompressed form.
   The shared secret they return uses the point's DH value and the hybrid
   bytes in the KEM context.
   **The AWS-LC reconstruction accepts it too**, as `enc` in `Decap` and as
   `pkR` in `Encap`, and checks only that the parity bit matches:
   `EC_POINT_oct2point` masks the low bit of the prefix and dispatches
   `0x06`/`0x07` to `ec_point_from_hybrid`
   (`aws-lc:crypto/fipsmodule/ec/oct.c:17-26`, `:95-114`, `:146-154`). BoringSSL,
   from which AWS-LC forked, rejects both. This is a property of AWS-LC's
   point decoder as the reconstruction uses it; AWS-LC offers no P-384 DHKEM
   of its own that could be tested.
3. **OpenSSL accepts a private key `>= n`** that is non-zero mod `n`, and
   computes with `sk mod n`: `EVP_PKEY_fromdata` imports any 48-byte value,
   and the DHKEM's `eckey_check` (`openssl:providers/implementations/kem/ec_kem.c`, lines 68-99) only rejects
   `sk = 0 mod n`. `n + 1` and `2^384 - 1` are accepted; `0` and `n` are not.
   The 4.1.0-dev build behaves the same. AWS-LC rejects all four
   out-of-range keys: `EC_KEY_set_private_key` fails for a value not below
   `n` (`ec_bignum_to_scalar`, `aws-lc:crypto/fipsmodule/ec/ec_key.c:175-197`).
   The SymCrypt reconstruction rejects all four as well.

**SymCrypt under its default validation has none of the three.** The
reconstruction accepts only the `0x04` prefix; `SymCryptEckeySetValue`
rejects a coordinate not below `p`, a point off the curve, and a private key
that is zero or not below `n`. `SymCryptEckeySetValue`'s own documentation
states that the private key "is taken modulo the order of the subgroup"
(`symcrypt:inc/symcrypt.h:8460-8462`); that holds only under the opt-out
flags `SYMCRYPT_FLAG_KEY_NO_FIPS | SYMCRYPT_FLAG_KEY_MINIMAL_VALIDATION`,
which skip the range check (`symcrypt:lib/eckey.c:367-407`) and the curve
check (`:470-481`). `symcrypt_minimal_validation_opt_out` pins the
behaviour under those flags: a private key `n + 1` is accepted and acts as
`1`, zero is still refused, a point off the curve is accepted and
`SymCryptEcDhSecretAgreement` multiplies it, and a coordinate equal to `p`
is still refused (`symcrypt:lib/ecpoint.c:645-660` runs under every flag).
`SYMCRYPT_FLAG_KEY_NO_FIPS` alone keeps the curve check. The reconstruction
does not use `SYMCRYPT_FLAG_KEY_MINIMAL_VALIDATION`.

### Commands

    # the DHKEM suites (kernel, then C libraries)
    P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n,production \
      --test dhkem --test dhkem_production -- --nocapture

    # the DHKEM benchmark alone, one process per AUCurves field
    cargo build --offline --release --features s2n,production --bin bench
    P384_NO_CRYPTOPT=1 BENCH_SECTIONS=dhkem BENCH_REPS=15 BENCH_ITERS=300 \
      taskset -c 15 ./target/release/bench
    BENCH_SECTIONS=dhkem BENCH_REPS=15 BENCH_ITERS=300 \
      taskset -c 15 ./target/release/bench
    P384_S2N_FIELD=$S2N_BIGNUM_DIR/x86/libs2nbignum.a \
      BENCH_SECTIONS=dhkem BENCH_REPS=15 BENCH_ITERS=300 taskset -c 15 ./target/release/bench

    # the AWS-LC, SymCrypt and OpenSSL 4.1.0-dev runs recorded in PERF.md
    P384_NO_CRYPTOPT=1 cargo build --offline --release --features s2n,production --bin bench
    P384_OPENSSL36_LIBCRYPTO=../../../bench_refs/openssl-install/lib/libcrypto.so.4 \
      BENCH_SECTIONS=dhkem,ecdsa BENCH_REPS=15 BENCH_ITERS=300 BENCH_MICRO_ITERS=4000 \
      taskset -c 15 ./target/release/bench
    # the SymCrypt run's second process, AUCurves over the encoded montmul
    P384_S2N_FIELD=../s2n_import/gen/bignum_montmul_p384_encoded.s \
      cargo build --offline --release --features s2n,production --bin bench
    P384_OPENSSL36_LIBCRYPTO=../../../bench_refs/openssl-install/lib/libcrypto.so.4 \
      BENCH_SECTIONS=ecdsa,dhkem BENCH_REPS=15 BENCH_ITERS=300 BENCH_MICRO_ITERS=4000 \
      taskset -c 15 ./target/release/bench

Rebuild before each run: the field configuration is a build-time choice, so
set the same variable on the `cargo build` line. `make dhkem` and
`make bench-dhkem` wrap these. `BENCH_SECTIONS` defaults to `ecdsa,dhkem`, so
the plain benchmark commands above print the DHKEM table after the ECDSA
ones.
