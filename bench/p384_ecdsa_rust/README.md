# `p384_ecdsa_rust` — leaf shims, KATs and a benchmark for the emitted P-384 ECDSA source

kind: authored · authority: canonical for this directory · freshness: the
benchmark numbers below are a single dated run and go stale with the machine,
the toolchain and the contents of `gen/`

The CatCrypt compiler emits the orchestration of ECDSA-P-384 as Rust that
calls thirteen leaf functions. This crate supplies those leaves, a second
implementation to test the emitted code against, the FIPS 186-4 CAVP
vectors, the Wycheproof adversarial corpus, equivalence and interop tests
against RustCrypto and Graviola, and a wall-clock comparison with both.
Behind `--features production` it adds the C libraries production TLS
stacks run, OpenSSL 3.0, BoringSSL and AWS-LC, to the interop suite and the
benchmark ([§ OpenSSL and BoringSSL](#openssl-and-boringssl-the-production-opponents),
[§ AWS-LC](#aws-lc-the-third-production-opponent)).

The leaves come in **three backends**, and the same emitted orchestration is
compiled over each: AUCurves `p384-safe-rust` with the fiat-crypto field,
the same with the CryptOpt assembly field, and — behind `--features s2n` —
AWS s2n-bignum assembly. The third exists to answer one question. Graviola's
P-384 arithmetic *is* s2n-bignum, so putting our orchestration on the same
assembly turns the comparison with it into one of orchestration alone.
[§ Whole operation, three backends](#whole-operation-three-backends) is the
answer, and [§ The three leaf backends](#the-three-leaf-backends) says what
each configuration is for.

The crate also carries **DHKEM(P-384, HKDF-SHA384)**, RFC 9180 KEM id
`0x0011`, `Encap` and `Decap` only, over the same backends, with its own
reference, interop suite and benchmark:
[§ DHKEM(P-384, HKDF-SHA384)](#dhkemp-384-hkdf-sha384).

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
| mod-`n` divstep inverse | the same port, instantiated at the group order in `safegcd-rs/src/safegcd_p384_order.rs` | ours |
| mod-`n` multiply, squaring, Montgomery conversions | fiat-crypto `p384_scalar_64.rs` | external, machine-generated and machine-checked |
| base field | fiat-crypto `p384_64.rs`, and optionally the CryptOpt assembly | external |
| reference sign and verify (`src/reference.rs`) | this crate | ours |
| RustCrypto `p384` 0.13.1 / `ecdsa` 0.16.9 | external | reference and benchmark baseline, never ours |
| Graviola 0.4.1 | external, s2n-bignum assembly | second reference and benchmark baseline, never ours |
| OpenSSL 3.0.13 `libcrypto.so.3` | external, system library | production opponent (`--features production`), never ours |
| BoringSSL at `956bac6e4db9` | external, `libcrypto.a` | production opponent (`--features production`), never ours |
| AWS-LC 5.9.0 at `f3798b6fe6a8` | external, `libcrypto.so` of the build tree `~/Claude/bench_refs/aws-lc-build`, P-384 field in s2n-bignum assembly | production opponent, ECDSA and DHKEM reconstruction (`--features production`, skipped when absent), never ours |
| DHKEM orchestration (`gen/p384_dhkem_*.rs`, transcription until they land) | CatCrypt compiler emit | ours |
| DHKEM leaves (`src/leaves.rs`, `src/leaves_s2n.rs`, `src/dhkem_kdf.rs`, `src/sec1.rs`) | this crate | ours (plumbing; HKDF is `hkdf` 0.12.4 / `hmac` 0.12.1 / `sha2` 0.10.9, external) |
| reference DHKEM (`src/dhkem_ref.rs`) | this crate over RustCrypto `p384` ECDH and `hkdf` | reference, not a kernel |
| hpke-rs 0.7.0 with `hpke-rs-rust-crypto` 0.7.0 | external | DHKEM production opponent, never ours |
| OpenSSL 3.6.0, Microsoft Defender's `libcrypto.so.3` | external, found on the machine | DHKEM native-API opponent (`--features production`), never ours |
| OpenSSL 4.1.0-dev, `~/Claude/bench_refs/openssl-install/lib/libcrypto.so.4` | external, built from the `bench_refs/openssl` checkout (HEAD `83ef562`; that the install matches this HEAD was not checked) | the same role, selected with `P384_OPENSSL36_LIBCRYPTO`, never ours |

Every layer that differs between the two sides is ours. The field is the one
layer neither side owns and both sides share: RustCrypto's
`p384-0.13.1/src/arithmetic/field/p384_64.rs` and the field AUCurves calls are
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

The archive is read from `bench/reference_install/s2n-bignum/x86`, never
modified, and linked by `build.rs` behind the `s2n` feature.
`S2N_BIGNUM_DIR` overrides the directory. With the feature off the crate
builds and tests exactly as before.

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
omitted. All three are in the tables below, and where we lose the row says
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
Graviola's own public `Hmac<Sha384>` following `high/hmac_drbg.rs`: four
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
message is 25 bytes, one SHA-384 block, and the measurement below puts the
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
`~/Claude/bench_refs/boringssl` (commit `956bac6e4db9`), as two more
opponents. `src/ossl.rs` and `src/bssl.rs` are the bridges, `tests/production.rs`
the interop suite; the benchmark gains an OpenSSL and a BoringSSL column. Off
by default: without the feature the crate builds and tests exactly as before
(80 tests without `s2n`, 94 with it). AWS-LC, a third production opponent
behind the same feature, has its own section below.

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
`CMakeCache.txt`). OpenSSL is Ubuntu's `3.0.13-0ubuntu3.15` build.

### Their P-384 arithmetic

Neither library has P-384-specific arithmetic. Both run the generic
Montgomery EC method over a generic word-serial Montgomery multiply in
perlasm, which at six limbs takes the plain `MUL` loop and no MULX/ADX path.

**OpenSSL 3.0.13.** The source is not on this machine at that version (the
checkout in `bench_refs/openssl` is master, 4.1.0-dev, which has
`ecp_nistp384.c`); the files below were read from the `openssl-3.0.13` tag
on GitHub.

| layer | 3.0.13 source |
|---|---|
| method | `crypto/ec/ec_curve.c`: the `NID_secp384r1` entry carries a method only under `S390X_EC_ASM`, so `ec_group_new_from_data` calls `EC_GROUP_new_curve_GFp`; `crypto/ec/ec_cvt.c` returns `EC_GFp_mont_method()` whenever `OPENSSL_BN_ASM_MONT` is defined. `ecp_nistp384.c` does not exist in 3.0. The system library exports `EC_GFp_nistp224_method`, `_nistp256_` and `_nistp521_` and no P-384 method |
| field multiply | `ossl_ec_GFp_mont_field_mul` → `BN_mod_mul_montgomery` → `bn_mul_mont_fixed_top` (`crypto/bn/bn_mont.c`) → `bn_mul_mont` (`crypto/bn/asm/x86_64-mont.pl`), whose entry sends a limb count with `num & 3 != 0` to `.Lmul_enter`, the generic loop; `bn_mulx4x_mont` needs a multiple of four limbs, at least eight |
| points | `BIGNUM` Jacobian, `ossl_ec_GFp_simple_add` / `_dbl` (`crypto/ec/ecp_smpl.c`) |
| `k*G` in signing | `ossl_ec_scalar_mul_ladder` (`crypto/ec/ec_mult.c`), Montgomery ladder with coordinate blinding, no precomputed table |
| `u1*G + u2*Q` | `ossl_ec_wNAF_mul`, interleaved wNAF, window 4 at 384 bits (`EC_window_bits_for_scalar_size`) |
| scalar inverse | `ec_field_inverse_mod_ord` (`crypto/ec/ec_lib.c`): Fermat, `BN_mod_exp_mont` to `n - 2` |
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
commit carries `p256_64.h`, `p256_field_64.br.c.inc` and the Curve25519
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
(`include/openssl/ecdsa.h`, defined in `crypto/ecdsa/ecdsa_asn1.cc`) and
reaches the same `ecdsa_sign_impl` as `ECDSA_do_sign`; what it skips is
`ecdsa_sign_fixed`'s SHA-512 of the private key and digest and its
rejection-sampled DRBG draw. The self-test hook `ecdsa_sign_fixed` calls is
an inline no-op outside FIPS builds (`crypto/internal.h`). That column is
like for like.

OpenSSL's `ECDSA_do_sign_ex` exists in 3.0.13, but with `kinv` and `r` given
`ossl_ecdsa_simple_sign_sig` (`crypto/ec/ecdsa_ossl.c`) skips
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
draw hashed with SHA-512, `crypto/bn/bn_rand.c`), and BoringSSL's pair
rebuilt from `SHA512` over the same 96 bytes and `BN_rand_range_ex(k, 1, n)`,
which runs the same `bn_rand_range_words` DRBG loop with zero additional
data. Neither is isolated inside the library's own call.

Verification needs no caveat: both columns are `ECDSA_do_verify` on the
digest and a pre-built `ECDSA_SIG`.

### Interop

`tests/production.rs`, ten of its sixteen tests (the other six are AWS-LC's,
below), all passing on both leaf backends in both
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

### Measured

2026-09-16, the same machine as the sections above (AMD Ryzen 7 PRO 7840U,
Linux 7.0.0-31-generic, rustc 1.93.0, `--release`, pinned to core 15), 15
repetitions of 300 iterations, every column interleaved round-robin in one
process. **The box was loaded: load average 3.8 to 9.6 across the runs, with
Lean workers and another field benchmark on other cores**, so the
absolute figures are inflated and vary by up to a factor of two between
processes; the
ratios, which the interleaving protects, are what is reported. Eight
processes were run: four of the committed binary (load 7.2 to 9.6) and,
before it, four of a binary identical in every timed arm except that it
lacked the BoringSSL nonce-derivation arm (load 3.8 to 7.0).

Absolute figures, committed binary, the lower-load process of each pair:

| configuration | op | backend | ours | RustCrypto | Graviola | OpenSSL | BoringSSL |
|---|---|---|---|---|---|---|---|
| pure Rust | sign | `aucurves` | 110 695 | 678 005 | 164 552 | 891 753 | 536 049 |
| pure Rust | sign | `s2n` | 33 877 | 678 005 | 164 552 | 891 753 | 536 049 |
| pure Rust | verify | `aucurves` | 621 089 | 1 240 531 | 296 337 | 700 770 | 557 621 |
| pure Rust | verify | `s2n` | 187 960 | 1 240 531 | 296 337 | 700 770 | 557 621 |
| CryptOpt | sign | `aucurves` | 97 202 | 815 286 | 198 086 | 914 053 | 594 536 |
| CryptOpt | sign | `s2n` | 37 623 | 815 286 | 198 086 | 914 053 | 594 536 |
| CryptOpt | verify | `aucurves` | 508 338 | 1 418 192 | 333 705 | 790 534 | 610 648 |
| CryptOpt | verify | `s2n` | 197 543 | 1 418 192 | 333 705 | 790 534 | 610 648 |

ns/op, median of the per-repetition figures. The OpenSSL and BoringSSL sign
columns are the nonce-supplied ones.

Ratios, ours over theirs, range over the four processes of each field
configuration (eight for the `s2n` rows, which do not depend on it):

| op | our row | vs OpenSSL | vs BoringSSL | tier against both |
|---|---|---|---|---|
| sign | `aucurves`, pure Rust | 0.11 – 0.13 | 0.19 – 0.21 | not same tier, against us |
| sign | `aucurves`, CryptOpt | 0.10 – 0.11 | 0.14 – 0.16 | same tier on the field |
| sign | `s2n` | 0.03 – 0.04 | 0.05 – 0.06 | not same tier, in our favour |
| verify | `aucurves`, pure Rust | 0.83 – 0.89 | **1.11 – 1.28** | not same tier, against us |
| verify | `aucurves`, CryptOpt | 0.61 – 0.68 | 0.74 – 0.85 | same tier on the field |
| verify | `s2n` | 0.24 – 0.27 | 0.31 – 0.37 | not same tier, in our favour |

The sign rows against BoringSSL are like for like; against OpenSSL they are
against the reconstruction described above. The verify rows are like for
like on both.

**Where we lose.** Verification in the pure-Rust `aucurves` configuration
against BoringSSL, 1.11 in three of the four processes and 1.28 in the most
loaded one:
our group law and orchestration over the fiat-crypto Rust field are slower
than BoringSSL's C group law over its generic assembly Montgomery loop. The
same row is a win against OpenSSL (0.83 to 0.89), and with the CryptOpt field
it is a win against both (0.61 to 0.68 and 0.74 to 0.85). Against Graviola
the losses recorded above stand, unchanged in these runs: 1.88 to 2.10 pure
Rust and 1.46 to 1.61 with the CryptOpt field. Every other row is a win.

Signing, full API against the nonce-supplied column:

| process | BoringSSL, nonce supplied | BoringSSL, `ECDSA_do_sign` | its nonce derivation | OpenSSL, nonce supplied | OpenSSL, `ECDSA_do_sign` | `BN_generate_dsa_nonce` |
|---|---|---|---|---|---|---|
| pure Rust | 536 049 | 540 872 | 893 | 891 753 | 862 858 | 2 577 |
| CryptOpt | 594 536 | 641 323 | 1 023 | 914 053 | 945 265 | 2 885 |

The nonce derivation is 0.2% of BoringSSL's signature and 0.3% of OpenSSL's
(0.9 to 1.4 µs and 2.1 to 3.5 µs over all processes). The full-API minus
nonce-supplied difference moves between −85 µs and +115 µs across processes,
two orders of magnitude above the component it would measure, so it does not
resolve the derivation, and on this box it cannot distinguish the OpenSSL
reconstruction from the production entry point either. Against the full API
the sign ratios are 0.14 to 0.20 (`aucurves`) and 0.05 to 0.06 (`s2n`) for
BoringSSL, 0.10 to 0.13 and 0.03 to 0.04 for OpenSSL; they are not like for
like, and differ from the nonce-supplied ratios by less than the spread.

`openssl speed -seconds 3 ecdsap384` on core 15 in the same window gives
977.6 signs/s and 1363.1 verifies/s, 1.02 ms and 734 µs, through the EVP
provider path; the harness's `ECDSA_do_sign` and `ECDSA_do_verify` figures
over the eight processes, 0.72 to 1.24 ms and 0.58 to 0.97 ms, are the same
magnitude.

**What could not be isolated or verified.** OpenSSL's nonce-supplied signing
cost through its own `ecdsa_sign_setup`: no exported entry point takes `k`,
so the column is the public-API reconstruction. BoringSSL's nonce derivation
inside `ECDSA_do_sign`: `BCM_rand_bytes_with_additional_data` is not
exported, so the component is `BN_rand_range_ex` with zero additional data.
The OpenSSL 3.0.13 source was read from the upstream tag, not from Ubuntu's
patched source package, which is not on this machine; the build options
`openssl version -a` prints do not change the method selection it describes.

## AWS-LC, the third production opponent

`--features production` also brings in AWS-LC 5.9.0, the shared
`libcrypto.so` of the build tree `~/Claude/bench_refs/aws-lc-build`, built
from the checkout `~/Claude/bench_refs/aws-lc` at `f3798b6fe6a8`.
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
its `CMakeCache.txt`, so `BORINGSSL_FIPS` is undefined and the lazy
self-test hooks are no-ops (`crypto/internal.h:1257`).

### Its P-384 arithmetic

Unlike BoringSSL and OpenSSL, AWS-LC has a dedicated P-384 method, and its
field is s2n-bignum assembly, the arithmetic of our `s2n` backend and of
Graviola. File:line references are to the checkout above.

| layer | source |
|---|---|
| method | `crypto/fipsmodule/ec/ec.c:129-146`, `EC_group_p384`: `out->meth = EC_GFp_nistp384_method()` unless `OPENSSL_SMALL` |
| field selection | `crypto/fipsmodule/ec/ec_nistp.h:20-25` defines `EC_NISTP_USE_S2N_BIGNUM` when `OPENSSL_NO_ASM` is unset, the OS is Linux or Apple, and on x86-64 `MY_ASSEMBLER_IS_TOO_OLD_FOR_ADX_AVX2` is unset (it is `OFF` in `CMakeCache.txt`) |
| field multiply, square | `crypto/fipsmodule/ec/p384.c:45-55` and `:288-302` map them to `bignum_montmul_p384_selector` / `bignum_montsqr_p384_selector`; `third_party/s2n-bignum/s2n-bignum_aws-lc.h:88-90` and `:112-120` call `bignum_montmul_p384` / `bignum_montsqr_p384` (MULX/ADX) when the CPU has BMI2 and ADX, and the `_alt` variants otherwise. The Ryzen 7840U has both, so the non-`_alt` routines run (inferred from the selector and `/proc/cpuinfo`, not traced) |
| point double | `p384.c:259`, `p384_montjdouble_selector`, s2n-bignum assembly |
| point add | `p384.c:275-284`, `ec_nistp_point_add` in C (`ec_nistp.c`) over the s2n-bignum field calls |
| variable-base multiply (ECDH) | `p384.c:464-484`: `p384_montjscalarmul_selector` (`:475`), s2n-bignum's `p384_montjscalarmul`, the routine of the same name that our "montjscalarmul on G" micro-benchmark calls from the vendored archive (the two s2n-bignum copies were not compared) |
| `k*G` in signing | `p384.c:491`, `ec_nistp_scalar_mul_base` (`ec_nistp.c:507-565`): a comb over the precomputed `p384_g_pre_comp` table with regular-wNAF digits, window 5 (`ec_nistp.c:308`) |
| `u1*G + u2*Q` in verification | `p384.c:513`, `ec_nistp_scalar_mul_public` (`ec_nistp.c:647-699`): textbook wNAF, `w = 5` for both scalars, the first sub-table of the precomputed table for `G` |
| scalar inverse | `crypto/fipsmodule/ec/scalar.c:128-133`, `bn_mod_inverse0_prime_mont_small` (`bn/exponentiation.c:756-762`): Fermat; the verifier's `ec_scalar_to_montgomery_inv_vartime` (`scalar.c:135`) uses the same routine |
| scalar multiply mod `n` | `bn_mod_mul_montgomery_small` (`bn/montgomery.c:491-506`) → `bn_mul_mont` (`:523-540`), which at six limbs fails `bn_mulx4x_mont_capable` and `bn_mul4x_mont_capable` (`bn/internal.h:305-313`, both need `num >= 8 && num % 4 == 0`) and calls `bn_mul_mont_nohw` |
| sign | `crypto/fipsmodule/ecdsa/ecdsa.c:157-221`, `ecdsa_sign_impl`; `ECDSA_sign_with_nonce_and_leak_private_key_for_testing` (`:251-258`) and `ECDSA_do_sign` (`:260-326`) both reach it |
| verify | `ecdsa.c:103-148`, `ec_point_mul_scalar_public` at `:137` |
| ECDH | `crypto/ecdh_extra/ecdh_extra.c:26-34` → `ECDH_compute_shared_secret` (`crypto/fipsmodule/ecdh/ecdh.c:28`), which copies the peer point into a fresh `EC_KEY` and runs `EC_KEY_check_fips` on it (`:58`) on every call, then `ec_point_mul_scalar` (`:64`) |

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
`ec_key.c:247`), which is key setup and not timed.

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

### Measured

2026-09-16, the machine of [§ Measured](#measured), pinned to core 15, one
process of the pure-Rust AUCurves build (`P384_NO_CRYPTOPT=1`),
`BENCH_SECTIONS=dhkem,ecdsa BENCH_REPS=15 BENCH_ITERS=300`, every column
interleaved round-robin. **Load average 4.0 before the run and 6.7 after**,
with Lean and C compiler processes on other cores, so absolute figures are
from a loaded machine. `gen/` held the emitted ECDSA sources and no DHKEM
source, so the ECDSA rows are emitted kernels and the DHKEM rows the
transcription.

| op | ours `aucurves` | ours `s2n` | AWS-LC | `aucurves` / AWS-LC | `s2n` / AWS-LC |
|---|---|---|---|---|---|
| sign, nonce supplied | 97 407 | 30 356 | 74 443 | **1.31** | 0.41 |
| verify | 532 002 | 155 941 | 176 936 | **3.01** | 0.88 |
| sign, AWS-LC full API | | | 81 541 | 1.19 | 0.37 |

ns/op, median of the per-repetition figures. AWS-LC's nonce-derivation arm
is 603 ns. In the same process: OpenSSL 3.0.13 sign 762 421 and verify
622 992, BoringSSL 491 900 and 483 369, Graviola 145 965 and 269 249.

**Where we lose.** Both `aucurves` rows. In the pure-Rust configuration our
group law over the fiat-crypto Rust field is slower than AWS-LC's comb and
wNAF over s2n-bignum assembly: 1.31 on signing and 3.01 on verification. The
same arithmetic tier is the `s2n` row, which is faster on both, 0.41 and
0.88. Two differences on the signing path are known from the sources and
were not isolated inside AWS-LC: its scalar inverse is Fermat over the
generic `bn_mul_mont_nohw`, where the `s2n` backend calls the divstep
inverse (in this process our own Fermat chain took 38.7 µs and the divstep
2.6 µs), and its comb is `ec_nistp_scalar_mul_base` in C with a C point
addition, where ours is `src/comb_s2n.rs`. Both sides verify with a width-5 two-term pass over
the same field, and the verification margin is the narrower one.

The CryptOpt and s2n-montmul AUCurves field configurations were not run
against AWS-LC.

## Paths

The three path dependencies are relative and assume the AUCurves checkout is
at `~/Claude/BLS/AUCurves`, the layout the sibling bench directories already
use:

    p384        -> ../../../BLS/AUCurves/p384-safe-rust   (features = ["extracted"])
    fiat-crypto -> ../../../BLS/AUCurves/fiat-crypto/fiat-rust
    safegcd     -> ../../../BLS/AUCurves/safegcd-rs

`features = ["extracted"]` is needed for `p384::wnaf::{point_to_bytes,
point_from_bytes}`, which fix the 144-byte point encoding. RustCrypto's
`p384` is imported under the name `p384_rc` because the path dependency already occupies
the name.

Two more paths are read, never written, and are not cargo dependencies:

    s2n-bignum   -> ../reference_install/s2n-bignum/x86/libs2nbignum.a
                    (feature `s2n`; override with S2N_BIGNUM_DIR)
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

The two `.s` files are untracked build output of their Lean emitters.
`build.rs` hands them to the linker of the `fieldbench` binary and never
regenerates them; regenerate with lake before recording a figure from them.

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
`safegcd_p384.rs`, the base-field instance behind `fp_inv`: `n` and `p` are
both odd and both 384 bits wide, so both take 7×62-bit signed limbs and the
same 15 outer iterations of 59 divsteps. `ModInfo::outer_iters` requires
`ceil((9437*b + 1) / (4096*59))` for a b-bit modulus under the δ₀=1/2
encoding, which is 15 at `b = 384`, and `modinv_62` requires only that the
bottom limb be odd; `safegcd_p384_order.rs` asserts both, and its in-crate
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
cost of both is in the table below.

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
measurement below shows.

## `gen/` and the fallback

`build.rs` collects every `gen/*.rs`, in sorted order, into one module that
has the leaf shims in scope, and sets `cfg(p384_emitted)`. With no such file
the crate uses the hand-written transcription in
`src/generated.rs::fallback`, which is the same three call sequences written
out by hand. `p384_ecdsa_rust::EMITTED` reports which path a binary took, and
`--features force-fallback` selects the transcription even when `gen/` is
populated, so the two can be compared.

`gen/` currently holds four files emitted by `lake exe emit-p384-rust`:
`p384_ecdsa_verify.rs`, `p384_ecdsa_sign.rs`, `p384_ecdsa_verify_msm.rs` and
`p384_msm_term.rs`. Their call sequences agree with the fallback
transcription leaf call for leaf call — thirteen for verify, ten for sign,
three for the two-term MSM. Nothing under `gen/` is hand-edited; the
provenance note lives in `gen/PROVENANCE.md` rather than `gen/README`
because the emitter writes into that directory.

## Test vectors

**FIPS 186-4 CAVP, `[P-384,SHA-384]` SigGen, 15 vectors** — in
`src/vectors.rs`. NIST publishes them in `SigGen.txt` inside
`186-4ecdsatestvectors.zip`; the copy transcribed here is the one in the
RustCrypto `p384` 0.13.1 crate at `src/test_vectors/ecdsa.rs`, which names
that source and whose `m` field is the SHA-384 prehash of the original `Msg`.
That crate is in this machine's cargo registry cache. Nothing was fetched
from the network and no vector was constructed here.

**CAVP SigVer is not on this machine.** No `.rsp` file for ECDSA P-384
verification was found under `~/Claude`, `~/.cargo` or the AUCurves tree. The
negative-verification corpus used instead is Google Wycheproof's
`ecdsa_secp384r1_sha384_p1363_test.txt`, in BoringSSL's converted text form
at `~/Claude/bench_refs/boringssl/third_party/wycheproof_testvectors`. It is
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
every differential input in `tests/`, the kernel's verdict agrees with
RustCrypto's.

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

    # every test, every backend, pure-Rust AUCurves field
    P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n -- --nocapture

    # the same with the CryptOpt assembly linked
    cargo test --offline --release --features s2n -- --nocapture

    # the two AUCurves backends alone, as the crate builds without the archive
    P384_NO_CRYPTOPT=1 cargo test --offline --release -- --nocapture

    # the CAVP vectors only
    P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n --test cavp -- --nocapture

    # the Wycheproof corpus only
    WYCHEPROOF_DIR=$HOME/Claude/bench_refs/boringssl/third_party/wycheproof_testvectors \
      P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n --test wycheproof -- --nocapture

    # the Graviola interop suite only
    P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n --test graviola -- --nocapture

    # the OpenSSL, BoringSSL and AWS-LC interop suite
    P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n,production --test production -- --nocapture

    # the same with AWS-LC from another build, or absent (its tests then skip)
    P384_AWSLC_LIBCRYPTO=/path/to/libcrypto.so P384_NO_CRYPTOPT=1 \
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

    # the same with the OpenSSL, BoringSSL and (when present) AWS-LC columns
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
`field`. `--offline` is required: the
registry cache holds the pinned RustCrypto and Graviola versions and the
network is not reliable here.

The suite is 94 tests with `--features s2n`: 5 CAVP, 13 differential against
`src/reference.rs`, 19 leaf, 6 against RustCrypto, 8 against Graviola, 14
s2n-backend, 13 scalar-field, the Wycheproof corpus, and 15 DHKEM
(`tests/dhkem.rs`). Every test that drives a kernel runs once per backend, so
the counts are test functions, not scored cases. Without the feature it is
80, the s2n file compiling to nothing. With `--features s2n,production` it is
116, the sixteen of `tests/production.rs` (ten for OpenSSL and BoringSSL,
six for AWS-LC) and the six of `tests/dhkem_production.rs` added; those
files compile to nothing without `production`. The three counts, 80, 94 and
116, were rerun on 2026-09-16 after AWS-LC was added, with
`P384_NO_CRYPTOPT=1` only, every test passing. Under `--features force-fallback` two fewer, because the two
ECDSA `built_against_the_emitted_sources` assertions are compiled out; the
DHKEM one checks the fallback instead. Before AWS-LC was added, all five
configurations were run on 2026-09-16 with every test passing, the
`s2n,production` one under each of the three AUCurves field configurations. The
`safegcd` crate's own suite is 18 tests, three of them the P-384 group-order
instance:

    cd ~/Claude/BLS/AUCurves/safegcd-rs && cargo test --offline --release

## Measured

2026-09-16, AMD Ryzen 7 PRO 7840U (Zen 4, 8 cores / 16 threads), Linux
7.0.0-31-generic, rustc 1.93.0, `--release`, pinned to core 15, load average
1.1 to 1.9 during the run — one Rocq worker was saturating another core. The
figure is the median of the per-repetition ns/op. Our side, RustCrypto and
Graviola, and the two arms of each micro-benchmark, are interleaved
round-robin within each process, because on this machine the clock drifts by
more over a sequential sweep than the variants differ from each other
(the `build.sh` script of the AUCurves `p384-safe-rust` crate records that
measurement).

Whether the CryptOpt assembly is linked is a compile-time choice of
`p384-safe-rust`, so the two configurations cannot be interleaved against
each other; they are separate processes and separate rows. Against
RustCrypto only the pure-Rust row is a same-tier comparison: the assembly row
has a hand-superoptimized field multiply on our side and Rust on
RustCrypto's. Against Graviola it is the assembly row that is same-tier and
the pure-Rust row that is not.

The Graviola figures are a later run on the same machine, core and pinning;
the RustCrypto columns were re-measured inside the same two processes, so the
three columns of a row are directly comparable. Against the earlier
`### Whole operation` table the RustCrypto column sits 7 to 10% lower, which
bounds the drift between the two runs; the four ratios reproduce to two
decimals across them.

### The scalar inverse

15 repetitions of 4000 iterations, one fixed scalar, pure-Rust field. The
scalar field is fiat-crypto in both configurations and the divstep inverter
calls neither `fp_mul` nor `fp_square`, so the assembly configuration
reproduces these three rows to within 1%.

| inverse | ns/op | vs Fermat |
|---|---|---|
| Fermat `a^(n-2)`, 383 squarings + 287 multiplications | 33 016 | 1.00 |
| divstep, 15 × 59, `safegcd_p384_order` | 2 228 | 0.07 |
| base-field `fp_inv`, `safegcd_p384`, for scale | 2 256 | — |

The two divstep inverses cost the same, as they should: identical limb
count, identical iteration count, and a modulus that enters only as data.
`bench/p384_safegcd_compare` recorded `fp_inv` at 2333 ns/op on this box,
which is the same figure to 3%.

Both are the half-delta variant. The safegcd core starts `zeta = -1`, the
δ₀ = 1/2 encoding, and `ModInfo::outer_iters` documents the requirement
`outer_iters ≥ ⌈(9437·b + 1)/(4096·59)⌉`, which is fifteen at `b = 384` and
gives 885 divsteps; the classic δ₀ = 1 bound at that width is 1110, which
needs nineteen outer iterations. Running the same step over the same modulus
at each count, and asserting the two agree on 256 inputs first:

| bound | divsteps | ns/op | ratio |
|---|---|---|---|
| classic δ₀ = 1, 19 × 59 | 1121 | 2718 | 1.00 |
| half δ₀ = 1/2, 15 × 59 | 885 | 2145 | 0.79 |

The ratio is the iteration ratio, 885/1121, to two decimals — the per-step
cost is the same and only the count differs. At the whole-operation level it
is worth about 570 ns, under one percent of a signature, because the inverse
is now a few percent of the operation rather than the quarter of it that the
Fermat chain was.

### The two-term multiply

15 repetitions of 200 iterations, on the `u1`, `u2` and `Q` of the verify
row below.

| configuration | route | ns/op | ratio |
|---|---|---|---|
| fiat-crypto field, pure Rust | `mul_base` + `mul` + `add`, 3 leaves | 480 031 | 1.00 |
| fiat-crypto field, pure Rust | `p384_lincomb`, interleaved, w = 5 | 445 379 | 0.93 |
| CryptOpt assembly field | `mul_base` + `mul` + `add`, 3 leaves | 353 576 | 1.00 |
| CryptOpt assembly field | `p384_lincomb`, interleaved, w = 5 | 329 233 | 0.93 |

### Whole operation

15 repetitions of 300 iterations.

| configuration | op | ours ns/op | RustCrypto ns/op | ratio | same tier |
|---|---|---|---|---|---|
| fiat-crypto field, pure Rust | sign | 80 490 | 505 369 | 0.16 | yes |
| fiat-crypto field, pure Rust | verify | 455 950 | 927 494 | 0.49 | yes |
| CryptOpt assembly field | sign | 62 281 | 505 166 | 0.12 | no |
| CryptOpt assembly field | verify | 339 054 | 951 083 | 0.36 | no |

Ratio is ours / RustCrypto; below 1.00 means our side is faster. A repeat of
the whole measurement gave the same four ratios to two decimals (ours:
80 767 / 458 594 pure, 62 486 / 339 050 assembly; RustCrypto: 506 812 /
931 008 and 506 800 / 933 626). The RustCrypto column differs by 2.5%
between the two processes of a run, which bounds the drift between them.

### Whole operation, all three implementations

15 repetitions of 300 iterations, one process per field configuration, the
three sides interleaved round-robin inside each. Same machine, core and
pinning as the two-column table above, but a separate run: read the ratios
across the two tables and the absolutes only within one.

| configuration | op | ours ns/op | RustCrypto | vs RC | Graviola | vs GV |
|---|---|---|---|---|---|---|
| fiat-crypto field, pure Rust | sign | 73 061 | 461 528 | 0.16 | 108 205 | 0.68 |
| fiat-crypto field, pure Rust | verify | 414 759 | 851 848 | 0.49 | 206 189 | **2.01** |
| CryptOpt assembly field | sign | 57 460 | 468 695 | 0.12 | 112 181 | 0.51 |
| CryptOpt assembly field | verify | 310 122 | 857 869 | 0.36 | 201 581 | **1.54** |

A repeat of the whole measurement gave the same ratios against RustCrypto to
two decimals and against Graviola to within 4%: ours 73 891 / 417 078 pure
and 57 019 / 305 075 assembly, Graviola 109 703 / 199 535 and 108 776 /
197 638, so 0.67 and 2.09 pure, 0.52 and 1.54 assembly. The Graviola verify
column is the noisiest of the six, moving 1.3% between the two runs.

Tier per row, and what each column includes:

| row | vs RustCrypto | vs Graviola |
|---|---|---|
| pure Rust, sign | same tier; both prehashed and both given `k` | not same tier (Rust against assembly), *and* not like for like (their column is the whole `sign` API) |
| pure Rust, verify | same tier | not same tier; like for like up to a 0.1% message hash |
| assembly, sign | not same tier | same tier, but not like for like |
| assembly, verify | not same tier | **same tier and like for like — the headline Graviola row** |

The RustCrypto ratios are unchanged from the previous measurement: 0.16 and
0.49 against 0.16 and 0.50 pure Rust, 0.12 and 0.36 against 0.12 and 0.36
with the assembly field.

**Where we lose.** Verification, against Graviola, in both configurations.
The headline row — same tier, like for like — is 310 µs against 202 µs, a
factor of 1.54 slower. The pure-Rust row is 2.01, which is the tier gap and
is reported as such. Both are the two-term multiply: our `p384_lincomb` is
Shamir with a 5-bit window over the AUCurves group law, and Graviola runs two
5-bit-window Booth multiplications in s2n-bignum assembly and still finishes
first. The 1.54 is the figure to move, and it is not a compiler-emit figure:
the orchestration above the leaves is a handful of calls either way.

**Where we win, and by how much once the caveat is paid.** Signing, in both
configurations, but the column is not like for like: Graviola's `sign` does
SHA-384, a system-RNG read and an RFC 6979 nonce derivation that our kernel
does not. Timing those three separately bounds the part that can be
subtracted:

| configuration | component | ns/op | of `sign` |
|---|---|---|---|
| pure Rust | SHA-384 of the 25-byte message | 193 | 0.2% |
| pure Rust | system RNG, 16 bytes | 426 | 0.4% |
| pure Rust | RFC 6979 HMAC_DRBG, 7 × HMAC-SHA-384 | 5 422 | 5.0% |
| pure Rust | subtotal | 6 041 | 5.6% |
| pure Rust | `sign`, measured | 108 205 | 100% |
| pure Rust | arithmetic only, upper bound | 102 164 | — |
| CryptOpt assembly | subtotal of the same three | 6 022 | 5.4% |
| CryptOpt assembly | `sign`, measured | 112 181 | 100% |
| CryptOpt assembly | arithmetic only, upper bound | 106 159 | — |

Against that upper bound the sign ratio is at most 0.72 pure Rust and 0.54
with the assembly field, so the signing win survives the caveat in both
configurations. It comes from the fixed-base comb: Graviola's README states
that its P-384 base-point multiplication uses the same 5-bit window as its
variable-point one, "leaving some P384 base point performance on the table".

The subtraction is bounded and not exact. The three components are timed
outside `sign`, because `rfc6979_sign_with_random` is private and the `Hash`
parameter cannot be instantiated downstream; the DRBG figure is the
reconstruction described above, over Graviola's own `Hmac<Sha384>`. Whatever
else `sign` does — the private-key encode, the zeroise, the rejection test —
is unaccounted, so the arithmetic-only row is an upper bound and the ratio
against it is an upper bound too. **What could not be isolated:** Graviola's
arithmetic-only signing cost exactly, and its internal HMAC_DRBG object,
which is `pub(crate)`.

On the verify side the hash is 193 ns of a 206 189 ns row, 0.09%, so removing
it moves the pure-Rust ratio from 2.011 to 2.013 and the assembly ratio from
1.538 to 1.540. The message is 25 bytes, one SHA-384 block; a longer message
would raise Graviola's column and flatter ours, which is why a short one is
used.

### Against the previous kernel

The previous kernel used the Fermat scalar inverse and reached `u1*G + u2*Q`
through `p384_scalar_mul_base`, `p384_scalar_mul` and `p384_point_add`. Only
the ratio columns compare across the two dates: the RustCrypto baseline was
457 677 – 458 128 ns/op for sign and 838 679 – 839 781 for verify on the
earlier run and 505 166 – 506 812 and 927 494 – 951 083 here, on the same
machine, binary and pinning, with a Rocq worker on the box this time.

| configuration | op | ratio, previous | ratio, now |
|---|---|---|---|
| fiat-crypto field, pure Rust | sign | 0.22 | 0.16 |
| fiat-crypto field, pure Rust | verify | 0.56 | 0.49 |
| CryptOpt assembly field | sign | 0.18 | 0.12 |
| CryptOpt assembly field | verify | 0.42 | 0.36 |

Nothing got slower. The movement is attributable to the two changes
separately, and the two micro-benchmarks account for it within 2%. Scaling
the previous absolute figures by the RustCrypto baseline's own movement puts
the previous kernel at 111.4 µs and 520.9 µs (pure Rust) and 93.3 µs and
401.2 µs (assembly) under this run's conditions. Signing calls the inverse
once and not the two-term multiply, so it should drop by the inverse's
30.8 µs; verification calls both, so it should drop by 30.8 µs plus the
34.7 µs (pure Rust) or 24.3 µs (assembly) of the multiply:

| configuration | op | previous, rescaled | predicted | measured |
|---|---|---|---|---|
| fiat-crypto field, pure Rust | sign | 111.4 µs | 80.6 µs | 80.5 µs |
| fiat-crypto field, pure Rust | verify | 520.9 µs | 455.4 µs | 456.0 µs |
| CryptOpt assembly field | sign | 93.3 µs | 62.5 µs | 62.3 µs |
| CryptOpt assembly field | verify | 401.2 µs | 346.0 µs | 339.1 µs |

The rescaling is an estimate, not a measurement: it assumes our side and
RustCrypto's were slowed by the same factor between the two dates. The
micro-benchmarks are direct, and they are what the attribution rests on.

These are whole-operation numbers for an orchestration the compiler emitted
over our own verified leaves. They say nothing about the correctness of the emit;
that is the Lean equivalence proof, and a passing KAT is not a substitute for
it (`../AGENTS.md`, "KAT vs correctness proof").

## Measured, the s2n-bignum backend

2026-09-16, same machine as the tables above (AMD Ryzen 7 PRO 7840U, Zen 4,
8 cores / 16 threads, Linux 7.0.0-31-generic, rustc 1.93.0, `--release`,
pinned to core 15). **The box was busier than during the run recorded above:
load average 2.4 to 4.9, with Lean workers on other cores throughout.** Every
absolute figure in this section is inflated by that — RustCrypto's sign
column reads 582 to 705 µs here against 462 to 469 µs there — so read the
ratios, which the round-robin interleaving protects, and not the absolutes.
Four processes were run, two per AUCurves field configuration, and the spread
between them is quoted on every row.

### The P-384 field multiply, which decides what could be built

Before any configuration was built on our own field kernels, the two emitted
P-384 field kernels in the tree were measured against s2n-bignum's. Neither
had been measured against anything recorded: `bench/framework/geomean_ratios.tsv`
has no P-384 row, and `bench/p384_fieldmul_compare/README.md`'s bench section
is deferred.

`src/bin/fieldbench.rs`, `--features s2n,emit-field`. Known-answer gate
first, 100 361 operand pairs per arm — all pairs of corner operands plus
100 000 random pairs below `p` — every output byte-identical to a reference
built from `bignum_montmul_p384` itself, and every output below `p`. No
timing is printed unless every arm passes. Then a serial dependent chain,
301 samples of 2000 multiplies, arms interleaved in rotating order within
each sample. The figure is invariant-TSC reference cycles, minimum and
median.

| arm | computes | min cyc | med cyc | min ns | ratio to s2n |
|---|---|---|---|---|---|
| `p384_montmul_proven`, CatCrypt emit | `x y R⁻¹ mod p`, `R = 2^384` | 330.1 | 343.7 | 100.1 | **2.58** |
| `bignum_montmul_p384`, s2n-bignum | `x y R⁻¹ mod p`, `R = 2^384` | 127.9 | 132.1 | 38.8 | 1.00 |
| `p384::fp_mul`, fiat-crypto Rust | `x y R⁻¹ mod p` | 210.2 | 219.8 | 63.8 | 1.64 |
| `p384::fp_mul`, CryptOpt assembly | `x y R⁻¹ mod p` | 144.6 | 150.3 | 43.9 | 1.23 |
| `p384_mul_x86_from_lean`, CatCrypt emit | `x y mod p`, ordinary domain | 299.5 | 311.1 | 90.9 | 2.34 |

The two CryptOpt and fiat rows come from two processes (the field is a
compile-time choice); the other three rows are from the pure-Rust process and
reproduce in the assembly process to within 3%.

**The first row is the answer, and it is a loss.** Our emitted P-384
Montgomery multiply is **2.58× slower** than s2n-bignum's on the minima and
2.60× on the medians, on the same function, the same Montgomery domain, the
same six-limb layout and the same calling convention. Three runs gave 2.573,
2.575 and 2.581 on the minima, so the figure is not noise. It is also slower
than the fiat-crypto Rust it would replace, by a factor of 1.57.

This is consistent with what `bench/p384_fieldmul_compare/README.md` already
says of the other kernel: correctness-first, unscheduled emit, with no
register-residence or scheduling pass applied. Nothing about the result is
surprising and nothing about it is hidden.

The Solinas row is a different shape of comparison and not a like-for-like
one: it computes `x y mod p` in the ordinary domain through a 6×6 MULX/ADCX
schoolbook and a derived signed eleven-term Solinas reduction, where the
montmul rows compute `x y R⁻¹ mod p`. It does more of one kind of work and
none of another. It is timed as the other emitted P-384 field kernel; it does not substitute
for the montmul.

**Consequence for the backends.** A fourth configuration with our emitted
field kernels under the group law was not built. On these numbers it would be
slower than all three existing ones and would answer no question the others
do not. The field layer is where the work is, and until the emitted montmul
is within reach of 127 cycles there is nothing to compose it into. Note also
that a mixed configuration would have to be internally consistent about the
Montgomery domain: `p384_montmul_proven` and `bignum_montmul_p384` agree on
`R = 2^384`, but `p384_mul_x86_from_lean` is in the ordinary domain and
cannot be dropped in beside either.

At the group layer there is nothing to compose at all. The six-limb emitted
point-operation stack has uninhabited realizer bundles and a ladder that
cannot read its scalar, so the group law in every configuration here comes
from AUCurves or from s2n-bignum.

### The base-point multiply, the first orchestration lever

The comb against the archive's own windowed multiplication, on identical
s2n-bignum arithmetic. 15 repetitions of 200 iterations, round-robin. The
second row is the route Graviola takes for its base point.

| route | ns/op, pure process | ns/op, assembly process | ratio |
|---|---|---|---|
| `p384_montjscalarmul` on `G` (as Graviola) | 151 409 | 128 834 | 1.00 |
| fixed-base comb, `w = 5`, `p384_montjmixadd` | 29 261 | 25 433 | **0.19 – 0.20** |
| AUCurves fixed-base comb, `w = 5`, for scale | 102 404 | 64 091 | 0.68 / 0.50 |

The first two rows run the same field operations and the same point
operations. They differ only in how the multiplication is organised, so the
ratio is the comb's alone: **5.1× on the base-point multiply**, from trading
three hundred and eighty-four doublings for a 229 KB table. The repeat
process gave 0.19 and 0.19.

### The two-term multiply, the second lever

| backend | route | ns/op, pure | ns/op, assembly | ratio |
|---|---|---|---|---|
| `aucurves` | `mul_base` + `mul` + `add`, 3 leaves | 1 114 346 | 733 373 | 1.00 |
| `aucurves` | interleaved, `w = 5` | 648 330 | 422 349 | 0.58 |
| `s2n` | `mul_base` + `mul` + `add`, 3 leaves | 302 991 | 279 040 | 1.00 |
| `s2n` | interleaved, `w = 5` | 185 161 | 169 004 | **0.61** |

The `s2n` split route, 303 µs and 279 µs, is within a few percent of
Graviola's whole verify row measured in the same processes (298 µs and 286
µs), which is the expected reading of a verification that performs two
separate window multiplications and one addition.

### The scalar inverse

15 repetitions of 4000 iterations, round-robin, pure-Rust process.

| inverse | ns/op | vs Fermat |
|---|---|---|
| Fermat `a^(n-2)`, 383 squarings + 287 multiplications | 45 742 | 1.00 |
| divstep, 15 × 59, `safegcd_p384_order` | 3 045 | 0.07 |
| base-field `fp_inv`, for scale | 3 371 | 0.07 |
| s2n-bignum generic `bignum_modinv` at the group order | 3 119 | 0.07 |

s2n-bignum has **no** group-order inverse for P-384: `bignum_inv_p384` and
`bignum_montinv_p384` are both modulo the field prime. What it has is the
generic `bignum_modinv` for an arbitrary odd modulus, and that is the last
row. It computes the same function as the divstep inverse
(`tests/s2n.rs::generic_modinv_matches_the_divstep_inverse`, sixteen random
scalars) and runs within 3% of it across all four processes, sometimes above
and sometimes below. On that showing there is no reason to swap, and the
`s2n` backend keeps the crate's divstep inverse, as every other backend does.

### Whole operation, three backends

15 repetitions of 300 iterations, one process per AUCurves field
configuration, every side interleaved round-robin inside each. The `s2n`
rows appear in both processes and should agree; the spread between them
bounds the run-to-run drift.

Pure-Rust process, first run:

| op | backend | ours ns/op | RustCrypto | vs RC | Graviola | vs GV |
|---|---|---|---|---|---|---|
| sign | `aucurves` | 108 486 | 704 823 | 0.15 | 176 435 | 0.61 |
| sign | `s2n` | 34 459 | 704 823 | 0.05 | 176 435 | **0.20** |
| verify | `aucurves` | 649 971 | 1 294 174 | 0.50 | 297 669 | 2.18 |
| verify | `s2n` | 193 854 | 1 294 174 | 0.15 | 297 669 | **0.65** |

CryptOpt-assembly process, first run:

| op | backend | ours ns/op | RustCrypto | vs RC | Graviola | vs GV |
|---|---|---|---|---|---|---|
| sign | `aucurves` | 79 333 | 626 086 | 0.13 | 153 930 | 0.52 |
| sign | `s2n` | 32 005 | 626 086 | 0.05 | 153 930 | **0.21** |
| verify | `aucurves` | 431 953 | 1 162 307 | 0.37 | 286 174 | 1.51 |
| verify | `s2n` | 167 488 | 1 162 307 | 0.14 | 286 174 | **0.59** |

Four processes, the ratios that matter:

| ratio | pure #1 | pure #2 | asm #1 | asm #2 |
|---|---|---|---|---|
| `s2n` sign / Graviola | 0.20 | 0.20 | 0.21 | 0.21 |
| `s2n` verify / Graviola | 0.65 | 0.59 | 0.59 | 0.62 |
| `s2n` sign / RustCrypto | 0.05 | 0.05 | 0.05 | 0.05 |
| `s2n` verify / RustCrypto | 0.15 | 0.14 | 0.15 | 0.14 |
| `aucurves` verify / Graviola | 2.18 | 2.04 | 1.51 | 1.51 |

The `aucurves` ratios reproduce the run recorded in the section above — 0.15
to 0.16 and 0.50 for sign and verify against RustCrypto pure-Rust, 0.13 and
0.37 with the assembly field, 1.51 against Graviola — which is the check that
the harness change did not move them.

**On identical s2n-bignum arithmetic, our orchestration beats Graviola on
both operations: sign at 0.20 to 0.21, verify at 0.59 to 0.65.** Graviola's
sign column is its whole API and not like for like; subtracting the three
components it performs and our kernel does not (SHA-384, the system-RNG read
and the RFC 6979 HMAC_DRBG nonce, 5.1% and 5.4% of the row) puts the bound at
0.21 pure and 0.22 assembly, so the signing win survives the caveat with room
to spare. The verify row needs no caveat beyond the 0.09% message hash.

Where the two wins come from, in the same processes: the base-point multiply
at 0.19 of the route Graviola takes, and the two-term multiply at 0.61 of the
two-separate-multiplications route its verification takes. Those two
micro-benchmarks account for the two whole-operation rows.

**The `aucurves` verify row against Graviola is still a loss**, 1.51 with the
assembly field, unchanged from the earlier run. That row compares our group
law on a CryptOpt field against s2n-bignum assembly, which is a different
question from the one the `s2n` row answers, and both are kept for that
reason. What the `s2n` row shows is that the 1.51 is not an orchestration
deficit: with the arithmetic held fixed the same orchestration wins by a
factor of 1.6 on the same operation.

## Measured, all field configurations (2026-09-17)

One process per AUCurves field configuration, run one after another, each with
`BENCH_SECTIONS=ecdsa,dhkem BENCH_REPS=15 BENCH_ITERS=300
BENCH_MICRO_ITERS=4000`, `--features s2n,production`, core 15, OpenSSL 4.1.0-dev
for the native DHKEM row. The load average was 2.8–3.8 in the first three
processes. The last two processes, with `P384_S2N_FIELD` set to
`bench/s2n_import/gen/bignum_montmul_p384_encoded.s` and to the framed file with
its symbol renamed, ran later on a quieter machine, and their opponent columns
are 5–10 % lower than in the first three. Compare rows within one process only.
Median µs per operation; the `aucurves` rows change with the field, the `s2n`
rows are the s2n-bignum backend in the same process.

| field under `aucurves` | sign `aucurves` | sign `s2n` | verify `aucurves` | verify `s2n` | encap `aucurves` | decap `aucurves` | base-point comb `aucurves` |
|---|---|---|---|---|---|---|---|
| fiat-crypto Rust | 94.9 | 29.3 | 543.7 | 161.0 | 560.6 | 454.8 | 82.0 |
| CryptOpt assembly | 68.7 | 28.0 | 380.4 | 151.7 | 386.3 | 328.0 | 59.2 |
| s2n-bignum montmul and montsqr | 56.2 | 26.5 | 293.0 | 141.9 | 310.6 | 262.9 | 49.8 |
| our encoded montmul (square as montmul) | 53.1 | 25.0 | 272.8 | 132.3 | 288.4 | 241.6 | 44.3 |
| our framed montmul (square as montmul) | 53.1 | 25.0 | 278.0 | 132.6 | 287.7 | 240.5 | 44.6 |

Ratios, ours over the opponent in the same process, for the pure-Rust process
(`aucurves` / `s2n`):

| op | RustCrypto | Graviola | OpenSSL 3.0 | BoringSSL | AWS-LC |
|---|---|---|---|---|---|
| sign | 0.16 / 0.05 | 0.65 / 0.20 | 0.13 / 0.04 | 0.20 / 0.06 | 1.26 / 0.39 |
| verify | 0.51 / 0.15 | 2.16 / 0.64 | 0.91 / 0.27 | 1.12 / 0.33 | 3.12 / 0.92 |

and for the process with our encoded montmul:

| op | RustCrypto | Graviola | OpenSSL 3.0 | BoringSSL | AWS-LC |
|---|---|---|---|---|---|
| sign | 0.10 / 0.05 | 0.45 / 0.21 | 0.08 / 0.04 | 0.13 / 0.06 | 0.80 / 0.38 |
| verify | 0.29 / 0.14 | 1.27 / 0.61 | 0.52 / 0.25 | 0.65 / 0.31 | 1.80 / 0.87 |

The Graviola sign column is its whole API (hash, RNG and RFC 6979 nonce
included) and is not like for like; the verify column is. The two montmul files
differ only in the frame (red-zone moves or `push`/`pop`), and their rows agree
within the run-to-run spread.

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
checks it against the directory. Both files have been in `gen/` since 2026-09-17; the tables below marked
"transcription" predate that, and [§ Emitted kernels](#emitted-kernels) holds
the run on the emitted sources.

### Reference and opponents

What exists on this machine, established from the source in the registry
cache and the checkouts, not assumed:

| implementation | P-384 DHKEM? | used here as |
|---|---|---|
| `src/dhkem_ref.rs` | — | independent reference: RustCrypto `p384` 0.13.1 `ecdh::diffie_hellman` and `hkdf` 0.12.4 streaming, no leaf shared |
| hpke-rs 0.7.0, `hpke-rs-rust-crypto` 0.7.0 | **yes**: the `DhKemP384` arms of `dh`, `secret_to_public`, `kem_key_gen` in `hpke-rs-rust-crypto-0.7.0/src/lib.rs`, over RustCrypto `p384` 0.13 and `hkdf` 0.13 | native API (`Hpke::setup_sender` / `setup_receiver`), and a reconstruction over its provider trait (`src/hpke_rs.rs`) |
| hpke-rs 0.7.0, `hpke-rs-libcrux` 0.7.0 | only through RustCrypto `p384` **0.14.0-rc.8** behind `rustcrypto-p-curves` (`hpke-rs-libcrux-0.7.0/src/lib.rs`, lines 15-19 and 75-84); `libcrux-ecdh` 0.0.8 itself has no P-384 (`src/ecdh.rs`: `derive` returns `UnknownAlgorithm`) | not used: `p384` 0.14.0-rc.8 is not in the registry cache |
| Graviola 0.4.1 | ECDH yes (`key_agreement::p384`, `mid/p384.rs`), HMAC yes, no HKDF, no HPKE | reconstruction (`src/grav.rs`) |
| BoringSSL `956bac6e4db9` | its HPKE has KEMs `0x0010`, `0x0020`, X-Wing and ML-KEM only (`include/openssl/hpke.h`) | reconstruction from `EC_POINT_*`, `ECDH_compute_key`, `HKDF_extract`/`HKDF_expand` (`src/bssl.rs`) |
| OpenSSL 3.0.13 (system) | no HPKE (no `OSSL_HPKE_*` export) and no DHKEM operation; both arrived in 3.2 | reconstruction from `EVP_PKEY_derive` and `EVP_KDF "HKDF"` (`src/ossl_kem.rs`) |
| OpenSSL 3.6.0, `/opt/microsoft/mdatp/lib/libcrypto.so.3` | **yes**: `EVP_PKEY_encapsulate` / `EVP_PKEY_decapsulate` with `operation = "DHKEM"` (the layer under `OSSL_HPKE_encap`) | native API, and the same reconstruction |
| OpenSSL 4.1.0-dev, `bench_refs/openssl-install/lib/libcrypto.so.4` | **yes**, the same operation | the same two roles, when `P384_OPENSSL36_LIBCRYPTO` names it |
| AWS-LC 5.9.0 at `f3798b6fe6a8` | its HPKE has KEMs X25519 (`0x0020`) and ML-KEM only (`include/openssl/hpke.h:41-44`); no P-384 KEM | reconstruction from `EC_POINT_*`, `ECDH_compute_key`, `HKDF_extract`/`HKDF_expand`, in the shape of the BoringSSL one (`src/awslc.rs`) |

The OpenSSL 3.6.0 library is the copy Microsoft Defender for Endpoint ships,
used as found and loaded with `dlopen` (override with
`P384_OPENSSL36_LIBCRYPTO`; the tests skip it when absent). Its build
configuration is not published. It exports no `EC_GFp_nistp*_method`, which
3.x exports exactly when `enable-ec_nistp_64_gcc_128` is set, so secp384r1
gets no dedicated method (`crypto/ec/ec_curve.c`) and runs the generic
`EC_GFp_mont_method`; it carries the CRYPTOGAMS `x86_64-mont` code. That is
an inference from its exports and strings.

The OpenSSL 4.1.0-dev library in `bench_refs/openssl-install` was built
from the `bench_refs/openssl` checkout; its `configdata.pm` lists
`no-ec_nistp_64_gcc_128`, under which `crypto/ec/ec_curve.c:2722-2730`
gives secp384r1 no method, and `nm` finds no `nistp384` symbol in it, so it
too runs the generic `EC_GFp_mont_method` (the `x86_64-mont` path is
inferred, not traced). `OpenSSL_version_num()` reports `0x40100000`; the
tests and the benchmark label it `openssl 4.1` from that number.

AWS-LC's P-384 is described in
[§ AWS-LC](#aws-lc-the-third-production-opponent): a dedicated method over
s2n-bignum assembly. `ECDH_compute_key` copies the peer point into a fresh
`EC_KEY` and runs `EC_KEY_check_fips` on it on every call, and that cost is
inside its DHKEM rows.

**Test vectors.** No official DHKEM(P-384) vectors are on this machine. The
CFRG `test-vectors.json` in `~/Claude/libcrux/tests/hpke_test_vectors.json`
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

`tests/dhkem_production.rs`, 6 tests under `--features production`:
BoringSSL, OpenSSL 3.0, OpenSSL 3.2+ and AWS-LC reconstructions agree bit
for bit with our `Encap` (16 cases per backend) and interoperate both ways;
the OpenSSL 3.2+ native DHKEM
with `ikme` gives the same `(enc, ss)` as our `Encap` with
`skE = DeriveKeyPair(ikme)`, and decapsulates ours; the invalid strings above
(plus prefix `0x07` and `x = p` for `(0, sqrt b)`) and out-of-range keys are
checked on every C side, each side declaring which of the divergences below
it has; `awslc_accepts_the_hybrid_encoding` pins AWS-LC's. The AWS-LC cases
print `SKIP:` and pass when its library is absent. All six pass with the
OpenSSL 3.2+ side set to Defender's 3.6.0 and, separately, to the 4.1.0-dev
build.

### Divergences of the opponents from RFC 9180

Our kernels reject every invalid input above. Five opponents accept some
(Graviola, the three OpenSSL builds and the AWS-LC reconstruction),
and each divergence is pinned by a test rather than skipped:

1. **Graviola 0.4.1 accepts a coordinate `>= p`** when it reduces to a curve
   point. `AffineMontPoint::from_x962_uncompressed`
   (`graviola-0.4.1/src/mid/p384.rs`, lines 249-273) converts both
   coordinates to the Montgomery domain, which reduces them mod `p`, and
   checks only the curve equation. `x = p` with `y = sqrt(b)` is accepted as
   `(0, sqrt b)` (`tests/dhkem.rs::graviola_accepts_a_non_canonical_x_coordinate`).
   RustCrypto, hpke-rs, BoringSSL, AWS-LC and every OpenSSL reject it.
2. **OpenSSL 3.0.13, 3.6.0 and 4.1.0-dev accept the X9.62 hybrid
   encoding**, prefix
   `0x06` or `0x07` whose low bit matches the parity of `y`, both on key
   import and in the native DHKEM `Decap` (`crypto/ec/ecp_oct.c` admits
   `POINT_CONVERSION_HYBRID`; `ec_kem.c` parses `enc` through
   `EC_KEY_oct2key`). RFC 9180 §7.1.1 specifies the uncompressed form.
   The shared secret they return uses the point's DH value and the hybrid
   bytes in the KEM context.
   **The AWS-LC reconstruction accepts it too**, as `enc` in `Decap` and as
   `pkR` in `Encap`, and checks only that the parity bit matches:
   `EC_POINT_oct2point` masks the low bit of the prefix and dispatches
   `0x06`/`0x07` to `ec_point_from_hybrid`
   (`crypto/fipsmodule/ec/oct.c:17-26`, `:95-114`, `:146-154`). BoringSSL,
   from which AWS-LC forked, rejects both. This is a property of AWS-LC's
   point decoder as the reconstruction uses it; AWS-LC offers no P-384 DHKEM
   of its own that could be tested.
3. **OpenSSL accepts a private key `>= n`** that is non-zero mod `n`, and
   computes with `sk mod n`: `EVP_PKEY_fromdata` imports any 48-byte value,
   and the DHKEM's `eckey_check` (`ec_kem.c`, lines 68-99) only rejects
   `sk = 0 mod n`. `n + 1` and `2^384 - 1` are accepted; `0` and `n` are not.
   The 4.1.0-dev build behaves the same. AWS-LC rejects all four
   out-of-range keys: `EC_KEY_set_private_key` fails for a value not below
   `n` (`ec_bignum_to_scalar`, `crypto/fipsmodule/ec/ec_key.c:175-197`).

### Measured

2026-09-16, the machine of [§ Measured](#measured), rustc 1.93.0,
`--release`, pinned to core 15, `BENCH_SECTIONS=dhkem BENCH_REPS=15
BENCH_ITERS=300`, one process per AUCurves field configuration, every arm
interleaved round-robin within the process. **The load average was 6.6 to
8.7 throughout** — two C compiler processes, Lean and Python were running on
other cores — so these are figures from a loaded machine. The `s2n` rows
appear in all three processes and differ by up to 7% (encap 188.7 to 195.4
µs, decap 149.8 to 161.0 µs), which bounds the run-to-run drift. Both DHKEM
kernels were the transcription (`gen/` held no DHKEM file).

Median µs per operation. `pure`, `asm` and `s2n-f` are the processes with the
AUCurves field in fiat-crypto Rust, the CryptOpt assembly, and s2n-bignum's
`bignum_montmul_p384`/`bignum_montsqr_p384` (`P384_S2N_FIELD`); only the
`ours/aucurves` row runs a different field in each, the others show the drift.

| op | implementation | kind | arithmetic | pure | asm | s2n-f |
|---|---|---|---|---|---|---|
| encap | ours, `aucurves` | transcription | AUCurves RCB over the column's field | 692.5 | 484.4 | 413.2 |
| encap | ours, `s2n` | transcription | s2n-bignum asm | 195.4 | 188.7 | 192.0 |
| encap | reference | reconstruction | RustCrypto `p384` 0.13.1, fiat Rust | 1303.7 | 1312.4 | 1223.7 |
| encap | hpke-rs `setup_sender` | native, + DeriveKeyPair + key schedule | RustCrypto `p384` 0.13.1 | 1411.8 | 1303.1 | 1237.8 |
| encap | hpke-rs provider | reconstruction | RustCrypto `p384` 0.13.1 | 1337.4 | 1282.5 | 1240.7 |
| encap | Graviola 0.4.1 | reconstruction | s2n-bignum asm | 348.0 | 320.3 | 320.6 |
| encap | BoringSSL | reconstruction | generic Montgomery C, `bn_mul_mont_nohw` | 1132.9 | 1064.1 | 1006.5 |
| encap | OpenSSL 3.0.13 | reconstruction | `EC_GFp_mont`, `x86_64-mont` | 2346.8 | 2280.3 | 2191.7 |
| encap | OpenSSL 3.6.0 | reconstruction | `EC_GFp_mont`, `x86_64-mont` (inferred) | 1854.6 | 1787.7 | 1720.3 |
| encap | OpenSSL 3.6.0 DHKEM | native, + DeriveKeyPair | as above | 1780.1 | 1730.3 | 1666.1 |
| decap | ours, `aucurves` | transcription | AUCurves RCB over the column's field | 591.7 | 415.5 | 341.0 |
| decap | ours, `s2n` | transcription | s2n-bignum asm | 161.0 | 150.6 | 149.8 |
| decap | reference | reconstruction | RustCrypto `p384` 0.13.1 | 671.9 | 657.9 | 608.4 |
| decap | hpke-rs `setup_receiver` | native, + pk(skR) + key schedule | RustCrypto `p384` 0.13.1 | 1333.8 | 1319.1 | 1256.7 |
| decap | hpke-rs provider | reconstruction | RustCrypto `p384` 0.13.1 | 663.6 | 631.8 | 622.7 |
| decap | Graviola 0.4.1 | reconstruction | s2n-bignum asm | 176.7 | 170.0 | 164.0 |
| decap | BoringSSL | reconstruction | generic Montgomery C | 546.7 | 517.8 | 495.6 |
| decap | OpenSSL 3.0.13 | reconstruction | `EC_GFp_mont` | 1462.1 | 1440.7 | 1412.8 |
| decap | OpenSSL 3.6.0 | reconstruction | `EC_GFp_mont` (inferred) | 914.5 | 957.5 | 909.3 |
| decap | OpenSSL 3.6.0 DHKEM | native | as above | 896.8 | 875.1 | 864.2 |

The ratios that decide the comparison, ours / theirs:

| ratio | pure | asm | s2n-f |
|---|---|---|---|
| `s2n` encap / Graviola | 0.56 | 0.59 | 0.60 |
| `s2n` decap / Graviola | 0.91 | 0.89 | 0.91 |
| `aucurves` encap / Graviola | 1.99 | 1.51 | 1.29 |
| `aucurves` decap / Graviola | 3.35 | 2.44 | 2.08 |
| `aucurves` encap / hpke-rs, adjusted | 0.50 | 0.38 | 0.34 |
| `aucurves` decap / hpke-rs, adjusted | 0.89 | 0.61 | 0.55 |
| `s2n` encap / hpke-rs, adjusted | 0.14 | 0.15 | 0.16 |
| `s2n` decap / hpke-rs, adjusted | 0.24 | 0.22 | 0.24 |
| `aucurves` decap / BoringSSL | 1.08 | 0.80 | 0.69 |
| `s2n` encap / OpenSSL 3.6 DHKEM | 0.11 | 0.11 | 0.12 |
| `s2n` decap / OpenSSL 3.6 DHKEM | 0.18 | 0.17 | 0.17 |

"Adjusted" subtracts from hpke-rs's native row the separately timed parts
our kernel does not perform: the base-mode key schedule (10.0 to 11.2 µs)
from both, the KDF part of `DeriveKeyPair` (2.7 to 2.9 µs, timed over `hkdf`
0.12 as an estimate) from encap, and `pk(skR)` (621 to 657 µs) from decap.
hpke-rs's `setup_receiver` recomputes `pkR` from `skR` on every call
(`dh_kem::decaps`), which roughly doubles its decapsulation cost. The
OpenSSL 3.6 DHKEM encap row still includes `DeriveKeyPair`, whose KDF part
is under 5 µs of its 1.7 ms.

**The HKDF share is small.** `ExtractAndExpand` alone, µs: ours 3.0 to 3.8,
the reference 3.0 to 3.1, hpke-rs's provider 2.9 to 3.7, Graviola's HMAC 2.5
to 2.9, BoringSSL 2.4 to 2.6, OpenSSL 3.0 4.3 to 5.0, OpenSSL 3.6 4.0 to 4.7.
It is 0.5 to 1.0% of our `aucurves` rows and 1.9 to 2.3% of our `s2n` rows;
the rest is the two scalar multiplications (encap) or one (decap).

**Where we lose.**

* **`aucurves` against Graviola, in every field configuration**: encap 1.29
  to 1.99, decap 2.08 to 3.35. This is our group law and variable-base
  multiply over fiat-crypto, CryptOpt or s2n-bignum field code against
  s2n-bignum's Jacobian point operations; with the arithmetic held equal
  (the `s2n` row) the same orchestration wins on both operations, so the
  loss is in the arithmetic under the leaves, not in the emitted sequence.
  Decap loses by more because it has no fixed-base multiply, where the comb
  recovers ground.
* **`aucurves` pure-Rust decap against the BoringSSL reconstruction**: 1.08.
  BoringSSL runs C with an assembly Montgomery loop, so this is not
  same-tier; with an assembly field under AUCurves the row is 0.80 or 0.69.
* **The `s2n` decap margin over Graviola is narrow**: 0.89 to 0.91, within
  the order of the drift between processes. Both run a width-5 window over
  the same point operations; our decap has no comb to spend.
* **Our KDF leaves take 1.3 to 1.5 times as long as BoringSSL's HKDF**, the
  fastest here, about 1 µs per operation; against the reference and
  hpke-rs's provider the difference is within the noise.

Against the same-tier production opponent, hpke-rs over RustCrypto
(`aucurves` pure-Rust row), ours is faster: 0.50 encap and 0.89 decap
adjusted, 0.49 and 0.44 unadjusted. Against the C libraries in these three
processes every row of ours is faster except the BoringSSL decap above.

**AWS-LC and OpenSSL 4.1.0-dev**, a later single process: pure-Rust
AUCurves build, `BENCH_SECTIONS=dhkem,ecdsa BENCH_REPS=15 BENCH_ITERS=300`,
core 15, `P384_OPENSSL36_LIBCRYPTO` set to the 4.1.0-dev build, load average
4.0 before and 6.7 after (the run whose ECDSA rows are in
[§ AWS-LC](#aws-lc-the-third-production-opponent)). Median µs per operation,
and ours over theirs:

| op | implementation | kind | µs | `aucurves` / this | `s2n` / this |
|---|---|---|---|---|---|
| encap | ours, `aucurves` | transcription | 627.6 | 1.00 | 0.27 |
| encap | ours, `s2n` | transcription | 170.3 | 3.68 | 1.00 |
| encap | Graviola 0.4.1 | reconstruction | 301.2 | 2.08 | 0.57 |
| encap | BoringSSL | reconstruction | 974.9 | 0.64 | 0.17 |
| encap | AWS-LC 5.9.0 | reconstruction | 200.8 | **3.13** | 0.85 |
| encap | OpenSSL 4.1.0-dev | reconstruction | 2261.1 | 0.28 | 0.08 |
| encap | OpenSSL 4.1.0-dev DHKEM | native, + DeriveKeyPair | 1548.0 | 0.41 | 0.11 |
| decap | ours, `aucurves` | transcription | 517.6 | 1.00 | 0.27 |
| decap | ours, `s2n` | transcription | 138.1 | 3.75 | 1.00 |
| decap | Graviola 0.4.1 | reconstruction | 151.3 | 3.42 | 0.91 |
| decap | BoringSSL | reconstruction | 477.6 | **1.08** | 0.29 |
| decap | AWS-LC 5.9.0 | reconstruction | 138.3 | **3.74** | **1.00** |
| decap | OpenSSL 4.1.0-dev | reconstruction | 1539.7 | 0.34 | 0.09 |
| decap | OpenSSL 4.1.0-dev DHKEM | native | 789.3 | 0.66 | 0.17 |

AWS-LC's `ExtractAndExpand` alone took 2.6 µs, OpenSSL 4.1.0-dev's 3.1 µs.

* **`s2n` decap against AWS-LC is a tie**: 138.1 against 138.3 µs, a ratio
  of 1.00. Both run the same s2n-bignum field and the same assembly
  variable-base multiply by name (`p384_montjscalarmul`), plus the SEC1
  decoding and validation and the KDF; AWS-LC's figure also includes the
  per-call `EC_KEY` copy and `EC_KEY_check_fips`. `s2n` encap is 0.85;
  encap adds a fixed-base multiply, which is AWS-LC's C comb on one side and
  `src/comb_s2n.rs` on the other, and the split of the difference was not
  measured.
* **`aucurves` pure Rust loses to AWS-LC** by 3.13 (encap) and 3.74
  (decap), the same shape as the Graviola loss above: Rust group law over
  the fiat-crypto Rust field against s2n-bignum assembly.
* The OpenSSL 4.1.0-dev reconstruction is slower than its own native DHKEM
  (2261 against 1548 µs encap, 1540 against 789 µs decap). The
  reconstruction builds its `EVP_PKEY` objects and KDF contexts on every
  call; its cost was not decomposed.

### Emitted kernels

`lake exe emit-p384-rust` wrote `gen/p384_dhkem_encap.rs` and
`gen/p384_dhkem_decap.rs` on 2026-09-17; the build reports both as emitted.
`P384_NO_CRYPTOPT=1 cargo test --offline --release --features s2n,production`
passes 116 tests on them. Bench: pure-Rust AUCurves build,
`BENCH_SECTIONS=dhkem BENCH_REPS=15 BENCH_ITERS=300`, core 15,
`P384_OPENSSL36_LIBCRYPTO` set to the 4.1.0-dev build, load average 1.7 before
and 2.5 after. Median µs per operation, and ours over theirs:

| op | implementation | kind | µs | `aucurves` / this | `s2n` / this |
|---|---|---|---|---|---|
| encap | ours, `aucurves` | emitted | 523.2 | 1.00 | 0.27 |
| encap | ours, `s2n` | emitted | 140.2 | 3.73 | 1.00 |
| encap | Graviola 0.4.1 | reconstruction | 240.7 | 2.17 | 0.58 |
| encap | AWS-LC 5.9.0 | reconstruction | 163.0 | 3.21 | 0.86 |
| encap | hpke-rs 0.7.0 | native, + DeriveKeyPair, + key schedule | 1007.1 | 0.52 | 0.14 |
| encap | BoringSSL | reconstruction | 852.3 | 0.61 | 0.16 |
| encap | OpenSSL 4.1.0-dev DHKEM | native, + DeriveKeyPair | 1327.5 | 0.39 | 0.11 |
| decap | ours, `aucurves` | emitted | 440.1 | 1.00 | 0.27 |
| decap | ours, `s2n` | emitted | 116.7 | 3.77 | 1.00 |
| decap | Graviola 0.4.1 | reconstruction | 123.0 | 3.58 | 0.95 |
| decap | AWS-LC 5.9.0 | reconstruction | 118.7 | 3.71 | 0.98 |
| decap | hpke-rs 0.7.0 | native, + pk(skR), + key schedule | 998.5 | 0.44 | 0.12 |
| decap | BoringSSL | reconstruction | 427.8 | 1.03 | 0.27 |
| decap | OpenSSL 4.1.0-dev DHKEM | native | 664.8 | 0.66 | 0.18 |

The emitted `s2n` rows are 0.86 (encap) and 0.98 (decap) of AWS-LC and 0.58
and 0.95 of Graviola; the decap margins are within the run-to-run drift
recorded above. The `aucurves` pure-Rust rows lose to Graviola and AWS-LC by
2.2–3.7 and to BoringSSL decap by 1.03. All rows of this run are faster than
the earlier runs, including the opponents, because the machine was less
loaded; compare within a run only.

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
    P384_S2N_FIELD=$PWD/../reference_install/s2n-bignum/x86/libs2nbignum.a \
      BENCH_SECTIONS=dhkem BENCH_REPS=15 BENCH_ITERS=300 taskset -c 15 ./target/release/bench

    # the AWS-LC and OpenSSL 4.1.0-dev run recorded above
    P384_NO_CRYPTOPT=1 cargo build --offline --release --features s2n,production --bin bench
    P384_OPENSSL36_LIBCRYPTO=$HOME/Claude/bench_refs/openssl-install/lib/libcrypto.so.4 \
      BENCH_SECTIONS=dhkem,ecdsa BENCH_REPS=15 BENCH_ITERS=300 BENCH_MICRO_ITERS=4000 \
      taskset -c 15 ./target/release/bench

Rebuild before each run: the field configuration is a build-time choice, so
set the same variable on the `cargo build` line. `make dhkem` and
`make bench-dhkem` wrap these. `BENCH_SECTIONS` defaults to `ecdsa,dhkem`, so
the plain benchmark commands above print the DHKEM table after the ECDSA
ones.
