# `bench/p384_ecdsa_rust/gen/`: compiler output, not hand-edited

kind: authored · authority: canonical for this directory · freshness: the file
list goes stale when the emitter changes

Every `*.rs` file here is produced by `lake exe emit-p384-rust`, run from the
root of this repository, from the CatCrypt Lean fronts, and is regenerated from
Lean, never patched here. An edit made in this directory is lost on the next
emit and breaks the provenance chain that
`~/Claude/SSProve-lean/bench/framework/AUDIT_EMIT_BYPASS.md` records.

This note is `PROVENANCE.md` rather than `README` because the emitter writes
into this directory and overwrote an earlier `README`.

Present as of 2026-09-17:

    p384_ecdsa_verify.rs
    p384_ecdsa_sign.rs
    p384_ecdsa_verify_msm.rs
    p384_msm_term.rs
    p384_dhkem_encap.rs
    p384_dhkem_decap.rs

`build.rs` collects every `*.rs` here, in sorted order, into one module that
has the leaf shims of `src/leaves.rs` in scope, and sets `cfg(p384_emitted)`.
File names do not matter to the build; the module must define

    pub fn p384_ecdsa_verify(e: &[u8;48], r: &[u8;48], s: &[u8;48],
                             Q: &[u8;144], ok: &mut u64)
    pub fn p384_ecdsa_sign(e: &[u8;48], d: &[u8;48], k: &[u8;48],
                           r: &mut [u8;48], s: &mut [u8;48], ok: &mut u64)
    pub fn p384_ecdsa_verify_msm(u1: &[u8;48], G: &[u8;144],
                                 u2: &[u8;48], Q: &[u8;144],
                                 __result: &mut [u8;144])

The two ECDSA kernels take no `G`: their generator multiples go through the
fixed-base leaf `p384_scalar_mul_base`. The `ok` output of the signing kernel
is the range condition on the `r` and `s` it produces, and a caller resamples
`k` when it is zero.

The ECDSA kernels call only the thirteen ECDSA leaves listed in `src/leaves.rs`. The
verification kernel reaches the two-term multiply through the single
`p384_lincomb` leaf rather than through a fixed-base multiply, a variable-base
multiply and an addition.
`p384_msm_term` is emitted as well and is re-exported, unused by the harness.

The two DHKEM(P-384, HKDF-SHA384) kernels come from
`CatCrypt.Crypto.Jasmin.P384DhkemReflect` and define

    pub fn p384_dhkem_encap(skE: &[u8;48], pkR: &[u8;97], enc: &mut [u8;97],
                            ss: &mut [u8;48], ok: &mut u64)
    pub fn p384_dhkem_decap(enc: &[u8;97], skR: &[u8;48], pkR: &[u8;97],
                            ss: &mut [u8;48], ok: &mut u64)

The private keys are 48 bytes holding six little-endian 64-bit limbs, the P-384 scalar form of the
other kernels; a caller converts RFC 9180's big-endian serialisation. Besides
the group and range leaves they call the SEC1 leaves (`p384_sec1_decode`,
`p384_sec1_valid`, `p384_sec1_encode`), `p384_dh_x_be`, `p384_kem_context`
and the HKDF-SHA384 leaves `dhkem_p384_extract` and `dhkem_p384_expand`.
`build.rs` sets `cfg(p384_dhkem_encap_emitted)` and
`cfg(p384_dhkem_decap_emitted)` for each kernel it finds, independently of the
ECDSA switch.

With no `*.rs` file here, or with `--features force-fallback`, the crate uses
the hand-written transcription in `src/generated.rs::fallback` and
`p384_ecdsa_rust::EMITTED` is false.
