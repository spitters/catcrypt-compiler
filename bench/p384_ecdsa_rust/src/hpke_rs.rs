//! Bridge to hpke-rs 0.7.0 with its RustCrypto provider
//! (`hpke-rs-rust-crypto` 0.7.0): the native-API DHKEM(P-384) opponent.
//!
//! hpke-rs is the HPKE library OpenMLS uses, so this is the implementation
//! an MLS client on ciphersuite 7 (`MLS_192_DHKEMP384_AES256GCM_SHA384_P384`)
//! runs.  Its provider implements `KemAlgorithm::DhKemP384` with RustCrypto
//! `p384` 0.13 (`hpke-rs-rust-crypto-0.7.0/src/lib.rs`, the `DhKemP384` arms
//! of `dh`, `secret_to_public` and `kem_key_gen`) and HKDF with `hkdf` 0.13
//! over `sha2` 0.11 (`src/hkdf.rs`).  The ECDH is therefore the same
//! RustCrypto arithmetic as `crate::dhkem_ref`; the key derivation is a
//! different release of the HKDF crate.
//!
//! The libcrux provider is not an opponent here.  `libcrux-ecdh` 0.0.8
//! implements X25519 and P-256 only (`src/ecdh.rs`, `derive` returns
//! `UnknownAlgorithm` for `P384`), and `hpke-rs-libcrux` 0.7.0 reaches P-384
//! only through RustCrypto `p384` 0.14.0-rc.8 behind its
//! `rustcrypto-p-curves` feature, which is not in the registry cache.
//!
//! **What the public API exposes.**  The DHKEM itself (`kem::encaps`,
//! `dh_kem::encaps`) is crate-private.  The public entry points are
//! `Hpke::setup_sender` and `Hpke::setup_receiver`, which run the KEM and
//! then the base-mode key schedule, and return a `Context`.  The shared
//! secret is never returned, so the interop tests compare it through the
//! key schedule: the exporter output of hpke-rs's context against that of
//! `Hpke::key_schedule` applied to our shared secret.  The ephemeral key is
//! not an input either: `setup_sender` draws `Nsk = 48` random bytes and
//! runs `DeriveKeyPair` on them.  `Hpke::seed` (feature `hpke-test`) fixes
//! those bytes, and `Hpke::derive_key_pair` on the same bytes gives the
//! `skE` to hand the kernel.
//!
//! [`prims_encap`] and [`prims_decap`] are a reconstruction for the
//! benchmark: the calls `dh_kem::encaps` / `dh_kem::decaps` make, through
//! the provider's public `HpkeCrypto` trait, with `DeriveKeyPair` left out
//! and, for decapsulation, the recomputation of `pkR` left out, so they do
//! what the emitted kernels do.

use hpke_rs::hpke_types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm};
use hpke_rs::prelude::{Hpke, HpkeMode, HpkePrivateKey, HpkePublicKey};
use hpke_rs::Context;
use hpke_rs_crypto::HpkeCrypto;
use hpke_rs_rust_crypto::HpkeRustCrypto;

/// hpke-rs over its RustCrypto provider.
pub type Provider = HpkeRustCrypto;

/// The `info` string the tests pass to the key schedule.
pub const INFO: &[u8] = b"catcrypt dhkem p384 interop";

/// The exporter label the tests read the key schedule back through.
pub const EXPORT_LABEL: &[u8] = b"catcrypt dhkem p384 export";

/// Base mode, DHKEM(P-384, HKDF-SHA384), HKDF-SHA384, AES-256-GCM: the HPKE
/// suite of MLS ciphersuite 7.
pub fn new() -> Hpke<Provider> {
    Hpke::new(
        HpkeMode::Base,
        KemAlgorithm::DhKemP384,
        KdfAlgorithm::HkdfSha384,
        AeadAlgorithm::Aes256Gcm,
    )
}

fn arr<const N: usize>(v: &[u8]) -> [u8; N] {
    let mut out = [0u8; N];
    out.copy_from_slice(v);
    out
}

/// `DeriveKeyPair(ikm)` through hpke-rs: `(skX, pkX)`, `skX` big-endian.
pub fn derive_key_pair(h: &Hpke<Provider>, ikm: &[u8]) -> ([u8; 48], [u8; 97]) {
    let kp = h.derive_key_pair(ikm).expect("hpke-rs DeriveKeyPair failed");
    let (sk, pk) = kp.into_keys();
    (arr(sk.as_slice()), arr(pk.as_slice()))
}

/// `SetupBaseS(pkR, INFO)` with the ephemeral randomness fixed to `ikm_e`:
/// `(enc, context)`, or `None` when hpke-rs rejects `pkR`.
pub fn setup_sender(
    h: &mut Hpke<Provider>,
    pk_r: &[u8; 97],
    ikm_e: &[u8; 48],
) -> Option<([u8; 97], Context<Provider>)> {
    h.seed(ikm_e).expect("hpke-rs seed");
    let pk = HpkePublicKey::new(pk_r.to_vec());
    let (enc, ctx) = h.setup_sender(&pk, INFO, None, None, None).ok()?;
    Some((arr(&enc), ctx))
}

/// `SetupBaseR(enc, skR, INFO)`, or `None` when hpke-rs rejects `enc` or
/// `skR`.  `skR` is big-endian.
pub fn setup_receiver(h: &Hpke<Provider>, enc: &[u8; 97], sk_r_be: &[u8; 48]) -> Option<Context<Provider>> {
    let sk = HpkePrivateKey::new(sk_r_be.to_vec());
    h.setup_receiver(enc, &sk, INFO, None, None, None).ok()
}

/// 48 bytes of `Context.Export(EXPORT_LABEL, 48)`.
pub fn export(ctx: &Context<Provider>) -> [u8; 48] {
    arr(&ctx.export(EXPORT_LABEL, 48).expect("hpke-rs export"))
}

/// `KeySchedule(Base, shared_secret, INFO, "", "")` through hpke-rs, read
/// back through [`export`].  This is how a shared secret computed outside
/// hpke-rs is compared with one hpke-rs computed.
pub fn export_for_shared_secret(h: &Hpke<Provider>, ss: &[u8; 48]) -> [u8; 48] {
    export(&h.key_schedule(ss, INFO, &[], &[]).expect("hpke-rs key schedule"))
}

/// hpke-rs's base-mode key schedule alone, for the benchmark: the part of
/// `setup_sender` / `setup_receiver` that follows the KEM.
pub fn key_schedule(h: &Hpke<Provider>, ss: &[u8; 48]) -> Context<Provider> {
    h.key_schedule(ss, INFO, &[], &[]).expect("hpke-rs key schedule")
}

fn labeled_info(label: &[u8], info: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(2 + 7 + 5 + label.len() + info.len());
    v.extend_from_slice(&48u16.to_be_bytes());
    v.extend_from_slice(crate::dhkem_kdf::HPKE_VERSION);
    v.extend_from_slice(&crate::dhkem_kdf::SUITE_ID);
    v.extend_from_slice(label);
    v.extend_from_slice(info);
    v
}

/// `ExtractAndExpand(dh, kem_context)` through the provider's `kdf_extract`
/// and `kdf_expand`, over the labelled buffers `hpke-rs` builds.
pub fn extract_and_expand(dh: &[u8], kem_context: &[u8]) -> Vec<u8> {
    let mut ikm = Vec::with_capacity(7 + 5 + 7 + dh.len());
    ikm.extend_from_slice(crate::dhkem_kdf::HPKE_VERSION);
    ikm.extend_from_slice(&crate::dhkem_kdf::SUITE_ID);
    ikm.extend_from_slice(b"eae_prk");
    ikm.extend_from_slice(dh);
    let prk = Provider::kdf_extract(KdfAlgorithm::HkdfSha384, &[], &ikm).expect("kdf_extract");
    Provider::kdf_expand(
        KdfAlgorithm::HkdfSha384,
        &prk,
        &labeled_info(b"shared_secret", kem_context),
        48,
    )
    .expect("kdf_expand")
}

/// The provider calls of `dh_kem::encaps` after `DeriveKeyPair`:
/// `secret_to_public(skE)`, `dh(pkR, skE)`, then `kdf_extract` and
/// `kdf_expand` over the labelled buffers hpke-rs builds.  A
/// reconstruction, not an hpke-rs entry point.
pub fn prims_encap(sk_e_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<([u8; 97], [u8; 48])> {
    let alg = KemAlgorithm::DhKemP384;
    let enc = Provider::secret_to_public(alg, sk_e_be).ok()?;
    let dh = Provider::dh(alg, pk_r, sk_e_be).ok()?;
    let mut ctx = Vec::with_capacity(194);
    ctx.extend_from_slice(&enc);
    ctx.extend_from_slice(pk_r);
    let ss = extract_and_expand(&dh, &ctx);
    Some((arr(&enc), arr(&ss)))
}

/// The provider calls of `dh_kem::decaps` with `pkR` supplied: `dh(enc,
/// skR)`, `kdf_extract`, `kdf_expand`.  hpke-rs itself also calls
/// `secret_to_public(skR)`, a fixed-base multiply that the emitted kernel
/// does not perform; [`setup_receiver`] includes it.
pub fn prims_decap(enc: &[u8; 97], sk_r_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<[u8; 48]> {
    let dh = Provider::dh(KemAlgorithm::DhKemP384, enc, sk_r_be).ok()?;
    let mut ctx = Vec::with_capacity(194);
    ctx.extend_from_slice(enc);
    ctx.extend_from_slice(pk_r);
    Some(arr(&extract_and_expand(&dh, &ctx)))
}

/// `secret_to_public(skR)`, the step `dh_kem::decaps` adds to [`prims_decap`].
pub fn secret_to_public(sk_be: &[u8; 48]) -> Option<[u8; 97]> {
    Some(arr(&Provider::secret_to_public(KemAlgorithm::DhKemP384, sk_be).ok()?))
}
