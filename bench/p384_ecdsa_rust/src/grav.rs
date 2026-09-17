//! Bridge to Graviola 0.4.1: the second differential opponent and benchmark
//! baseline.
//!
//! Graviola's P-384 field and scalar arithmetic is hand-written x86-64
//! assembly imported from AWS s2n-bignum and machine-checked in HOL Light
//! (`bignum_montmul_p384`, `bignum_montsqr_p384`, `p384_montjadd`,
//! `p384_montjdouble`, `bignum_inv_p384`), so it is a different
//! implementation tier from the fiat-crypto Rust that this crate and
//! RustCrypto both run.
//!
//! The ABI difference: this crate's scalars are canonical little-endian
//! `[u64; 6]`, Graviola's are big-endian 48-byte strings, a fixed-length
//! signature is `r || s` big-endian, and a public key is the 97-byte X9.62
//! uncompressed encoding `0x04 || X || Y`.  [`be48`] and [`from_be48`] are
//! the scalar conversions; [`x962`] builds the public key.
//!
//! Graviola's ECDSA API is message-oriented and admits no prehashed input.
//! `sign` and `verify` take the message and hash it with `H`, and `sign`
//! additionally reads sixteen bytes from the system RNG and derives its own
//! nonce through RFC 6979 / HMAC_DRBG.  `rfc6979_sign_with_random` is
//! private, and the `Hash` parameter cannot be instantiated downstream
//! either: `Hash::zeroed_block` returns `graviola::high::hash::HashBlock`,
//! a type that no public path names, so the trait is un-implementable
//! outside the crate.  Three things follow.
//!
//! * A digest-only vector cannot be put through Graviola's verify at all.
//!   [`sha384`] is the reachable substitute: hash a message that both sides
//!   then agree on.
//! * The signing figure is the whole `sign` API.  [`drbg_nonce_path`]
//!   reconstructs its RFC 6979 HMAC_DRBG part from Graviola's own public
//!   `Hmac`, following the call sequence of `high/ecdsa.rs` and
//!   `high/hmac_drbg.rs`, so that part can be subtracted.
//! * Verification takes no RNG and no DRBG, so the verify row differs from
//!   this crate's kernel only by the message hash.

use graviola::hashing::hmac::Hmac;
use graviola::hashing::{Hash, Sha384};
use graviola::key_agreement::p384::{PublicKey, StaticPrivateKey};
use graviola::signing::ecdsa::{P384, SigningKey, VerifyingKey};

/// The size of a P-384 scalar in bytes.
pub const SCALAR_LEN: usize = 48;

/// The size of a fixed-length P-384 signature, `r || s` big-endian.
pub const SIG_LEN: usize = 2 * SCALAR_LEN;

/// The size of an X9.62 uncompressed P-384 public key, `0x04 || X || Y`.
pub const POINT_LEN: usize = 1 + 2 * SCALAR_LEN;

/// Big-endian 48 bytes from canonical little-endian limbs.
pub fn be48(l: &[u64; 6]) -> [u8; SCALAR_LEN] {
    let mut out = [0u8; SCALAR_LEN];
    for i in 0..6 {
        out[40 - 8 * i..48 - 8 * i].copy_from_slice(&l[i].to_be_bytes());
    }
    out
}

/// Canonical little-endian limbs from big-endian 48 bytes.
pub fn from_be48(b: &[u8; SCALAR_LEN]) -> [u64; 6] {
    let mut out = [0u64; 6];
    for i in 0..6 {
        let mut w = [0u8; 8];
        w.copy_from_slice(&b[40 - 8 * i..48 - 8 * i]);
        out[i] = u64::from_be_bytes(w);
    }
    out
}

/// The X9.62 uncompressed encoding of the affine point `(x, y)`.
pub fn x962(x: &[u64; 6], y: &[u64; 6]) -> [u8; POINT_LEN] {
    let mut out = [0u8; POINT_LEN];
    out[0] = 0x04;
    out[1..1 + SCALAR_LEN].copy_from_slice(&be48(x));
    out[1 + SCALAR_LEN..].copy_from_slice(&be48(y));
    out
}

/// The fixed-length signature encoding of `(r, s)`.
pub fn signature(r: &[u64; 6], s: &[u64; 6]) -> [u8; SIG_LEN] {
    let mut out = [0u8; SIG_LEN];
    out[..SCALAR_LEN].copy_from_slice(&be48(r));
    out[SCALAR_LEN..].copy_from_slice(&be48(s));
    out
}

/// `(r, s)` as canonical limbs from a fixed-length signature.
pub fn split_signature(sig: &[u8]) -> ([u64; 6], [u64; 6]) {
    assert_eq!(sig.len(), SIG_LEN, "not a fixed-length P-384 signature");
    let mut r = [0u8; SCALAR_LEN];
    let mut s = [0u8; SCALAR_LEN];
    r.copy_from_slice(&sig[..SCALAR_LEN]);
    s.copy_from_slice(&sig[SCALAR_LEN..]);
    (from_be48(&r), from_be48(&s))
}

/// A Graviola signing key for the private scalar `d`, or `None` when `d` is
/// zero or not below `n`.
pub fn signing_key(d: &[u64; 6]) -> Option<SigningKey<P384>> {
    let private_key = StaticPrivateKey::from_bytes(&be48(d)).ok()?;
    Some(SigningKey { private_key })
}

/// The X9.62 uncompressed public key of a signing key.
pub fn public_key_bytes(sk: &SigningKey<P384>) -> [u8; POINT_LEN] {
    sk.private_key.public_key_uncompressed()
}

/// A Graviola verifying key from an X9.62 uncompressed encoding, or `None`
/// when the point is not a valid public key.
pub fn verifying_key(encoded: &[u8]) -> Option<VerifyingKey<P384>> {
    let public_key = PublicKey::from_x962_uncompressed(encoded).ok()?;
    Some(VerifyingKey { public_key })
}

/// A Graviola verifying key from canonical affine coordinates.
pub fn verifying_key_from_coords(x: &[u64; 6], y: &[u64; 6]) -> Option<VerifyingKey<P384>> {
    verifying_key(&x962(x, y))
}

/// Whether Graviola accepts `sig` on `message` under `vk`, hashing with
/// SHA-384.  This is the full public verification API.
pub fn verify_message(vk: &VerifyingKey<P384>, message: &[u8], sig: &[u8]) -> bool {
    vk.verify::<Sha384>(&[message], sig).is_ok()
}

/// Graviola's full signing API on `message`: SHA-384, sixteen bytes from the
/// system RNG, an RFC 6979 HMAC_DRBG nonce, then the curve arithmetic.
///
/// Returns the fixed-length signature.
pub fn sign_message(sk: &SigningKey<P384>, message: &[u8]) -> [u8; SIG_LEN] {
    let mut out = [0u8; SIG_LEN];
    let used = sk
        .sign::<Sha384>(&[message], &mut out)
        .expect("Graviola signing failed");
    assert_eq!(used.len(), SIG_LEN);
    out
}

/// SHA-384 of `message` through Graviola's own implementation, as 48 bytes.
pub fn sha384(message: &[u8]) -> [u8; SCALAR_LEN] {
    let mut out = [0u8; SCALAR_LEN];
    out.copy_from_slice(Sha384::hash(message).as_ref());
    out
}

/// Sixteen bytes from Graviola's system RNG, the read `sign` performs before
/// seeding its DRBG.
pub fn sign_rng_read() -> [u8; 16] {
    let mut out = [0u8; 16];
    graviola::random::fill(&mut out).expect("system RNG failed");
    out
}

/// The RFC 6979 HMAC_DRBG nonce derivation inside Graviola's `sign`,
/// reconstructed from Graviola's public `Hmac<Sha384>`.
///
/// `high/ecdsa.rs` seeds `HmacDrbg::<H>::new(d, e, random)` and then draws
/// one 48-byte scalar per attempt through `RandomSource::fill`.  Following
/// `high/hmac_drbg.rs`, seeding is four HMAC invocations (the two `K`/`V`
/// pairs of an `update` with non-empty additional input) and one `fill` of
/// 48 bytes is three more (one `generate_block`, then an `update` with empty
/// additional input, which returns after its first `K`/`V` pair).  Seven
/// HMAC-SHA-384 invocations in all; a rejected candidate would add three,
/// which for P-384 happens with probability about `2^-194`.
///
/// Returns the 48 candidate bytes, so the caller can check the
/// reconstruction against the nonce path rather than time dead code.
pub fn drbg_nonce_path(d: &[u8; SCALAR_LEN], e: &[u8; SCALAR_LEN], random: &[u8]) -> [u8; 48] {
    let mut k = [0u8; SCALAR_LEN];
    let mut v = [1u8; SCALAR_LEN];

    // HmacDrbg::new -> update(&[d, e, random]).
    for tag in [0u8, 1u8] {
        let mut ctx = Hmac::<Sha384>::new(k);
        ctx.update(v);
        ctx.update([tag]);
        ctx.update(d);
        ctx.update(e);
        ctx.update(random);
        k.copy_from_slice(ctx.finish().as_ref());

        let mut ctx = Hmac::<Sha384>::new(k);
        ctx.update(v);
        v.copy_from_slice(ctx.finish().as_ref());
    }

    // RandomSource::fill of one 48-byte block: generate_block, then
    // update(&[]), which returns after the first K/V pair.
    let mut ctx = Hmac::<Sha384>::new(k);
    ctx.update(v);
    v.copy_from_slice(ctx.finish().as_ref());
    let candidate = v;

    let mut ctx = Hmac::<Sha384>::new(k);
    ctx.update(v);
    ctx.update([0u8]);
    k.copy_from_slice(ctx.finish().as_ref());

    let mut ctx = Hmac::<Sha384>::new(k);
    ctx.update(v);
    v.copy_from_slice(ctx.finish().as_ref());
    let _ = v;

    candidate
}

// ---------------------------------------------------------------------------
// DHKEM(P-384, HKDF-SHA384), reconstructed
// ---------------------------------------------------------------------------
//
// Graviola 0.4.1 has P-384 key agreement (`key_agreement::p384`,
// `StaticPrivateKey::diffie_hellman`, `mid/p384.rs`) and HMAC
// (`hashing::hmac::Hmac`), but no HKDF and no HPKE.  What follows is
// DHKEM(P-384) built from those two by hand: a reconstruction, not a
// Graviola API.  HKDF-Extract with an empty salt is one HMAC-SHA-384 under
// the empty key (RFC 5869 pads it to the zero block, as it pads the
// `HashLen` zero salt), and HKDF-Expand to 48 bytes is one HMAC-SHA-384 of
// `info || 0x01`.
//
// Parsing a public key (`PublicKey::from_x962_uncompressed`) validates the
// point and also builds a width-5 table of its multiples, so the
// decapsulation row includes that table.

use crate::dhkem_kdf::{HPKE_VERSION, SUITE_ID};

/// `ExtractAndExpand(dh, kem_context)` over Graviola's `Hmac<Sha384>`.
pub fn dhkem_extract_and_expand(dh: &[u8; 48], kem_context: &[u8; 194]) -> [u8; 48] {
    let mut ctx = Hmac::<Sha384>::new([0u8; 0]);
    ctx.update(HPKE_VERSION);
    ctx.update(SUITE_ID);
    ctx.update(b"eae_prk");
    ctx.update(dh);
    let prk = ctx.finish();

    let mut ctx = Hmac::<Sha384>::new(prk.as_ref());
    ctx.update(48u16.to_be_bytes());
    ctx.update(HPKE_VERSION);
    ctx.update(SUITE_ID);
    ctx.update(b"shared_secret");
    ctx.update(kem_context);
    ctx.update([1u8]);
    let mut ss = [0u8; 48];
    ss.copy_from_slice(ctx.finish().as_ref());
    ss
}

/// `Encap(pkR)` with `skE` supplied (big-endian): `(enc, shared_secret)`, or
/// `None` when Graviola rejects `skE` or `pkR`.
pub fn dhkem_encap(sk_e_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<([u8; 97], [u8; 48])> {
    let sk = StaticPrivateKey::from_bytes(sk_e_be).ok()?;
    let enc = sk.public_key_uncompressed();
    let peer = PublicKey::from_x962_uncompressed(pk_r).ok()?;
    let dh = sk.diffie_hellman(&peer).ok()?;
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(&enc);
    ctx[97..].copy_from_slice(pk_r);
    Some((enc, dhkem_extract_and_expand(&dh.0, &ctx)))
}

/// `Decap(enc, skR)` with `pkR` supplied, or `None` when Graviola rejects
/// `enc` or `skR`.
pub fn dhkem_decap(enc: &[u8; 97], sk_r_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<[u8; 48]> {
    let sk = StaticPrivateKey::from_bytes(sk_r_be).ok()?;
    let peer = PublicKey::from_x962_uncompressed(enc).ok()?;
    let dh = sk.diffie_hellman(&peer).ok()?;
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(enc);
    ctx[97..].copy_from_slice(pk_r);
    Some(dhkem_extract_and_expand(&dh.0, &ctx))
}
