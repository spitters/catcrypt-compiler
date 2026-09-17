//! The three DHKEM(P-384, HKDF-SHA384) leaves that involve no curve
//! arithmetic, shared by every leaf backend.
//!
//! RFC 9180 §4.1, KEM id `0x0011`: `suite_id = "KEM" || I2OSP(0x0011, 2)`,
//! and every label is prefixed with `"HPKE-v1"` (§4):
//!
//! ```text
//! LabeledExtract(salt, label, ikm) =
//!     HKDF-Extract(salt, "HPKE-v1" || suite_id || label || ikm)
//! LabeledExpand(prk, label, info, L) =
//!     HKDF-Expand(prk, I2OSP(L, 2) || "HPKE-v1" || suite_id || label || info, L)
//! ```
//!
//! `ExtractAndExpand(dh, kem_context)` is
//! `LabeledExpand(LabeledExtract("", "eae_prk", dh), "shared_secret", kem_context, 48)`,
//! split here into [`dhkem_p384_extract`] and [`dhkem_p384_expand`] so the
//! emitted kernel calls them as two leaves.  HKDF and HMAC are the RustCrypto
//! `hkdf` 0.12.4 / `hmac` 0.12.1 / `sha2` 0.10.9 crates.
//!
//! The byte strings here are the RFC's wire forms and are big-endian where
//! they encode integers; this module handles no scalar.
//!
//! Constant time: HMAC-SHA-384 over fixed-length inputs, with no branch on
//! the data.

use hkdf::Hkdf;
use sha2::Sha384;

/// `"HPKE-v1"`, RFC 9180 §4.
pub const HPKE_VERSION: &[u8; 7] = b"HPKE-v1";

/// `suite_id = "KEM" || I2OSP(0x0011, 2)`, RFC 9180 §4.1.
pub const SUITE_ID: [u8; 5] = [b'K', b'E', b'M', 0x00, 0x11];

/// The length of an encoded public key and of `enc`, `Npk = Nenc = 97`.
pub const NPK: usize = 97;

/// The length of the shared secret, `Nsecret = 48`.
pub const NSECRET: usize = 48;

/// The length of `kem_context = enc || pkRm`.
pub const KEM_CONTEXT_LEN: usize = 2 * NPK;

const EAE_PRK: &[u8] = b"eae_prk";
const SHARED_SECRET: &[u8] = b"shared_secret";

/// `c = enc || pkR`, the KEM context of RFC 9180 §4.1 `Encap` and `Decap`.
pub fn p384_kem_context(c: &mut [u8; 194], enc: &[u8; 97], pk_r: &[u8; 97]) {
    c[..NPK].copy_from_slice(enc);
    c[NPK..].copy_from_slice(pk_r);
}

/// `prk = LabeledExtract("", "eae_prk", dh)`.
///
/// Shim for `hkdf::Hkdf::<Sha384>::new(Some(&[]), ..)` over the labelled
/// input `"HPKE-v1" || suite_id || "eae_prk" || dh`.  An empty HMAC key and
/// the all-zero `Nh`-byte salt of RFC 5869 give the same PRK.
pub fn dhkem_p384_extract(prk: &mut [u8; 48], dh: &[u8; 48]) {
    let mut ikm = [0u8; 7 + 5 + 7 + 48];
    ikm[..7].copy_from_slice(HPKE_VERSION);
    ikm[7..12].copy_from_slice(&SUITE_ID);
    ikm[12..19].copy_from_slice(EAE_PRK);
    ikm[19..].copy_from_slice(dh);
    let (out, _) = Hkdf::<Sha384>::extract(Some(&[]), &ikm);
    prk.copy_from_slice(&out);
}

/// `ss = LabeledExpand(prk, "shared_secret", ctx, 48)`.
///
/// Shim for `hkdf::Hkdf::<Sha384>::from_prk(prk)?.expand(info, ss)` over
/// `info = I2OSP(48, 2) || "HPKE-v1" || suite_id || "shared_secret" || ctx`.
/// `L = 48 = Nh`, so this is one HMAC-SHA-384 invocation.
pub fn dhkem_p384_expand(ss: &mut [u8; 48], prk: &[u8; 48], ctx: &[u8; 194]) {
    let mut info = [0u8; 2 + 7 + 5 + 13 + 194];
    info[..2].copy_from_slice(&(NSECRET as u16).to_be_bytes());
    info[2..9].copy_from_slice(HPKE_VERSION);
    info[9..14].copy_from_slice(&SUITE_ID);
    info[14..27].copy_from_slice(SHARED_SECRET);
    info[27..].copy_from_slice(ctx);
    Hkdf::<Sha384>::from_prk(prk)
        .expect("a 48-byte PRK is a valid HMAC-SHA-384 key")
        .expand(&info, ss)
        .expect("48 bytes is within HKDF-SHA384's 255 * 48 output bound");
}

/// Big-endian 48 bytes from the little-endian limb bytes of the scalar ABI.
///
/// RFC 9180 §7.1.2 serialises a P-384 private key as 48 big-endian bytes;
/// the emitted kernels take six little-endian limbs.  Every caller that
/// moves a private key between the two conversions goes through this pair.
pub fn sk_be_from_le(le: &[u8; 48]) -> [u8; 48] {
    let mut be = [0u8; 48];
    for i in 0..48 {
        be[i] = le[47 - i];
    }
    be
}

/// Little-endian limb bytes from a big-endian RFC 9180 private key; the
/// inverse of [`sk_be_from_le`].
pub fn sk_le_from_be(be: &[u8; 48]) -> [u8; 48] {
    sk_be_from_le(be)
}
