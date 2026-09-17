//! An independent DHKEM(P-384, HKDF-SHA384), RFC 9180 §4.1 with KEM id
//! `0x0011`, over RustCrypto `p384` 0.13.1 ECDH and `hkdf` 0.12.4.
//!
//! It shares no code with the leaves: the curve arithmetic is RustCrypto's
//! (`p384::ecdh::diffie_hellman`, `SecretKey::public_key`,
//! `PublicKey::from_sec1_bytes`), and the key derivation goes through
//! `hkdf::HkdfExtract` and `Hkdf::expand_multi_info`, with the labelled
//! inputs passed as separate pieces rather than the concatenated buffers
//! `crate::dhkem_kdf` builds.  What it shares with `crate::dhkem_kdf` is the
//! `hkdf` crate itself; independence of the key derivation comes from the
//! other implementations the tests compare against.
//!
//! Private keys are RFC 9180 §7.1.2 serialisations, 48 big-endian bytes,
//! not the little-endian limbs of the kernel ABI.

// `GenericArray::from_slice` carries a deprecation warning pointing to generic-array 1.x,
// which this pinned dependency set predates.
#![allow(deprecated)]

use elliptic_curve::sec1::ToEncodedPoint;
use hkdf::{Hkdf, HkdfExtract};
use p384_rc::ecdh::diffie_hellman;
use p384_rc::{FieldBytes, PublicKey, SecretKey};
use sha2::Sha384;

use crate::dhkem_kdf::{HPKE_VERSION, NSECRET, SUITE_ID};

/// `LabeledExtract(salt, label, ikm)`, RFC 9180 §4.
pub fn labeled_extract(salt: &[u8], label: &[u8], ikm: &[u8]) -> [u8; 48] {
    let mut ex = HkdfExtract::<Sha384>::new(Some(salt));
    ex.input_ikm(HPKE_VERSION);
    ex.input_ikm(&SUITE_ID);
    ex.input_ikm(label);
    ex.input_ikm(ikm);
    let (prk, _) = ex.finalize();
    let mut out = [0u8; 48];
    out.copy_from_slice(&prk);
    out
}

/// `LabeledExpand(prk, label, info, L)`, RFC 9180 §4.
pub fn labeled_expand(prk: &[u8; 48], label: &[u8], info: &[u8], out: &mut [u8]) {
    let len = (out.len() as u16).to_be_bytes();
    Hkdf::<Sha384>::from_prk(prk)
        .expect("48-byte PRK")
        .expand_multi_info(&[&len, HPKE_VERSION, &SUITE_ID, label, info], out)
        .expect("output within HKDF bound");
}

/// `ExtractAndExpand(dh, kem_context)`, RFC 9180 §4.1.
pub fn extract_and_expand(dh: &[u8; 48], kem_context: &[u8]) -> [u8; 48] {
    let prk = labeled_extract(&[], b"eae_prk", dh);
    let mut ss = [0u8; NSECRET];
    labeled_expand(&prk, b"shared_secret", kem_context, &mut ss);
    ss
}

/// `SerializePublicKey`, the 97-byte SEC1 uncompressed encoding.
pub fn serialize_public(pk: &PublicKey) -> [u8; 97] {
    let ep = pk.to_encoded_point(false);
    let mut out = [0u8; 97];
    out.copy_from_slice(ep.as_bytes());
    out
}

/// The private key for `sk_be`, or `None` when it is zero or not below `n`.
pub fn secret_key(sk_be: &[u8; 48]) -> Option<SecretKey> {
    SecretKey::from_bytes(FieldBytes::from_slice(sk_be)).ok()
}

/// `pk(sk)` serialised, or `None` for an invalid `sk`.
pub fn public_key(sk_be: &[u8; 48]) -> Option<[u8; 97]> {
    Some(serialize_public(&secret_key(sk_be)?.public_key()))
}

/// `DeserializePublicKey`, or `None` when the string is not a valid,
/// non-identity, uncompressed P-384 point.
pub fn deserialize_public(s: &[u8; 97]) -> Option<PublicKey> {
    if s[0] != 0x04 {
        return None;
    }
    PublicKey::from_sec1_bytes(s).ok()
}

/// `DH(sk, pk)`, the 48-byte big-endian x-coordinate of `sk * pk`, or
/// `None` for an invalid `sk` or `pk`.
pub fn dh(sk_be: &[u8; 48], pk: &[u8; 97]) -> Option<[u8; 48]> {
    let sk = secret_key(sk_be)?;
    let pk = deserialize_public(pk)?;
    let z = diffie_hellman(sk.to_nonzero_scalar(), pk.as_affine());
    let mut out = [0u8; 48];
    out.copy_from_slice(z.raw_secret_bytes());
    Some(out)
}

/// `Encap(pkR)` with `skE` supplied: `(enc, shared_secret)`, or `None` when
/// `skE` or `pkR` is invalid.
pub fn encap(sk_e_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<([u8; 97], [u8; 48])> {
    let sk_e = secret_key(sk_e_be)?;
    let pk_r_point = deserialize_public(pk_r)?;
    let enc = serialize_public(&sk_e.public_key());
    let dh = diffie_hellman(sk_e.to_nonzero_scalar(), pk_r_point.as_affine());
    let mut dh_bytes = [0u8; 48];
    dh_bytes.copy_from_slice(dh.raw_secret_bytes());
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(&enc);
    ctx[97..].copy_from_slice(pk_r);
    Some((enc, extract_and_expand(&dh_bytes, &ctx)))
}

/// `Decap(enc, skR)` as RFC 9180 writes it, recomputing `pkRm` from `skR`,
/// or `None` when `enc` or `skR` is invalid.
pub fn decap(enc: &[u8; 97], sk_r_be: &[u8; 48]) -> Option<[u8; 48]> {
    let sk_r = secret_key(sk_r_be)?;
    let pk_e = deserialize_public(enc)?;
    let dh = diffie_hellman(sk_r.to_nonzero_scalar(), pk_e.as_affine());
    let mut dh_bytes = [0u8; 48];
    dh_bytes.copy_from_slice(dh.raw_secret_bytes());
    let pk_rm = serialize_public(&sk_r.public_key());
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(enc);
    ctx[97..].copy_from_slice(&pk_rm);
    Some(extract_and_expand(&dh_bytes, &ctx))
}

/// `Decap` with `pkR` supplied rather than recomputed, the form the
/// emitted kernel takes, for the benchmark.
pub fn decap_with_pk(enc: &[u8; 97], sk_r_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<[u8; 48]> {
    let sk_r = secret_key(sk_r_be)?;
    let pk_e = deserialize_public(enc)?;
    let dh = diffie_hellman(sk_r.to_nonzero_scalar(), pk_e.as_affine());
    let mut dh_bytes = [0u8; 48];
    dh_bytes.copy_from_slice(dh.raw_secret_bytes());
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(enc);
    ctx[97..].copy_from_slice(pk_r);
    Some(extract_and_expand(&dh_bytes, &ctx))
}

/// `DeriveKeyPair(ikm)`, RFC 9180 §7.1.3 for P-384: `(skX, pkX)` with
/// `skX` big-endian, by rejection sampling on `candidate` with bitmask
/// `0xff`.  `None` if all 256 counters are rejected.
pub fn derive_key_pair(ikm: &[u8]) -> Option<([u8; 48], [u8; 97])> {
    let dkp_prk = labeled_extract(&[], b"dkp_prk", ikm);
    for counter in 0u8..=255 {
        let mut sk = [0u8; 48];
        labeled_expand(&dkp_prk, b"candidate", &[counter], &mut sk);
        sk[0] &= 0xff;
        if let Some(pk) = public_key(&sk) {
            return Some((sk, pk));
        }
    }
    None
}
