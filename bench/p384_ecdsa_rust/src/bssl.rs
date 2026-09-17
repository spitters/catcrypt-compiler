//! Bridge to BoringSSL's `libcrypto`: a production opponent, linked
//! statically by `build.rs` under the `production` feature.
//!
//! BoringSSL's P-384 is its generic Montgomery EC method, not a dedicated
//! curve implementation.  `EC_group_p384` (`crypto/fipsmodule/ec/ec.cc.inc`)
//! sets `EC_GFp_mont_method()`; the field multiply `ec_felem_mul`
//! (`felem.cc.inc`) is `bn_mod_mul_montgomery_small`, which calls
//! `bn_mul_mont_words` (`bn/montgomery.cc.inc`), and at six limbs every
//! specialised x86-64 path is ruled out (`bn_mul4x_mont_capable` needs at
//! least eight limbs and a multiple of four), so the call lands in
//! `bn_mul_mont_nohw`, the generic word-serial Montgomery loop of
//! `bn/asm/x86_64-mont.pl`.  The point operations are C Jacobian formulas in
//! `ec_montgomery.cc.inc`; the base-point multiply is `ec_GFp_mont_mul` over
//! the generator (a 5-bit fixed window with a constant-time scan of a
//! 32-entry table built per call, `simple_mul.cc.inc`); verification is
//! `ec_GFp_mont_mul_public_batch`, an interleaved width-4 wNAF
//! (`wnaf.cc.inc`); both scalar inverses are Fermat,
//! `bn_mod_inverse0_prime_mont_small` (`bn/exponentiation.cc.inc`).  There is
//! no fiat-crypto code on this path: `third_party/fiat` at the linked
//! checkout carries P-256 and Curve25519 only.
//!
//! Signing with a caller-supplied nonce is
//! `ECDSA_sign_with_nonce_and_leak_private_key_for_testing`
//! (`include/openssl/ecdsa.h`), which reaches the same `ecdsa_sign_impl` as
//! `ECDSA_do_sign` and skips only the nonce derivation — a SHA-512 of the
//! private key and digest, then rejection sampling from the RBG
//! (`ecdsa_sign_fixed`, `ecdsa.cc.inc`).  The self-test hook both paths name
//! is an inline no-op outside FIPS builds (`crypto/internal.h`).
//!
//! The two C libraries export the same names (`ECDSA_do_sign`,
//! `EC_KEY_new_by_curve_name`, …), so only one of them can be linked by name
//! into a binary.  BoringSSL is the one linked; [`crate::ossl`] reaches
//! OpenSSL through `dlopen`.

#![allow(non_camel_case_types)]

use std::ffi::{c_int, c_void};
use std::ptr;

type EC_KEY = c_void;
type BIGNUM = c_void;
type ECDSA_SIG = c_void;

const NID_SECP384R1: c_int = 715;

extern "C" {
    fn EC_KEY_new_by_curve_name(nid: c_int) -> *mut EC_KEY;
    fn EC_KEY_free(key: *mut EC_KEY);
    fn EC_KEY_set_private_key(key: *mut EC_KEY, priv_: *const BIGNUM) -> c_int;
    fn EC_KEY_set_public_key_affine_coordinates(
        key: *mut EC_KEY,
        x: *const BIGNUM,
        y: *const BIGNUM,
    ) -> c_int;
    fn BN_bin2bn(input: *const u8, len: usize, ret: *mut BIGNUM) -> *mut BIGNUM;
    fn BN_bn2bin_padded(out: *mut u8, len: usize, input: *const BIGNUM) -> c_int;
    fn BN_free(bn: *mut BIGNUM);
    fn ECDSA_SIG_new() -> *mut ECDSA_SIG;
    fn ECDSA_SIG_free(sig: *mut ECDSA_SIG);
    fn ECDSA_SIG_get0(sig: *const ECDSA_SIG, r: *mut *const BIGNUM, s: *mut *const BIGNUM);
    fn ECDSA_SIG_set0(sig: *mut ECDSA_SIG, r: *mut BIGNUM, s: *mut BIGNUM) -> c_int;
    fn ECDSA_do_sign(digest: *const u8, digest_len: usize, key: *const EC_KEY) -> *mut ECDSA_SIG;
    fn ECDSA_do_verify(
        digest: *const u8,
        digest_len: usize,
        sig: *const ECDSA_SIG,
        key: *const EC_KEY,
    ) -> c_int;
    fn EC_KEY_get0_group(key: *const EC_KEY) -> *const c_void;
    fn EC_GROUP_get0_order(group: *const c_void) -> *const BIGNUM;
    fn BN_new() -> *mut BIGNUM;
    fn BN_rand_range_ex(r: *mut BIGNUM, min_inclusive: u64, max_exclusive: *const BIGNUM) -> c_int;
    fn SHA512(data: *const u8, len: usize, out: *mut u8) -> *mut u8;
    fn EC_POINT_new(group: *const c_void) -> *mut c_void;
    fn EC_POINT_free(point: *mut c_void);
    fn EC_POINT_oct2point(
        group: *const c_void,
        point: *mut c_void,
        buf: *const u8,
        len: usize,
        ctx: *mut c_void,
    ) -> c_int;
    fn EC_POINT_point2oct(
        group: *const c_void,
        point: *const c_void,
        form: c_int,
        buf: *mut u8,
        max_out: usize,
        ctx: *mut c_void,
    ) -> usize;
    fn EC_POINT_mul(
        group: *const c_void,
        r: *mut c_void,
        n: *const BIGNUM,
        q: *const c_void,
        m: *const BIGNUM,
        ctx: *mut c_void,
    ) -> c_int;
    fn ECDH_compute_key(
        out: *mut c_void,
        outlen: usize,
        pub_key: *const c_void,
        priv_key: *const EC_KEY,
        kdf: *const c_void,
    ) -> c_int;
    fn EVP_sha384() -> *const c_void;
    fn HKDF_extract(
        out_key: *mut u8,
        out_len: *mut usize,
        digest: *const c_void,
        secret: *const u8,
        secret_len: usize,
        salt: *const u8,
        salt_len: usize,
    ) -> c_int;
    fn HKDF_expand(
        out_key: *mut u8,
        out_len: usize,
        digest: *const c_void,
        prk: *const u8,
        prk_len: usize,
        info: *const u8,
        info_len: usize,
    ) -> c_int;
    fn ECDSA_sign_with_nonce_and_leak_private_key_for_testing(
        digest: *const u8,
        digest_len: usize,
        key: *const EC_KEY,
        nonce: *const u8,
        nonce_len: usize,
    ) -> *mut ECDSA_SIG;
}

/// The BoringSSL checkout `build.rs` linked, as recorded at build time.
pub const REVISION: &str = env!("P384_BORINGSSL_REVISION");

/// A BIGNUM from 48 big-endian bytes.
fn bn(be: &[u8; 48]) -> *mut BIGNUM {
    let p = unsafe { BN_bin2bn(be.as_ptr(), be.len(), ptr::null_mut()) };
    assert!(!p.is_null(), "BN_bin2bn failed");
    p
}

/// A P-384 `EC_KEY`, freed on drop.
pub struct Key(*mut EC_KEY);

impl Drop for Key {
    fn drop(&mut self) {
        unsafe { EC_KEY_free(self.0) }
    }
}

fn new_key() -> *mut EC_KEY {
    let k = unsafe { EC_KEY_new_by_curve_name(NID_SECP384R1) };
    assert!(!k.is_null(), "EC_KEY_new_by_curve_name(secp384r1) failed");
    k
}

/// A signing key: the private scalar `d` and its public point `(x, y)`, all
/// big-endian.  `None` when BoringSSL refuses either.
pub fn signing_key(d: &[u8; 48], x: &[u8; 48], y: &[u8; 48]) -> Option<Key> {
    let key = Key(new_key());
    let (dbn, xbn, ybn) = (bn(d), bn(x), bn(y));
    let ok = unsafe {
        EC_KEY_set_private_key(key.0, dbn) == 1
            && EC_KEY_set_public_key_affine_coordinates(key.0, xbn, ybn) == 1
    };
    unsafe {
        BN_free(dbn);
        BN_free(xbn);
        BN_free(ybn);
    }
    ok.then_some(key)
}

/// A verifying key for the affine point `(x, y)`, big-endian.  `None` when
/// BoringSSL rejects the point.
pub fn verifying_key(x: &[u8; 48], y: &[u8; 48]) -> Option<Key> {
    let key = Key(new_key());
    let (xbn, ybn) = (bn(x), bn(y));
    let ok = unsafe { EC_KEY_set_public_key_affine_coordinates(key.0, xbn, ybn) == 1 };
    unsafe {
        BN_free(xbn);
        BN_free(ybn);
    }
    ok.then_some(key)
}

/// An `ECDSA_SIG`, freed on drop.
pub struct Sig(*mut ECDSA_SIG);

impl Drop for Sig {
    fn drop(&mut self) {
        unsafe { ECDSA_SIG_free(self.0) }
    }
}

/// `(r, s)` as an `ECDSA_SIG`, big-endian.
pub fn sig(r: &[u8; 48], s: &[u8; 48]) -> Sig {
    let sig = unsafe { ECDSA_SIG_new() };
    assert!(!sig.is_null(), "ECDSA_SIG_new failed");
    let ok = unsafe { ECDSA_SIG_set0(sig, bn(r), bn(s)) };
    assert_eq!(ok, 1, "ECDSA_SIG_set0 failed");
    Sig(sig)
}

/// `(r, s)` of a returned signature as big-endian bytes; frees it.
fn take(sig: *mut ECDSA_SIG) -> Option<([u8; 48], [u8; 48])> {
    if sig.is_null() {
        return None;
    }
    let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
    let (mut rp, mut sp) = (ptr::null(), ptr::null());
    let ok = unsafe {
        ECDSA_SIG_get0(sig, &mut rp, &mut sp);
        let ok = BN_bn2bin_padded(r.as_mut_ptr(), 48, rp) == 1
            && BN_bn2bin_padded(s.as_mut_ptr(), 48, sp) == 1;
        ECDSA_SIG_free(sig);
        ok
    };
    ok.then_some((r, s))
}

/// Signs the 48-byte digest with the nonce `k`, both big-endian, through
/// `ECDSA_sign_with_nonce_and_leak_private_key_for_testing`.  Returns
/// `(r, s)` big-endian, or `None` when BoringSSL refuses.
pub fn sign_with_nonce(key: &Key, digest: &[u8; 48], k: &[u8; 48]) -> Option<([u8; 48], [u8; 48])> {
    take(unsafe {
        ECDSA_sign_with_nonce_and_leak_private_key_for_testing(
            digest.as_ptr(),
            digest.len(),
            key.0,
            k.as_ptr(),
            k.len(),
        )
    })
}

/// Signs the 48-byte digest through `ECDSA_do_sign`, which derives its own
/// nonce.  Returns `(r, s)` big-endian.
pub fn sign(key: &Key, digest: &[u8; 48]) -> ([u8; 48], [u8; 48]) {
    take(unsafe { ECDSA_do_sign(digest.as_ptr(), digest.len(), key.0) })
        .expect("BoringSSL ECDSA_do_sign failed")
}

/// Whether `ECDSA_do_verify` accepts `sig` on the 48-byte digest.
pub fn verify(key: &Key, digest: &[u8; 48], sig: &Sig) -> bool {
    unsafe { ECDSA_do_verify(digest.as_ptr(), digest.len(), sig.0, key.0) == 1 }
}

/// Reusable output `BIGNUM` for [`nonce_parts`].
pub struct NonceState(*mut BIGNUM);

impl NonceState {
    pub fn new() -> Self {
        let p = unsafe { BN_new() };
        assert!(!p.is_null(), "BN_new failed");
        NonceState(p)
    }
}

impl Default for NonceState {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for NonceState {
    fn drop(&mut self) {
        unsafe { BN_free(self.0) }
    }
}

/// The two parts of the nonce derivation `ecdsa_sign_fixed` adds to the
/// nonce-supplied path, rebuilt from exported functions: SHA-512 over the
/// six private-key words and the digest (one-shot `SHA512` over the same 96
/// bytes, one compression, where the source makes two `BCM_sha512_update`
/// calls), then `BN_rand_range_ex(k, 1, n)`, which runs the same
/// `bn_rand_range_words` rejection loop and DRBG call as
/// `ec_random_nonzero_scalar` with all-zero additional data in place of the
/// hash.  `priv_words` is the private scalar as the little-endian words
/// BoringSSL hashes.
pub fn nonce_parts(key: &Key, priv_words: &[u8; 48], digest: &[u8; 48], st: &mut NonceState) {
    let mut buf = [0u8; 96];
    buf[..48].copy_from_slice(priv_words);
    buf[48..].copy_from_slice(digest);
    let mut out = [0u8; 64];
    unsafe {
        SHA512(buf.as_ptr(), buf.len(), out.as_mut_ptr());
        let order = EC_GROUP_get0_order(EC_KEY_get0_group(key.0));
        assert_eq!(BN_rand_range_ex(st.0, 1, order), 1, "BN_rand_range_ex failed");
    }
    std::hint::black_box(out);
}

// ---------------------------------------------------------------------------
// DHKEM(P-384, HKDF-SHA384), reconstructed
// ---------------------------------------------------------------------------
//
// BoringSSL's HPKE (`include/openssl/hpke.h`) offers the KEMs 0x0010
// (P-256), 0x0020 (X25519), X-Wing and ML-KEM; there is no P-384 KEM.  Its
// P-256 DHKEM (`crypto/hpke/hpke.cc`, `p256_encap_with_seed`, `p256`) runs on
// internal `ec_*` functions that are not exported.  What follows is
// DHKEM(P-384) rebuilt from the exported API — `EC_POINT_oct2point`,
// `EC_POINT_mul`, `EC_POINT_point2oct`, `ECDH_compute_key` and
// `HKDF_extract` / `HKDF_expand` over `EVP_sha384()` — following the call
// structure of `dhkem_extract_and_expand` in the same file.  It is a
// reconstruction, not a BoringSSL entry point.
//
// The `EC_KEY`, the two `EC_POINT`s and the `BIGNUM` are allocated once in
// [`KemState`] and reused, so the per-call cost is the arithmetic, the
// key-setting validation and the KDF, not allocation of the wrappers.

/// `POINT_CONVERSION_UNCOMPRESSED`.
const UNCOMPRESSED_FORM: c_int = 4;

/// Reusable objects for [`dhkem_encap`] and [`dhkem_decap`].
pub struct KemState {
    key: *mut EC_KEY,
    group: *const c_void,
    peer: *mut c_void,
    eph: *mut c_void,
    scalar: *mut BIGNUM,
}

impl KemState {
    pub fn new() -> Self {
        unsafe {
            let key = new_key();
            let group = EC_KEY_get0_group(key);
            let peer = EC_POINT_new(group);
            let eph = EC_POINT_new(group);
            let scalar = BN_new();
            assert!(!peer.is_null() && !eph.is_null() && !scalar.is_null());
            KemState { key, group, peer, eph, scalar }
        }
    }
}

impl Default for KemState {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for KemState {
    fn drop(&mut self) {
        unsafe {
            BN_free(self.scalar);
            EC_POINT_free(self.eph);
            EC_POINT_free(self.peer);
            EC_KEY_free(self.key);
        }
    }
}

/// `ExtractAndExpand(dh, kem_context)` through `HKDF_extract` and
/// `HKDF_expand` with `EVP_sha384()`.
pub fn dhkem_extract_and_expand(dh: &[u8; 48], kem_context: &[u8; 194]) -> Option<[u8; 48]> {
    use crate::dhkem_kdf::{HPKE_VERSION, SUITE_ID};
    let mut ikm = [0u8; 7 + 5 + 7 + 48];
    ikm[..7].copy_from_slice(HPKE_VERSION);
    ikm[7..12].copy_from_slice(&SUITE_ID);
    ikm[12..19].copy_from_slice(b"eae_prk");
    ikm[19..].copy_from_slice(dh);
    let mut info = [0u8; 2 + 7 + 5 + 13 + 194];
    info[..2].copy_from_slice(&48u16.to_be_bytes());
    info[2..9].copy_from_slice(HPKE_VERSION);
    info[9..14].copy_from_slice(&SUITE_ID);
    info[14..27].copy_from_slice(b"shared_secret");
    info[27..].copy_from_slice(kem_context);
    let mut prk = [0u8; 48];
    let mut prk_len = 0usize;
    let mut ss = [0u8; 48];
    let ok = unsafe {
        let md = EVP_sha384();
        HKDF_extract(prk.as_mut_ptr(), &mut prk_len, md, ikm.as_ptr(), ikm.len(), ptr::null(), 0) == 1
            && prk_len == 48
            && HKDF_expand(ss.as_mut_ptr(), 48, md, prk.as_ptr(), 48, info.as_ptr(), info.len()) == 1
    };
    ok.then_some(ss)
}

/// Sets the private scalar of the state's key; `false` when BoringSSL
/// rejects it (zero or not below `n`).
fn set_private(st: &mut KemState, sk_be: &[u8; 48]) -> bool {
    unsafe {
        !BN_bin2bn(sk_be.as_ptr(), 48, st.scalar).is_null()
            && EC_KEY_set_private_key(st.key, st.scalar) == 1
    }
}

/// `x(sk * peer)` into `dh`, with `peer` parsed from `peer_enc`; `false` when
/// BoringSSL rejects the point.
fn ecdh(st: &mut KemState, peer_enc: &[u8; 97], dh: &mut [u8; 48]) -> bool {
    unsafe {
        EC_POINT_oct2point(st.group, st.peer, peer_enc.as_ptr(), 97, ptr::null_mut()) == 1
            && ECDH_compute_key(dh.as_mut_ptr().cast(), 48, st.peer, st.key, ptr::null()) == 48
    }
}

/// `Encap(pkR)` with `skE` supplied (big-endian), or `None` when BoringSSL
/// rejects `skE` or `pkR`.
pub fn dhkem_encap(st: &mut KemState, sk_e_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<([u8; 97], [u8; 48])> {
    if !set_private(st, sk_e_be) {
        return None;
    }
    let mut enc = [0u8; 97];
    let ok = unsafe {
        EC_POINT_mul(st.group, st.eph, st.scalar, ptr::null(), ptr::null(), ptr::null_mut()) == 1
            && EC_POINT_point2oct(st.group, st.eph, UNCOMPRESSED_FORM, enc.as_mut_ptr(), 97, ptr::null_mut()) == 97
    };
    let mut dh = [0u8; 48];
    if !ok || !ecdh(st, pk_r, &mut dh) {
        return None;
    }
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(&enc);
    ctx[97..].copy_from_slice(pk_r);
    Some((enc, dhkem_extract_and_expand(&dh, &ctx)?))
}

/// `Decap(enc, skR)` with `pkR` supplied, or `None` when BoringSSL rejects
/// `enc` or `skR`.
pub fn dhkem_decap(st: &mut KemState, enc: &[u8; 97], sk_r_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<[u8; 48]> {
    let mut dh = [0u8; 48];
    if !set_private(st, sk_r_be) || !ecdh(st, enc, &mut dh) {
        return None;
    }
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(enc);
    ctx[97..].copy_from_slice(pk_r);
    dhkem_extract_and_expand(&dh, &ctx)
}
