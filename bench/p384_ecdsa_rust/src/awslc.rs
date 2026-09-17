//! Bridge to AWS-LC's `libcrypto.so`: a production opponent, loaded with
//! `dlopen` under the `production` feature.
//!
//! **Why `dlopen`.**  AWS-LC is a BoringSSL fork and exports the same C
//! names as the statically linked BoringSSL ([`crate::bssl`]) and as
//! OpenSSL ([`crate::ossl`]).  As for OpenSSL, the shared library is opened
//! by absolute path with `RTLD_NOW | RTLD_LOCAL | RTLD_DEEPBIND` and every
//! function is taken from that handle with `dlsym`, so its internal calls
//! resolve inside itself.  The path is [`library_path`]: the environment
//! variable `P384_AWSLC_LIBCRYPTO` at run time, else the build tree
//! `bench_refs/aws-lc-build/crypto/libcrypto.so` next to this repository.
//! Nothing is linked at build time, so a missing library is not a build
//! error: [`available`] reports it and the tests skip.
//!
//! **What its P-384 arithmetic is** (checkout `f3798b6fe6a8`, AWS-LC 5.9.0,
//! `CMAKE_BUILD_TYPE=Release`, not FIPS, assembly enabled).
//! `EC_group_p384` (`crypto/fipsmodule/ec/ec.c`) sets
//! `EC_GFp_nistp384_method()` unless `OPENSSL_SMALL`.  `ec_nistp.h` defines
//! `EC_NISTP_USE_S2N_BIGNUM` on x86-64 Linux without `OPENSSL_NO_ASM`, and
//! `p384.c` then maps the field operations to s2n-bignum:
//! `bignum_montmul_p384_selector` and `bignum_montsqr_p384_selector` call the
//! MULX/ADX routines when the CPU has BMI2 and ADX and the `_alt` routines
//! otherwise (`third_party/s2n-bignum/s2n-bignum_aws-lc.h`).  The
//! variable-base multiply (ECDH) is s2n-bignum's `p384_montjscalarmul`; the
//! base-point multiply (signing) is `ec_nistp_scalar_mul_base`, a comb over
//! a precomputed table in C over those field calls; the two-term multiply
//! (verification) is `ec_nistp_scalar_mul_public`, interleaved wNAF of
//! width 5; the scalar inverse is Fermat, `bn_mod_inverse0_prime_mont_small`,
//! over the generic `bn_mul_mont` at six limbs.  The README gives the
//! file:line of each step.
//!
//! **Signing with a supplied nonce** is
//! `ECDSA_sign_with_nonce_and_leak_private_key_for_testing`, which reaches
//! the same `ecdsa_sign_impl` as `ECDSA_do_sign`
//! (`crypto/fipsmodule/ecdsa/ecdsa.c`) and skips the nonce derivation, as in
//! BoringSSL.  In this non-FIPS build the self-test hook it calls is an
//! inline no-op (`crypto/internal.h`).
//!
//! **DHKEM(P-384, HKDF-SHA384).**  AWS-LC's HPKE (`include/openssl/hpke.h`)
//! offers X25519 and ML-KEM KEMs only.  [`dhkem_encap`] and [`dhkem_decap`]
//! reconstruct DHKEM(P-384) from the exported `EC_POINT_oct2point`,
//! `EC_POINT_mul`, `EC_POINT_point2oct`, `ECDH_compute_key` and
//! `HKDF_extract` / `HKDF_expand` over `EVP_sha384()`, in the shape of
//! [`crate::bssl`].  `ECDH_compute_key` (`crypto/ecdh_extra/ecdh_extra.c`)
//! calls `ECDH_compute_shared_secret` (`crypto/fipsmodule/ecdh/ecdh.c`),
//! which copies the peer point into a fresh `EC_KEY` and runs
//! `EC_KEY_check_fips` on it on every call, in the non-FIPS build too.
//!
//! **Hybrid points.**  `EC_POINT_oct2point` (`crypto/fipsmodule/ec/oct.c`,
//! `ec_GFp_simple_oct2point` and `ec_point_from_hybrid`) accepts the X9.62
//! hybrid encoding, prefix `0x06` or `0x07` with the low bit equal to the
//! parity of `y`.  BoringSSL, from which AWS-LC forked, rejects it.  The
//! reconstruction therefore accepts a hybrid `enc`; RFC 9180 §7.1.1
//! specifies the uncompressed form, and `tests/dhkem_production.rs` pins
//! the difference.

#![allow(non_camel_case_types)]

use std::ffi::{c_char, c_int, c_ulong, c_void, CStr, CString};
use std::ptr;
use std::sync::OnceLock;

type EC_KEY = c_void;
type EC_GROUP = c_void;
type EC_POINT = c_void;
type BIGNUM = c_void;
type ECDSA_SIG = c_void;
type EVP_MD = c_void;

const NID_SECP384R1: c_int = 715;
/// `POINT_CONVERSION_UNCOMPRESSED`.
const UNCOMPRESSED_FORM: c_int = 4;
/// `OPENSSL_VERSION` for `OpenSSL_version`.
const OPENSSL_VERSION: c_int = 0;

const RTLD_NOW: c_int = 0x2;
const RTLD_LOCAL: c_int = 0x0;
const RTLD_DEEPBIND: c_int = 0x8;

extern "C" {
    fn dlopen(filename: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
}

/// The AWS-LC functions this bridge calls, resolved from the `dlopen`
/// handle.  Prototypes are those of the AWS-LC headers, which use `size_t`
/// lengths where OpenSSL uses `int`.
struct Api {
    version_num: unsafe extern "C" fn() -> c_ulong,
    api_version_num: unsafe extern "C" fn() -> c_ulong,
    version: unsafe extern "C" fn(c_int) -> *const c_char,
    err_clear_error: unsafe extern "C" fn(),
    ec_key_new_by_curve_name: unsafe extern "C" fn(c_int) -> *mut EC_KEY,
    ec_key_free: unsafe extern "C" fn(*mut EC_KEY),
    ec_key_set_private_key: unsafe extern "C" fn(*mut EC_KEY, *const BIGNUM) -> c_int,
    ec_key_set_public_key_affine_coordinates:
        unsafe extern "C" fn(*mut EC_KEY, *const BIGNUM, *const BIGNUM) -> c_int,
    ec_key_get0_group: unsafe extern "C" fn(*const EC_KEY) -> *const EC_GROUP,
    ec_group_get0_order: unsafe extern "C" fn(*const EC_GROUP) -> *const BIGNUM,
    bn_new: unsafe extern "C" fn() -> *mut BIGNUM,
    bn_free: unsafe extern "C" fn(*mut BIGNUM),
    bn_bin2bn: unsafe extern "C" fn(*const u8, usize, *mut BIGNUM) -> *mut BIGNUM,
    bn_bn2bin_padded: unsafe extern "C" fn(*mut u8, usize, *const BIGNUM) -> c_int,
    bn_rand_range_ex: unsafe extern "C" fn(*mut BIGNUM, u64, *const BIGNUM) -> c_int,
    sha512: unsafe extern "C" fn(*const u8, usize, *mut u8) -> *mut u8,
    ecdsa_sig_new: unsafe extern "C" fn() -> *mut ECDSA_SIG,
    ecdsa_sig_free: unsafe extern "C" fn(*mut ECDSA_SIG),
    ecdsa_sig_get0: unsafe extern "C" fn(*const ECDSA_SIG, *mut *const BIGNUM, *mut *const BIGNUM),
    ecdsa_sig_set0: unsafe extern "C" fn(*mut ECDSA_SIG, *mut BIGNUM, *mut BIGNUM) -> c_int,
    ecdsa_do_sign: unsafe extern "C" fn(*const u8, usize, *const EC_KEY) -> *mut ECDSA_SIG,
    ecdsa_do_verify: unsafe extern "C" fn(*const u8, usize, *const ECDSA_SIG, *const EC_KEY) -> c_int,
    ecdsa_sign_with_nonce: unsafe extern "C" fn(*const u8, usize, *const EC_KEY, *const u8, usize) -> *mut ECDSA_SIG,
    ec_point_new: unsafe extern "C" fn(*const EC_GROUP) -> *mut EC_POINT,
    ec_point_free: unsafe extern "C" fn(*mut EC_POINT),
    ec_point_oct2point: unsafe extern "C" fn(*const EC_GROUP, *mut EC_POINT, *const u8, usize, *mut c_void) -> c_int,
    ec_point_point2oct:
        unsafe extern "C" fn(*const EC_GROUP, *const EC_POINT, c_int, *mut u8, usize, *mut c_void) -> usize,
    ec_point_mul: unsafe extern "C" fn(
        *const EC_GROUP,
        *mut EC_POINT,
        *const BIGNUM,
        *const EC_POINT,
        *const BIGNUM,
        *mut c_void,
    ) -> c_int,
    ecdh_compute_key: unsafe extern "C" fn(*mut c_void, usize, *const EC_POINT, *const EC_KEY, *const c_void) -> c_int,
    evp_sha384: unsafe extern "C" fn() -> *const EVP_MD,
    hkdf_extract:
        unsafe extern "C" fn(*mut u8, *mut usize, *const EVP_MD, *const u8, usize, *const u8, usize) -> c_int,
    hkdf_expand: unsafe extern "C" fn(*mut u8, usize, *const EVP_MD, *const u8, usize, *const u8, usize) -> c_int,
}

/// The library path: `P384_AWSLC_LIBCRYPTO`, else the AWS-LC build tree at
/// `~/Claude/bench_refs/aws-lc-build`, located relative to this crate.
pub fn library_path() -> String {
    std::env::var("P384_AWSLC_LIBCRYPTO").unwrap_or_else(|_| {
        concat!(env!("CARGO_MANIFEST_DIR"), "/../../../bench_refs/aws-lc-build/crypto/libcrypto.so").to_string()
    })
}

fn load(path: &str) -> Option<Api> {
    if !std::path::Path::new(path).is_file() {
        return None;
    }
    let cpath = CString::new(path).ok()?;
    let handle = unsafe { dlopen(cpath.as_ptr(), RTLD_NOW | RTLD_LOCAL | RTLD_DEEPBIND) };
    if handle.is_null() {
        return None;
    }
    macro_rules! sym {
        ($name:literal) => {{
            let p = unsafe { dlsym(handle, concat!($name, "\0").as_ptr() as *const c_char) };
            assert!(!p.is_null(), concat!("AWS-LC libcrypto has no symbol ", $name));
            unsafe { std::mem::transmute(p) }
        }};
    }
    Some(Api {
        version_num: sym!("OpenSSL_version_num"),
        api_version_num: sym!("awslc_api_version_num"),
        version: sym!("OpenSSL_version"),
        err_clear_error: sym!("ERR_clear_error"),
        ec_key_new_by_curve_name: sym!("EC_KEY_new_by_curve_name"),
        ec_key_free: sym!("EC_KEY_free"),
        ec_key_set_private_key: sym!("EC_KEY_set_private_key"),
        ec_key_set_public_key_affine_coordinates: sym!("EC_KEY_set_public_key_affine_coordinates"),
        ec_key_get0_group: sym!("EC_KEY_get0_group"),
        ec_group_get0_order: sym!("EC_GROUP_get0_order"),
        bn_new: sym!("BN_new"),
        bn_free: sym!("BN_free"),
        bn_bin2bn: sym!("BN_bin2bn"),
        bn_bn2bin_padded: sym!("BN_bn2bin_padded"),
        bn_rand_range_ex: sym!("BN_rand_range_ex"),
        sha512: sym!("SHA512"),
        ecdsa_sig_new: sym!("ECDSA_SIG_new"),
        ecdsa_sig_free: sym!("ECDSA_SIG_free"),
        ecdsa_sig_get0: sym!("ECDSA_SIG_get0"),
        ecdsa_sig_set0: sym!("ECDSA_SIG_set0"),
        ecdsa_do_sign: sym!("ECDSA_do_sign"),
        ecdsa_do_verify: sym!("ECDSA_do_verify"),
        ecdsa_sign_with_nonce: sym!("ECDSA_sign_with_nonce_and_leak_private_key_for_testing"),
        ec_point_new: sym!("EC_POINT_new"),
        ec_point_free: sym!("EC_POINT_free"),
        ec_point_oct2point: sym!("EC_POINT_oct2point"),
        ec_point_point2oct: sym!("EC_POINT_point2oct"),
        ec_point_mul: sym!("EC_POINT_mul"),
        ecdh_compute_key: sym!("ECDH_compute_key"),
        evp_sha384: sym!("EVP_sha384"),
        hkdf_extract: sym!("HKDF_extract"),
        hkdf_expand: sym!("HKDF_expand"),
    })
}

fn try_api() -> Option<&'static Api> {
    static API: OnceLock<Option<Api>> = OnceLock::new();
    API.get_or_init(|| load(&library_path())).as_ref()
}

/// Whether the library at [`library_path`] exists and was loaded.  Every
/// other function in this module panics when it was not.
pub fn available() -> bool {
    try_api().is_some()
}

fn api() -> &'static Api {
    try_api().unwrap_or_else(|| panic!("AWS-LC libcrypto not loadable from {}", library_path()))
}

/// `OpenSSL_version_num()`, `awslc_api_version_num()` and
/// `OpenSSL_version(OPENSSL_VERSION)` of the loaded library.
pub fn version() -> (u64, u64, String) {
    let a = api();
    let num = unsafe { (a.version_num)() } as u64;
    let api_num = unsafe { (a.api_version_num)() } as u64;
    let text = unsafe { CStr::from_ptr((a.version)(OPENSSL_VERSION)) }.to_string_lossy().into_owned();
    (num, api_num, text)
}

/// A BIGNUM from 48 big-endian bytes.
fn bn(be: &[u8; 48]) -> *mut BIGNUM {
    let p = unsafe { (api().bn_bin2bn)(be.as_ptr(), 48, ptr::null_mut()) };
    assert!(!p.is_null(), "BN_bin2bn failed");
    p
}

/// A P-384 `EC_KEY`, freed on drop.
pub struct Key(*mut EC_KEY);

impl Drop for Key {
    fn drop(&mut self) {
        unsafe { (api().ec_key_free)(self.0) }
    }
}

fn new_key() -> *mut EC_KEY {
    let k = unsafe { (api().ec_key_new_by_curve_name)(NID_SECP384R1) };
    assert!(!k.is_null(), "EC_KEY_new_by_curve_name(secp384r1) failed");
    k
}

/// A signing key: the private scalar `d` and its public point `(x, y)`, all
/// big-endian.  `None` when AWS-LC refuses either.  Setting the public key
/// of a key that holds a private one runs AWS-LC's pairwise consistency
/// check (`ec_key_gen_pct`, `crypto/fipsmodule/ec/ec_key.c`).
pub fn signing_key(d: &[u8; 48], x: &[u8; 48], y: &[u8; 48]) -> Option<Key> {
    let a = api();
    let key = Key(new_key());
    let (dbn, xbn, ybn) = (bn(d), bn(x), bn(y));
    let ok = unsafe {
        (a.ec_key_set_private_key)(key.0, dbn) == 1
            && (a.ec_key_set_public_key_affine_coordinates)(key.0, xbn, ybn) == 1
    };
    unsafe {
        (a.bn_free)(dbn);
        (a.bn_free)(xbn);
        (a.bn_free)(ybn);
        if !ok {
            (a.err_clear_error)();
        }
    }
    ok.then_some(key)
}

/// A verifying key for the affine point `(x, y)`, big-endian.  `None` when
/// AWS-LC rejects the point.
pub fn verifying_key(x: &[u8; 48], y: &[u8; 48]) -> Option<Key> {
    let a = api();
    let key = Key(new_key());
    let (xbn, ybn) = (bn(x), bn(y));
    let ok = unsafe { (a.ec_key_set_public_key_affine_coordinates)(key.0, xbn, ybn) == 1 };
    unsafe {
        (a.bn_free)(xbn);
        (a.bn_free)(ybn);
        if !ok {
            (a.err_clear_error)();
        }
    }
    ok.then_some(key)
}

/// An `ECDSA_SIG`, freed on drop.
pub struct Sig(*mut ECDSA_SIG);

impl Drop for Sig {
    fn drop(&mut self) {
        unsafe { (api().ecdsa_sig_free)(self.0) }
    }
}

/// `(r, s)` as an `ECDSA_SIG`, big-endian.
pub fn sig(r: &[u8; 48], s: &[u8; 48]) -> Sig {
    let a = api();
    let sig = unsafe { (a.ecdsa_sig_new)() };
    assert!(!sig.is_null(), "ECDSA_SIG_new failed");
    let ok = unsafe { (a.ecdsa_sig_set0)(sig, bn(r), bn(s)) };
    assert_eq!(ok, 1, "ECDSA_SIG_set0 failed");
    Sig(sig)
}

/// `(r, s)` of a returned signature as big-endian bytes; frees it.
fn take(sig: *mut ECDSA_SIG) -> Option<([u8; 48], [u8; 48])> {
    let a = api();
    if sig.is_null() {
        unsafe { (a.err_clear_error)() };
        return None;
    }
    let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
    let (mut rp, mut sp) = (ptr::null(), ptr::null());
    let ok = unsafe {
        (a.ecdsa_sig_get0)(sig, &mut rp, &mut sp);
        let ok = (a.bn_bn2bin_padded)(r.as_mut_ptr(), 48, rp) == 1
            && (a.bn_bn2bin_padded)(s.as_mut_ptr(), 48, sp) == 1;
        (a.ecdsa_sig_free)(sig);
        ok
    };
    ok.then_some((r, s))
}

/// Signs the 48-byte digest with the nonce `k`, both big-endian, through
/// `ECDSA_sign_with_nonce_and_leak_private_key_for_testing`.  Returns
/// `(r, s)` big-endian, or `None` when AWS-LC refuses.
pub fn sign_with_nonce(key: &Key, digest: &[u8; 48], k: &[u8; 48]) -> Option<([u8; 48], [u8; 48])> {
    take(unsafe { (api().ecdsa_sign_with_nonce)(digest.as_ptr(), 48, key.0, k.as_ptr(), 48) })
}

/// Signs the 48-byte digest through `ECDSA_do_sign`, which derives its own
/// nonce.  Returns `(r, s)` big-endian.
pub fn sign(key: &Key, digest: &[u8; 48]) -> ([u8; 48], [u8; 48]) {
    take(unsafe { (api().ecdsa_do_sign)(digest.as_ptr(), 48, key.0) }).expect("AWS-LC ECDSA_do_sign failed")
}

/// Whether `ECDSA_do_verify` accepts `sig` on the 48-byte digest.
pub fn verify(key: &Key, digest: &[u8; 48], sig: &Sig) -> bool {
    let a = api();
    let ok = unsafe { (a.ecdsa_do_verify)(digest.as_ptr(), 48, sig.0, key.0) == 1 };
    if !ok {
        unsafe { (a.err_clear_error)() };
    }
    ok
}

/// Reusable output `BIGNUM` for [`nonce_parts`].
pub struct NonceState(*mut BIGNUM);

impl NonceState {
    pub fn new() -> Self {
        let p = unsafe { (api().bn_new)() };
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
        unsafe { (api().bn_free)(self.0) }
    }
}

/// The two parts of the nonce derivation `ECDSA_do_sign` adds to the
/// nonce-supplied path, rebuilt from exported functions as for BoringSSL:
/// SHA-512 over the six private-key words and the digest (one-shot `SHA512`
/// where the source makes two `SHA512_Update` calls), then
/// `BN_rand_range_ex(k, 1, n)`, which runs the `bn_rand_range_words`
/// rejection loop that `ec_random_nonzero_scalar` runs, with all-zero
/// additional data in place of the hash.  `priv_words` is the private
/// scalar as little-endian words.
pub fn nonce_parts(key: &Key, priv_words: &[u8; 48], digest: &[u8; 48], st: &mut NonceState) {
    let a = api();
    let mut buf = [0u8; 96];
    buf[..48].copy_from_slice(priv_words);
    buf[48..].copy_from_slice(digest);
    let mut out = [0u8; 64];
    unsafe {
        (a.sha512)(buf.as_ptr(), buf.len(), out.as_mut_ptr());
        let order = (a.ec_group_get0_order)((a.ec_key_get0_group)(key.0));
        assert_eq!((a.bn_rand_range_ex)(st.0, 1, order), 1, "BN_rand_range_ex failed");
    }
    std::hint::black_box(out);
}

// ---------------------------------------------------------------------------
// DHKEM(P-384, HKDF-SHA384), reconstructed
// ---------------------------------------------------------------------------

/// Reusable objects for [`dhkem_encap`] and [`dhkem_decap`]: an `EC_KEY`
/// holding only the private scalar, the parsed peer point, the ephemeral
/// public point and a `BIGNUM`.
pub struct KemState {
    key: *mut EC_KEY,
    group: *const EC_GROUP,
    peer: *mut EC_POINT,
    eph: *mut EC_POINT,
    scalar: *mut BIGNUM,
}

impl KemState {
    pub fn new() -> Self {
        let a = api();
        unsafe {
            let key = new_key();
            let group = (a.ec_key_get0_group)(key);
            let peer = (a.ec_point_new)(group);
            let eph = (a.ec_point_new)(group);
            let scalar = (a.bn_new)();
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
        let a = api();
        unsafe {
            (a.bn_free)(self.scalar);
            (a.ec_point_free)(self.eph);
            (a.ec_point_free)(self.peer);
            (a.ec_key_free)(self.key);
        }
    }
}

/// `ExtractAndExpand(dh, kem_context)` through `HKDF_extract` and
/// `HKDF_expand` with `EVP_sha384()`.
pub fn dhkem_extract_and_expand(dh: &[u8; 48], kem_context: &[u8; 194]) -> Option<[u8; 48]> {
    use crate::dhkem_kdf::{HPKE_VERSION, SUITE_ID};
    let a = api();
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
        let md = (a.evp_sha384)();
        (a.hkdf_extract)(prk.as_mut_ptr(), &mut prk_len, md, ikm.as_ptr(), ikm.len(), ptr::null(), 0) == 1
            && prk_len == 48
            && (a.hkdf_expand)(ss.as_mut_ptr(), 48, md, prk.as_ptr(), 48, info.as_ptr(), info.len()) == 1
    };
    ok.then_some(ss)
}

/// Sets the private scalar of the state's key; `false` when AWS-LC rejects
/// it (zero or not below `n`).
fn set_private(st: &mut KemState, sk_be: &[u8; 48]) -> bool {
    let a = api();
    let ok = unsafe {
        !(a.bn_bin2bn)(sk_be.as_ptr(), 48, st.scalar).is_null() && (a.ec_key_set_private_key)(st.key, st.scalar) == 1
    };
    if !ok {
        unsafe { (a.err_clear_error)() };
    }
    ok
}

/// `x(sk * peer)` into `dh`, with `peer` parsed from `peer_enc`; `false` when
/// AWS-LC rejects the point.
fn ecdh(st: &mut KemState, peer_enc: &[u8; 97], dh: &mut [u8; 48]) -> bool {
    let a = api();
    let ok = unsafe {
        (a.ec_point_oct2point)(st.group, st.peer, peer_enc.as_ptr(), 97, ptr::null_mut()) == 1
            && (a.ecdh_compute_key)(dh.as_mut_ptr().cast(), 48, st.peer, st.key, ptr::null()) == 48
    };
    if !ok {
        unsafe { (a.err_clear_error)() };
    }
    ok
}

/// `Encap(pkR)` with `skE` supplied (big-endian), or `None` when AWS-LC
/// rejects `skE` or `pkR`.
pub fn dhkem_encap(st: &mut KemState, sk_e_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<([u8; 97], [u8; 48])> {
    if !set_private(st, sk_e_be) {
        return None;
    }
    let a = api();
    let mut enc = [0u8; 97];
    let ok = unsafe {
        (a.ec_point_mul)(st.group, st.eph, st.scalar, ptr::null(), ptr::null(), ptr::null_mut()) == 1
            && (a.ec_point_point2oct)(st.group, st.eph, UNCOMPRESSED_FORM, enc.as_mut_ptr(), 97, ptr::null_mut()) == 97
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

/// `Decap(enc, skR)` with `pkR` supplied, or `None` when AWS-LC rejects
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
