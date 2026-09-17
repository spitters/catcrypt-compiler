//! Bridge to OpenSSL 3.0's `libcrypto.so.3`: a production opponent, loaded
//! with `dlopen` under the `production` feature.
//!
//! **Why `dlopen`.**  BoringSSL is linked statically into the same binary
//! ([`crate::bssl`]) and exports the same C names, so linking OpenSSL by name
//! as well would bind every call to whichever definition the linker met
//! first.  The system library is instead opened with
//! `RTLD_NOW | RTLD_LOCAL | RTLD_DEEPBIND` and each function is taken from
//! that handle with `dlsym`, so its own internal calls resolve inside itself.
//! A call through the resulting pointer is an indirect call, which is what a
//! dynamically linked production caller pays through the PLT as well.
//! `build.rs` fixes the path at build time (`P384_OPENSSL_LIBCRYPTO`) and
//! checks that the file exists; [`version`] reports what was loaded.
//!
//! **What its P-384 arithmetic is (3.0.13 sources).**  The `secp384r1`
//! entry of `crypto/ec/ec_curve.c` carries no method outside s390x, so
//! `ec_group_new_from_data` builds the group with `EC_GROUP_new_curve_GFp`,
//! and `crypto/ec/ec_cvt.c` picks `EC_GFp_mont_method()` whenever
//! `OPENSSL_BN_ASM_MONT` is defined.  The dedicated `ecp_nistp384.c` does not
//! exist in 3.0 (it arrived in 3.2); P-256 has `ecp_nistz256` assembly and
//! P-384 has nothing comparable.  The system library confirms the build:
//! it exports `EC_GFp_nistp224_method`, `EC_GFp_nistp256_method` and
//! `EC_GFp_nistp521_method` and no P-384 method.  The field multiply is
//! `ossl_ec_GFp_mont_field_mul` → `BN_mod_mul_montgomery` →
//! `bn_mul_mont_fixed_top` (`crypto/bn/bn_mont.c`) → `bn_mul_mont` in
//! `crypto/bn/asm/x86_64-mont.pl`, whose entry sends a limb count that is
//! not a multiple of four (six, here) to `.Lmul_enter`, the generic
//! word-serial MUL loop.  Points are `BIGNUM` Jacobian triples under the
//! `ecp_smpl.c` formulas; the base-point multiply in signing is
//! `ossl_ec_scalar_mul_ladder` (`crypto/ec/ec_mult.c`), a Montgomery ladder
//! with coordinate blinding; verification is `ossl_ec_wNAF_mul`, interleaved
//! wNAF with a 4-bit window at 384 bits; the scalar inverse is Fermat,
//! `BN_mod_exp_mont` to the exponent `n - 2` (`ec_field_inverse_mod_ord`,
//! `crypto/ec/ec_lib.c`).
//!
//! **Supplying the nonce.**  `ECDSA_do_sign_ex` takes a precomputed `kinv`
//! and `r`, and with both given `ossl_ecdsa_simple_sign_sig`
//! (`crypto/ec/ecdsa_ossl.c`) skips `ecdsa_sign_setup` entirely — no `k*G`
//! and no inverse, only `s = kinv (e + d r)`.  Timing it alone would leave out
//! most of the arithmetic.  [`sign_with_nonce`] therefore performs the steps
//! of `ecdsa_sign_setup` after the nonce draw through the public API, with
//! the same functions and arguments — `EC_POINT_mul(group, P, k, NULL, NULL,
//! ctx)`, `EC_POINT_get_affine_coordinates`, `BN_nnmod`, and
//! `BN_mod_exp_mont(kinv, k, n - 2, n, ctx, EC_GROUP_get_mont_data(group))`
//! — and then calls `ECDSA_do_sign_ex`.  It is a reconstruction of the
//! production sequence, not the production entry point; [`sign`] is the
//! entry point, and [`dsa_nonce`] is the nonce derivation it adds.

#![allow(non_camel_case_types)]

use std::ffi::{c_char, c_int, c_ulong, c_void, CStr, CString};
use std::ptr;
use std::sync::OnceLock;

type EC_KEY = c_void;
type EC_GROUP = c_void;
type EC_POINT = c_void;
type BIGNUM = c_void;
type BN_CTX = c_void;
type BN_MONT_CTX = c_void;
type ECDSA_SIG = c_void;

const NID_SECP384R1: c_int = 715;

const RTLD_NOW: c_int = 0x2;
const RTLD_LOCAL: c_int = 0x0;
const RTLD_DEEPBIND: c_int = 0x8;

extern "C" {
    fn dlopen(filename: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
    fn dlerror() -> *const c_char;
}

/// The OpenSSL functions this bridge calls, resolved from the `dlopen`
/// handle.  Prototypes are those of the 3.0 headers.
struct Api {
    version_num: unsafe extern "C" fn() -> c_ulong,
    version: unsafe extern "C" fn(c_int) -> *const c_char,
    ec_key_new_by_curve_name: unsafe extern "C" fn(c_int) -> *mut EC_KEY,
    ec_key_free: unsafe extern "C" fn(*mut EC_KEY),
    ec_key_set_private_key: unsafe extern "C" fn(*mut EC_KEY, *const BIGNUM) -> c_int,
    ec_key_set_public_key_affine_coordinates:
        unsafe extern "C" fn(*mut EC_KEY, *mut BIGNUM, *mut BIGNUM) -> c_int,
    ec_key_get0_group: unsafe extern "C" fn(*const EC_KEY) -> *const EC_GROUP,
    ec_key_get0_private_key: unsafe extern "C" fn(*const EC_KEY) -> *const BIGNUM,
    ec_group_get0_order: unsafe extern "C" fn(*const EC_GROUP) -> *const BIGNUM,
    ec_group_get_mont_data: unsafe extern "C" fn(*const EC_GROUP) -> *mut BN_MONT_CTX,
    ec_point_new: unsafe extern "C" fn(*const EC_GROUP) -> *mut EC_POINT,
    ec_point_free: unsafe extern "C" fn(*mut EC_POINT),
    ec_point_mul: unsafe extern "C" fn(
        *const EC_GROUP,
        *mut EC_POINT,
        *const BIGNUM,
        *const EC_POINT,
        *const BIGNUM,
        *mut BN_CTX,
    ) -> c_int,
    ec_point_get_affine_coordinates: unsafe extern "C" fn(
        *const EC_GROUP,
        *const EC_POINT,
        *mut BIGNUM,
        *mut BIGNUM,
        *mut BN_CTX,
    ) -> c_int,
    bn_new: unsafe extern "C" fn() -> *mut BIGNUM,
    bn_free: unsafe extern "C" fn(*mut BIGNUM),
    bn_bin2bn: unsafe extern "C" fn(*const u8, c_int, *mut BIGNUM) -> *mut BIGNUM,
    bn_bn2binpad: unsafe extern "C" fn(*const BIGNUM, *mut u8, c_int) -> c_int,
    bn_set_word: unsafe extern "C" fn(*mut BIGNUM, c_ulong) -> c_int,
    bn_sub: unsafe extern "C" fn(*mut BIGNUM, *const BIGNUM, *const BIGNUM) -> c_int,
    bn_nnmod: unsafe extern "C" fn(*mut BIGNUM, *const BIGNUM, *const BIGNUM, *mut BN_CTX) -> c_int,
    bn_mod_exp_mont: unsafe extern "C" fn(
        *mut BIGNUM,
        *const BIGNUM,
        *const BIGNUM,
        *const BIGNUM,
        *mut BN_CTX,
        *mut BN_MONT_CTX,
    ) -> c_int,
    bn_ctx_new: unsafe extern "C" fn() -> *mut BN_CTX,
    bn_ctx_free: unsafe extern "C" fn(*mut BN_CTX),
    bn_generate_dsa_nonce: unsafe extern "C" fn(
        *mut BIGNUM,
        *const BIGNUM,
        *const BIGNUM,
        *const u8,
        usize,
        *mut BN_CTX,
    ) -> c_int,
    ecdsa_sig_new: unsafe extern "C" fn() -> *mut ECDSA_SIG,
    ecdsa_sig_free: unsafe extern "C" fn(*mut ECDSA_SIG),
    ecdsa_sig_get0: unsafe extern "C" fn(*const ECDSA_SIG, *mut *const BIGNUM, *mut *const BIGNUM),
    ecdsa_sig_set0: unsafe extern "C" fn(*mut ECDSA_SIG, *mut BIGNUM, *mut BIGNUM) -> c_int,
    ecdsa_do_sign: unsafe extern "C" fn(*const u8, c_int, *mut EC_KEY) -> *mut ECDSA_SIG,
    ecdsa_do_sign_ex: unsafe extern "C" fn(
        *const u8,
        c_int,
        *const BIGNUM,
        *const BIGNUM,
        *mut EC_KEY,
    ) -> *mut ECDSA_SIG,
    ecdsa_do_verify: unsafe extern "C" fn(*const u8, c_int, *const ECDSA_SIG, *mut EC_KEY) -> c_int,
}

/// The library path `build.rs` recorded, overridable at run time with the
/// same variable.
pub fn library_path() -> String {
    std::env::var("P384_OPENSSL_LIBCRYPTO")
        .unwrap_or_else(|_| env!("P384_OPENSSL_LIBCRYPTO").to_string())
}

fn api() -> &'static Api {
    static API: OnceLock<Api> = OnceLock::new();
    API.get_or_init(|| {
        let path = CString::new(library_path()).expect("library path contains NUL");
        let handle = unsafe { dlopen(path.as_ptr(), RTLD_NOW | RTLD_LOCAL | RTLD_DEEPBIND) };
        if handle.is_null() {
            let why = unsafe { CStr::from_ptr(dlerror()) }.to_string_lossy().into_owned();
            panic!("dlopen({}) failed: {why}", library_path());
        }
        macro_rules! sym {
            ($name:literal) => {{
                let p = unsafe { dlsym(handle, concat!($name, "\0").as_ptr() as *const c_char) };
                assert!(!p.is_null(), concat!("libcrypto has no symbol ", $name));
                unsafe { std::mem::transmute(p) }
            }};
        }
        Api {
            version_num: sym!("OpenSSL_version_num"),
            version: sym!("OpenSSL_version"),
            ec_key_new_by_curve_name: sym!("EC_KEY_new_by_curve_name"),
            ec_key_free: sym!("EC_KEY_free"),
            ec_key_set_private_key: sym!("EC_KEY_set_private_key"),
            ec_key_set_public_key_affine_coordinates: sym!("EC_KEY_set_public_key_affine_coordinates"),
            ec_key_get0_group: sym!("EC_KEY_get0_group"),
            ec_key_get0_private_key: sym!("EC_KEY_get0_private_key"),
            ec_group_get0_order: sym!("EC_GROUP_get0_order"),
            ec_group_get_mont_data: sym!("EC_GROUP_get_mont_data"),
            ec_point_new: sym!("EC_POINT_new"),
            ec_point_free: sym!("EC_POINT_free"),
            ec_point_mul: sym!("EC_POINT_mul"),
            ec_point_get_affine_coordinates: sym!("EC_POINT_get_affine_coordinates"),
            bn_new: sym!("BN_new"),
            bn_free: sym!("BN_free"),
            bn_bin2bn: sym!("BN_bin2bn"),
            bn_bn2binpad: sym!("BN_bn2binpad"),
            bn_set_word: sym!("BN_set_word"),
            bn_sub: sym!("BN_sub"),
            bn_nnmod: sym!("BN_nnmod"),
            bn_mod_exp_mont: sym!("BN_mod_exp_mont"),
            bn_ctx_new: sym!("BN_CTX_new"),
            bn_ctx_free: sym!("BN_CTX_free"),
            bn_generate_dsa_nonce: sym!("BN_generate_dsa_nonce"),
            ecdsa_sig_new: sym!("ECDSA_SIG_new"),
            ecdsa_sig_free: sym!("ECDSA_SIG_free"),
            ecdsa_sig_get0: sym!("ECDSA_SIG_get0"),
            ecdsa_sig_set0: sym!("ECDSA_SIG_set0"),
            ecdsa_do_sign: sym!("ECDSA_do_sign"),
            ecdsa_do_sign_ex: sym!("ECDSA_do_sign_ex"),
            ecdsa_do_verify: sym!("ECDSA_do_verify"),
        }
    })
}

/// `OpenSSL_version_num()` and `OpenSSL_version(OPENSSL_VERSION)` of the
/// loaded library.
pub fn version() -> (u64, String) {
    let a = api();
    let num = unsafe { (a.version_num)() } as u64;
    let text = unsafe { CStr::from_ptr((a.version)(0)) }.to_string_lossy().into_owned();
    (num, text)
}

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

fn set_public(key: *mut EC_KEY, x: &[u8; 48], y: &[u8; 48]) -> bool {
    let a = api();
    let (xbn, ybn) = (bn(x), bn(y));
    let ok = unsafe { (a.ec_key_set_public_key_affine_coordinates)(key, xbn, ybn) == 1 };
    unsafe {
        (a.bn_free)(xbn);
        (a.bn_free)(ybn);
    }
    ok
}

/// A signing key: the private scalar `d` and its public point `(x, y)`, all
/// big-endian.  `None` when OpenSSL refuses either.
pub fn signing_key(d: &[u8; 48], x: &[u8; 48], y: &[u8; 48]) -> Option<Key> {
    let a = api();
    let key = Key(new_key());
    let dbn = bn(d);
    let ok = unsafe { (a.ec_key_set_private_key)(key.0, dbn) == 1 };
    unsafe { (a.bn_free)(dbn) };
    (ok && set_public(key.0, x, y)).then_some(key)
}

/// A verifying key for the affine point `(x, y)`, big-endian.  `None` when
/// OpenSSL rejects the point.
pub fn verifying_key(x: &[u8; 48], y: &[u8; 48]) -> Option<Key> {
    let key = Key(new_key());
    set_public(key.0, x, y).then_some(key)
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
    if sig.is_null() {
        return None;
    }
    let a = api();
    let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
    let (mut rp, mut sp) = (ptr::null(), ptr::null());
    let ok = unsafe {
        (a.ecdsa_sig_get0)(sig, &mut rp, &mut sp);
        let ok = (a.bn_bn2binpad)(rp, r.as_mut_ptr(), 48) == 48
            && (a.bn_bn2binpad)(sp, s.as_mut_ptr(), 48) == 48;
        (a.ecdsa_sig_free)(sig);
        ok
    };
    ok.then_some((r, s))
}

/// Signs the 48-byte digest with the nonce `k`, both big-endian: the steps
/// of `ecdsa_sign_setup` after its nonce draw, then `ECDSA_do_sign_ex`.
/// Returns `(r, s)` big-endian, or `None` when OpenSSL refuses (including a
/// zero `r`, which the production loop would answer by drawing again).
pub fn sign_with_nonce(key: &Key, digest: &[u8; 48], k: &[u8; 48]) -> Option<([u8; 48], [u8; 48])> {
    let a = api();
    unsafe {
        let group = (a.ec_key_get0_group)(key.0);
        let order = (a.ec_group_get0_order)(group);
        let ctx = (a.bn_ctx_new)();
        let kbn = bn(k);
        let r = (a.bn_new)();
        let x = (a.bn_new)();
        let e = (a.bn_new)();
        let point = (a.ec_point_new)(group);
        assert!(!ctx.is_null() && !r.is_null() && !x.is_null() && !e.is_null() && !point.is_null());

        // ecdsa_sign_setup: r = x(k*G) mod n.
        let mut ok = (a.ec_point_mul)(group, point, kbn, ptr::null(), ptr::null(), ctx) == 1
            && (a.ec_point_get_affine_coordinates)(group, point, x, ptr::null_mut(), ctx) == 1
            && (a.bn_nnmod)(r, x, order, ctx) == 1;
        // ec_field_inverse_mod_ord: kinv = k^(n-2) mod n.
        ok = ok
            && (a.bn_set_word)(e, 2) == 1
            && (a.bn_sub)(e, order, e) == 1
            && (a.bn_mod_exp_mont)(kbn, kbn, e, order, ctx, (a.ec_group_get_mont_data)(group)) == 1;
        let out = if ok {
            take((a.ecdsa_do_sign_ex)(digest.as_ptr(), 48, kbn, r, key.0))
        } else {
            None
        };

        (a.ec_point_free)(point);
        (a.bn_free)(e);
        (a.bn_free)(x);
        (a.bn_free)(r);
        (a.bn_free)(kbn);
        (a.bn_ctx_free)(ctx);
        out
    }
}

/// Signs the 48-byte digest through `ECDSA_do_sign`, which derives its own
/// nonce.  Returns `(r, s)` big-endian.
pub fn sign(key: &Key, digest: &[u8; 48]) -> ([u8; 48], [u8; 48]) {
    take(unsafe { (api().ecdsa_do_sign)(digest.as_ptr(), 48, key.0) })
        .expect("OpenSSL ECDSA_do_sign failed")
}

/// Whether `ECDSA_do_verify` accepts `sig` on the 48-byte digest.
pub fn verify(key: &Key, digest: &[u8; 48], sig: &Sig) -> bool {
    unsafe { (api().ecdsa_do_verify)(digest.as_ptr(), 48, sig.0, key.0) == 1 }
}

/// Reusable state for [`dsa_nonce`]: a `BN_CTX` and the output `BIGNUM`.
pub struct NonceState {
    ctx: *mut BN_CTX,
    k: *mut BIGNUM,
}

impl NonceState {
    pub fn new() -> Self {
        let a = api();
        let ctx = unsafe { (a.bn_ctx_new)() };
        let k = unsafe { (a.bn_new)() };
        assert!(!ctx.is_null() && !k.is_null());
        NonceState { ctx, k }
    }
}

impl Default for NonceState {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for NonceState {
    fn drop(&mut self) {
        let a = api();
        unsafe {
            (a.bn_free)(self.k);
            (a.bn_ctx_free)(self.ctx);
        }
    }
}

/// The nonce derivation `ecdsa_sign_setup` performs when given a digest:
/// `BN_generate_dsa_nonce(k, n, d, digest, 48, ctx)`.  For the 56 bytes a
/// 48-byte order needs it fetches SHA-512 through `EVP_MD_fetch` and runs two
/// rounds, each drawing 64 bytes from the private RNG and hashing them with a
/// counter, the private key and the digest, then reduces mod `n`
/// (`crypto/bn/bn_rand.c`).  Returns the nonce, big-endian.
pub fn dsa_nonce(key: &Key, digest: &[u8; 48], st: &mut NonceState) -> [u8; 48] {
    let a = api();
    let mut out = [0u8; 48];
    unsafe {
        let group = (a.ec_key_get0_group)(key.0);
        let order = (a.ec_group_get0_order)(group);
        let d = (a.ec_key_get0_private_key)(key.0);
        let ok = (a.bn_generate_dsa_nonce)(st.k, order, d, digest.as_ptr(), 48, st.ctx);
        assert_eq!(ok, 1, "BN_generate_dsa_nonce failed");
        assert_eq!((a.bn_bn2binpad)(st.k, out.as_mut_ptr(), 48), 48);
    }
    out
}
