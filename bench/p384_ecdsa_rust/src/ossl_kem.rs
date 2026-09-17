//! DHKEM(P-384, HKDF-SHA384) over OpenSSL `libcrypto.so.3`, loaded with
//! `dlopen` under the `production` feature, from two libraries:
//!
//! * the system OpenSSL 3.0.13 (`/usr/lib/x86_64-linux-gnu`), the library
//!   [`crate::ossl`] already opens.  3.0 has ECDH (`EVP_PKEY_derive`) and an
//!   HKDF KDF (`EVP_KDF "HKDF"`) but no HPKE and no DHKEM operation: both
//!   arrived in 3.2 (`providers/implementations/kem/ec_kem.c`,
//!   `crypto/hpke/`), and the loaded library exports no `OSSL_HPKE_*`
//!   symbol.  The DHKEM here is a **reconstruction** from those two
//!   primitives, in the shape of 3.2's `ec_kem.c`.
//! * an OpenSSL 3.6.0 `libcrypto.so.3` that Microsoft Defender for Endpoint
//!   ships at `/opt/microsoft/mdatp/lib` (override with
//!   `P384_OPENSSL36_LIBCRYPTO`).  It is the only OpenSSL on this machine
//!   with the 3.2+ API, and it is used as found: its build configuration
//!   is not documented, so which P-384 field code it runs is not known.
//!   It exports `EVP_PKEY_encapsulate` / `EVP_PKEY_decapsulate`, and with
//!   the KEM operation `"DHKEM"` those are the **native** RFC 9180 DHKEM of
//!   `ec_kem.c`, the layer `OSSL_HPKE_encap` calls before its key
//!   schedule.  The same reconstruction runs on it too.
//!
//! Both are opened `RTLD_NOW | RTLD_LOCAL | RTLD_DEEPBIND` by absolute path,
//! so the two copies and the statically linked BoringSSL do not bind to each
//! other's symbols; glibc matches an absolute `dlopen` path by file, not by
//! `SONAME`, so the two `libcrypto.so.3` are separate objects.
//!
//! **The reconstruction** (`Lib::recon_encap`, `Lib::recon_decap`): keys
//! are built per call with `EVP_PKEY_fromdata` (group `P-384`, `priv` and/or
//! `pub`), which validates a public key on import; the ephemeral public key
//! is `EC_POINT_mul` on a cached `EC_GROUP` and `EC_POINT_point2oct`; the DH
//! value is `EVP_PKEY_derive` after `EVP_PKEY_derive_set_peer`; and the key
//! derivation is two `EVP_KDF_derive` calls on a per-call `EVP_KDF_CTX` of a
//! cached `"HKDF"` fetch, in `EXTRACT_ONLY` and `EXPAND_ONLY` mode with
//! digest `SHA384`, as `crypto/hpke/hpke_util.c` does.
//!
//! **Hybrid points.**  Both libraries accept the X9.62 hybrid encoding,
//! prefix `0x06` or `0x07` with the low bit equal to the parity of `y`, for
//! a public key: `EC_POINT_oct2point` (`crypto/ec/ecp_oct.c`) admits
//! `POINT_CONVERSION_HYBRID`, and the 3.2+ DHKEM parses `enc` through it
//! (`providers/implementations/kem/ec_kem.c`, `eckey_frompub`, via
//! `EC_KEY_oct2key`).  RFC 9180 §7.1.1 specifies the uncompressed
//! conversion, and the emitted kernels, BoringSSL, RustCrypto, hpke-rs and
//! Graviola reject the hybrid form; `tests/dhkem_production.rs` pins the
//! difference.
//!
//! **The native DHKEM** (`Lib::native_encap`, `Lib::native_decap`, 3.6
//! only): `EVP_PKEY_encapsulate_init` with `operation = "DHKEM"` on the
//! recipient's public key, and `ikme` set so the ephemeral key is
//! `DeriveKeyPair(ikme)`; `EVP_PKEY_decapsulate_init` with the same
//! operation on the recipient's key pair.  The encapsulation therefore
//! includes `DeriveKeyPair`, which the emitted kernel does not perform (it
//! takes `skE`).

#![allow(non_camel_case_types)]

use std::ffi::{c_char, c_int, c_uint, c_ulong, c_void, CStr, CString};
use std::ptr;
use std::sync::OnceLock;

type EVP_PKEY = c_void;
type EVP_PKEY_CTX = c_void;
type EVP_KDF = c_void;
type EVP_KDF_CTX = c_void;
type EC_GROUP = c_void;
type EC_POINT = c_void;
type BIGNUM = c_void;
type BN_CTX = c_void;

const NID_SECP384R1: c_int = 715;
const RTLD_NOW: c_int = 0x2;
const RTLD_LOCAL: c_int = 0x0;
const RTLD_DEEPBIND: c_int = 0x8;

const OSSL_PARAM_INTEGER: c_uint = 1;
const OSSL_PARAM_UNSIGNED_INTEGER: c_uint = 2;
const OSSL_PARAM_UTF8_STRING: c_uint = 4;
const OSSL_PARAM_OCTET_STRING: c_uint = 5;
const OSSL_PARAM_UNMODIFIED: usize = usize::MAX;

/// `EVP_PKEY_PUBLIC_KEY`: all parameters and the public key.
const EVP_PKEY_PUBLIC_KEY: c_int = 0x84 | 0x02;
/// `EVP_PKEY_KEYPAIR`.
const EVP_PKEY_KEYPAIR: c_int = EVP_PKEY_PUBLIC_KEY | 0x01;
/// `EVP_PKEY_PRIVATE_KEY`.
const EVP_PKEY_PRIVATE_KEY: c_int = 0x84 | 0x01;

const EVP_KDF_HKDF_MODE_EXTRACT_ONLY: c_int = 1;
const EVP_KDF_HKDF_MODE_EXPAND_ONLY: c_int = 2;
const POINT_CONVERSION_UNCOMPRESSED: c_int = 4;

extern "C" {
    fn dlopen(filename: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
}

/// `OSSL_PARAM`, `include/openssl/core.h`.
#[repr(C)]
#[derive(Clone, Copy)]
struct OsslParam {
    key: *const c_char,
    data_type: c_uint,
    data: *mut c_void,
    data_size: usize,
    return_size: usize,
}

impl OsslParam {
    fn new(key: &'static CStr, data_type: c_uint, data: *const c_void, data_size: usize) -> Self {
        OsslParam {
            key: key.as_ptr(),
            data_type,
            data: data as *mut c_void,
            data_size,
            return_size: OSSL_PARAM_UNMODIFIED,
        }
    }
    fn utf8(key: &'static CStr, value: &'static CStr) -> Self {
        Self::new(key, OSSL_PARAM_UTF8_STRING, value.as_ptr().cast(), value.to_bytes().len())
    }
    fn octets(key: &'static CStr, value: &[u8]) -> Self {
        Self::new(key, OSSL_PARAM_OCTET_STRING, value.as_ptr().cast(), value.len())
    }
    fn end() -> Self {
        OsslParam { key: ptr::null(), data_type: 0, data: ptr::null_mut(), data_size: 0, return_size: 0 }
    }
}

type Fromdata = unsafe extern "C" fn(*mut EVP_PKEY_CTX, *mut *mut EVP_PKEY, c_int, *mut OsslParam) -> c_int;
type KemInit = unsafe extern "C" fn(*mut EVP_PKEY_CTX, *const OsslParam) -> c_int;

/// The functions a loaded library provides; the KEM entry points are
/// `None` where the library predates 3.2.
struct Api {
    version_num: unsafe extern "C" fn() -> c_ulong,
    version: unsafe extern "C" fn(c_int) -> *const c_char,
    pkey_ctx_new_from_name: unsafe extern "C" fn(*mut c_void, *const c_char, *const c_char) -> *mut EVP_PKEY_CTX,
    pkey_ctx_new_from_pkey: unsafe extern "C" fn(*mut c_void, *mut EVP_PKEY, *const c_char) -> *mut EVP_PKEY_CTX,
    pkey_ctx_free: unsafe extern "C" fn(*mut EVP_PKEY_CTX),
    fromdata_init: unsafe extern "C" fn(*mut EVP_PKEY_CTX) -> c_int,
    fromdata: Fromdata,
    pkey_free: unsafe extern "C" fn(*mut EVP_PKEY),
    derive_init: unsafe extern "C" fn(*mut EVP_PKEY_CTX) -> c_int,
    derive_set_peer: unsafe extern "C" fn(*mut EVP_PKEY_CTX, *mut EVP_PKEY) -> c_int,
    derive: unsafe extern "C" fn(*mut EVP_PKEY_CTX, *mut u8, *mut usize) -> c_int,
    kdf_fetch: unsafe extern "C" fn(*mut c_void, *const c_char, *const c_char) -> *mut EVP_KDF,
    kdf_ctx_new: unsafe extern "C" fn(*mut EVP_KDF) -> *mut EVP_KDF_CTX,
    kdf_ctx_free: unsafe extern "C" fn(*mut EVP_KDF_CTX),
    kdf_derive: unsafe extern "C" fn(*mut EVP_KDF_CTX, *mut u8, usize, *const OsslParam) -> c_int,
    group_new_by_curve_name: unsafe extern "C" fn(c_int) -> *mut EC_GROUP,
    point_new: unsafe extern "C" fn(*const EC_GROUP) -> *mut EC_POINT,
    point_mul: unsafe extern "C" fn(
        *const EC_GROUP,
        *mut EC_POINT,
        *const BIGNUM,
        *const EC_POINT,
        *const BIGNUM,
        *mut BN_CTX,
    ) -> c_int,
    point2oct: unsafe extern "C" fn(*const EC_GROUP, *const EC_POINT, c_int, *mut u8, usize, *mut BN_CTX) -> usize,
    bn_bin2bn: unsafe extern "C" fn(*const u8, c_int, *mut BIGNUM) -> *mut BIGNUM,
    bn_new: unsafe extern "C" fn() -> *mut BIGNUM,
    bn_ctx_new: unsafe extern "C" fn() -> *mut BN_CTX,
    err_clear_error: unsafe extern "C" fn(),
    encapsulate_init: Option<KemInit>,
    encapsulate: Option<unsafe extern "C" fn(*mut EVP_PKEY_CTX, *mut u8, *mut usize, *mut u8, *mut usize) -> c_int>,
    decapsulate_init: Option<KemInit>,
    decapsulate: Option<unsafe extern "C" fn(*mut EVP_PKEY_CTX, *mut u8, *mut usize, *const u8, usize) -> c_int>,
}

/// One loaded `libcrypto.so.3` with the objects the reconstruction caches.
pub struct Lib {
    path: String,
    api: Api,
    hkdf: *mut EVP_KDF,
    group: *mut EC_GROUP,
}

// The cached objects are immutable after construction and OpenSSL's fetched
// algorithms and groups are safe to share between threads.
unsafe impl Send for Lib {}
unsafe impl Sync for Lib {}

fn load(path: &str) -> Option<Lib> {
    if !std::path::Path::new(path).is_file() {
        return None;
    }
    let cpath = CString::new(path).ok()?;
    let handle = unsafe { dlopen(cpath.as_ptr(), RTLD_NOW | RTLD_LOCAL | RTLD_DEEPBIND) };
    if handle.is_null() {
        return None;
    }
    let raw = |name: &str| -> *mut c_void {
        let c = CString::new(name).unwrap();
        unsafe { dlsym(handle, c.as_ptr()) }
    };
    macro_rules! req {
        ($name:literal) => {{
            let p = raw($name);
            assert!(!p.is_null(), concat!("libcrypto has no symbol ", $name));
            unsafe { std::mem::transmute(p) }
        }};
    }
    macro_rules! opt {
        ($name:literal) => {{
            let p = raw($name);
            if p.is_null() {
                None
            } else {
                Some(unsafe { std::mem::transmute(p) })
            }
        }};
    }
    let api = Api {
        version_num: req!("OpenSSL_version_num"),
        version: req!("OpenSSL_version"),
        pkey_ctx_new_from_name: req!("EVP_PKEY_CTX_new_from_name"),
        pkey_ctx_new_from_pkey: req!("EVP_PKEY_CTX_new_from_pkey"),
        pkey_ctx_free: req!("EVP_PKEY_CTX_free"),
        fromdata_init: req!("EVP_PKEY_fromdata_init"),
        fromdata: req!("EVP_PKEY_fromdata"),
        pkey_free: req!("EVP_PKEY_free"),
        derive_init: req!("EVP_PKEY_derive_init"),
        derive_set_peer: req!("EVP_PKEY_derive_set_peer"),
        derive: req!("EVP_PKEY_derive"),
        kdf_fetch: req!("EVP_KDF_fetch"),
        kdf_ctx_new: req!("EVP_KDF_CTX_new"),
        kdf_ctx_free: req!("EVP_KDF_CTX_free"),
        kdf_derive: req!("EVP_KDF_derive"),
        group_new_by_curve_name: req!("EC_GROUP_new_by_curve_name"),
        point_new: req!("EC_POINT_new"),
        point_mul: req!("EC_POINT_mul"),
        point2oct: req!("EC_POINT_point2oct"),
        bn_bin2bn: req!("BN_bin2bn"),
        bn_new: req!("BN_new"),
        bn_ctx_new: req!("BN_CTX_new"),
        err_clear_error: req!("ERR_clear_error"),
        encapsulate_init: opt!("EVP_PKEY_encapsulate_init"),
        encapsulate: opt!("EVP_PKEY_encapsulate"),
        decapsulate_init: opt!("EVP_PKEY_decapsulate_init"),
        decapsulate: opt!("EVP_PKEY_decapsulate"),
    };
    let hkdf = unsafe { (api.kdf_fetch)(ptr::null_mut(), c"HKDF".as_ptr(), ptr::null()) };
    let group = unsafe { (api.group_new_by_curve_name)(NID_SECP384R1) };
    assert!(!hkdf.is_null() && !group.is_null(), "{path}: HKDF or P-384 unavailable");
    Some(Lib { path: path.to_string(), api, hkdf, group })
}

/// The system OpenSSL, the library [`crate::ossl`] loads.
pub fn system() -> &'static Lib {
    static LIB: OnceLock<Lib> = OnceLock::new();
    LIB.get_or_init(|| load(&crate::ossl::library_path()).expect("system libcrypto"))
}

/// The OpenSSL 3.6 path, `P384_OPENSSL36_LIBCRYPTO` or Defender's copy.
pub fn v36_path() -> String {
    std::env::var("P384_OPENSSL36_LIBCRYPTO").unwrap_or_else(|_| "/opt/microsoft/mdatp/lib/libcrypto.so.3".to_string())
}

/// The OpenSSL 3.2+ library, or `None` when the file is absent.
pub fn v36() -> Option<&'static Lib> {
    static LIB: OnceLock<Option<Lib>> = OnceLock::new();
    LIB.get_or_init(|| load(&v36_path())).as_ref()
}

/// Per-thread scratch for [`Lib::recon_encap`]: a `BIGNUM`, an `EC_POINT`
/// and a `BN_CTX`, allocated once per library.
pub struct Scratch {
    bn: *mut BIGNUM,
    point: *mut EC_POINT,
    ctx: *mut BN_CTX,
}

impl Lib {
    /// `OpenSSL_version(OPENSSL_VERSION)` and the path it was loaded from.
    pub fn version(&self) -> (u64, String, &str) {
        let num = unsafe { (self.api.version_num)() } as u64;
        let text = unsafe { CStr::from_ptr((self.api.version)(0)) }.to_string_lossy().into_owned();
        (num, text, &self.path)
    }

    /// Whether the library has the DHKEM operation: version 3.2 or later.
    /// The symbols alone do not decide it, since 3.0 already exports
    /// `EVP_PKEY_encapsulate_init` for its RSASVE KEM.
    pub fn has_native_dhkem(&self) -> bool {
        let num = unsafe { (self.api.version_num)() } as u64;
        num >= 0x3020_0000 && self.api.encapsulate_init.is_some() && self.api.decapsulate_init.is_some()
    }

    /// Fresh reusable scratch objects.  They are never freed; a benchmark
    /// or test process allocates a handful.
    pub fn scratch(&self) -> Scratch {
        unsafe {
            let s = Scratch {
                bn: (self.api.bn_new)(),
                point: (self.api.point_new)(self.group),
                ctx: (self.api.bn_ctx_new)(),
            };
            assert!(!s.bn.is_null() && !s.point.is_null() && !s.ctx.is_null());
            s
        }
    }

    /// An `EVP_PKEY` on P-384 from `priv` (little-endian native integer,
    /// as `OSSL_PARAM_BN` stores it) and/or `pub` (SEC1).  Null when
    /// OpenSSL rejects the data.
    fn pkey(&self, sk_le: Option<&[u8; 48]>, pk: Option<&[u8; 97]>) -> *mut EVP_PKEY {
        let a = &self.api;
        let mut params = vec![OsslParam::utf8(c"group", c"P-384")];
        let selection = match (sk_le, pk) {
            (Some(_), Some(_)) => EVP_PKEY_KEYPAIR,
            (Some(_), None) => EVP_PKEY_PRIVATE_KEY,
            (None, _) => EVP_PKEY_PUBLIC_KEY,
        };
        if let Some(sk) = sk_le {
            params.push(OsslParam::new(c"priv", OSSL_PARAM_UNSIGNED_INTEGER, sk.as_ptr().cast(), 48));
        }
        if let Some(pk) = pk {
            params.push(OsslParam::octets(c"pub", pk));
        }
        params.push(OsslParam::end());
        unsafe {
            let ctx = (a.pkey_ctx_new_from_name)(ptr::null_mut(), c"EC".as_ptr(), ptr::null());
            assert!(!ctx.is_null());
            let mut out: *mut EVP_PKEY = ptr::null_mut();
            let ok = (a.fromdata_init)(ctx) == 1 && (a.fromdata)(ctx, &mut out, selection, params.as_mut_ptr()) == 1;
            (a.pkey_ctx_free)(ctx);
            if !ok {
                (a.err_clear_error)();
                if !out.is_null() {
                    (a.pkey_free)(out);
                }
                return ptr::null_mut();
            }
            out
        }
    }

    /// `EVP_PKEY_derive` of `mine` against `peer` into 48 bytes.
    fn derive(&self, mine: *mut EVP_PKEY, peer: *mut EVP_PKEY, out: &mut [u8; 48]) -> bool {
        let a = &self.api;
        unsafe {
            let ctx = (a.pkey_ctx_new_from_pkey)(ptr::null_mut(), mine, ptr::null());
            let mut len = 48usize;
            let ok = !ctx.is_null()
                && (a.derive_init)(ctx) == 1
                && (a.derive_set_peer)(ctx, peer) == 1
                && (a.derive)(ctx, out.as_mut_ptr(), &mut len) == 1
                && len == 48;
            if !ctx.is_null() {
                (a.pkey_ctx_free)(ctx);
            }
            if !ok {
                (a.err_clear_error)();
            }
            ok
        }
    }

    fn kdf(&self, out: &mut [u8; 48], mode: c_int, key: &[u8], extra_name: &'static CStr, extra: &[u8]) -> bool {
        let a = &self.api;
        let mut mode = mode;
        let params = [
            OsslParam::utf8(c"digest", c"SHA384"),
            OsslParam::new(c"mode", OSSL_PARAM_INTEGER, (&mut mode as *mut c_int).cast(), size_of::<c_int>()),
            OsslParam::octets(c"key", key),
            OsslParam::octets(extra_name, extra),
            OsslParam::end(),
        ];
        unsafe {
            let ctx = (a.kdf_ctx_new)(self.hkdf);
            let ok = !ctx.is_null() && (a.kdf_derive)(ctx, out.as_mut_ptr(), 48, params.as_ptr()) == 1;
            (a.kdf_ctx_free)(ctx);
            ok
        }
    }

    /// `ExtractAndExpand(dh, kem_context)` through `EVP_KDF "HKDF"`.
    pub fn extract_and_expand(&self, dh: &[u8; 48], kem_context: &[u8; 194]) -> Option<[u8; 48]> {
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
        let mut ss = [0u8; 48];
        // HKDF-Extract: "key" is the input keying material, "salt" the salt.
        (self.kdf(&mut prk, EVP_KDF_HKDF_MODE_EXTRACT_ONLY, &ikm, c"salt", &[])
            && self.kdf(&mut ss, EVP_KDF_HKDF_MODE_EXPAND_ONLY, &prk, c"info", &info))
            .then_some(ss)
    }

    /// The reconstructed `Encap(pkR)` with `skE` supplied (big-endian), or
    /// `None` when OpenSSL rejects an input.
    pub fn recon_encap(&self, s: &mut Scratch, sk_e_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<([u8; 97], [u8; 48])> {
        let a = &self.api;
        let sk_le = crate::dhkem_kdf::sk_le_from_be(sk_e_be);
        let mut enc = [0u8; 97];
        let pub_ok = unsafe {
            !(a.bn_bin2bn)(sk_e_be.as_ptr(), 48, s.bn).is_null()
                && (a.point_mul)(self.group, s.point, s.bn, ptr::null(), ptr::null(), s.ctx) == 1
                && (a.point2oct)(self.group, s.point, POINT_CONVERSION_UNCOMPRESSED, enc.as_mut_ptr(), 97, s.ctx) == 97
        };
        let mine = self.pkey(Some(&sk_le), None);
        let peer = self.pkey(None, Some(pk_r));
        let mut dh = [0u8; 48];
        let ok = pub_ok && !mine.is_null() && !peer.is_null() && self.derive(mine, peer, &mut dh);
        unsafe {
            (a.pkey_free)(mine);
            (a.pkey_free)(peer);
            if !ok {
                (a.err_clear_error)();
                return None;
            }
        }
        let mut ctx = [0u8; 194];
        ctx[..97].copy_from_slice(&enc);
        ctx[97..].copy_from_slice(pk_r);
        Some((enc, self.extract_and_expand(&dh, &ctx)?))
    }

    /// The reconstructed `Decap(enc, skR)` with `pkR` supplied, or `None`
    /// when OpenSSL rejects an input.
    pub fn recon_decap(&self, enc: &[u8; 97], sk_r_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<[u8; 48]> {
        let sk_le = crate::dhkem_kdf::sk_le_from_be(sk_r_be);
        let mine = self.pkey(Some(&sk_le), None);
        let peer = self.pkey(None, Some(enc));
        let mut dh = [0u8; 48];
        let ok = !mine.is_null() && !peer.is_null() && self.derive(mine, peer, &mut dh);
        unsafe {
            (self.api.pkey_free)(mine);
            (self.api.pkey_free)(peer);
        }
        if !ok {
            return None;
        }
        let mut ctx = [0u8; 194];
        ctx[..97].copy_from_slice(enc);
        ctx[97..].copy_from_slice(pk_r);
        self.extract_and_expand(&dh, &ctx)
    }

    /// A recipient key for the native KEM: `EVP_PKEY` from `pkR` alone, for
    /// encapsulation.  Owned by the caller through [`Pkey`].
    pub fn public_pkey(&self, pk: &[u8; 97]) -> Option<Pkey<'_>> {
        let p = self.pkey(None, Some(pk));
        (!p.is_null()).then_some(Pkey { lib: self, p })
    }

    /// A recipient key pair for the native KEM's decapsulation.  `skR` is
    /// big-endian.
    pub fn keypair_pkey(&self, sk_be: &[u8; 48], pk: &[u8; 97]) -> Option<Pkey<'_>> {
        let p = self.pkey(Some(&crate::dhkem_kdf::sk_le_from_be(sk_be)), Some(pk));
        (!p.is_null()).then_some(Pkey { lib: self, p })
    }

    /// Native DHKEM encapsulation, `EVP_PKEY_encapsulate` with `operation =
    /// "DHKEM"` and `ikme` fixing the ephemeral key: `(enc, shared_secret)`,
    /// or `None` on refusal.  3.2+ only.
    pub fn native_encap(&self, recipient: &Pkey<'_>, ikme: &[u8]) -> Option<([u8; 97], [u8; 48])> {
        let a = &self.api;
        if !self.has_native_dhkem() {
            return None;
        }
        let (init, encap) = (a.encapsulate_init?, a.encapsulate?);
        let params = [
            OsslParam::utf8(c"operation", c"DHKEM"),
            OsslParam::octets(c"ikme", ikme),
            OsslParam::end(),
        ];
        let mut enc = [0u8; 97];
        let mut ss = [0u8; 48];
        let (mut enclen, mut sslen) = (97usize, 48usize);
        unsafe {
            let ctx = (a.pkey_ctx_new_from_pkey)(ptr::null_mut(), recipient.p, ptr::null());
            let ok = !ctx.is_null()
                && init(ctx, params.as_ptr()) == 1
                && encap(ctx, enc.as_mut_ptr(), &mut enclen, ss.as_mut_ptr(), &mut sslen) == 1
                && enclen == 97
                && sslen == 48;
            if !ctx.is_null() {
                (a.pkey_ctx_free)(ctx);
            }
            if !ok {
                (a.err_clear_error)();
                return None;
            }
        }
        Some((enc, ss))
    }

    /// Native DHKEM decapsulation, `EVP_PKEY_decapsulate` with `operation =
    /// "DHKEM"`, or `None` on refusal.  3.2+ only.
    pub fn native_decap(&self, recipient: &Pkey<'_>, enc: &[u8; 97]) -> Option<[u8; 48]> {
        let a = &self.api;
        if !self.has_native_dhkem() {
            return None;
        }
        let (init, decap) = (a.decapsulate_init?, a.decapsulate?);
        let params = [OsslParam::utf8(c"operation", c"DHKEM"), OsslParam::end()];
        let mut ss = [0u8; 48];
        let mut sslen = 48usize;
        unsafe {
            let ctx = (a.pkey_ctx_new_from_pkey)(ptr::null_mut(), recipient.p, ptr::null());
            let ok = !ctx.is_null()
                && init(ctx, params.as_ptr()) == 1
                && decap(ctx, ss.as_mut_ptr(), &mut sslen, enc.as_ptr(), 97) == 1
                && sslen == 48;
            if !ctx.is_null() {
                (a.pkey_ctx_free)(ctx);
            }
            if !ok {
                (a.err_clear_error)();
                return None;
            }
        }
        Some(ss)
    }
}

/// An `EVP_PKEY` of a loaded library, freed on drop.
pub struct Pkey<'a> {
    lib: &'a Lib,
    p: *mut EVP_PKEY,
}

impl Drop for Pkey<'_> {
    fn drop(&mut self) {
        unsafe { (self.lib.api.pkey_free)(self.p) }
    }
}
