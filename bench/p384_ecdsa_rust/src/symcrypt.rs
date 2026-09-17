//! Bridge to Microsoft SymCrypt's shared module `libsymcrypt.so.103`: a
//! production opponent, loaded with `dlopen` under the `production` feature.
//!
//! **Loading.**  The module is opened by absolute path with
//! `RTLD_NOW | RTLD_LOCAL | RTLD_DEEPBIND`, as [`crate::awslc`] opens AWS-LC,
//! and every function is taken from that handle with `dlsym`.  The path is
//! [`library_path`]: the environment variable `P384_SYMCRYPT_LIB` at run
//! time, else the CMake build tree
//! `bench_refs/symcrypt/build/cmake/Linux_AMD64_GCC_Release/module/libsymcrypt.so.103`
//! next to this repository.  Nothing is linked at build time, so a missing
//! module is not a build error: [`available`] reports it and the tests skip.
//! The module's ELF constructor (`modules/posix/common/module.c`,
//! `SymCryptModuleMain`) calls `SymCryptInit` and `SymCryptRngInit`, so no
//! initialisation call is needed; [`load`] calls `SymCryptModuleInitEx(103,
//! 13)`, the version check `SYMCRYPT_MODULE_INIT_EX()` expands to, and
//! treats a refusal as absence.
//!
//! **What its P-384 arithmetic is** (v103.13.0, commit `286762b`, preset
//! `Linux_AMD64_GCC_Release`).  `SymCryptEcurveAllocate` builds the field
//! modulus with `SYMCRYPT_FLAG_DATA_PUBLIC` (`lib/ecurve.c:284-290`);
//! `SymCryptFdefDecideModulusType` (`lib/fdef_mod.c:300-319`) recognises the
//! P-384 prime and the selection table (`lib/a_dispatch.c:81`) then picks
//! `SymCryptFdefModMulMontgomeryMulxP384Asm`, a MULX/ADCX/ADOX Montgomery
//! multiply with a reduction specialised to the form of `p`
//! (`lib/amd64/fdef_mulx.symcryptasm:1439-1660`), when the CPU has BMI2 and
//! ADX.  The group order is built with an expected operation count of 1
//! (`lib/ecurve.c:14`, `:399-405`), below the Montgomery threshold of 10
//! (`lib/fdef_mod.c:300-303`), so it takes the generic table
//! (`lib/a_dispatch.c:101`): each multiply mod `n` is a MULX product and a
//! division.  Points are Jacobian; `k*G` is a signed fixed-window multiply,
//! `w = 6`, over sixteen odd multiples of `G` precomputed at curve
//! allocation; `u1*G + u2*Q` is interleaved wNAF (`lib/ec_mul.c`).  A gdb
//! count over one test (README § SymCrypt) confirms the field and group-order
//! routines.  The README gives the file:line of each step.
//!
//! **Signing.**  `SymCryptEcDsaSignEx`, which takes a nonce `piK`, is
//! defined in `lib/ec_dsa.c:146` but is not in the module's export list
//! (`modules/posix/common/exports.ver`), so the only signing entry point is
//! `SymCryptEcDsaSign`, which draws `k` from the module RNG
//! (`SymCryptEcpointSetRandom`).  There is no nonce-supplied arm: a SymCrypt
//! signature cannot be compared byte for byte with the kernel's, and the
//! benchmark's SymCrypt signing figure is the full API.  [`random48`] times
//! one 48-byte draw of that RNG, the dominant part of the nonce derivation.
//!
//! **DHKEM(P-384, HKDF-SHA384).**  SymCrypt has no HPKE.  [`dhkem_encap`]
//! and [`dhkem_decap`] reconstruct DHKEM(P-384) from `SymCryptEckeySetValue`,
//! `SymCryptEckeyGetValue`, `SymCryptEcDhSecretAgreement` and `SymCryptHkdf`
//! over `SymCryptHmacSha384Algorithm`.  `SymCryptHkdf` is RFC 5869
//! `Expand(Extract(salt, ikm), info, L)` in one call, so `ExtractAndExpand`
//! with the labelled `ikm` and `info` built here is a single call with an
//! empty salt.  SymCrypt takes public keys as the 96-byte `X || Y` string
//! (`SYMCRYPT_ECPOINT_FORMAT_XY`); the SEC1 prefix is checked here, and only
//! `0x04` is accepted.

#![allow(non_camel_case_types)]

use std::ffi::{c_char, c_int, c_void, CString};
use std::ptr;
use std::sync::OnceLock;

type ECURVE = c_void;
type ECKEY = c_void;
type MAC = c_void;
type SCError = c_int;

const SYMCRYPT_NO_ERROR: SCError = 0;
/// `SYMCRYPT_NUMBER_FORMAT_MSB_FIRST`.
const MSB_FIRST: c_int = 2;
/// `SYMCRYPT_ECPOINT_FORMAT_XY`.
const POINT_XY: c_int = 2;

/// `SYMCRYPT_FLAG_KEY_NO_FIPS`: skips the FIPS pairwise regeneration check
/// on import of a key pair and the self-tests.
pub const FLAG_KEY_NO_FIPS: u32 = 0x100;
/// `SYMCRYPT_FLAG_KEY_MINIMAL_VALIDATION`: skips the private-key range check
/// and the public-key curve check; only valid with [`FLAG_KEY_NO_FIPS`].
pub const FLAG_KEY_MINIMAL_VALIDATION: u32 = 0x200;
/// `SYMCRYPT_FLAG_ECKEY_ECDSA`.
pub const FLAG_ECKEY_ECDSA: u32 = 0x1000;
/// `SYMCRYPT_FLAG_ECKEY_ECDH`.
pub const FLAG_ECKEY_ECDH: u32 = 0x2000;

/// The API and minor version this bridge was written against
/// (`version.json` of the checkout).
pub const API_VERSION: (u32, u32) = (103, 13);

const RTLD_NOW: c_int = 0x2;
const RTLD_LOCAL: c_int = 0x0;
const RTLD_DEEPBIND: c_int = 0x8;

extern "C" {
    fn dlopen(filename: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
}

/// The SymCrypt functions this bridge calls, resolved from the `dlopen`
/// handle, and the P-384 curve object allocated once.  Prototypes are those
/// of `inc/symcrypt.h`; `SYMCRYPT_CALL` is empty on x86-64 Linux, and the
/// `SYMCRYPT_ERROR`, `SYMCRYPT_NUMBER_FORMAT` and `SYMCRYPT_ECPOINT_FORMAT`
/// enumerations are `int`.
struct Api {
    module_init_ex: unsafe extern "C" fn(u32, u32) -> SCError,
    eckey_allocate: unsafe extern "C" fn(*const ECURVE) -> *mut ECKEY,
    eckey_free: unsafe extern "C" fn(*mut ECKEY),
    eckey_set_value:
        unsafe extern "C" fn(*const u8, usize, *const u8, usize, c_int, c_int, u32, *mut ECKEY) -> SCError,
    eckey_get_value:
        unsafe extern "C" fn(*const ECKEY, *mut u8, usize, *mut u8, usize, c_int, c_int, u32) -> SCError,
    ecdsa_sign: unsafe extern "C" fn(*const ECKEY, *const u8, usize, c_int, u32, *mut u8, usize) -> SCError,
    ecdsa_verify: unsafe extern "C" fn(*const ECKEY, *const u8, usize, *const u8, usize, c_int, u32) -> SCError,
    ecdh: unsafe extern "C" fn(*const ECKEY, *const ECKEY, c_int, u32, *mut u8, usize) -> SCError,
    hkdf: unsafe extern "C" fn(*const MAC, *const u8, usize, *const u8, usize, *const u8, usize, *mut u8, usize)
        -> SCError,
    random: unsafe extern "C" fn(*mut u8, usize),
    hmac_sha384: *const MAC,
    curve: *mut ECURVE,
}

// The curve object is immutable after `SymCryptEcurveAllocate` and the MAC
// descriptor is a constant table; SymCrypt shares both between threads.
unsafe impl Send for Api {}
unsafe impl Sync for Api {}

/// The module path: `P384_SYMCRYPT_LIB`, else the SymCrypt CMake build tree
/// at `~/Claude/bench_refs/symcrypt`, located relative to this crate.
pub fn library_path() -> String {
    std::env::var("P384_SYMCRYPT_LIB").unwrap_or_else(|_| {
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../bench_refs/symcrypt/build/cmake/Linux_AMD64_GCC_Release/module/libsymcrypt.so.103"
        )
        .to_string()
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
    let lookup = |name: &str| -> *mut c_void {
        let cname = CString::new(name).unwrap();
        let p = unsafe { dlsym(handle, cname.as_ptr()) };
        assert!(!p.is_null(), "SymCrypt module has no symbol {name}");
        p
    };
    macro_rules! addr {
        ($name:literal) => {
            lookup($name)
        };
    }
    macro_rules! sym {
        ($name:literal) => {{
            unsafe { std::mem::transmute(addr!($name)) }
        }};
    }
    let module_init_ex: unsafe extern "C" fn(u32, u32) -> SCError = sym!("SymCryptModuleInitEx");
    if unsafe { module_init_ex(API_VERSION.0, API_VERSION.1) } != SYMCRYPT_NO_ERROR {
        return None;
    }
    // `SymCryptEcurveParamsNistP384` and `SymCryptHmacSha384Algorithm` are
    // exported `const` pointer variables; `dlsym` returns their address.
    let params = unsafe { *(addr!("SymCryptEcurveParamsNistP384") as *const *const c_void) };
    let hmac_sha384 = unsafe { *(addr!("SymCryptHmacSha384Algorithm") as *const *const MAC) };
    let ecurve_allocate: unsafe extern "C" fn(*const c_void, u32) -> *mut ECURVE = sym!("SymCryptEcurveAllocate");
    let curve = unsafe { ecurve_allocate(params, 0) };
    assert!(!curve.is_null(), "SymCryptEcurveAllocate(NistP384) failed");
    Some(Api {
        module_init_ex,
        eckey_allocate: sym!("SymCryptEckeyAllocate"),
        eckey_free: sym!("SymCryptEckeyFree"),
        eckey_set_value: sym!("SymCryptEckeySetValue"),
        eckey_get_value: sym!("SymCryptEckeyGetValue"),
        ecdsa_sign: sym!("SymCryptEcDsaSign"),
        ecdsa_verify: sym!("SymCryptEcDsaVerify"),
        ecdh: sym!("SymCryptEcDhSecretAgreement"),
        hkdf: sym!("SymCryptHkdf"),
        random: sym!("SymCryptRandom"),
        hmac_sha384,
        curve,
    })
}

fn try_api() -> Option<&'static Api> {
    static API: OnceLock<Option<Api>> = OnceLock::new();
    API.get_or_init(|| load(&library_path())).as_ref()
}

/// Whether the module at [`library_path`] exists, loaded, and accepted
/// [`API_VERSION`].  Every other function in this module panics when not.
pub fn available() -> bool {
    try_api().is_some()
}

fn api() -> &'static Api {
    try_api().unwrap_or_else(|| panic!("SymCrypt module not loadable from {}", library_path()))
}

/// Whether `SymCryptModuleInitEx(api, minor)` accepts the version: the same
/// API number and a minor version not above the module's.
pub fn accepts_version(api_version: u32, minor: u32) -> bool {
    unsafe { (api().module_init_ex)(api_version, minor) == SYMCRYPT_NO_ERROR }
}

/// A P-384 `SYMCRYPT_ECKEY`, freed on drop.
pub struct Key(*mut ECKEY);

impl Drop for Key {
    fn drop(&mut self) {
        unsafe { (api().eckey_free)(self.0) }
    }
}

fn new_key() -> Key {
    let a = api();
    let k = unsafe { (a.eckey_allocate)(a.curve) };
    assert!(!k.is_null(), "SymCryptEckeyAllocate failed");
    Key(k)
}

fn xy(x: &[u8; 48], y: &[u8; 48]) -> [u8; 96] {
    let mut p = [0u8; 96];
    p[..48].copy_from_slice(x);
    p[48..].copy_from_slice(y);
    p
}

fn set_value(key: &mut Key, sk: Option<&[u8; 48]>, pk_xy: Option<&[u8; 96]>, flags: u32) -> SCError {
    let (sp, sl) = sk.map_or((ptr::null(), 0), |s| (s.as_ptr(), 48));
    let (pp, pl) = pk_xy.map_or((ptr::null(), 0), |p| (p.as_ptr(), 96));
    unsafe { (api().eckey_set_value)(sp, sl, pp, pl, MSB_FIRST, POINT_XY, flags, key.0) }
}

/// `SymCryptEckeySetValue` into a fresh key with the given flags: a
/// big-endian private scalar, a big-endian `X || Y` public point, or both.
/// `Err` carries the `SYMCRYPT_ERROR` value.
pub fn import(sk: Option<&[u8; 48]>, pk_xy: Option<&[u8; 96]>, flags: u32) -> Result<Key, i32> {
    let mut key = new_key();
    match set_value(&mut key, sk, pk_xy, flags) {
        SYMCRYPT_NO_ERROR => Ok(key),
        e => Err(e),
    }
}

/// A signing key: the private scalar `d` and its public point `(x, y)`, all
/// big-endian, imported with `SYMCRYPT_FLAG_ECKEY_ECDSA` and the default
/// (FIPS) validation, which recomputes `d*G` and compares it with `(x, y)`
/// (`lib/eckey.c:486-529`).  `None` when SymCrypt refuses either.
pub fn signing_key(d: &[u8; 48], x: &[u8; 48], y: &[u8; 48]) -> Option<Key> {
    import(Some(d), Some(&xy(x, y)), FLAG_ECKEY_ECDSA).ok()
}

/// A verifying key for the affine point `(x, y)`, big-endian.  `None` when
/// SymCrypt rejects the point (a coordinate not below `p`, or off the curve).
pub fn verifying_key(x: &[u8; 48], y: &[u8; 48]) -> Option<Key> {
    import(None, Some(&xy(x, y)), FLAG_ECKEY_ECDSA).ok()
}

/// An ECDSA signature in SymCrypt's format: `r || s`, 48 big-endian bytes
/// each.
pub struct Sig([u8; 96]);

/// `(r, s)` as a SymCrypt signature, big-endian.
pub fn sig(r: &[u8; 48], s: &[u8; 48]) -> Sig {
    Sig(xy(r, s))
}

/// Signs the 48-byte digest through `SymCryptEcDsaSign`, which draws its own
/// nonce from the module RNG.  Flags 0: the digest is 384 bits, so the
/// standard truncation (`lib/ec_dsa.c:84-140`) leaves it unchanged.  Returns
/// `(r, s)` big-endian.
pub fn sign(key: &Key, digest: &[u8; 48]) -> ([u8; 48], [u8; 48]) {
    let mut out = [0u8; 96];
    let e = unsafe { (api().ecdsa_sign)(key.0, digest.as_ptr(), 48, MSB_FIRST, 0, out.as_mut_ptr(), 96) };
    assert_eq!(e, SYMCRYPT_NO_ERROR, "SymCryptEcDsaSign failed");
    let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
    r.copy_from_slice(&out[..48]);
    s.copy_from_slice(&out[48..]);
    (r, s)
}

/// Whether `SymCryptEcDsaVerify` accepts `sig` on the 48-byte digest.
pub fn verify(key: &Key, digest: &[u8; 48], sig: &Sig) -> bool {
    unsafe { (api().ecdsa_verify)(key.0, digest.as_ptr(), 48, sig.0.as_ptr(), 96, MSB_FIRST, 0) == SYMCRYPT_NO_ERROR }
}

/// One `SymCryptRandom` call for 48 bytes: the draw `SymCryptEcDsaSign` makes
/// for `k` through `SymCryptModSetRandom` (`lib/fdef_mod.c:784-803`, one
/// iteration unless the value is rejected).
pub fn random48(out: &mut [u8; 48]) {
    unsafe { (api().random)(out.as_mut_ptr(), 48) }
}

/// `x(sk * peer)` through `SymCryptEcDhSecretAgreement`, big-endian.
/// Both keys must carry `SYMCRYPT_FLAG_ECKEY_ECDH`.
pub fn ecdh(private: &Key, public: &Key) -> Option<[u8; 48]> {
    let mut dh = [0u8; 48];
    let e = unsafe { (api().ecdh)(private.0, public.0, MSB_FIRST, 0, dh.as_mut_ptr(), 48) };
    (e == SYMCRYPT_NO_ERROR).then_some(dh)
}

// ---------------------------------------------------------------------------
// DHKEM(P-384, HKDF-SHA384), reconstructed
// ---------------------------------------------------------------------------

/// Reusable key objects for [`dhkem_encap`] and [`dhkem_decap`]: one that
/// holds the private scalar, one that holds the peer's public point.
pub struct KemState {
    own: Key,
    peer: Key,
}

impl KemState {
    pub fn new() -> Self {
        KemState { own: new_key(), peer: new_key() }
    }
}

impl Default for KemState {
    fn default() -> Self {
        Self::new()
    }
}

/// `ExtractAndExpand(dh, kem_context)` as one `SymCryptHkdf` call over
/// `SymCryptHmacSha384Algorithm`, with an empty salt, the labelled `ikm`
/// and the labelled `info`.
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
    let mut ss = [0u8; 48];
    let e = unsafe {
        (a.hkdf)(
            a.hmac_sha384,
            ikm.as_ptr(),
            ikm.len(),
            ptr::null(),
            0,
            info.as_ptr(),
            info.len(),
            ss.as_mut_ptr(),
            48,
        )
    };
    (e == SYMCRYPT_NO_ERROR).then_some(ss)
}

/// The `X || Y` bytes of an uncompressed SEC1 point, or `None` for any other
/// prefix.
fn sec1_xy(s: &[u8; 97]) -> Option<[u8; 96]> {
    if s[0] != 0x04 {
        return None;
    }
    let mut p = [0u8; 96];
    p.copy_from_slice(&s[1..]);
    Some(p)
}

/// Imports `peer_enc` as an ECDH public key with the default validation.
fn set_peer(st: &mut KemState, peer_enc: &[u8; 97]) -> bool {
    match sec1_xy(peer_enc) {
        Some(p) => set_value(&mut st.peer, None, Some(&p), FLAG_ECKEY_ECDH) == SYMCRYPT_NO_ERROR,
        None => false,
    }
}

fn context(enc: &[u8; 97], pk_r: &[u8; 97]) -> [u8; 194] {
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(enc);
    ctx[97..].copy_from_slice(pk_r);
    ctx
}

/// `Encap(pkR)` with `skE` supplied (big-endian), or `None` when SymCrypt
/// rejects `skE` or `pkR`.  `skE` is imported alone with the default
/// validation, so `SymCryptEckeySetValue` computes `skE*G` (the one
/// fixed-base multiply of `Encap`), which `SymCryptEckeyGetValue` returns as
/// `enc`.
pub fn dhkem_encap(st: &mut KemState, sk_e_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<([u8; 97], [u8; 48])> {
    if set_value(&mut st.own, Some(sk_e_be), None, FLAG_ECKEY_ECDH) != SYMCRYPT_NO_ERROR {
        return None;
    }
    let mut enc = [0u8; 97];
    enc[0] = 0x04;
    let e = unsafe {
        (api().eckey_get_value)(st.own.0, ptr::null_mut(), 0, enc[1..].as_mut_ptr(), 96, MSB_FIRST, POINT_XY, 0)
    };
    if e != SYMCRYPT_NO_ERROR || !set_peer(st, pk_r) {
        return None;
    }
    let dh = ecdh(&st.own, &st.peer)?;
    Some((enc, dhkem_extract_and_expand(&dh, &context(&enc, pk_r))?))
}

/// `Decap(enc, skR)` with `pkR` supplied, or `None` when SymCrypt rejects
/// `enc`, `skR` or `pkR`.  The recipient key is imported as the pair
/// `(skR, pkR)` with `SYMCRYPT_FLAG_KEY_NO_FIPS`: the range check on `skR`
/// and the curve check on `pkR` run, and `skR*G` is not recomputed
/// (`lib/eckey.c:486-488`), as the kernel's `Decap` does not recompute it.
pub fn dhkem_decap(st: &mut KemState, enc: &[u8; 97], sk_r_be: &[u8; 48], pk_r: &[u8; 97]) -> Option<[u8; 48]> {
    let pk = sec1_xy(pk_r)?;
    if set_value(&mut st.own, Some(sk_r_be), Some(&pk), FLAG_ECKEY_ECDH | FLAG_KEY_NO_FIPS) != SYMCRYPT_NO_ERROR
        || !set_peer(st, enc)
    {
        return None;
    }
    let dh = ecdh(&st.own, &st.peer)?;
    dhkem_extract_and_expand(&dh, &context(enc, pk_r))
}
