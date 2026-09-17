//! DHKEM(P-384, HKDF-SHA384) interop between the emitted kernels, on every
//! backend, and the C libraries under `--features production`:
//!
//! * BoringSSL — a reconstruction from its exported ECDH and HKDF
//!   (`src/bssl.rs`); its HPKE has no P-384 KEM.
//! * OpenSSL 3.0.13 (system) — a reconstruction from `EVP_PKEY_derive` and
//!   `EVP_KDF "HKDF"` (`src/ossl_kem.rs`); 3.0 has no HPKE.
//! * OpenSSL 3.2 or later (by default Microsoft Defender's 3.6.0; any
//!   library named by `P384_OPENSSL36_LIBCRYPTO`) — the native DHKEM
//!   (`EVP_PKEY_encapsulate` with `operation = "DHKEM"`) and the same
//!   reconstruction.  Skipped, with a message, when the library is absent.
//! * AWS-LC — a reconstruction from its exported ECDH and HKDF
//!   (`src/awslc.rs`); its HPKE has no P-384 KEM.  Skipped, with a message,
//!   when the library is absent (`P384_AWSLC_LIBCRYPTO`).
//!
//! Private keys cross the boundary as RFC 9180 big-endian bytes and enter
//! the kernels as little-endian limbs, converted explicitly.

#![cfg(feature = "production")]

mod common;

use common::{Backend, Rng};
use p384_ecdsa_rust::dhkem_kdf::{sk_be_from_le, sk_le_from_be};
use p384_ecdsa_rust::{awslc, bssl, dhkem_ref, ossl_kem, scalar, sec1};

const CASES: usize = 16;

fn encap(b: &Backend, sk_le: &[u8; 48], pk_r: &[u8; 97]) -> ([u8; 97], [u8; 48], u64) {
    let (mut enc, mut ss, mut ok) = ([0u8; 97], [0u8; 48], 7u64);
    (b.dhkem_encap)(sk_le, pk_r, &mut enc, &mut ss, &mut ok);
    (enc, ss, ok)
}

fn decap(b: &Backend, enc: &[u8; 97], sk_le: &[u8; 48], pk_r: &[u8; 97]) -> ([u8; 48], u64) {
    let (mut ss, mut ok) = ([0u8; 48], 7u64);
    (b.dhkem_decap)(enc, sk_le, pk_r, &mut ss, &mut ok);
    (ss, ok)
}

/// `(le, be)` for a fresh private key in `[1, n)`.
fn key(rng: &mut Rng) -> ([u8; 48], [u8; 48]) {
    let le = common::sb(&rng.scalar());
    (le, sk_be_from_le(&le))
}

fn recipient(rng: &mut Rng) -> ([u8; 48], [u8; 48], [u8; 97]) {
    let (le, be) = key(rng);
    (le, be, dhkem_ref::public_key(&be).unwrap())
}

/// Invalid SEC1 strings built from a valid one: bad prefixes, the identity,
/// off-curve, and coordinates at or above `p`.
fn invalid(valid: &[u8; 97]) -> Vec<(&'static str, [u8; 97])> {
    let (x, y) = sec1::coords(valid);
    let enc = |x: &[u64; 6], y: &[u64; 6]| {
        let mut s = [0u8; 97];
        sec1::encode(&mut s, x, y);
        s
    };
    let mut out = Vec::new();
    for (name, p) in [
        ("prefix 0x00", 0u8),
        ("prefix 0x02", 2),
        ("prefix 0x03", 3),
        ("prefix 0x06", 6),
        ("prefix 0x07", 7),
    ] {
        let mut s = *valid;
        s[0] = p;
        out.push((name, s));
    }
    out.push(("all zero", [0u8; 97]));
    let mut z = [0u8; 97];
    z[0] = 4;
    out.push(("0x04 || 0^96", z));
    let mut s = *valid;
    s[96] ^= 1;
    out.push(("y bit flipped", s));
    out.push(("x = p", enc(&sec1::P, &y)));
    out.push(("y = p", enc(&x, &sec1::P)));
    out.push(("y = 2^384 - 1", enc(&x, &[u64::MAX; 6])));
    // x = p for the curve point (0, sqrt b): a non-canonical encoding of a
    // valid point, which Graviola accepts (tests/dhkem.rs).
    let root = common::sqrt_candidate(&p384::group::B_CANON);
    assert!(dhkem_ref::deserialize_public(&enc(&[0; 6], &root)).is_some());
    out.push(("x = p for the point (0, sqrt b)", enc(&sec1::P, &root)));
    out
}

/// Whether `s` is the X9.62 hybrid encoding of the valid point `valid`:
/// prefix `0x06` or `0x07` with the low bit equal to the parity of `y`.
/// OpenSSL accepts exactly these (`crypto/ec/ecp_oct.c`); RFC 9180 §7.1.1
/// admits only the uncompressed form.
fn is_matching_hybrid(s: &[u8; 97], valid: &[u8; 97]) -> bool {
    (s[0] == 6 || s[0] == 7) && s[1..] == valid[1..] && (s[0] & 1) == (s[96] & 1)
}

/// The shared secret OpenSSL derives for a hybrid `enc`: the DH value of the
/// point it encodes, and the KEM context over the bytes as sent.
fn hybrid_secret(enc: &[u8; 97], valid: &[u8; 97], sk_r_be: &[u8; 48], pk_r: &[u8; 97]) -> [u8; 48] {
    let dh = dhkem_ref::dh(sk_r_be, valid).unwrap();
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(enc);
    ctx[97..].copy_from_slice(pk_r);
    dhkem_ref::extract_and_expand(&dh, &ctx)
}

/// What OpenSSL computes for a private key outside `[1, n)`: it imports any
/// 48-byte value and its DHKEM checks only that the key is non-zero mod `n`
/// (`providers/implementations/kem/ec_kem.c`, `eckey_check`), so it works
/// with `sk mod n`.  `None` when that is zero.
fn openssl_reduced_secret(sk_be: &[u8; 48], enc: &[u8; 97], pk_r: &[u8; 97]) -> Option<[u8; 48]> {
    let r = scalar::reduce(&sec1::limbs_from_be(sk_be));
    if r == [0u64; 6] {
        return None;
    }
    let dh = dhkem_ref::dh(&sec1::be48(&r), enc)?;
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(enc);
    ctx[97..].copy_from_slice(pk_r);
    Some(dhkem_ref::extract_and_expand(&dh, &ctx))
}

fn out_of_range() -> Vec<(&'static str, [u8; 48])> {
    let mut n1 = scalar::N;
    n1[0] += 1;
    vec![
        ("0", [0u8; 48]),
        ("n", sk_be_from_le(&common::sb(&scalar::N))),
        ("n + 1", sk_be_from_le(&common::sb(&n1))),
        ("2^384 - 1", [0xffu8; 48]),
    ]
}

/// `"openssl M.m"` for a loaded OpenSSL, from `OpenSSL_version_num`.
fn openssl_label(lib: &ossl_kem::Lib) -> String {
    let (num, _, _) = lib.version();
    format!("openssl {}.{}", num >> 28, (num >> 20) & 0xff)
}

#[test]
fn library_versions() {
    let (num, text, path) = ossl_kem::system().version();
    println!("system openssl: {text} (0x{num:08x}) from {path}");
    assert_eq!(num >> 20, 0x300, "the system library is the 3.0 series");
    assert!(!ossl_kem::system().has_native_dhkem(), "3.0 has no DHKEM operation");
    match ossl_kem::v36() {
        Some(lib) => {
            let (num, text, path) = lib.version();
            println!("openssl 3.2+: {text} (0x{num:08x}) from {path}; native DHKEM: {}", lib.has_native_dhkem());
            assert!(num >> 20 >= 0x302);
            assert!(lib.has_native_dhkem());
        }
        None => println!("SKIP: no OpenSSL 3.2+ at {}", ossl_kem::v36_path()),
    }
    println!("boringssl: {}", bssl::REVISION);
    if awslc::available() {
        let (num, api_num, text) = awslc::version();
        println!("aws-lc: {text} (0x{num:08x}, api {api_num}) from {}", awslc::library_path());
        assert!(text.contains("AWS-LC"));
    } else {
        println!("SKIP: no AWS-LC libcrypto at {}", awslc::library_path());
    }
}

type CEncap = Box<dyn Fn(&[u8; 48], &[u8; 97]) -> Option<([u8; 97], [u8; 48])>>;
type CDecap = Box<dyn Fn(&[u8; 97], &[u8; 48], &[u8; 97]) -> Option<[u8; 48]>>;

/// One C side: `encap(skE, pkR)`, `decap(enc, skR, pkR)`, each `None` on
/// refusal, and the two documented divergences from RFC 9180 it has.
struct CSide {
    name: String,
    encap: CEncap,
    decap: CDecap,
    /// Accepts the X9.62 hybrid encoding whose parity bit matches `y`.
    accepts_hybrid: bool,
    /// Accepts a private key `>= n` that is non-zero mod `n`, as `sk mod n`.
    reduces_sk: bool,
}

/// Every C side.  The native OpenSSL KEM is tested separately, since it
/// takes `ikme` rather than `skE`.  AWS-LC is included when its library is
/// present.
fn c_sides() -> Vec<CSide> {
    let mut v = vec![CSide {
        name: "boringssl reconstruction".into(),
        encap: Box::new(|sk, pk| bssl::dhkem_encap(&mut bssl::KemState::new(), sk, pk)),
        decap: Box::new(|enc, sk, pk| bssl::dhkem_decap(&mut bssl::KemState::new(), enc, sk, pk)),
        accepts_hybrid: false,
        reduces_sk: false,
    }];
    let sys = ossl_kem::system();
    v.push(CSide {
        name: "openssl 3.0 reconstruction".into(),
        encap: Box::new(move |sk, pk| sys.recon_encap(&mut sys.scratch(), sk, pk)),
        decap: Box::new(move |enc, sk, pk| sys.recon_decap(enc, sk, pk)),
        accepts_hybrid: true,
        reduces_sk: true,
    });
    if let Some(lib) = ossl_kem::v36() {
        v.push(CSide {
            name: format!("{} reconstruction", openssl_label(lib)),
            encap: Box::new(move |sk, pk| lib.recon_encap(&mut lib.scratch(), sk, pk)),
            decap: Box::new(move |enc, sk, pk| lib.recon_decap(enc, sk, pk)),
            accepts_hybrid: true,
            reduces_sk: true,
        });
    }
    if awslc::available() {
        v.push(CSide {
            name: "aws-lc reconstruction".into(),
            encap: Box::new(|sk, pk| awslc::dhkem_encap(&mut awslc::KemState::new(), sk, pk)),
            decap: Box::new(|enc, sk, pk| awslc::dhkem_decap(&mut awslc::KemState::new(), enc, sk, pk)),
            // `EC_POINT_oct2point` admits POINT_CONVERSION_HYBRID
            // (crypto/fipsmodule/ec/oct.c); `EC_KEY_set_private_key` rejects
            // a scalar not below n (`ec_bignum_to_scalar`).
            accepts_hybrid: true,
            reduces_sk: false,
        });
    }
    v
}

#[test]
fn reconstructions_interoperate_with_every_backend() {
    for CSide { name, encap: c_encap, decap: c_decap, .. } in c_sides() {
        for b in common::backend::all() {
            let mut rng = Rng::new(0xc0de);
            for i in 0..CASES {
                let (r_le, r_be, pk_r) = recipient(&mut rng);
                let (e_le, e_be) = key(&mut rng);
                // Same skE: bit-for-bit.
                let (cenc, css) = c_encap(&e_be, &pk_r).unwrap_or_else(|| panic!("{name} encap refused"));
                let (enc, ss, ok) = encap(b, &e_le, &pk_r);
                assert_eq!((enc, ss, ok), (cenc, css, 1), "{name} / {} case {i}: encap", b.name);
                // Theirs -> ours, ours -> theirs (fresh skE).
                assert_eq!(decap(b, &cenc, &r_le, &pk_r), (css, 1), "{name} / {}: our decap", b.name);
                let (e2_le, _) = key(&mut rng);
                let (enc2, ss2, _) = encap(b, &e2_le, &pk_r);
                assert_eq!(c_decap(&enc2, &r_be, &pk_r), Some(ss2), "{name} / {}: their decap", b.name);
            }
        }
    }
}

#[test]
fn reconstructions_reject_what_the_kernels_reject() {
    let mut rng = Rng::new(0xc0df);
    let (r_le, r_be, pk_r) = recipient(&mut rng);
    let (_, e_be) = key(&mut rng);
    let (valid, _) = dhkem_ref::encap(&e_be, &pk_r).unwrap();
    let b = &common::backend::all()[0];
    for CSide { name, decap: c_decap, accepts_hybrid, reduces_sk, .. } in c_sides() {
        assert!(c_decap(&valid, &r_be, &pk_r).is_some());
        let mut hybrids = 0;
        for (what, enc) in invalid(&valid) {
            assert_eq!(decap(b, &enc, &r_le, &pk_r).1, 0, "kernel accepted {what}");
            if accepts_hybrid && is_matching_hybrid(&enc, &valid) {
                hybrids += 1;
                assert_eq!(
                    c_decap(&enc, &r_be, &pk_r),
                    Some(hybrid_secret(&enc, &valid, &r_be, &pk_r)),
                    "{name} on the hybrid encoding {what}"
                );
                continue;
            }
            assert_eq!(c_decap(&enc, &r_be, &pk_r), None, "{name} accepted enc with {what}");
        }
        if accepts_hybrid {
            assert_eq!(hybrids, 1, "exactly one of 0x06 / 0x07 matches y's parity");
        }
        println!("{name}: rejected every invalid enc except {hybrids} hybrid encoding(s)");
        for (what, sk) in out_of_range() {
            assert_eq!(decap(b, &valid, &sk_le_from_be(&sk), &pk_r).1, 0);
            let expected = if reduces_sk {
                openssl_reduced_secret(&sk, &valid, &pk_r)
            } else {
                None
            };
            assert_eq!(c_decap(&valid, &sk, &pk_r), expected, "{name} on skR = {what}");
        }
    }
}

/// AWS-LC accepts the hybrid encoding in both positions: as `enc` in
/// `Decap` and as `pkR` in `Encap`, where the KEM context carries the
/// hybrid bytes as given.  BoringSSL, the fork's parent, rejects both.
#[test]
fn awslc_accepts_the_hybrid_encoding() {
    if !awslc::available() {
        println!("SKIP: no AWS-LC libcrypto at {}", awslc::library_path());
        return;
    }
    let mut rng = Rng::new(0xc0e2);
    let (_, r_be, pk_r) = recipient(&mut rng);
    let (_, e_be) = key(&mut rng);
    let mut hybrid = pk_r;
    hybrid[0] = 6 | (pk_r[96] & 1);
    let (enc, ss) = awslc::dhkem_encap(&mut awslc::KemState::new(), &e_be, &hybrid)
        .expect("AWS-LC encapsulates to a hybrid pkR");
    let dh = dhkem_ref::dh(&e_be, &pk_r).unwrap();
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(&enc);
    ctx[97..].copy_from_slice(&hybrid);
    assert_eq!(ss, dhkem_ref::extract_and_expand(&dh, &ctx), "context over the hybrid bytes");
    assert_eq!(bssl::dhkem_encap(&mut bssl::KemState::new(), &e_be, &hybrid), None, "BoringSSL rejects it");
    let mut wrong = hybrid;
    wrong[0] ^= 1;
    assert_eq!(awslc::dhkem_encap(&mut awslc::KemState::new(), &e_be, &wrong), None, "parity bit is checked");
    let (valid, _) = dhkem_ref::encap(&e_be, &pk_r).unwrap();
    let mut henc = valid;
    henc[0] = 6 | (valid[96] & 1);
    assert_eq!(
        awslc::dhkem_decap(&mut awslc::KemState::new(), &henc, &r_be, &pk_r),
        Some(hybrid_secret(&henc, &valid, &r_be, &pk_r))
    );
    println!("aws-lc: hybrid pkR and hybrid enc accepted; mismatched parity rejected");
}

#[test]
fn openssl_native_dhkem_interop() {
    let Some(lib) = ossl_kem::v36() else {
        println!("SKIP: no OpenSSL 3.2+ at {}", ossl_kem::v36_path());
        return;
    };
    for b in common::backend::all() {
        let mut rng = Rng::new(0xc0e0);
        for i in 0..CASES {
            let (r_le, r_be, pk_r) = recipient(&mut rng);
            let recip_pub = lib.public_pkey(&pk_r).expect("openssl accepts pkR");
            let recip_pair = lib.keypair_pkey(&r_be, &pk_r).expect("openssl accepts (skR, pkR)");
            let ikme = common::sb(&rng.limbs384());
            let (nenc, nss) = lib.native_encap(&recip_pub, &ikme).expect("native encap");

            // Our kernel with skE = DeriveKeyPair(ikme) gives the same bytes.
            let (e_be, pk_e) = dhkem_ref::derive_key_pair(&ikme).unwrap();
            assert_eq!(pk_e, nenc, "case {i}: OpenSSL's enc is DeriveKeyPair(ikme)'s public key");
            let (enc, ss, ok) = encap(b, &sk_le_from_be(&e_be), &pk_r);
            assert_eq!((enc, ss, ok), (nenc, nss, 1), "{} case {i}: encap vs OpenSSL native", b.name);

            assert_eq!(decap(b, &nenc, &r_le, &pk_r), (nss, 1));
            let (e2_le, _) = key(&mut rng);
            let (enc2, ss2, _) = encap(b, &e2_le, &pk_r);
            assert_eq!(lib.native_decap(&recip_pair, &enc2), Some(ss2), "{} case {i}: native decap of ours", b.name);
        }
    }
}

#[test]
fn openssl_native_dhkem_rejects_what_the_kernels_reject() {
    let Some(lib) = ossl_kem::v36() else {
        println!("SKIP: no OpenSSL 3.2+ at {}", ossl_kem::v36_path());
        return;
    };
    let mut rng = Rng::new(0xc0e1);
    let (_, r_be, pk_r) = recipient(&mut rng);
    let (_, e_be) = key(&mut rng);
    let (valid, _) = dhkem_ref::encap(&e_be, &pk_r).unwrap();
    let pair = lib.keypair_pkey(&r_be, &pk_r).unwrap();
    assert!(lib.native_decap(&pair, &valid).is_some());
    for (what, enc) in invalid(&valid) {
        if is_matching_hybrid(&enc, &valid) {
            assert_eq!(
                lib.native_decap(&pair, &enc),
                Some(hybrid_secret(&enc, &valid, &r_be, &pk_r)),
                "native decap on the hybrid encoding {what}"
            );
            assert!(lib.public_pkey(&enc).is_some(), "EVP_PKEY_fromdata on the hybrid {what}");
            continue;
        }
        assert_eq!(lib.native_decap(&pair, &enc), None, "native decap accepted {what}");
        assert!(lib.public_pkey(&enc).is_none(), "EVP_PKEY_fromdata accepted pkR with {what}");
    }
    for (what, sk) in out_of_range() {
        let got = lib.keypair_pkey(&sk, &pk_r).and_then(|k| lib.native_decap(&k, &valid));
        assert_eq!(got, openssl_reduced_secret(&sk, &valid, &pk_r), "native decap on skR = {what}");
    }
}
