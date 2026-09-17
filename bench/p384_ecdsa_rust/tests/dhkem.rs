//! DHKEM(P-384, HKDF-SHA384), RFC 9180 KEM id `0x0011`: the emitted (or
//! transcribed) `p384_dhkem_encap` and `p384_dhkem_decap` on every backend,
//! against the independent reference in `src/dhkem_ref.rs`, hpke-rs 0.7.0
//! and a Graviola reconstruction.
//!
//! The kernels take private keys as six little-endian limbs; RFC 9180
//! §7.1.2 serialises them as 48 big-endian bytes.  Every test converts
//! explicitly with `dhkem_kdf::sk_le_from_be` / `sk_be_from_le`.
//!
//! No official DHKEM(P-384) known-answer vectors exist on this machine: the
//! CFRG `test-vectors.json` copy in `~/Claude/libcrux/tests` carries KEM ids
//! 0x0010, 0x0012, 0x0020 and 0x0021 only, BoringSSL's HPKE has no P-384
//! KEM, and hpke-rs 0.7.0 ships no test data.  Agreement across
//! implementations is the evidence here.

mod common;

use common::{Backend, Rng};
use p384_ecdsa_rust::dhkem_kdf::{sk_be_from_le, sk_le_from_be};
use p384_ecdsa_rust::{dhkem_ref, grav, hpke_rs, scalar, sec1};

const CASES: usize = 24;

/// A private key in `[1, n)`, in both forms: `(le limbs, be RFC bytes)`.
fn keypair_scalar(rng: &mut Rng) -> ([u8; 48], [u8; 48]) {
    let le = common::sb(&rng.scalar());
    (le, sk_be_from_le(&le))
}

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

fn recipient(rng: &mut Rng) -> ([u8; 48], [u8; 48], [u8; 97]) {
    let (le, be) = keypair_scalar(rng);
    let pk = dhkem_ref::public_key(&be).expect("valid skR");
    (le, be, pk)
}

#[test]
fn byte_order_conversion_round_trips() {
    let mut rng = Rng::new(0xd4e1);
    for _ in 0..CASES {
        let (le, be) = keypair_scalar(&mut rng);
        assert_eq!(sk_le_from_be(&be), le);
        // The big-endian form read as an integer is the limb value.
        assert_eq!(sec1::limbs_from_be(&be), common::sl(&le));
    }
}

#[test]
fn encap_matches_the_reference_bit_for_bit() {
    for b in common::backend::all() {
        let mut rng = Rng::new(0xd4e2);
        for i in 0..CASES {
            let (_, _, pk_r) = recipient(&mut rng);
            let (e_le, e_be) = keypair_scalar(&mut rng);
            let (enc, ss, ok) = encap(b, &e_le, &pk_r);
            let (renc, rss) = dhkem_ref::encap(&e_be, &pk_r).expect("reference encap");
            assert_eq!(ok, 1, "{} case {i}: ok", b.name);
            assert_eq!(enc, renc, "{} case {i}: enc", b.name);
            assert_eq!(ss, rss, "{} case {i}: shared secret", b.name);
        }
    }
}

#[test]
fn decap_agrees_with_the_reference_both_ways() {
    for b in common::backend::all() {
        let mut rng = Rng::new(0xd4e3);
        for i in 0..CASES {
            let (r_le, r_be, pk_r) = recipient(&mut rng);
            let (e_le, e_be) = keypair_scalar(&mut rng);

            // Reference encapsulates, ours decapsulates.
            let (renc, rss) = dhkem_ref::encap(&e_be, &pk_r).unwrap();
            let (ss, ok) = decap(b, &renc, &r_le, &pk_r);
            assert_eq!((ss, ok), (rss, 1), "{} case {i}: ours decaps reference", b.name);

            // Ours encapsulates, reference decapsulates (recomputing pkR).
            let (enc, oss, ok) = encap(b, &e_le, &pk_r);
            assert_eq!(ok, 1);
            assert_eq!(dhkem_ref::decap(&enc, &r_be), Some(oss), "{} case {i}: reference decaps ours", b.name);
        }
    }
}

#[test]
fn backends_agree_with_each_other() {
    let mut rng = Rng::new(0xd4e4);
    let all = common::backend::all();
    for _ in 0..CASES {
        let (r_le, _, pk_r) = recipient(&mut rng);
        let (e_le, _) = keypair_scalar(&mut rng);
        let first = encap(&all[0], &e_le, &pk_r);
        for b in &all[1..] {
            let this = encap(b, &e_le, &pk_r);
            assert_eq!(this, first, "{} vs {}", b.name, all[0].name);
            assert_eq!(decap(b, &first.0, &r_le, &pk_r), (first.1, 1));
        }
    }
}

#[test]
fn hpke_rs_derive_key_pair_matches_the_reference() {
    let h = hpke_rs::new();
    let mut rng = Rng::new(0xd4e5);
    for _ in 0..CASES {
        let ikm = common::sb(&rng.limbs384());
        let (sk, pk) = hpke_rs::derive_key_pair(&h, &ikm);
        assert_eq!(dhkem_ref::derive_key_pair(&ikm), Some((sk, pk)));
    }
}

/// hpke-rs encapsulates with fixed ephemeral randomness; our kernel, given
/// the `skE` that randomness derives, produces the same `enc` and a shared
/// secret that yields the same key schedule.  Then each side decapsulates
/// the other's `enc`.
#[test]
fn hpke_rs_interop() {
    for b in common::backend::all() {
        let mut h = hpke_rs::new();
        let mut rng = Rng::new(0xd4e6);
        for i in 0..CASES {
            let (r_le, r_be, pk_r) = recipient(&mut rng);
            let ikm_e = common::sb(&rng.limbs384());
            let (enc_h, ctx_h) = hpke_rs::setup_sender(&mut h, &pk_r, &ikm_e).expect("hpke-rs sender");
            let exp_h = hpke_rs::export(&ctx_h);

            let (e_be, pk_e) = hpke_rs::derive_key_pair(&h, &ikm_e);
            assert_eq!(pk_e, enc_h, "hpke-rs enc is DeriveKeyPair's public key");
            let (enc, ss, ok) = encap(b, &sk_le_from_be(&e_be), &pk_r);
            assert_eq!(ok, 1);
            assert_eq!(enc, enc_h, "{} case {i}: enc", b.name);
            assert_eq!(hpke_rs::export_for_shared_secret(&h, &ss), exp_h, "{} case {i}: our Encap vs hpke-rs", b.name);

            // hpke-rs Encap -> our Decap.
            let (ss_d, ok) = decap(b, &enc_h, &r_le, &pk_r);
            assert_eq!(ok, 1);
            assert_eq!(hpke_rs::export_for_shared_secret(&h, &ss_d), exp_h, "{} case {i}: our Decap of hpke-rs", b.name);

            // Our Encap (fresh skE) -> hpke-rs Decap.
            let (e2_le, _) = keypair_scalar(&mut rng);
            let (enc2, ss2, ok) = encap(b, &e2_le, &pk_r);
            assert_eq!(ok, 1);
            let ctx_r = hpke_rs::setup_receiver(&h, &enc2, &r_be).expect("hpke-rs receiver");
            assert_eq!(hpke_rs::export(&ctx_r), hpke_rs::export_for_shared_secret(&h, &ss2), "{} case {i}: hpke-rs Decap of ours", b.name);

            // The provider-level reconstruction the benchmark times.
            assert_eq!(hpke_rs::prims_encap(&e_be, &pk_r), Some((enc, ss)));
            assert_eq!(hpke_rs::prims_decap(&enc2, &r_be, &pk_r), Some(ss2));
        }
    }
}

#[test]
fn graviola_reconstruction_interop() {
    for b in common::backend::all() {
        let mut rng = Rng::new(0xd4e7);
        for i in 0..CASES {
            let (r_le, r_be, pk_r) = recipient(&mut rng);
            let (e_le, e_be) = keypair_scalar(&mut rng);
            let (genc, gss) = grav::dhkem_encap(&e_be, &pk_r).expect("graviola encap");
            let (enc, ss, ok) = encap(b, &e_le, &pk_r);
            assert_eq!((enc, ss, ok), (genc, gss, 1), "{} case {i}: encap vs graviola", b.name);
            assert_eq!(decap(b, &genc, &r_le, &pk_r), (gss, 1));
            assert_eq!(grav::dhkem_decap(&enc, &r_be, &pk_r), Some(ss));
        }
    }
}

// ---------------------------------------------------------------------------
// Rejection
// ---------------------------------------------------------------------------

fn sec1_string(x: &[u64; 6], y: &[u64; 6]) -> [u8; 97] {
    let mut s = [0u8; 97];
    sec1::encode(&mut s, x, y);
    s
}

/// The invalid encodings the kernels must reject, each with its name.
fn invalid_encodings(valid: &[u8; 97]) -> Vec<(String, [u8; 97])> {
    let mut out = Vec::new();
    for prefix in [0x00u8, 0x02, 0x03, 0x05, 0x06, 0x07, 0x14, 0xff] {
        let mut s = *valid;
        s[0] = prefix;
        out.push((format!("prefix {prefix:#04x}"), s));
    }
    // The SEC1 identity is the single byte 0x00; in a 97-byte slot it reads
    // as prefix 0x00 and zero coordinates.
    out.push(("identity 0x00 || 0^96".into(), [0u8; 97]));
    let mut z = [0u8; 97];
    z[0] = 0x04;
    out.push(("0x04 || 0^96".into(), z));
    // Off the curve: one bit of y flipped, and x + 1.
    let mut s = *valid;
    s[96] ^= 1;
    out.push(("y bit flipped".into(), s));
    let (x, y) = sec1::coords(valid);
    let mut x1 = x;
    x1[0] = x1[0].wrapping_add(1);
    out.push(("x + 1".into(), sec1_string(&x1, &y)));
    // Coordinates at or above p.
    out.push(("x = p".into(), sec1_string(&sec1::P, &y)));
    out.push(("y = p".into(), sec1_string(&x, &sec1::P)));
    out.push(("x = 2^384 - 1".into(), sec1_string(&[u64::MAX; 6], &y)));
    out.push(("y = 2^384 - 1".into(), sec1_string(&x, &[u64::MAX; 6])));
    // (0, sqrt(b)) is on the curve when b is a square; x = p is then a
    // non-canonical encoding of a curve point, which must still be rejected.
    let root = common::sqrt_candidate(&p384::group::B_CANON);
    let canonical = sec1_string(&[0; 6], &root);
    if dhkem_ref::deserialize_public(&canonical).is_some() {
        out.push(("x = p for the point (0, sqrt b)".into(), sec1_string(&sec1::P, &root)));
    }
    out
}

#[test]
fn the_point_with_x_zero_exists_and_is_accepted() {
    // The fixture above relies on (0, sqrt b) being a curve point; check it,
    // and that every backend accepts its canonical encoding.
    let root = common::sqrt_candidate(&p384::group::B_CANON);
    let s = sec1_string(&[0; 6], &root);
    let on_curve = dhkem_ref::deserialize_public(&s).is_some();
    println!("b is a square mod p: {on_curve}");
    if on_curve {
        let mut rng = Rng::new(0xd4e8);
        let (r_le, r_be, pk_r) = recipient(&mut rng);
        for b in common::backend::all() {
            let (ss, ok) = decap(b, &s, &r_le, &pk_r);
            assert_eq!(ok, 1, "{}", b.name);
            assert_eq!(dhkem_ref::decap_with_pk(&s, &r_be, &pk_r), Some(ss));
        }
    }
}

#[test]
fn invalid_enc_is_rejected() {
    let mut rng = Rng::new(0xd4e9);
    let (r_le, r_be, pk_r) = recipient(&mut rng);
    let (_, e_be) = keypair_scalar(&mut rng);
    let (valid, _) = dhkem_ref::encap(&e_be, &pk_r).unwrap();
    let cases = invalid_encodings(&valid);
    println!("{} invalid encodings", cases.len());
    for b in common::backend::all() {
        assert_eq!(decap(b, &valid, &r_le, &pk_r).1, 1);
        for (name, enc) in &cases {
            let (_, ok) = decap(b, enc, &r_le, &pk_r);
            assert_eq!(ok, 0, "{}: decap accepted enc with {name}", b.name);
            let mut f = 7u64;
            match b.name {
                #[cfg(feature = "s2n")]
                "s2n" => p384_ecdsa_rust::leaves_s2n::p384_sec1_valid(&mut f, enc),
                _ => p384_ecdsa_rust::leaves::p384_sec1_valid(&mut f, enc),
            }
            assert_eq!(f, 0, "{}: sec1_valid accepted {name}", b.name);
        }
    }
    for (name, enc) in &cases {
        assert_eq!(dhkem_ref::decap(enc, &r_be), None, "reference accepted {name}");
        assert!(hpke_rs::setup_receiver(&hpke_rs::new(), enc, &r_be).is_none(), "hpke-rs accepted {name}");
        if name.starts_with("x = p for the point") {
            continue;
        }
        assert_eq!(grav::dhkem_decap(enc, &r_be, &pk_r), None, "graviola accepted {name}");
    }
}

/// Graviola 0.4.1 accepts a public key whose x-coordinate is `p`, when
/// `(0, y)` is a curve point.  `AffineMontPoint::from_x962_uncompressed`
/// (`src/mid/p384.rs`, lines 249-273) converts both coordinates to the
/// Montgomery domain, which reduces them mod `p`, and then checks only the
/// curve equation; there is no `< p` check.  SEC1 v2 §2.3.4 and RFC 9180
/// §7.1.1 require the coordinates to be field elements, and our kernels,
/// the reference and hpke-rs all reject the string.  This test pins the
/// divergence: under Graviola the non-canonical string decapsulates with
/// the DH value of the canonical `(0, y)` and a KEM context over the bytes
/// as sent.
#[test]
fn graviola_accepts_a_non_canonical_x_coordinate() {
    let root = common::sqrt_candidate(&p384::group::B_CANON);
    let canonical = sec1_string(&[0; 6], &root);
    assert!(dhkem_ref::deserialize_public(&canonical).is_some(), "(0, sqrt b) is on the curve");
    let non_canonical = sec1_string(&sec1::P, &root);
    let mut rng = Rng::new(0xd4ed);
    let (r_le, r_be, pk_r) = recipient(&mut rng);
    for b in common::backend::all() {
        assert_eq!(decap(b, &non_canonical, &r_le, &pk_r).1, 0, "{}", b.name);
    }
    let g = grav::dhkem_decap(&non_canonical, &r_be, &pk_r).expect("graviola accepts x = p");
    let dh = dhkem_ref::dh(&r_be, &canonical).unwrap();
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(&non_canonical);
    ctx[97..].copy_from_slice(&pk_r);
    assert_eq!(g, dhkem_ref::extract_and_expand(&dh, &ctx));
}

#[test]
fn invalid_pk_r_is_rejected_by_encap() {
    let mut rng = Rng::new(0xd4ea);
    let (_, _, pk_r) = recipient(&mut rng);
    let (e_le, _) = keypair_scalar(&mut rng);
    for b in common::backend::all() {
        for (name, bad) in invalid_encodings(&pk_r) {
            let (_, _, ok) = encap(b, &e_le, &bad);
            assert_eq!(ok, 0, "{}: encap accepted pkR with {name}", b.name);
        }
    }
}

/// `0`, `n`, `n + 1`, `2^384 - 1` as private keys, little-endian limbs.
fn out_of_range_scalars() -> Vec<(&'static str, [u64; 6])> {
    let n = scalar::N;
    let mut n1 = n;
    n1[0] += 1;
    vec![("0", [0; 6]), ("n", n), ("n + 1", n1), ("2^384 - 1", [u64::MAX; 6])]
}

#[test]
fn out_of_range_private_keys_are_rejected() {
    let mut rng = Rng::new(0xd4eb);
    let (r_le, _, pk_r) = recipient(&mut rng);
    let (_, e_be) = keypair_scalar(&mut rng);
    let (valid_enc, _) = dhkem_ref::encap(&e_be, &pk_r).unwrap();
    for b in common::backend::all() {
        assert_eq!(decap(b, &valid_enc, &r_le, &pk_r).1, 1);
        for (name, l) in out_of_range_scalars() {
            let sk = common::sb(&l);
            assert_eq!(encap(b, &sk, &pk_r).2, 0, "{}: encap accepted skE = {name}", b.name);
            assert_eq!(decap(b, &valid_enc, &sk, &pk_r).1, 0, "{}: decap accepted skR = {name}", b.name);
            assert_eq!(dhkem_ref::encap(&sk_be_from_le(&sk), &pk_r), None, "reference accepted skE = {name}");
            assert_eq!(dhkem_ref::decap(&valid_enc, &sk_be_from_le(&sk)), None);
            assert_eq!(grav::dhkem_encap(&sk_be_from_le(&sk), &pk_r), None);
        }
    }
}

#[test]
fn boundary_private_keys_are_accepted() {
    // 1 and n - 1: the extremes of the valid range, where n - 1 gives
    // -G and -pkR.  None of them yields the identity (prime order).
    let mut rng = Rng::new(0xd4ec);
    let (r_le, _, pk_r) = recipient(&mut rng);
    let mut nm1 = scalar::N;
    nm1[0] -= 1;
    for b in common::backend::all() {
        for l in [[1u64, 0, 0, 0, 0, 0], nm1] {
            let sk = common::sb(&l);
            let (enc, ss, ok) = encap(b, &sk, &pk_r);
            assert_eq!(ok, 1, "{}", b.name);
            assert_eq!(dhkem_ref::encap(&sk_be_from_le(&sk), &pk_r), Some((enc, ss)), "{}", b.name);
            assert_eq!(decap(b, &enc, &r_le, &pk_r), (ss, 1), "{}", b.name);
        }
    }
}

#[test]
fn identity_point_encodes_to_zero_coordinates() {
    for b in common::backend::all() {
        let id = (b.identity)();
        let (mut s, mut d) = ([1u8; 97], [1u8; 48]);
        match b.name {
            #[cfg(feature = "s2n")]
            "s2n" => {
                p384_ecdsa_rust::leaves_s2n::p384_sec1_encode(&mut s, &id);
                p384_ecdsa_rust::leaves_s2n::p384_dh_x_be(&mut d, &id);
            }
            _ => {
                p384_ecdsa_rust::leaves::p384_sec1_encode(&mut s, &id);
                p384_ecdsa_rust::leaves::p384_dh_x_be(&mut d, &id);
            }
        }
        let mut z = [0u8; 97];
        z[0] = 4;
        assert_eq!(s, z, "{}", b.name);
        assert_eq!(d, [0u8; 48], "{}", b.name);
    }
}

#[test]
fn built_against_the_emitted_sources_when_present() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("gen");
    let mut text = String::new();
    if let Ok(rd) = std::fs::read_dir(&dir) {
        for e in rd.flatten() {
            if e.path().extension().and_then(|x| x.to_str()) == Some("rs") {
                text.push_str(&std::fs::read_to_string(e.path()).unwrap());
            }
        }
    }
    let forced = cfg!(feature = "force-fallback");
    let enc = !forced && text.contains("fn p384_dhkem_encap(");
    let dec = !forced && text.contains("fn p384_dhkem_decap(");
    println!("p384_dhkem_encap emitted: {}", p384_ecdsa_rust::DHKEM_ENCAP_EMITTED);
    println!("p384_dhkem_decap emitted: {}", p384_ecdsa_rust::DHKEM_DECAP_EMITTED);
    assert_eq!(p384_ecdsa_rust::DHKEM_ENCAP_EMITTED, enc);
    assert_eq!(p384_ecdsa_rust::DHKEM_DECAP_EMITTED, dec);
}
