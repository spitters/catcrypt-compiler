//! The emitted entry points against `src/reference.rs`, once per leaf
//! backend.
//!
//! Both sides compute the same relation; they differ in the group-law and
//! scalar routines underneath (see the table in `src/reference.rs`).  The
//! reference is the same for every backend, which is the point: each
//! backend's leaves are an independent implementation of the same
//! arithmetic, and the reference is a third.
//!
//! `reference::verify_core` is the arithmetic relation alone and
//! `reference::verify_checked` adds the FIPS 186-4 checks; the emitted
//! kernel performs the checks, so `verify_checked` is what its verdict is
//! compared against.

mod common;
use common::{affine_base, backend, pub_key, sb, sl, Rng};

use p384::group::{g1_identity, g1_scalar_mul_base};
use p384_ecdsa_rust::{reference, scalar};

/// Unless the build asked for the fallback, everything below must be
/// exercising the sources in `gen/`.
#[cfg(not(feature = "force-fallback"))]
#[test]
fn built_against_the_emitted_sources() {
    assert!(
        p384_ecdsa_rust::EMITTED,
        "gen/ holds no emitted source; this run tested the fallback transcription"
    );
}

/// The backends this binary holds, named once so a run says what it scored.
#[test]
fn backends_under_test() {
    for b in backend::all() {
        println!("backend {}: {}", b.name, b.arithmetic);
    }
    assert!(!backend::all().is_empty());
}

#[test]
fn sign_matches_the_reference() {
    for b in backend::all() {
        let mut rng = Rng::new(20);
        for _ in 0..12 {
            let e = rng.scalar();
            let d = rng.scalar();
            let k = rng.scalar();

            let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
            let mut ok = 0u64;
            (b.sign)(&sb(&e), &sb(&d), &sb(&k), &mut r, &mut s, &mut ok);

            let (rr, rs) = reference::sign_core(&e, &d, &k);
            assert_eq!(sl(&r), rr, "{}: r differs, k = {k:?}", b.name);
            assert_eq!(sl(&s), rs, "{}: s differs, k = {k:?}", b.name);
            assert_eq!(ok, 1, "{}: sign reported an out-of-range output, k = {k:?}", b.name);
            assert_eq!(reference::sign_checked(&e, &d, &k), Some((rr, rs)));
        }
    }
}

/// `k = 0` drives `r` to zero, which the `ok` flag reports.  The kernel
/// cannot resample, because `k` is one of its inputs.
#[test]
fn sign_reports_a_zero_nonce_through_ok() {
    for b in backend::all() {
        let mut rng = Rng::new(28);
        let e = rng.scalar();
        let d = rng.scalar();

        let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
        let mut ok = 7u64;
        (b.sign)(&sb(&e), &sb(&d), &sb(&[0u64; 6]), &mut r, &mut s, &mut ok);

        assert_eq!(sl(&r), [0u64; 6], "{}", b.name);
        assert_eq!(ok, 0, "{}", b.name);
        assert_eq!(reference::sign_checked(&e, &d, &[0u64; 6]), None);
    }
}

#[test]
fn verify_matches_the_reference_on_valid_signatures() {
    for b in backend::all() {
        let mut rng = Rng::new(21);
        for _ in 0..12 {
            let e = rng.scalar();
            let d = rng.scalar();
            let k = rng.scalar();
            let q = g1_scalar_mul_base(&d);

            let (r, s) = reference::sign_core(&e, &d, &k);

            let mut ok = 0u64;
            (b.verify)(&sb(&e), &sb(&r), &sb(&s), &pub_key(b, &d), &mut ok);
            assert_eq!(ok, 1, "{}: emitted verify rejected a valid signature", b.name);
            assert!(reference::verify_core(&e, &r, &s, &q));
            assert!(reference::verify_checked(&e, &r, &s, &q));
        }
    }
}

#[test]
fn verify_matches_the_reference_on_tampered_signatures() {
    for b in backend::all() {
        let mut rng = Rng::new(22);
        for _ in 0..12 {
            let e = rng.scalar();
            let d = rng.scalar();
            let k = rng.scalar();
            let q = g1_scalar_mul_base(&d);
            let qb = pub_key(b, &d);
            let (r, s) = reference::sign_core(&e, &d, &k);

            for tampered in [
                (scalar::add(&r, &scalar::one()), s),
                (r, scalar::add(&s, &scalar::one())),
                (r, s),
            ] {
                let (tr, ts) = tampered;
                let e_used = if tr == r && ts == s {
                    scalar::add(&e, &scalar::one())
                } else {
                    e
                };
                let mut ok = 0u64;
                (b.verify)(&sb(&e_used), &sb(&tr), &sb(&ts), &qb, &mut ok);
                assert_eq!(ok, 0, "{}: emitted verify accepted a tampered signature", b.name);
                assert!(!reference::verify_checked(&e_used, &tr, &ts, &q));
            }
        }
    }
}

#[test]
fn sign_then_verify_round_trip() {
    for b in backend::all() {
        let mut rng = Rng::new(23);
        for _ in 0..12 {
            let e = rng.scalar();
            let d = rng.scalar();
            let k = rng.scalar();
            let q = pub_key(b, &d);

            let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
            let mut signed = 0u64;
            (b.sign)(&sb(&e), &sb(&d), &sb(&k), &mut r, &mut s, &mut signed);
            assert_eq!(signed, 1, "{}", b.name);

            let mut ok = 0u64;
            (b.verify)(&sb(&e), &r, &s, &q, &mut ok);
            assert_eq!(ok, 1, "{}", b.name);
        }
    }
}

/// The two-term multiply through `p384_ecdsa_verify_msm`, whose result is
/// read back as a canonical affine `x` so the two point representations are
/// compared where they agree rather than byte for byte.
#[test]
fn msm_matches_the_reference() {
    for b in backend::all() {
        let mut rng = Rng::new(24);
        for _ in 0..8 {
            let u1 = rng.scalar();
            let u2 = rng.scalar();
            let dq = rng.scalar();
            let q = g1_scalar_mul_base(&dq);

            let mut out = [0u8; 144];
            (b.verify_msm)(
                &sb(&u1),
                &(b.generator)(),
                &sb(&u2),
                &pub_key(b, &dq),
                &mut out,
            );

            let expect = p384::group::g1_add(
                &p384::group::g1_scalar_mul(&u1, &reference::generator()),
                &p384::group::g1_scalar_mul(&u2, &q),
            );
            assert_eq!(
                (b.affine_x)(&out),
                reference::affine_x(&expect),
                "{}",
                b.name
            );
        }
    }
}

/// The generator each backend encodes is the standard base point.
#[test]
fn generator_is_the_standard_base_point() {
    let (gx, _) = affine_base(&scalar::one());
    for b in backend::all() {
        assert_eq!((b.affine_x)(&(b.generator)()), gx, "{}", b.name);
    }
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

fn n_minus_1() -> [u64; 6] {
    let mut v = scalar::N;
    v[0] -= 1;
    v
}

#[test]
fn edge_scalar_at_n_minus_1() {
    for b in backend::all() {
        let e = n_minus_1();
        let d = n_minus_1();
        let k = n_minus_1();

        let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
        let mut signed = 0u64;
        (b.sign)(&sb(&e), &sb(&d), &sb(&k), &mut r, &mut s, &mut signed);
        let (rr, rs) = reference::sign_core(&e, &d, &k);
        assert_eq!((sl(&r), sl(&s)), (rr, rs), "{}", b.name);
        assert_eq!(signed, 1, "{}", b.name);

        let mut ok = 0u64;
        (b.verify)(&sb(&e), &r, &s, &pub_key(b, &d), &mut ok);
        assert_eq!(ok, 1, "{}", b.name);
    }
}

#[test]
fn edge_s_equal_to_one() {
    // s = 1 makes s^-1 = 1, so u1 = e and u2 = r.
    for b in backend::all() {
        let mut rng = Rng::new(25);
        let e = rng.scalar();
        let d = rng.scalar();
        let q = g1_scalar_mul_base(&d);
        let one = scalar::one();

        let mut ok = 0u64;
        let r = rng.scalar();
        (b.verify)(&sb(&e), &sb(&r), &sb(&one), &pub_key(b, &d), &mut ok);
        assert_eq!(
            ok as u8,
            reference::verify_checked(&e, &r, &one, &q) as u8,
            "{}",
            b.name
        );
    }
}

#[test]
fn edge_identity_point_as_q() {
    for b in backend::all() {
        let mut rng = Rng::new(26);
        let e = rng.scalar();
        let r = rng.scalar();
        let s = rng.scalar();
        let id = g1_identity();

        let mut ok = 0u64;
        (b.verify)(&sb(&e), &sb(&r), &sb(&s), &(b.identity)(), &mut ok);
        assert_eq!(ok, 0, "{}: the identity is not a public key", b.name);
        assert_eq!(ok as u8, reference::verify_checked(&e, &r, &s, &id) as u8);
    }
}

#[test]
fn edge_zero_r_and_zero_s() {
    for b in backend::all() {
        let mut rng = Rng::new(27);
        let d = rng.scalar();
        let q = g1_scalar_mul_base(&d);
        let qb = pub_key(b, &d);
        let zero = [0u64; 6];
        let one = scalar::one();

        for (e, r, s) in [
            (zero, zero, one),
            (rng.scalar(), zero, zero),
            (rng.scalar(), rng.scalar(), zero),
        ] {
            let mut ok = 0u64;
            (b.verify)(&sb(&e), &sb(&r), &sb(&s), &qb, &mut ok);
            assert_eq!(ok, 0, "{}: e = {e:?}, r = {r:?}, s = {s:?}", b.name);
            assert_eq!(
                ok as u8,
                reference::verify_checked(&e, &r, &s, &q) as u8,
                "{}: e = {e:?}, r = {r:?}, s = {s:?}",
                b.name
            );
        }
    }
}
