//! FIPS 186-4 CAVP `[P-384,SHA-384]` signature-generation vectors through
//! the emitted sign and verify, once per leaf backend.
//!
//! Provenance of the vectors is in `src/vectors.rs`.  Each vector gives
//! `d`, `Q`, `k`, the digest `m` and the expected `(r, s)`; signing with
//! that `k` must reproduce `(r, s)` byte for byte, and verifying must
//! accept.  The reduction `e = m mod n` is applied before signing, which is
//! what FIPS 186-4 specifies for a digest as wide as `n`.
//!
//! `Q` is encoded from its published affine coordinates into whichever
//! representation the backend under test uses, so the same vector is scored
//! against every backend.

mod common;
use common::{backend, sb, sl};

use p384_ecdsa_rust::codec::limbs_from_be_hex;
use p384_ecdsa_rust::{reference, scalar, vectors::CAVP};

#[test]
fn cavp_sign_reproduces_r_and_s() {
    for b in backend::all() {
        let mut passed = 0;
        for (i, v) in CAVP.iter().enumerate() {
            let d = limbs_from_be_hex(v.d);
            let k = limbs_from_be_hex(v.k);
            let e = scalar::reduce(&limbs_from_be_hex(v.m));
            let want_r = limbs_from_be_hex(v.r);
            let want_s = limbs_from_be_hex(v.s);

            let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
            let mut ok = 0u64;
            (b.sign)(&sb(&e), &sb(&d), &sb(&k), &mut r, &mut s, &mut ok);

            assert_eq!(sl(&r), want_r, "{}: vector {i}: r", b.name);
            assert_eq!(sl(&s), want_s, "{}: vector {i}: s", b.name);
            assert_eq!(ok, 1, "{}: vector {i}: sign reported an out-of-range output", b.name);
            passed += 1;
        }
        assert_eq!(passed, CAVP.len());
        println!("CAVP SigGen [{}]: {passed}/{} reproduced", b.name, CAVP.len());
    }
}

#[test]
fn cavp_public_key_is_d_times_g() {
    for (i, v) in CAVP.iter().enumerate() {
        let d = limbs_from_be_hex(v.d);
        let qx = limbs_from_be_hex(v.q_x);
        let qy = limbs_from_be_hex(v.q_y);
        let q = p384::group::g1_scalar_mul_base(&d);
        let expect = reference::point_from_canonical_affine(&qx, &qy);
        assert!(reference::is_valid_public_key(&expect), "vector {i}: Q off curve");
        assert_eq!(
            reference::affine_x(&q),
            reference::affine_x(&expect),
            "vector {i}: d*G != Q"
        );
    }
}

/// Every backend's own base-point multiplication takes each vector's `d` to
/// the published public key.
///
/// The signing kernel's first three leaves are `k*G`, its affine `x` and
/// that `x` mod `n`, so signing with `k = d` puts `x(d*G) mod n` in `r`,
/// which is the published `Qx` reduced.  The second assertion checks the
/// other direction: the published coordinates, encoded into this backend's
/// point representation, come back out of its `p384_point_affine_x`.
#[test]
fn cavp_public_key_is_d_times_g_in_every_backend() {
    for b in backend::all() {
        for (i, v) in CAVP.iter().enumerate() {
            let d = limbs_from_be_hex(v.d);
            let qx = limbs_from_be_hex(v.q_x);
            let qy = limbs_from_be_hex(v.q_y);

            let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
            let mut ok = 0u64;
            (b.sign)(&sb(&scalar::one()), &sb(&d), &sb(&d), &mut r, &mut s, &mut ok);
            assert_eq!(sl(&r), scalar::reduce(&qx), "{}: vector {i}: x(d*G)", b.name);

            assert_eq!(
                (b.affine_x)(&(b.point_from_affine)(&qx, &qy)),
                qx,
                "{}: vector {i}: affine_x of the published key",
                b.name
            );
        }
        println!("CAVP d*G [{}]: {} match", b.name, CAVP.len());
    }
}

#[test]
fn cavp_verify_accepts() {
    for b in backend::all() {
        let mut accepted = 0;
        for (i, v) in CAVP.iter().enumerate() {
            let e = scalar::reduce(&limbs_from_be_hex(v.m));
            let r = limbs_from_be_hex(v.r);
            let s = limbs_from_be_hex(v.s);
            let q = (b.point_from_affine)(
                &limbs_from_be_hex(v.q_x),
                &limbs_from_be_hex(v.q_y),
            );

            let mut ok = 0u64;
            (b.verify)(&sb(&e), &sb(&r), &sb(&s), &q, &mut ok);
            assert_eq!(ok, 1, "{}: vector {i}: emitted verify rejected", b.name);
            accepted += 1;
        }
        assert_eq!(accepted, CAVP.len());
        println!(
            "CAVP SigVer (positive) [{}]: {accepted}/{} accepted",
            b.name,
            CAVP.len()
        );
    }
}

#[test]
fn cavp_verify_rejects_a_flipped_bit() {
    for b in backend::all() {
        let mut rejected = 0;
        for v in CAVP.iter() {
            let e = scalar::reduce(&limbs_from_be_hex(v.m));
            let mut r = limbs_from_be_hex(v.r);
            let s = limbs_from_be_hex(v.s);
            let q = (b.point_from_affine)(
                &limbs_from_be_hex(v.q_x),
                &limbs_from_be_hex(v.q_y),
            );
            r[0] ^= 1;

            let mut ok = 0u64;
            (b.verify)(&sb(&e), &sb(&r), &sb(&s), &q, &mut ok);
            assert_eq!(ok, 0, "{}", b.name);
            rejected += 1;
        }
        println!(
            "CAVP SigVer (bit-flipped r) [{}]: {rejected}/{} rejected",
            b.name,
            CAVP.len()
        );
    }
}
