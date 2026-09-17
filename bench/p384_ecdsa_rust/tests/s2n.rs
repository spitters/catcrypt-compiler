//! The s2n-bignum backend: its constants, its two orchestration routines,
//! and the two places where its Jacobian point encoding has to agree with
//! the projective one of the `p384-safe-rust` backend.
//!
//! The 144-byte point ABI carries a Jacobian triple here and a homogeneous
//! projective one there (see `src/leaves_s2n.rs`), so a point string is not
//! portable between the two.  That is safe only because the emitted kernel
//! never inspects point bytes.  What the two backends must agree on is
//! exactly the two facts that leave the point representation:
//!
//! * [`affine_x_agrees_with_the_projective_backend`] — the same canonical
//!   `x` for the same curve point, and zero for the identity.
//! * [`point_valid_agrees_with_the_projective_backend`] — the same verdict
//!   on a valid public key, on the identity, and on an off-curve string.
//!
//! Both are checked on the same curve points, encoded once per backend from
//! canonical affine coordinates.

#![cfg(feature = "s2n")]

mod common;
use common::{sb, Rng};

use p384_ecdsa_rust::codec::limbs_from_be_hex;
use p384_ecdsa_rust::{comb_s2n, leaves, leaves_s2n, lincomb_s2n, s2n, scalar, vectors::CAVP};

/// Canonical affine coordinates of `k * G` from the `p384-safe-rust`
/// backend, the reference this file encodes points from.
fn affine_of_k_times_g(k: &[u64; 6]) -> ([u64; 6], [u64; 6]) {
    let p = p384::group::g1_scalar_mul_base(k);
    let (x, y) = p384::group::g1_to_affine(&p).expect("k*G is not the identity");
    let mut xr = p384::FpRaw([0u64; 6]);
    let mut yr = p384::FpRaw([0u64; 6]);
    p384::fp_from_montgomery(&mut xr, &x);
    p384::fp_from_montgomery(&mut yr, &y);
    (xr.0, yr.0)
}

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// `2^768 mod n`, the constant `bignum_montifier` produced, against the same
/// value by 768 doublings mod `n`.
#[test]
fn montifier_constant_is_two_to_the_768_mod_n() {
    let mut acc = scalar::one();
    for _ in 0..768 {
        acc = scalar::add(&acc, &acc);
    }
    assert_eq!(*s2n::R2_N, acc);
}

/// The curve constants this backend carries are the ones AUCurves carries,
/// in the same Montgomery domain.
#[test]
fn curve_constants_agree_with_aucurves() {
    assert_eq!(*s2n::B_MONT, p384::group::B_MONT.0, "b in Montgomery form");

    let (gx, gy) = affine_of_k_times_g(&scalar::one());
    assert_eq!(s2n::GX_CANON, gx, "generator x");
    assert_eq!(s2n::GY_CANON, gy, "generator y");

    let one = {
        let mut v = [0u64; 6];
        v[0] = 1;
        v
    };
    assert_eq!(s2n::deamont(&s2n::ONE_MONT), one, "2^384 mod p");
}

/// The 144 bytes round-trip through this backend's point conversions.
#[test]
fn point_bytes_round_trip() {
    let mut rng = Rng::new(80);
    for _ in 0..8 {
        let (x, y) = affine_of_k_times_g(&rng.scalar());
        let b = s2n::point_bytes_from_canonical_affine(&x, &y);
        let p = s2n::point_from_bytes(&b);
        assert_eq!(s2n::point_to_bytes(&p), b);
        assert_eq!(s2n::to_affine(&p), Some((x, y)));
    }
}

// ---------------------------------------------------------------------------
// Agreement point 1: the affine x-coordinate
// ---------------------------------------------------------------------------

/// The same canonical `x` out of the two backends, for the same curve
/// point, with each point string built in that backend's own encoding.
///
/// Also the identity, which both backends must map to the zero field
/// element, because the verification kernel reduces that `x` mod `n` and
/// compares it against `r`.
#[test]
fn affine_x_agrees_with_the_projective_backend() {
    let mut rng = Rng::new(81);
    let mut agreed = 0;

    for _ in 0..24 {
        let (x, y) = affine_of_k_times_g(&rng.scalar());

        let proj = p384_ecdsa_rust::backend::AUCURVES;
        let jac = p384_ecdsa_rust::backend::S2N;

        let mut xa = [0u8; 48];
        leaves::p384_point_affine_x(&mut xa, &(proj.point_from_affine)(&x, &y));
        let mut xb = [0u8; 48];
        leaves_s2n::p384_point_affine_x(&mut xb, &(jac.point_from_affine)(&x, &y));

        assert_eq!(xa, xb, "the two backends disagree on x");
        assert_eq!(xa, sb(&x), "neither backend returned the canonical x");
        agreed += 1;
    }

    // The identity, in each backend's own encoding.
    let mut xa = [0u8; 48];
    leaves::p384_point_affine_x(&mut xa, &(p384_ecdsa_rust::backend::AUCURVES.identity)());
    let mut xb = [0u8; 48];
    leaves_s2n::p384_point_affine_x(&mut xb, &(p384_ecdsa_rust::backend::S2N.identity)());
    assert_eq!(xa, [0u8; 48], "projective identity did not give x = 0");
    assert_eq!(xb, [0u8; 48], "jacobian identity did not give x = 0");

    println!("affine_x agreement: {agreed}/24 points, plus the identity");
}

// ---------------------------------------------------------------------------
// Agreement point 2: identity and validity
// ---------------------------------------------------------------------------

/// The two backends return the same validity flag on a valid public key, on
/// the identity, and on an off-curve string.
#[test]
fn point_valid_agrees_with_the_projective_backend() {
    let mut rng = Rng::new(82);
    let proj = p384_ecdsa_rust::backend::AUCURVES;
    let jac = p384_ecdsa_rust::backend::S2N;

    let verdicts = |pa: &[u8; 144], pb: &[u8; 144]| {
        let mut a = 0u64;
        leaves::p384_point_valid(&mut a, pa);
        let mut b = 0u64;
        leaves_s2n::p384_point_valid(&mut b, pb);
        (a, b)
    };

    let mut valid = 0;
    for _ in 0..24 {
        let (x, y) = affine_of_k_times_g(&rng.scalar());
        let (a, b) = verdicts(
            &(proj.point_from_affine)(&x, &y),
            &(jac.point_from_affine)(&x, &y),
        );
        assert_eq!((a, b), (1, 1), "a public key was not accepted by both");
        valid += 1;
    }

    let (a, b) = verdicts(&(proj.identity)(), &(jac.identity)());
    assert_eq!((a, b), (0, 0), "the identity was accepted");

    // An off-curve string: a valid point with its x-coordinate moved.
    let mut off = 0;
    for _ in 0..8 {
        let (mut x, y) = affine_of_k_times_g(&rng.scalar());
        x[0] ^= 1;
        let (a, b) = verdicts(
            &(proj.point_from_affine)(&x, &y),
            &(jac.point_from_affine)(&x, &y),
        );
        assert_eq!((a, b), (0, 0), "an off-curve point was accepted");
        off += 1;
    }

    println!("point_valid agreement: {valid} valid, {off} off-curve, and the identity");
}

/// The CAVP public keys are valid in this backend too, and their `x` is the
/// published one.
#[test]
fn cavp_public_keys_are_valid_in_this_backend() {
    let mut checked = 0;
    for (i, v) in CAVP.iter().enumerate() {
        let qx = limbs_from_be_hex(v.q_x);
        let qy = limbs_from_be_hex(v.q_y);
        let b = s2n::point_bytes_from_canonical_affine(&qx, &qy);

        let mut ok = 0u64;
        leaves_s2n::p384_point_valid(&mut ok, &b);
        assert_eq!(ok, 1, "vector {i}: public key rejected");

        let mut x = [0u8; 48];
        leaves_s2n::p384_point_affine_x(&mut x, &b);
        assert_eq!(x, sb(&qx), "vector {i}: x differs");
        checked += 1;
    }
    assert_eq!(checked, CAVP.len());
    println!("CAVP keys under s2n: {checked}/{} valid", CAVP.len());
}

// ---------------------------------------------------------------------------
// The two orchestration routines
// ---------------------------------------------------------------------------

/// The fixed-base comb agrees with the archive's own scalar multiplication
/// on the base point, which is the reference it is supposed to beat and not
/// to differ from.
#[test]
fn comb_matches_jscalarmul_on_the_base_point() {
    let mut rng = Rng::new(83);
    let g = s2n::point_from_bytes(&s2n::generator_bytes());

    for _ in 0..16 {
        let k = rng.scalar();
        let comb = comb_s2n::scalar_mul_base(&k);
        let want = s2n::jscalarmul(&k, &g);
        assert!(s2n::same_point(&comb, &want), "comb differs at k = {k:?}");
    }
}

/// The comb's edge cases: zero, one, and a scalar at `n - 1`.
#[test]
fn comb_edge_scalars() {
    let g = s2n::point_from_bytes(&s2n::generator_bytes());

    assert!(s2n::is_identity(&comb_s2n::scalar_mul_base(&[0u64; 6])));
    assert!(s2n::same_point(&comb_s2n::scalar_mul_base(&scalar::one()), &g));

    let mut n_minus_1 = scalar::N;
    n_minus_1[0] -= 1;
    assert!(s2n::same_point(
        &comb_s2n::scalar_mul_base(&n_minus_1),
        &s2n::jscalarmul(&n_minus_1, &g)
    ));

    // A scalar at n reduces to zero, as it does in the archive's own
    // multiplication.
    assert!(s2n::is_identity(&comb_s2n::scalar_mul_base(&scalar::N)));
}

/// Every digit value occurs in the comb, so the table scan is exercised
/// across its whole range rather than on whatever a random scalar happens
/// to touch.
#[test]
fn comb_covers_every_digit() {
    let g = s2n::point_from_bytes(&s2n::generator_bytes());
    // 0x08421 repeated puts a different five-bit digit in each window.
    for d in 0..32u64 {
        let mut k = [0u64; 6];
        for (i, w) in k.iter_mut().enumerate() {
            *w = d.wrapping_mul(0x0842_1084_2108_4210).rotate_left(3 * i as u32);
        }
        k = s2n::mod_n(&k);
        assert!(
            s2n::same_point(&comb_s2n::scalar_mul_base(&k), &s2n::jscalarmul(&k, &g)),
            "comb differs at digit seed {d}"
        );
    }
}

/// The interleaved two-term multiply agrees with two separate
/// multiplications and an addition.
#[test]
fn lincomb_matches_the_split_route() {
    let mut rng = Rng::new(84);
    let g = s2n::point_from_bytes(&s2n::generator_bytes());

    for _ in 0..12 {
        let u1 = rng.scalar();
        let u2 = rng.scalar();
        let q = s2n::jscalarmul(&rng.scalar(), &g);

        let fast = lincomb_s2n::lincomb(&u1, &u2, &q);
        let slow = lincomb_s2n::add_general(&s2n::jscalarmul(&u1, &g), &s2n::jscalarmul(&u2, &q));
        assert!(s2n::same_point(&fast, &slow), "u1 = {u1:?}, u2 = {u2:?}");
    }
}

/// The two-term multiply's degenerate inputs: a zero scalar on either side,
/// the identity as `Q`, and `u1*G = -u2*Q`, which cancels.
#[test]
fn lincomb_degenerate_inputs() {
    let mut rng = Rng::new(85);
    let g = s2n::point_from_bytes(&s2n::generator_bytes());
    let zero = [0u64; 6];

    let u = rng.scalar();
    let q = s2n::jscalarmul(&rng.scalar(), &g);

    assert!(s2n::same_point(
        &lincomb_s2n::lincomb(&u, &zero, &q),
        &s2n::jscalarmul(&u, &g)
    ));
    assert!(s2n::same_point(
        &lincomb_s2n::lincomb(&zero, &u, &q),
        &s2n::jscalarmul(&u, &q)
    ));
    assert!(s2n::is_identity(&lincomb_s2n::lincomb(
        &zero,
        &zero,
        &q
    )));
    assert!(s2n::same_point(
        &lincomb_s2n::lincomb(&u, &u, &s2n::identity()),
        &s2n::jscalarmul(&u, &g)
    ));

    // u1*G + u2*Q with Q = G and u2 = n - u1, so the two terms cancel.
    let mut minus_u = scalar::N;
    let mut borrow = false;
    for i in 0..6 {
        let (t, b1) = minus_u[i].overflowing_sub(u[i]);
        let (t2, b2) = t.overflowing_sub(borrow as u64);
        minus_u[i] = t2;
        borrow = b1 | b2;
    }
    assert!(s2n::is_identity(&lincomb_s2n::lincomb(&u, &minus_u, &g)));
}

/// The general addition is correct where `p384_montjadd` alone is not: on
/// equal arguments, on mutually inverse ones, and with the identity on
/// either side.
#[test]
fn point_add_handles_doubling_and_cancellation() {
    let mut rng = Rng::new(86);
    let g = s2n::point_from_bytes(&s2n::generator_bytes());
    let p = s2n::jscalarmul(&rng.scalar(), &g);

    assert!(s2n::same_point(
        &lincomb_s2n::add_general(&p, &p),
        &s2n::jdouble(&p)
    ));
    assert!(s2n::is_identity(&lincomb_s2n::add_general(
        &p,
        &s2n::jneg(&p)
    )));
    assert!(s2n::same_point(
        &lincomb_s2n::add_general(&p, &s2n::identity()),
        &p
    ));
    assert!(s2n::same_point(
        &lincomb_s2n::add_general(&s2n::identity(), &p),
        &p
    ));
    assert!(s2n::is_identity(&lincomb_s2n::add_general(
        &s2n::identity(),
        &s2n::identity()
    )));

    // Raw `p384_montjadd` returns the identity on equal arguments, which is
    // the case the wrapper exists to repair.
    assert!(s2n::is_identity(&s2n::jadd(&p, &p)));
}

// ---------------------------------------------------------------------------
// The scalar leaves
// ---------------------------------------------------------------------------

/// The four scalar leaves over s2n-bignum compute the same functions as the
/// fiat-crypto ones.
#[test]
fn scalar_leaves_match_the_fiat_backend() {
    let mut rng = Rng::new(87);
    for _ in 0..64 {
        let a = rng.scalar();
        let b = rng.scalar();
        let wide = rng.limbs384();

        let mut m = [0u8; 48];
        leaves_s2n::p384_scalar_muln(&mut m, &sb(&a), &sb(&b));
        assert_eq!(m, sb(&scalar::mul(&a, &b)), "mul");

        let mut s = [0u8; 48];
        leaves_s2n::p384_scalar_addn(&mut s, &sb(&a), &sb(&b));
        assert_eq!(s, sb(&scalar::add(&a, &b)), "add");

        let mut r = [0u8; 48];
        leaves_s2n::p384_scalar_reduce(&mut r, &sb(&wide));
        assert_eq!(r, sb(&scalar::reduce(&wide)), "reduce");

        let mut eq = 0u64;
        leaves_s2n::p384_scalar_is_eq(&mut eq, &sb(&a), &sb(&a));
        assert_eq!(eq, 1);
        leaves_s2n::p384_scalar_is_eq(&mut eq, &sb(&a), &sb(&b));
        assert_eq!(eq, 0);

        let mut inr = 0u64;
        leaves_s2n::p384_scalar_in_range(&mut inr, &sb(&a));
        assert_eq!(inr, 1);
        leaves_s2n::p384_scalar_in_range(&mut inr, &sb(&[0u64; 6]));
        assert_eq!(inr, 0);
        leaves_s2n::p384_scalar_in_range(&mut inr, &sb(&scalar::N));
        assert_eq!(inr, 0);
    }
}

/// The archive's generic modular inverse computes the same function as the
/// divstep inverse the leaf uses, which is what lets the benchmark time
/// them against each other.
#[test]
fn generic_modinv_matches_the_divstep_inverse() {
    let mut rng = Rng::new(88);
    for _ in 0..16 {
        let a = rng.scalar();
        assert_eq!(s2n::modinv_n(&a), scalar::inv_divstep(&a));
    }
}
