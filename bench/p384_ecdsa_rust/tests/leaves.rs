//! The twelve leaf shims against the library functions they wrap.

mod common;
use common::{sb, sl, Rng};

use p384::group::{g1_add, g1_identity, g1_scalar_mul, g1_scalar_mul_base};
use p384_ecdsa_rust::codec::{point, point_bytes};
use p384_ecdsa_rust::leaves::*;
use p384_ecdsa_rust::reference;
use p384_ecdsa_rust::scalar;

#[test]
fn point_bytes_round_trip() {
    let mut rng = Rng::new(10);
    for _ in 0..10 {
        let p = g1_scalar_mul_base(&rng.scalar());
        let b = point_bytes(&p);
        let q = point(&b);
        assert_eq!(point_bytes(&q), b);
    }
}

#[test]
fn scalar_mul_leaf_matches_g1_scalar_mul() {
    let mut rng = Rng::new(11);
    let base = point_bytes(&reference::generator());
    for _ in 0..10 {
        let k = rng.scalar();
        let mut out = [0u8; 144];
        p384_scalar_mul(&mut out, &sb(&k), &base);
        let expect = point_bytes(&g1_scalar_mul(&k, &reference::generator()));
        assert_eq!(out, expect);
    }
}

#[test]
fn point_add_leaf_matches_g1_add() {
    let mut rng = Rng::new(12);
    for _ in 0..10 {
        let p = g1_scalar_mul_base(&rng.scalar());
        let q = g1_scalar_mul_base(&rng.scalar());
        let mut out = [0u8; 144];
        p384_point_add(&mut out, &point_bytes(&p), &point_bytes(&q));
        assert_eq!(out, point_bytes(&g1_add(&p, &q)));
    }
}

#[test]
fn point_add_leaf_absorbs_the_identity() {
    let mut rng = Rng::new(13);
    let p = g1_scalar_mul_base(&rng.scalar());
    let id = point_bytes(&g1_identity());
    let mut out = [0u8; 144];
    p384_point_add(&mut out, &point_bytes(&p), &id);
    // Projectively equal, not necessarily byte-equal: compare affine x.
    let mut xa = [0u8; 48];
    let mut xb = [0u8; 48];
    p384_point_affine_x(&mut xa, &out);
    p384_point_affine_x(&mut xb, &point_bytes(&p));
    assert_eq!(xa, xb);
}

#[test]
fn affine_x_of_the_identity_is_zero() {
    let mut out = [0u8; 48];
    p384_point_affine_x(&mut out, &point_bytes(&g1_identity()));
    assert_eq!(out, [0u8; 48]);
}

#[test]
fn affine_x_matches_the_reference() {
    let mut rng = Rng::new(14);
    for _ in 0..10 {
        let p = g1_scalar_mul_base(&rng.scalar());
        let mut out = [0u8; 48];
        p384_point_affine_x(&mut out, &point_bytes(&p));
        assert_eq!(sl(&out), reference::affine_x(&p));
    }
}

#[test]
fn scalar_leaves_match_the_field() {
    let mut rng = Rng::new(15);
    for _ in 0..100 {
        let a = rng.scalar();
        let b = rng.scalar();
        let (ab, bb) = (sb(&a), sb(&b));

        let mut out = [0u8; 48];
        p384_scalar_muln(&mut out, &ab, &bb);
        assert_eq!(sl(&out), scalar::mul(&a, &b));

        p384_scalar_addn(&mut out, &ab, &bb);
        assert_eq!(sl(&out), reference::add_mod_n(&a, &b));

        p384_scalar_inv(&mut out, &ab);
        assert_eq!(sl(&out), reference::inv_var(&a));

        let m = rng.limbs384();
        p384_scalar_reduce(&mut out, &sb(&m));
        assert_eq!(sl(&out), reference::reduce_once(&m));
    }
}

/// The scalar leaves take an input at or above `n` modulo `n` instead of
/// rejecting it.  This is what makes the emitted verify accept `s + n`
/// wherever it accepts `s` (Wycheproof `ecdsa_secp384r1_sha384_p1363`
/// tcId 165), so the property is pinned here rather than left implicit.
#[test]
fn scalar_leaves_reduce_out_of_range_inputs() {
    let mut rng = Rng::new(17);
    for _ in 0..50 {
        // `2^384 - n` is about `2^190.2`, so `a < 2^189` keeps `a + n`
        // below `2^384`.
        let mut a = rng.limbs384();
        a[3] = 0;
        a[4] = 0;
        a[5] = 0;
        a[2] &= (1u64 << 61) - 1;
        let mut a_plus_n = a;
        let mut carry = false;
        for i in 0..6 {
            let (t, c1) = a_plus_n[i].overflowing_add(scalar::N[i]);
            let (t2, c2) = t.overflowing_add(carry as u64);
            a_plus_n[i] = t2;
            carry = c1 | c2;
        }
        assert!(!carry);

        let b = rng.scalar();
        let (mut lo, mut hi) = ([0u8; 48], [0u8; 48]);
        p384_scalar_muln(&mut lo, &sb(&a), &sb(&b));
        p384_scalar_muln(&mut hi, &sb(&a_plus_n), &sb(&b));
        assert_eq!(lo, hi, "muln did not reduce an out-of-range input");

        p384_scalar_inv(&mut lo, &sb(&a));
        p384_scalar_inv(&mut hi, &sb(&a_plus_n));
        assert_eq!(lo, hi, "inv did not reduce an out-of-range input");
    }
}

#[test]
fn is_eq_leaf() {
    let mut rng = Rng::new(16);
    let a = sb(&rng.scalar());
    let mut flag = 7u64;
    p384_scalar_is_eq(&mut flag, &a, &a);
    assert_eq!(flag, 1);

    let mut b = a;
    b[17] ^= 1;
    p384_scalar_is_eq(&mut flag, &a, &b);
    assert_eq!(flag, 0);

    p384_scalar_is_eq(&mut flag, &[0u8; 48], &[0u8; 48]);
    assert_eq!(flag, 1);
}

// ---------------------------------------------------------------------------
// The fixed-base, validity and flag leaves
// ---------------------------------------------------------------------------

/// Affine coordinates of an encoded point, as canonical limbs.  The two
/// scalar-multiplication routines use different window widths, so they
/// agree projectively but not byte for byte.
fn affine_pair(b: &[u8; 144]) -> ([u64; 6], [u64; 6]) {
    let (x, y) = p384::group::g1_to_affine(&point(b)).expect("not the identity");
    let mut xr = p384::FpRaw([0u64; 6]);
    let mut yr = p384::FpRaw([0u64; 6]);
    p384::fp_from_montgomery(&mut xr, &x);
    p384::fp_from_montgomery(&mut yr, &y);
    (xr.0, yr.0)
}

/// The fixed-base table is the table for this generator: `k*G` through the
/// precomputed path must be the same point as `k*G` through the
/// variable-base ladder.
#[test]
fn scalar_mul_base_agrees_with_variable_base() {
    let mut rng = Rng::new(40);
    let base = point_bytes(&reference::generator());
    for _ in 0..10 {
        let k = sb(&rng.scalar());
        let mut fixed = [0u8; 144];
        let mut variable = [0u8; 144];
        p384_scalar_mul_base(&mut fixed, &k);
        p384_scalar_mul(&mut variable, &k, &base);
        assert_eq!(affine_pair(&fixed), affine_pair(&variable), "k = {k:?}");
    }
}

#[test]
fn scalar_mul_base_of_one_is_the_generator() {
    let mut out = [0u8; 144];
    p384_scalar_mul_base(&mut out, &sb(&scalar::one()));
    assert_eq!(
        affine_pair(&out),
        affine_pair(&point_bytes(&reference::generator()))
    );
}

#[test]
fn in_range_leaf_rejects_zero_n_and_above() {
    let mut n_minus_1 = scalar::N;
    n_minus_1[0] -= 1;
    let mut n_plus_1 = scalar::N;
    n_plus_1[0] += 1;
    let one = scalar::one();

    for (a, want) in [
        ([0u64; 6], 0u64),
        (one, 1),
        (n_minus_1, 1),
        (scalar::N, 0),
        (n_plus_1, 0),
        ([u64::MAX; 6], 0),
    ] {
        let mut flag = 7u64;
        p384_scalar_in_range(&mut flag, &sb(&a));
        assert_eq!(flag, want, "a = {a:?}");
    }
}

#[test]
fn in_range_leaf_accepts_random_scalars() {
    let mut rng = Rng::new(41);
    for _ in 0..50 {
        let mut flag = 0u64;
        p384_scalar_in_range(&mut flag, &sb(&rng.scalar()));
        assert_eq!(flag, 1);
    }
}

#[test]
fn point_valid_leaf_accepts_the_generator_and_random_multiples() {
    let mut flag = 0u64;
    p384_point_valid(&mut flag, &point_bytes(&reference::generator()));
    assert_eq!(flag, 1, "the generator is a valid public key");

    let mut rng = Rng::new(42);
    for _ in 0..10 {
        let p = g1_scalar_mul_base(&rng.scalar());
        p384_point_valid(&mut flag, &point_bytes(&p));
        assert_eq!(flag, 1);
        assert!(reference::is_valid_public_key(&p));
    }
}

#[test]
fn point_valid_leaf_rejects_the_identity_and_off_curve_points() {
    // The identity, (0 : 1 : 0).
    let mut flag = 7u64;
    p384_point_valid(&mut flag, &point_bytes(&g1_identity()));
    assert_eq!(flag, 0, "the identity is not a public key");

    // A point on the curve re-encoded with Z = 0: the homogeneous equation
    // is satisfied only in the degenerate sense, and the leaf rejects it on
    // Z alone.
    let mut rng = Rng::new(43);
    let p = point_bytes(&g1_scalar_mul_base(&rng.scalar()));
    let mut z_zero = p;
    for b in z_zero[96..].iter_mut() {
        *b = 0;
    }
    p384_point_valid(&mut flag, &z_zero);
    assert_eq!(flag, 0, "a Z = 0 encoding is not a public key");

    // A valid point with one coordinate perturbed is off the curve.
    let mut off = p;
    off[0] ^= 1;
    p384_point_valid(&mut flag, &off);
    assert_eq!(flag, 0, "an off-curve point is not a public key");
    assert!(!reference::is_valid_public_key(&point(&off)));

    // The all-zero encoding, (0 : 0 : 0).
    p384_point_valid(&mut flag, &[0u8; 144]);
    assert_eq!(flag, 0);
}

// ---------------------------------------------------------------------------
// The two-term multiplication
// ---------------------------------------------------------------------------

/// `p384_point_add(p384_scalar_mul_base(u1), p384_scalar_mul(u2, Q))`, the
/// three-leaf route the interleaved pass replaces.
fn lincomb_by_three_leaves(u1: &[u8; 48], u2: &[u8; 48], q: &[u8; 144]) -> [u8; 144] {
    let mut t1 = [0u8; 144];
    p384_scalar_mul_base(&mut t1, u1);
    let mut t2 = [0u8; 144];
    p384_scalar_mul(&mut t2, u2, q);
    let mut out = [0u8; 144];
    p384_point_add(&mut out, &t1, &t2);
    out
}

/// Projective equality: the two routes use different window schemes, so
/// they agree as points and not as byte strings.
fn same_point(a: &[u8; 144], b: &[u8; 144]) -> bool {
    let (pa, pb) = (point(a), point(b));
    let (ia, ib) = (p384::group::g1_is_identity(&pa), p384::group::g1_is_identity(&pb));
    if ia || ib {
        return ia == ib;
    }
    let mut l = p384::Fp([0u64; 6]);
    let mut r = p384::Fp([0u64; 6]);
    p384::fp_mul(&mut l, &pa.x, &pb.z);
    p384::fp_mul(&mut r, &pb.x, &pa.z);
    if l.0 != r.0 {
        return false;
    }
    p384::fp_mul(&mut l, &pa.y, &pb.z);
    p384::fp_mul(&mut r, &pb.y, &pa.z);
    l.0 == r.0
}

#[test]
fn lincomb_leaf_matches_the_three_leaf_route() {
    let mut rng = Rng::new(50);
    for _ in 0..20 {
        let u1 = sb(&rng.scalar());
        let u2 = sb(&rng.scalar());
        let q = point_bytes(&g1_scalar_mul_base(&rng.scalar()));

        let mut out = [0u8; 144];
        p384_lincomb(&mut out, &u1, &u2, &q);
        assert!(
            same_point(&out, &lincomb_by_three_leaves(&u1, &u2, &q)),
            "u1 = {u1:?}, u2 = {u2:?}"
        );
    }
}

#[test]
fn lincomb_leaf_edge_cases() {
    let mut rng = Rng::new(51);
    let zero = sb(&[0u64; 6]);
    let one = sb(&scalar::one());
    let mut n_minus_1 = scalar::N;
    n_minus_1[0] -= 1;
    let nm1 = sb(&n_minus_1);

    let k = rng.scalar();
    let q = point_bytes(&g1_scalar_mul_base(&k));
    let id = point_bytes(&g1_identity());
    let a = sb(&rng.scalar());

    let cases: [([u8; 48], [u8; 48], [u8; 144]); 10] = [
        (zero, zero, q),
        (zero, a, q),
        (a, zero, q),
        (zero, zero, id),
        (a, a, q),   // u1 = u2
        (a, a, id),  // u1 = u2, Q the identity
        (a, zero, id),
        (zero, a, id),
        (one, nm1, q),
        (nm1, nm1, q),
    ];

    for (i, (u1, u2, qq)) in cases.iter().enumerate() {
        let mut out = [0u8; 144];
        p384_lincomb(&mut out, u1, u2, qq);
        assert!(
            same_point(&out, &lincomb_by_three_leaves(u1, u2, qq)),
            "case {i}"
        );
    }
}

/// The leaf and the reference agree on the affine x-coordinate, which is
/// the only part of `R` the verify sequence reads.
#[test]
fn lincomb_leaf_matches_the_reference_affine_x() {
    let mut rng = Rng::new(52);
    for _ in 0..10 {
        let u1 = rng.scalar();
        let u2 = rng.scalar();
        let q = g1_scalar_mul_base(&rng.scalar());

        let mut out = [0u8; 144];
        p384_lincomb(&mut out, &sb(&u1), &sb(&u2), &point_bytes(&q));

        let expect = g1_add(
            &g1_scalar_mul_base(&u1),
            &g1_scalar_mul(&u2, &q),
        );
        assert_eq!(reference::affine_x(&point(&out)), reference::affine_x(&expect));
    }
}

#[test]
fn flag_and_leaf() {
    for a in [0u64, 1] {
        for b in [0u64, 1] {
            let mut out = 7u64;
            p384_flag_and(&mut out, &a, &b);
            assert_eq!(out, a & b);
        }
    }
}
