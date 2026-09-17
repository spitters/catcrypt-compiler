//! The scalar field the leaves are built on.

mod common;
use common::Rng;

use p384_ecdsa_rust::reference;
use p384_ecdsa_rust::scalar;

#[test]
fn inv_cost_constants_match_the_exponent() {
    let bits: u32 = scalar::N_MINUS_2.iter().map(|w| w.count_ones()).sum();
    assert_eq!(scalar::INV_SQUARINGS, 383);
    assert_eq!(scalar::INV_MULTIPLICATIONS, bits - 1);
}

#[test]
fn n_minus_2_is_n_minus_two() {
    let mut e = scalar::N_MINUS_2;
    let (v, c) = e[0].overflowing_add(2);
    e[0] = v;
    assert!(!c);
    assert_eq!(e, scalar::N);
}

#[test]
fn bytes_round_trip() {
    let mut rng = Rng::new(1);
    for _ in 0..200 {
        let a = rng.limbs384();
        let mut b = [0u8; 48];
        scalar::bytes_from_limbs(&mut b, &a);
        assert_eq!(scalar::limbs_from_bytes(&b), a);
    }
}

#[test]
fn bytes_are_little_endian() {
    let mut a = [0u64; 6];
    a[0] = 0x0102_0304_0506_0708;
    let mut b = [0u8; 48];
    scalar::bytes_from_limbs(&mut b, &a);
    assert_eq!(&b[..8], &[0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]);
    assert!(b[8..].iter().all(|&x| x == 0));
}

#[test]
fn reduce_matches_the_single_conditional_subtraction() {
    let mut rng = Rng::new(2);
    for _ in 0..500 {
        let m = rng.limbs384();
        assert_eq!(scalar::reduce(&m), reference::reduce_once(&m), "m = {m:?}");
    }
    // Boundaries: 0, n-1, n, n+1, 2^384-1.
    let mut n_minus_1 = scalar::N;
    n_minus_1[0] -= 1;
    let mut n_plus_1 = scalar::N;
    n_plus_1[0] += 1;
    for m in [[0u64; 6], n_minus_1, scalar::N, n_plus_1, [u64::MAX; 6]] {
        assert_eq!(scalar::reduce(&m), reference::reduce_once(&m), "m = {m:?}");
    }
}

#[test]
fn reduce_of_n_is_zero() {
    assert_eq!(scalar::reduce(&scalar::N), [0u64; 6]);
}

#[test]
fn add_matches_the_reference() {
    let mut rng = Rng::new(3);
    for _ in 0..500 {
        let a = rng.scalar();
        let b = rng.scalar();
        assert_eq!(scalar::add(&a, &b), reference::add_mod_n(&a, &b));
    }
}

#[test]
fn fermat_inverse_matches_binary_xgcd() {
    let mut rng = Rng::new(4);
    for _ in 0..40 {
        let a = rng.scalar();
        assert_eq!(scalar::inv(&a), reference::inv_var(&a), "a = {a:?}");
    }
}

/// The two inverses in the crate compute the same function: the divstep
/// one the leaf calls, and the Fermat chain kept as its reference.
#[test]
fn divstep_inverse_matches_fermat() {
    let mut rng = Rng::new(6);
    for _ in 0..200 {
        let a = rng.scalar();
        assert_eq!(scalar::inv_divstep(&a), scalar::inv(&a), "a = {a:?}");
    }

    let mut n_minus_1 = scalar::N;
    n_minus_1[0] -= 1;
    let mut n_minus_2 = scalar::N;
    n_minus_2[0] -= 2;
    for a in [
        [0u64; 6],
        [1u64, 0, 0, 0, 0, 0],
        [2u64, 0, 0, 0, 0, 0],
        n_minus_2,
        n_minus_1,
    ] {
        assert_eq!(scalar::inv_divstep(&a), scalar::inv(&a), "a = {a:?}");
        assert_eq!(scalar::inv_divstep(&a), reference::inv_var(&a), "a = {a:?}");
    }
}

/// Both inverses take an input at or above `n` modulo `n`, which is what
/// `tests/leaves.rs::scalar_leaves_reduce_out_of_range_inputs` pins for the
/// leaf.  `2^384 - n` is about `2^190.2`, so `a < 2^189` keeps `a + n`
/// below `2^384`.
#[test]
fn divstep_inverse_reduces_out_of_range_inputs() {
    let mut rng = Rng::new(7);
    for _ in 0..50 {
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
        assert_eq!(
            scalar::inv_divstep(&a_plus_n),
            scalar::inv_divstep(&a),
            "a = {a:?}"
        );
        assert_eq!(scalar::inv_divstep(&a_plus_n), scalar::inv(&a_plus_n));
    }
}

#[test]
fn divstep_inverse_times_self_is_one() {
    let mut rng = Rng::new(8);
    let one = scalar::one();
    for _ in 0..100 {
        let a = rng.scalar();
        assert_eq!(scalar::mul(&a, &scalar::inv_divstep(&a)), one, "a = {a:?}");
    }
    let mut n_minus_1 = scalar::N;
    n_minus_1[0] -= 1;
    for a in [[1u64, 0, 0, 0, 0, 0], [2u64, 0, 0, 0, 0, 0], n_minus_1] {
        assert_eq!(scalar::mul(&a, &scalar::inv_divstep(&a)), one, "a = {a:?}");
    }
    assert_eq!(scalar::inv_divstep(&[0u64; 6]), [0u64; 6]);
}

#[test]
fn inverse_times_self_is_one() {
    let mut rng = Rng::new(5);
    let one = scalar::one();
    for _ in 0..40 {
        let a = rng.scalar();
        assert_eq!(scalar::mul(&a, &scalar::inv(&a)), one, "a = {a:?}");
    }
    let mut n_minus_1 = scalar::N;
    n_minus_1[0] -= 1;
    for a in [[1u64, 0, 0, 0, 0, 0], [2u64, 0, 0, 0, 0, 0], n_minus_1] {
        assert_eq!(scalar::mul(&a, &scalar::inv(&a)), one, "a = {a:?}");
    }
}

#[test]
fn inverse_of_zero_is_zero() {
    assert_eq!(scalar::inv(&[0u64; 6]), [0u64; 6]);
    assert_eq!(reference::inv_var(&[0u64; 6]), [0u64; 6]);
}
