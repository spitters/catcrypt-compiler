//! A second ECDSA-P-384 sign and verify, written against `p384-safe-rust`
//! and fiat's scalar field rather than against the leaf shims.
//!
//! The two implementations differ where a differential test can see it:
//!
//! | step                  | leaf path (`crate::leaves`)        | here                                    |
//! |-----------------------|------------------------------------|-----------------------------------------|
//! | scalar inverse        | Bernstein-Yang divstep             | variable-time binary extended GCD       |
//! | reduction mod `n`     | 384 rounds of double-and-add       | one conditional subtraction             |
//! | scalar addition       | limb add + masked subtract         | limb add + branching subtract           |
//! | range and key checks  | mask comparisons, projective curve equation | `ge`/`is_zero` and `g1_to_affine` + `g1_is_on_curve_affine` |
//!
//! Multiplication mod `n` is `fiat_p384_scalar_mul` on both sides and the
//! field arithmetic under the group law is fiat's on both sides, so the
//! differential test does not cover either.
//!
//! The two-term multiplication is `p384_lincomb`'s interleaved pass on the
//! leaf side and `g1_scalar_mul_base` plus `g1_scalar_mul` plus `g1_add`
//! here, so the differential test does cover it; the three routines under
//! the reference side are checked against each other by
//! `tests/leaves.rs::scalar_mul_base_agrees_with_variable_base`.
//!
//! The divstep inverse is covered here by `inv_var`, and by the
//! `a * a^-1 = 1` check in `tests/scalar.rs`.
//!
//! Nothing here is constant time, and it is not meant to be.

use p384::group::{
    g1_add, g1_from_affine, g1_generator, g1_is_on_curve_affine, g1_scalar_mul,
    g1_scalar_mul_base, g1_to_affine, G1, N_CANON,
};
use p384::{fp_from_montgomery, fp_to_montgomery, Fp, FpRaw};

use crate::scalar;

// ---------------------------------------------------------------------------
// Big-integer helpers on canonical little-endian limbs
// ---------------------------------------------------------------------------

fn is_zero(a: &[u64; 6]) -> bool {
    a.iter().all(|&x| x == 0)
}

fn is_one(a: &[u64; 6]) -> bool {
    a[0] == 1 && a[1..].iter().all(|&x| x == 0)
}

/// `a >= b`, most-significant limb first.
fn ge(a: &[u64; 6], b: &[u64; 6]) -> bool {
    for i in (0..6).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}

fn shr1(a: &mut [u64; 6]) {
    for i in 0..5 {
        a[i] = (a[i] >> 1) | (a[i + 1] << 63);
    }
    a[5] >>= 1;
}

fn sub_assign(a: &mut [u64; 6], b: &[u64; 6]) {
    let mut borrow = false;
    for i in 0..6 {
        let (t, b1) = a[i].overflowing_sub(b[i]);
        let (t2, b2) = t.overflowing_sub(borrow as u64);
        a[i] = t2;
        borrow = b1 | b2;
    }
}

/// `a += b`, returning the carry out of the top limb.
fn add_assign(a: &mut [u64; 6], b: &[u64; 6]) -> u64 {
    let mut carry = false;
    for i in 0..6 {
        let (t, c1) = a[i].overflowing_add(b[i]);
        let (t2, c2) = t.overflowing_add(carry as u64);
        a[i] = t2;
        carry = c1 | c2;
    }
    carry as u64
}

/// `m mod n` for `m < 2^384`.
///
/// `n > 2^383`, so `m / n < 2` and one conditional subtraction suffices.
pub fn reduce_once(m: &[u64; 6]) -> [u64; 6] {
    let mut out = *m;
    if ge(&out, &N_CANON) {
        sub_assign(&mut out, &N_CANON);
    }
    out
}

/// `a + b mod n`, for `a, b < n`.
pub fn add_mod_n(a: &[u64; 6], b: &[u64; 6]) -> [u64; 6] {
    let mut out = *a;
    let carry = add_assign(&mut out, b);
    if carry == 1 || ge(&out, &N_CANON) {
        sub_assign(&mut out, &N_CANON);
    }
    out
}

/// `a - b mod n`, for `a, b < n`.
pub fn sub_mod_n(a: &[u64; 6], b: &[u64; 6]) -> [u64; 6] {
    let mut out = *a;
    if ge(a, b) {
        sub_assign(&mut out, b);
    } else {
        add_assign(&mut out, &N_CANON);
        sub_assign(&mut out, b);
    }
    out
}

/// `x /= 2 mod n`, for `x < n`.
fn half_mod_n(x: &mut [u64; 6]) {
    if x[0] & 1 == 0 {
        shr1(x);
    } else {
        let carry = add_assign(x, &N_CANON);
        shr1(x);
        x[5] |= carry << 63;
    }
}

/// `a^-1 mod n` by the binary extended Euclidean algorithm, and `0` for
/// `a = 0`.  Variable time.
pub fn inv_var(a: &[u64; 6]) -> [u64; 6] {
    if is_zero(a) {
        return [0u64; 6];
    }
    let mut u = reduce_once(a);
    let mut v = N_CANON;
    let mut x1 = {
        let mut o = [0u64; 6];
        o[0] = 1;
        o
    };
    let mut x2 = [0u64; 6];

    while !is_one(&u) && !is_one(&v) {
        while u[0] & 1 == 0 {
            shr1(&mut u);
            half_mod_n(&mut x1);
        }
        while v[0] & 1 == 0 {
            shr1(&mut v);
            half_mod_n(&mut x2);
        }
        if ge(&u, &v) {
            sub_assign(&mut u, &v);
            x1 = sub_mod_n(&x1, &x2);
        } else {
            sub_assign(&mut v, &u);
            x2 = sub_mod_n(&x2, &x1);
        }
    }

    if is_one(&u) {
        x1
    } else {
        x2
    }
}

// ---------------------------------------------------------------------------
// Points
// ---------------------------------------------------------------------------

/// The affine x-coordinate of `p` as a canonical field element, and `0`
/// when `p` is the identity.
///
/// The identity convention matches what the leaf sequence produces: the
/// zero field element, which then reduces to the zero scalar.
pub fn affine_x(p: &G1) -> [u64; 6] {
    match g1_to_affine(p) {
        Some((x, _)) => {
            let mut raw = FpRaw([0u64; 6]);
            fp_from_montgomery(&mut raw, &x);
            raw.0
        }
        None => [0u64; 6],
    }
}

/// Whether `p` is the identity.
pub fn is_identity(p: &G1) -> bool {
    p.z.0.iter().all(|&w| w == 0)
}

/// A projective point from canonical affine coordinates.
pub fn point_from_canonical_affine(x: &[u64; 6], y: &[u64; 6]) -> G1 {
    let mut xm = Fp([0u64; 6]);
    let mut ym = Fp([0u64; 6]);
    fp_to_montgomery(&mut xm, &FpRaw(*x));
    fp_to_montgomery(&mut ym, &FpRaw(*y));
    g1_from_affine(&xm, &ym)
}

/// Whether `p` is a non-identity point satisfying the curve equation.
pub fn is_valid_public_key(p: &G1) -> bool {
    match g1_to_affine(p) {
        Some((x, y)) => g1_is_on_curve_affine(&x, &y),
        None => false,
    }
}

// ---------------------------------------------------------------------------
// ECDSA
// ---------------------------------------------------------------------------

/// `(r, s)` for digest `e`, private scalar `d` and nonce `k`, as canonical
/// limbs, with no check that either output is non-zero.
pub fn sign_core(e: &[u64; 6], d: &[u64; 6], k: &[u64; 6]) -> ([u64; 6], [u64; 6]) {
    let rpoint = g1_scalar_mul_base(k);
    let r = reduce_once(&affine_x(&rpoint));
    let kinv = inv_var(k);
    let rd = scalar::mul(&r, d);
    let sum = add_mod_n(e, &rd);
    let s = scalar::mul(&kinv, &sum);
    (r, s)
}

/// `sign_core` with the FIPS 186-4 checks: `k` in `[1, n-1]`, and neither
/// output zero.
pub fn sign_checked(
    e: &[u64; 6],
    d: &[u64; 6],
    k: &[u64; 6],
) -> Option<([u64; 6], [u64; 6])> {
    if is_zero(k) || ge(k, &N_CANON) {
        return None;
    }
    let (r, s) = sign_core(e, d, k);
    if is_zero(&r) || is_zero(&s) {
        return None;
    }
    Some((r, s))
}

/// The verification relation only: `(x(u1*G + u2*Q) mod n) == r`.
///
/// No range or zero checks, and the identity maps to `x = 0`.  This is the
/// relation the emitted kernel computes before its validity flags are
/// applied; [`verify_checked`] is the counterpart of the whole emitted
/// sequence.
pub fn verify_core(e: &[u64; 6], r: &[u64; 6], s: &[u64; 6], q: &G1) -> bool {
    let sinv = inv_var(s);
    let u1 = scalar::mul(e, &sinv);
    let u2 = scalar::mul(r, &sinv);
    let rpoint = g1_add(&g1_scalar_mul_base(&u1), &g1_scalar_mul(&u2, q));
    reduce_once(&affine_x(&rpoint)) == *r
}

/// `verify_core` with the FIPS 186-4 checks: `Q` a valid public key,
/// `r` and `s` in `[1, n-1]`, and `u1*G + u2*Q` not the identity.
///
/// The counterpart of the emitted `p384_ecdsa_verify`.  The emitted
/// sequence has no explicit identity check on `R`; it does not need one,
/// because the identity gives `x = 0`, which no in-range `r` equals.
pub fn verify_checked(e: &[u64; 6], r: &[u64; 6], s: &[u64; 6], q: &G1) -> bool {
    if !is_valid_public_key(q) {
        return false;
    }
    if is_zero(r) || ge(r, &N_CANON) || is_zero(s) || ge(s, &N_CANON) {
        return false;
    }
    let sinv = inv_var(s);
    let u1 = scalar::mul(e, &sinv);
    let u2 = scalar::mul(r, &sinv);
    let rpoint = g1_add(&g1_scalar_mul_base(&u1), &g1_scalar_mul(&u2, q));
    if is_identity(&rpoint) {
        return false;
    }
    reduce_once(&affine_x(&rpoint)) == *r
}

/// The standard base point in projective coordinates.
pub fn generator() -> G1 {
    g1_generator()
}
