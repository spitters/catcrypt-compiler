//! `u1*G + u2*Q` in one interleaved pass — Shamir's trick.
//!
//! The two terms share one accumulator, so the accumulator is doubled once
//! per bit position rather than once per term per bit position. Each term
//! contributes an addition only at the bit positions where its own digit is
//! non-zero.
//!
//! The digits are width-[`W`] non-adjacent form, so a term's table holds
//! only its odd multiples `1P, 3P, ..., (2^(W-1) - 1)P` — [`TABLE_LEN`]
//! points — and a negative digit is served by negating an entry. A
//! Cartesian joint table `i*G + j*Q` is the other way to index one
//! interleaved pass; it is not used here because at a window wide enough to
//! matter its build cost dominates: at 4 bits per window the cross terms
//! alone are 225 additions, against the 14 additions the two non-adjacent
//! tables cost together.
//!
//! Field multiplications at 384 bits, counting `g1_double` at 13 and
//! `g1_add` at 14, and taking the non-adjacent form's mean digit density of
//! `1/(W + 1)`:
//!
//! | route | doublings | additions | field mul |
//! |---|---|---|---|
//! | `g1_scalar_mul_base(u1)` then `g1_scalar_mul(u2, Q)` then `g1_add` | 387 | 180 | 7551 |
//! | this pass | 386 | 142 | 7006 |
//!
//! # Constant time
//!
//! **No.** The digit loop branches on the digits of both scalars and
//! indexes both tables by digit. `u1` and `u2` are derived from `r`, `s`
//! and the digest, all of them public verification inputs, so there is no
//! secret to leak; this is the same footing as `p384_point_affine_x`.
//! Nothing here is usable for a secret scalar — `g1_scalar_mul` and
//! `g1_scalar_mul_base` are the constant-time routines.

use p384::group::{g1_add, g1_double, g1_generator, g1_identity, g1_neg, G1};

/// Window width of the non-adjacent form, in bits.
///
/// Digits lie in `{0, ±1, ±3, ..., ±(2^(W-1) - 1)}`. Widening by one bit
/// halves neither the doublings (384 either way) nor the additions enough
/// to pay for doubling the table: at `W = 6` the two tables cost 30
/// additions to build and save 18 in the loop.
pub const W: u32 = 5;

/// Digit count: one per bit of a 384-bit scalar, plus the carry position
/// the top digit of a non-adjacent form can occupy.
pub const DIGITS: usize = 385;

/// Odd multiples per table, `2^(W-2)`.
pub const TABLE_LEN: usize = 1 << (W - 2);

/// Width-[`W`] non-adjacent form of `k`, least significant digit first,
/// together with one past the index of the most significant non-zero
/// digit.
///
/// Every non-zero digit is odd and `|d| < 2^(W-1)`, and no two non-zero
/// digits are within `W - 1` positions of each other, which is what bounds
/// the mean density at `1/(W + 1)`.
pub fn wnaf_digits(k: &[u64; 6]) -> ([i32; DIGITS], usize) {
    // Seven limbs: subtracting a negative digit adds to the accumulator,
    // and a 384-bit input must not carry out of the top.
    let mut acc = [0u64; 7];
    acc[..6].copy_from_slice(k);

    let mut out = [0i32; DIGITS];
    let mut top = 0usize;
    let modulus = 1i64 << W;
    let half = 1i64 << (W - 1);

    for (i, slot) in out.iter_mut().enumerate() {
        let d: i64 = if acc[0] & 1 == 1 {
            let m = (acc[0] & (modulus as u64 - 1)) as i64;
            if m >= half {
                m - modulus
            } else {
                m
            }
        } else {
            0
        };
        *slot = d as i32;
        if d != 0 {
            top = i + 1;
        }

        if d >= 0 {
            let mut borrow = d as u64;
            for limb in acc.iter_mut() {
                let (v, b) = limb.overflowing_sub(borrow);
                *limb = v;
                borrow = b as u64;
            }
        } else {
            let mut carry = (-d) as u64;
            for limb in acc.iter_mut() {
                let (v, c) = limb.overflowing_add(carry);
                *limb = v;
                carry = c as u64;
            }
        }

        for j in 0..6 {
            acc[j] = (acc[j] >> 1) | (acc[j + 1] << 63);
        }
        acc[6] >>= 1;
    }

    (out, top)
}

/// `[1P, 3P, 5P, ..., (2*TABLE_LEN - 1)P]`, one doubling and
/// `TABLE_LEN - 1` additions.
fn odd_multiples(p: &G1) -> [G1; TABLE_LEN] {
    let two = g1_double(p);
    let mut t = [*p; TABLE_LEN];
    for i in 1..TABLE_LEN {
        t[i] = g1_add(&t[i - 1], &two);
    }
    t
}

/// `acc + d*P`, where `t` holds the odd multiples of `P` and `d` is a
/// non-adjacent-form digit.
#[inline]
fn add_digit(acc: &G1, t: &[G1; TABLE_LEN], d: i32) -> G1 {
    if d == 0 {
        return *acc;
    }
    let e = &t[(d.unsigned_abs() as usize - 1) / 2];
    if d > 0 {
        g1_add(acc, e)
    } else {
        g1_add(acc, &g1_neg(e))
    }
}

/// `u1*G + u2*Q`, for the standard base point `G`.
///
/// `u1` and `u2` are 6 little-endian u64 limbs, integers in `[0, 2^384)`
/// with no reduction mod `n` — the convention of `g1_scalar_mul`.
///
/// Both scalars are zero gives the identity. `Q` the identity is absorbed
/// by the complete addition formula, leaving `u1*G`.
///
/// Not constant time; see the module header.
pub fn lincomb(u1: &[u64; 6], u2: &[u64; 6], q: &G1) -> G1 {
    let (d1, top1) = wnaf_digits(u1);
    let (d2, top2) = wnaf_digits(u2);
    let top = top1.max(top2);
    if top == 0 {
        return g1_identity();
    }

    let tg = odd_multiples(&g1_generator());
    let tq = odd_multiples(q);

    let mut acc = g1_identity();
    let mut i = top;
    while i > 0 {
        i -= 1;
        // The accumulator is the identity above the top digit, so the
        // doubling there is skipped; `i` and `top` are public.
        if i + 1 != top {
            acc = g1_double(&acc);
        }
        acc = add_digit(&acc, &tg, d1[i]);
        acc = add_digit(&acc, &tq, d2[i]);
    }
    acc
}
