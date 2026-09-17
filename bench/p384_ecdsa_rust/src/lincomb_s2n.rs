//! `u1*G + u2*Q` in one interleaved pass over s2n-bignum's Jacobian point
//! operations.
//!
//! The same structure as [`crate::lincomb`] — Shamir's trick over width-`W`
//! non-adjacent digits of both scalars, one accumulator doubled once per bit
//! position, one table of odd multiples per term — with the group law
//! swapped for `p384_montjdouble`, `p384_montjadd` and, for the generator
//! term, `p384_montjmixadd`.  The digit recoding is
//! [`crate::lincomb::wnaf_digits`] unchanged: it reads and writes integers,
//! not points, so it is shared between the two backends.
//!
//! The generator's odd multiples are affine and precomputed
//! ([`crate::comb_s2n::generator_odd_multiples`]), so its additions are
//! mixed; `Q` is an input, so its table is built per call and its additions
//! are general.  Graviola's verification runs two separate five-bit window
//! multiplications and adds the results, which is twice the doublings.
//!
//! Field multiplications at 384 bits, counting `p384_montjdouble` at 11,
//! `p384_montjadd` at 16 and `p384_montjmixadd` at 11, and taking the
//! non-adjacent form's mean digit density of `1/(W + 1)`:
//!
//! | route | doublings | mixed additions | general additions | field mul |
//! |---|---|---|---|---|
//! | two five-bit window multiplications, then one addition | 768 | 0 | 155 | 10 928 |
//! | this pass | 384 | 64 | 64 | 6 032 |
//!
//! # The degenerate case
//!
//! `p384_montjadd` and `p384_montjmixadd` handle a zero accumulator but
//! return the identity when their two arguments are equal, where the answer
//! is the double.  [`crate::comb_s2n`] excludes that case by an argument
//! about partial sums; an interleaved pass has no such argument, so it is
//! detected and repaired instead: an addition of two non-identity points
//! that returns the identity is either a doubling, which
//! `p384_montjdouble` then performs, or a genuine cancellation, which the
//! identity already is.  The test is one comparison of the result's `Z`
//! against zero on the fast path.
//!
//! # Constant time
//!
//! **No**, for the same reason [`crate::lincomb`] is not: the pass branches
//! on the digits of both scalars and indexes both tables by digit, and the
//! repair above branches further.  `u1` and `u2` are derived from the
//! digest and the signature, all public verification inputs.

use crate::comb_s2n::generator_odd_multiples;
use crate::lincomb::{wnaf_digits, TABLE_LEN};
use crate::s2n::{self, Aff, Fe, Jac};

/// `p + q`, correct on every input pair.
///
/// The fast path is one `p384_montjadd`.  A zero `Z` on the result with
/// neither argument the identity means the arguments were equal or mutually
/// inverse; the first case is the double and the second is the identity the
/// call already returned.
pub fn add_general(p: &Jac, q: &Jac) -> Jac {
    let r = s2n::jadd(p, q);
    if !s2n::is_identity(&r) || s2n::is_identity(p) || s2n::is_identity(q) {
        return r;
    }
    if s2n::same_point(p, q) {
        s2n::jdouble(p)
    } else {
        r
    }
}

/// `p + a` with `a` affine, correct on every input pair; see
/// [`add_general`].
pub fn add_mixed(p: &Jac, a: &Aff) -> Jac {
    let r = s2n::jmixadd(p, a);
    if !s2n::is_identity(&r) || s2n::is_identity(p) {
        return r;
    }
    add_general(p, &s2n::aff_to_jac(a))
}

/// `[1P, 3P, 5P, ..., (2*TABLE_LEN - 1)P]` in Jacobian coordinates.
fn odd_multiples(p: &Jac) -> [Jac; TABLE_LEN] {
    let two = s2n::jdouble(p);
    let mut t = [*p; TABLE_LEN];
    for i in 1..TABLE_LEN {
        t[i] = add_general(&t[i - 1], &two);
    }
    t
}

/// `acc + d*P` for a non-adjacent-form digit `d`, over a Jacobian table.
#[inline]
fn add_digit(acc: &Jac, t: &[Jac; TABLE_LEN], d: i32) -> Jac {
    if d == 0 {
        return *acc;
    }
    let e = &t[(d.unsigned_abs() as usize - 1) / 2];
    if d > 0 {
        add_general(acc, e)
    } else {
        add_general(acc, &s2n::jneg(e))
    }
}

/// `acc + d*G` for a non-adjacent-form digit `d`, over the affine generator
/// table, through the mixed addition.
#[inline]
fn add_digit_mixed(acc: &Jac, t: &[Aff; TABLE_LEN], d: i32) -> Jac {
    if d == 0 {
        return *acc;
    }
    let e = &t[(d.unsigned_abs() as usize - 1) / 2];
    if d > 0 {
        add_mixed(acc, e)
    } else {
        add_mixed(acc, &s2n::aneg(e))
    }
}

/// `u1*G + u2*Q`, for the standard base point `G`.
///
/// `u1` and `u2` are canonical little-endian limbs below `n`, the scalars
/// the verification kernel derives.  Both zero gives the identity, and `Q`
/// the identity leaves `u1*G`.
pub fn lincomb(u1: &Fe, u2: &Fe, q: &Jac) -> Jac {
    let (d1, top1) = wnaf_digits(u1);
    let (d2, top2) = wnaf_digits(u2);
    let top = top1.max(top2);
    if top == 0 {
        return s2n::identity();
    }

    let tg = generator_odd_multiples();
    let tq = odd_multiples(q);

    let mut acc = s2n::identity();
    let mut i = top;
    while i > 0 {
        i -= 1;
        // The accumulator is the identity above the top digit, so the
        // doubling there is skipped; `i` and `top` are public.
        if i + 1 != top {
            acc = s2n::jdouble(&acc);
        }
        acc = add_digit_mixed(&acc, tg, d1[i]);
        acc = add_digit(&acc, &tq, d2[i]);
    }
    acc
}
