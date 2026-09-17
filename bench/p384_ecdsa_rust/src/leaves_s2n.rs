//! The leaf shims over s2n-bignum: the third backend of the emitted P-384
//! ECDSA source.
//!
//! Same names and same signatures as [`crate::leaves`] — thirteen ECDSA
//! leaves and seven DHKEM ones — so the emitted orchestration in `gen/`
//! compiles over either.  Nothing here
//! implements arithmetic: every leaf converts the byte ABI to six or
//! eighteen limbs, calls into [`crate::s2n`], and converts back.  The two
//! leaves whose callee is in this crate are [`p384_scalar_mul_base`], over
//! [`crate::comb_s2n`], and [`p384_lincomb`], over [`crate::lincomb_s2n`];
//! those two are the orchestration this backend exists to measure.
//!
//! # The 144 bytes are Jacobian here
//!
//! **The point ABI means something different in this backend.**  In
//! [`crate::leaves`] a point is the homogeneous projective triple
//! `(X : Y : Z)` of the Renes-Costello-Batina formulas, where the affine
//! point is `(X/Z, Y/Z)`.  Here it is a **Jacobian** triple, where the
//! affine point is `(X/Z^2, Y/Z^3)`, because that is what `p384_montjadd`,
//! `p384_montjmixadd` and `p384_montjscalarmul` operate on.  Both are
//! `X || Y || Z` as three 48-byte little-endian Montgomery field elements,
//! so the two encodings are the same 144 bytes with different meanings, and
//! a point string is not portable between the backends.
//!
//! This is safe because the emitted kernel never inspects point bytes: it
//! receives `Q` from its caller, passes it to leaves, and reads a scalar
//! back out.  The backend has to be internally consistent, and it has to
//! agree with the others at exactly two places, both of which `tests/s2n.rs`
//! checks directly against the `p384-safe-rust` backend:
//!
//! 1. [`p384_point_affine_x`] yields the same canonical `x` for the same
//!    curve point, and zero for the identity.
//! 2. [`p384_point_valid`] has the same identity and validity semantics: one
//!    for a non-identity point of the curve, zero for the identity and for
//!    anything off the curve.
//!
//! Callers that build a point string for this backend use
//! [`crate::s2n::from_canonical_affine`] and
//! [`crate::s2n::point_to_bytes`]; the identity is the all-zero string,
//! whose `Z` is zero.
//!
//! # Encodings
//!
//! Scalars, field elements and flags are unchanged from [`crate::leaves`]:
//! `[u8; 48]` canonical little-endian integers and `u64` flags.  The scalar
//! field is the same set of values; only the routines under it differ.
//!
//! # Constant time
//!
//! As in [`crate::leaves`], this is a claim about the shim and the assembly
//! it calls, read off the code, not a measurement.  The two leaves that are
//! not constant time are [`p384_lincomb`] and [`p384_point_add`], both of
//! which handle only public verification inputs; each says so below.

use crate::s2n::{self, Fe};
use crate::{comb_s2n, lincomb_s2n, scalar};

/// Reads a scalar or field element from the byte ABI.
#[inline]
fn fe(b: &[u8; 48]) -> Fe {
    s2n::fe_from_bytes(b)
}

/// `out = k * p`.
///
/// Shim for `p384_montjscalarmul`, the archive's own complete
/// constant-time scalar multiplication: it reduces `k` mod `n`, builds a
/// sixteen-entry table of multiples of `p`, recodes `k` into signed
/// five-bit digits and runs seventy-six steps of five doublings and one
/// addition, selecting the table entry by a constant-time sweep.  Nothing
/// is reimplemented here.
///
/// Constant time.
pub fn p384_scalar_mul(out: &mut [u8; 144], k: &[u8; 48], p: &[u8; 144]) {
    let r = s2n::jscalarmul(&fe(k), &s2n::point_from_bytes(p));
    *out = s2n::point_to_bytes(&r);
}

/// `out = k * G`, for the standard base point `G`.
///
/// Shim for [`crate::comb_s2n::scalar_mul_base`]: a fixed-base comb of
/// seventy-seven five-bit windows over `p384_montjmixadd`, with every
/// multiple in a precomputed affine table, so the pass performs no
/// doublings at all.
///
/// Constant time: the window and entry counts are compile-time constants,
/// the table lookup is a full linear scan with a mask select, and the zero
/// digit is handled by a mask select of the accumulator rather than a
/// branch.
pub fn p384_scalar_mul_base(out: &mut [u8; 144], k: &[u8; 48]) {
    *out = s2n::point_to_bytes(&comb_s2n::scalar_mul_base(&fe(k)));
}

/// `out = u1*G + u2*q`, for the standard base point `G`.
///
/// Shim for [`crate::lincomb_s2n::lincomb`]: one interleaved left-to-right
/// pass over width-5 non-adjacent digits of both scalars, the generator's
/// additions mixed against a precomputed affine table and `q`'s general
/// against a per-call one.
///
/// Not constant time; see the module header of [`crate::lincomb_s2n`].
pub fn p384_lincomb(out: &mut [u8; 144], u1: &[u8; 48], u2: &[u8; 48], q: &[u8; 144]) {
    let r = lincomb_s2n::lincomb(&fe(u1), &fe(u2), &s2n::point_from_bytes(q));
    *out = s2n::point_to_bytes(&r);
}

/// `out = a + b`.
///
/// Shim for `p384_montjadd` with the degenerate case repaired, as
/// [`crate::lincomb_s2n::add_general`] describes: the Jacobian addition
/// returns the identity where its two arguments are equal, and the double
/// is substituted there.
///
/// Not constant time: the repair branches on whether the sum is the
/// identity, which is a public fact about the two summands.  The leaf is
/// reached only from `p384_ecdsa_verify_msm`, over public inputs.
pub fn p384_point_add(out: &mut [u8; 144], a: &[u8; 144], b: &[u8; 144]) {
    let r = lincomb_s2n::add_general(&s2n::point_from_bytes(a), &s2n::point_from_bytes(b));
    *out = s2n::point_to_bytes(&r);
}

/// `out = a^-1 mod n`, and `out = 0` for `a = 0`.
///
/// Shim for `crate::scalar::inv_divstep`, the same Bernstein-Yang divstep
/// inversion the other backends use.  s2n-bignum has no group-order
/// inverse for P-384: the archive carries `bignum_inv_p384` and
/// `bignum_montinv_p384`, both modulo the field prime, and a generic
/// `bignum_modinv` for an arbitrary odd modulus.  The generic routine is
/// exposed as [`crate::s2n::modinv_n`] and timed against the divstep
/// inverse in the benchmark rather than substituted for it.
///
/// Constant time.
pub fn p384_scalar_inv(out: &mut [u8; 48], a: &[u8; 48]) {
    let r = scalar::inv_divstep(&fe(a));
    s2n::fe_to_bytes(out, &r);
}

/// `out = a * b mod n`.
///
/// Shim for the archive's generic `bignum_montmul` at the group order,
/// twice: once against `2^768 mod n` to enter the Montgomery domain and
/// once against `b` to leave it.  s2n-bignum has no `bignum_montmul_n384`,
/// and the montifier constant comes from the archive's own
/// `bignum_montifier`.
///
/// Constant time.
pub fn p384_scalar_muln(out: &mut [u8; 48], a: &[u8; 48], b: &[u8; 48]) {
    let r = s2n::mul_n(&fe(a), &fe(b));
    s2n::fe_to_bytes(out, &r);
}

/// `out = a + b mod n`.
///
/// Shim for the archive's generic `bignum_modadd` at the group order.
///
/// Constant time.
pub fn p384_scalar_addn(out: &mut [u8; 48], a: &[u8; 48], b: &[u8; 48]) {
    let r = s2n::add_n(&fe(a), &fe(b));
    s2n::fe_to_bytes(out, &r);
}

/// `out = a mod n`, for `a` any 384-bit little-endian integer.
///
/// Shim for `bignum_mod_n384_6`: one addition of `2^384 - n` and a masked
/// select of the two results.
///
/// Constant time.
pub fn p384_scalar_reduce(out: &mut [u8; 48], a: &[u8; 48]) {
    let r = s2n::mod_n(&fe(a));
    s2n::fe_to_bytes(out, &r);
}

/// `out = x(p)`, the affine x-coordinate of `p` as a canonical field
/// element, and `out = 0` when `p` is the identity.
///
/// `p` is Jacobian, so the affine `x` is `X / Z^2`: one
/// `bignum_montinv_p384`, one `bignum_montsqr_p384`, one
/// `bignum_montmul_p384` and one `bignum_deamont_p384`.
///
/// The identity needs no special case.  `bignum_montinv_p384` returns zero
/// for an input divisible by `p`, so a zero `Z` drives the product to zero
/// and the leaf returns the zero field element, which is what the other
/// backends return for the identity.
///
/// Constant time, unlike the corresponding leaf in [`crate::leaves`]:
/// `bignum_montinv_p384` runs a fixed divstep count and there is no branch
/// on `Z`.
pub fn p384_point_affine_x(out: &mut [u8; 48], p: &[u8; 144]) {
    let pt = s2n::point_from_bytes(p);
    let zi = s2n::montinv(&s2n::jz(&pt));
    let zi2 = s2n::montsqr(&zi);
    let x = s2n::deamont(&s2n::montmul(&s2n::jx(&pt), &zi2));
    s2n::fe_to_bytes(out, &x);
}

/// `out = 1` when `a == b`, else `out = 0`.
///
/// Shim for `bignum_eq`, a difference accumulation with no early exit.
///
/// Constant time.
pub fn p384_scalar_is_eq(out: &mut u64, a: &[u8; 48], b: &[u8; 48]) {
    *out = s2n::eq(&fe(a), &fe(b));
}

/// `out = 1` when `1 <= a < n`, else `out = 0`.
///
/// Shim for `bignum_lt` against `n` and `bignum_iszero`.  The value is
/// compared, never reduced, so `a >= n` gives 0 and `a = 0` gives 0.
///
/// Constant time.
pub fn p384_scalar_in_range(out: &mut u64, a: &[u8; 48]) {
    let l = fe(a);
    *out = s2n::lt(&l, &s2n::N) & (1 ^ s2n::iszero(&l));
}

/// `out = 1` when `p` satisfies the curve equation and is not the identity,
/// else `out = 0`.
///
/// The Jacobian curve equation `Y^2 = X^3 - 3 X Z^4 + b Z^6`, evaluated
/// with `bignum_montsqr_p384`, `bignum_montmul_p384`, `bignum_add_p384` and
/// `bignum_sub_p384` over the Montgomery coordinates the point ABI carries,
/// and `and`-ed with `Z != 0`, which rejects the identity and every other
/// `Z = 0` encoding.  This is the same predicate as the corresponding leaf
/// in [`crate::leaves`], read in Jacobian rather than homogeneous
/// coordinates.
///
/// The three coordinates are taken to be canonical Montgomery values below
/// `p`, which is what the point ABI carries and what the field routines
/// require of their inputs.
///
/// Constant time: straight-line field arithmetic and two comparisons, with
/// no inversion and no branch.
pub fn p384_point_valid(out: &mut u64, p: &[u8; 144]) {
    let pt = s2n::point_from_bytes(p);
    let (x, y, z) = (s2n::jx(&pt), s2n::jy(&pt), s2n::jz(&pt));

    let z2 = s2n::montsqr(&z);
    let z4 = s2n::montsqr(&z2);
    let z6 = s2n::montmul(&z4, &z2);

    let x2 = s2n::montsqr(&x);
    let x3 = s2n::montmul(&x2, &x);

    let xz4 = s2n::montmul(&x, &z4);
    let three_xz4 = s2n::fadd(&s2n::fadd(&xz4, &xz4), &xz4);
    let bz6 = s2n::montmul(&s2n::B_MONT, &z6);

    let rhs = s2n::fadd(&s2n::fsub(&x3, &three_xz4), &bz6);
    let lhs = s2n::montsqr(&y);

    *out = s2n::eq(&lhs, &rhs) & (1 ^ s2n::iszero(&z));
}

/// `out = a & b`, the bitwise and of two flags.
///
/// No shim: a single `u64` and, with no branch.
///
/// Constant time.
pub fn p384_flag_and(out: &mut u64, a: &u64, b: &u64) {
    *out = *a & *b;
}

// ---------------------------------------------------------------------------
// DHKEM(P-384, HKDF-SHA384) leaves
// ---------------------------------------------------------------------------

/// The three leaves without curve arithmetic, shared by every backend.
pub use crate::dhkem_kdf::{dhkem_p384_expand, dhkem_p384_extract, p384_kem_context};

use crate::sec1;

/// `P = (x, y, 1)` in Jacobian Montgomery coordinates for the SEC1 string
/// `s = 0x04 || X || Y`.
///
/// Shim for `bignum_tomont_p384` on each coordinate.  The prefix is not
/// inspected and nothing is validated; [`p384_sec1_valid`] is the check.
///
/// Constant time.
pub fn p384_sec1_decode(out: &mut [u8; 144], s: &[u8; 97]) {
    let (x, y) = sec1::coords(s);
    *out = s2n::point_bytes_from_canonical_affine(&x, &y);
}

/// `f = 1` when `s` has prefix `0x04`, both coordinates below `p`, and lies
/// on the curve; else `f = 0`.
///
/// The syntactic checks are `sec1::ct_well_formed`; the curve equation is
/// [`p384_point_valid`] on the decoded Jacobian point, with `Z = 1`.
///
/// Constant time.
pub fn p384_sec1_valid(f: &mut u64, s: &[u8; 97]) {
    let mut pt = [0u8; 144];
    p384_sec1_decode(&mut pt, s);
    let mut on_curve = 0u64;
    p384_point_valid(&mut on_curve, &pt);
    *f = sec1::ct_well_formed(s) & on_curve;
}

/// `s = 0x04 || be(X/Z^2) || be(Y/Z^3)`, and `s = 0x04 || 0^96` when
/// `Z = 0`.
///
/// One `bignum_montinv_p384`, which returns zero for a zero input, so the
/// identity needs no special case; then `bignum_montsqr_p384`, three
/// `bignum_montmul_p384` and two `bignum_deamont_p384`.
///
/// Constant time.
pub fn p384_sec1_encode(s: &mut [u8; 97], point: &[u8; 144]) {
    let pt = s2n::point_from_bytes(point);
    let zi = s2n::montinv(&s2n::jz(&pt));
    let zi2 = s2n::montsqr(&zi);
    let zi3 = s2n::montmul(&zi2, &zi);
    let x = s2n::deamont(&s2n::montmul(&s2n::jx(&pt), &zi2));
    let y = s2n::deamont(&s2n::montmul(&s2n::jy(&pt), &zi3));
    sec1::encode(s, &x, &y);
}

/// `d = be(X/Z^2)`, the Diffie-Hellman output of RFC 9180 §7.1.1; zero when
/// `Z = 0`.
///
/// [`p384_point_affine_x`] followed by a byte reversal.
///
/// Constant time.
pub fn p384_dh_x_be(d: &mut [u8; 48], point: &[u8; 144]) {
    let mut le = [0u8; 48];
    p384_point_affine_x(&mut le, point);
    for i in 0..48 {
        d[i] = le[47 - i];
    }
}
