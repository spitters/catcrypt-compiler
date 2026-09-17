//! The leaf shims the compiler-emitted P-384 ECDSA and DHKEM(P-384) sources
//! call: thirteen for ECDSA, and seven for DHKEM at the end of the file
//! (`p384_sec1_decode`, `p384_sec1_valid`, `p384_sec1_encode`,
//! `p384_dh_x_be`, and the three re-exported from [`crate::dhkem_kdf`]).
//!
//! Each function takes its destination first as `&mut`, then its inputs as
//! `&`.  Nothing here implements arithmetic: every leaf converts the byte
//! ABI to the representation of an existing function in `p384-safe-rust`,
//! `safegcd` or `fiat-crypto`, calls it, and converts back.
//! [`p384_lincomb`] is the one leaf whose callee is in this crate rather
//! than in a library under it, in [`crate::lincomb`].
//!
//! # Encodings
//!
//! * scalar, `[u8; 48]` — the canonical integer in `[0, n)`, little-endian,
//!   not in the Montgomery domain.  [`p384_scalar_reduce`] and
//!   [`p384_scalar_in_range`] are the two leaves that accept a value
//!   outside that range: the first reduces it, the second reports it.
//! * field element, `[u8; 48]` — the canonical integer in `[0, p)`,
//!   little-endian.  Produced by [`p384_point_affine_x`].
//! * point, `[u8; 144]` — `X || Y || Z` in homogeneous projective
//!   coordinates, 48 little-endian Montgomery bytes each; the layout of
//!   `p384::wnaf::point_to_bytes`.
//! * flag, `u64` — 1 or 0.
//!
//! # Constant time
//!
//! "Constant time" below means the instruction trace and the memory
//! addresses touched are independent of the input *values*.  It is a claim
//! about this shim and the function it calls, not a measurement.

use p384::group::{g1_add, g1_scalar_mul, g1_scalar_mul_base, g1_to_affine, A_MONT, B_MONT};
use p384::wnaf::{point_from_bytes, point_to_bytes};
use p384::{fp_add, fp_from_montgomery, fp_mul, fp_square, Fp, FpRaw};

use crate::scalar;

/// `out = k * p`.
///
/// Shim for `p384::group::g1_scalar_mul` (fixed 4-bit window, full linear
/// table scan) over `point_from_bytes` / `point_to_bytes`.
///
/// Constant time.
pub fn p384_scalar_mul(out: &mut [u8; 144], k: &[u8; 48], p: &[u8; 144]) {
    let limbs = scalar::limbs_from_bytes(k);
    let point = point_from_bytes(p);
    *out = point_to_bytes(&g1_scalar_mul(&limbs, &point));
}

/// `out = k * G`, for the standard base point `G`.
///
/// Shim for `p384::group::g1_scalar_mul_base`: a 5-bit fixed window over the
/// precomputed table `G_TABLE`, one complete addition per window and no
/// doublings.
///
/// Constant time: each window selects its table entry by a full linear scan
/// of all 31 non-zero digits with a limb-mask select, so the addresses
/// touched and the instruction trace depend only on the window width and the
/// window count.
pub fn p384_scalar_mul_base(out: &mut [u8; 144], k: &[u8; 48]) {
    let limbs = scalar::limbs_from_bytes(k);
    *out = point_to_bytes(&g1_scalar_mul_base(&limbs));
}

/// `out = u1*G + u2*q`, for the standard base point `G`.
///
/// Shim for `crate::lincomb::lincomb`: one interleaved left-to-right pass
/// over width-5 non-adjacent digits of both scalars, with the accumulator
/// doubled once per bit position and one table of odd multiples per term.
///
/// Not constant time: the pass branches on the digits of both scalars and
/// indexes both tables by digit. `u1 = e * s^-1` and `u2 = r * s^-1` are
/// derived from the digest and the signature, all public verification
/// inputs, so this is on the same footing as `p384_point_affine_x`.
pub fn p384_lincomb(out: &mut [u8; 144], u1: &[u8; 48], u2: &[u8; 48], q: &[u8; 144]) {
    let k1 = scalar::limbs_from_bytes(u1);
    let k2 = scalar::limbs_from_bytes(u2);
    let point = point_from_bytes(q);
    *out = point_to_bytes(&crate::lincomb::lincomb(&k1, &k2, &point));
}

/// `out = a + b`.
///
/// Shim for `p384::group::g1_add`, the Renes-Costello-Batina complete
/// `a = -3` addition, over `point_from_bytes` / `point_to_bytes`.  Complete,
/// so the identity and the doubling case need no special handling.
///
/// Constant time.
pub fn p384_point_add(out: &mut [u8; 144], a: &[u8; 144], b: &[u8; 144]) {
    let pa = point_from_bytes(a);
    let pb = point_from_bytes(b);
    *out = point_to_bytes(&g1_add(&pa, &pb));
}

/// `out = a^-1 mod n`, and `out = 0` for `a = 0`.
///
/// Shim for `crate::scalar::inv_divstep`: the Bernstein-Yang divstep
/// inversion of `safegcd::safegcd_p384_order`, 15 outer iterations of 59
/// divsteps, preceded by one masked conditional subtraction of `n` that
/// brings an out-of-range input into the inverter's domain.
///
/// `crate::scalar::inv`, the Fermat exponentiation to `n - 2`, computes the
/// same function and is the differential reference for this leaf in
/// `tests/scalar.rs`.
///
/// Constant time: the divstep count is a compile-time constant and every
/// step is a masked select.
pub fn p384_scalar_inv(out: &mut [u8; 48], a: &[u8; 48]) {
    let r = scalar::inv_divstep(&scalar::limbs_from_bytes(a));
    scalar::bytes_from_limbs(out, &r);
}

/// `out = a * b mod n`.
///
/// Shim for `fiat_p384_scalar_mul`, with `fiat_p384_scalar_to_montgomery`
/// and `fiat_p384_scalar_from_montgomery` around it.
///
/// Constant time.
pub fn p384_scalar_muln(out: &mut [u8; 48], a: &[u8; 48], b: &[u8; 48]) {
    let r = scalar::mul(
        &scalar::limbs_from_bytes(a),
        &scalar::limbs_from_bytes(b),
    );
    scalar::bytes_from_limbs(out, &r);
}

/// `out = a + b mod n`.
///
/// Shim for `crate::scalar::add`: limb addition with a mask-selected
/// conditional subtraction of `n`.
///
/// Constant time.
pub fn p384_scalar_addn(out: &mut [u8; 48], a: &[u8; 48], b: &[u8; 48]) {
    let r = scalar::add(
        &scalar::limbs_from_bytes(a),
        &scalar::limbs_from_bytes(b),
    );
    scalar::bytes_from_limbs(out, &r);
}

/// `out = a mod n`, for `a` any 384-bit little-endian integer.
///
/// Shim for `crate::scalar::reduce`: 384 rounds of double-and-add mod `n`.
///
/// Constant time.
pub fn p384_scalar_reduce(out: &mut [u8; 48], a: &[u8; 48]) {
    let r = scalar::reduce(&scalar::limbs_from_bytes(a));
    scalar::bytes_from_limbs(out, &r);
}

/// `out = x(p)`, the affine x-coordinate of `p` as a canonical field
/// element, and `out = 0` when `p` is the identity.
///
/// Shim for `p384::group::g1_to_affine` (which inverts `Z` with the
/// Bernstein-Yang `fp_inv`) followed by `fiat_p384_from_montgomery`.
///
/// Not constant time: `g1_to_affine` branches on `Z = 0`.  Whether `R` is
/// the identity is a public fact about a verification input, so this is on
/// the same footing as the surrounding accept/reject decision.
pub fn p384_point_affine_x(out: &mut [u8; 48], p: &[u8; 144]) {
    let point = point_from_bytes(p);
    match g1_to_affine(&point) {
        Some((x, _)) => {
            let mut raw = FpRaw([0u64; 6]);
            fp_from_montgomery(&mut raw, &x);
            fiat_crypto::p384_64::fiat_p384_to_bytes(out, &raw.0);
        }
        None => *out = [0u8; 48],
    }
}

/// `out = 1` when `a == b`, else `out = 0`.
///
/// Byte-wise difference accumulation with no early exit.
///
/// Constant time.
pub fn p384_scalar_is_eq(out: &mut u64, a: &[u8; 48], b: &[u8; 48]) {
    let mut diff = 0u8;
    for i in 0..48 {
        diff |= a[i] ^ b[i];
    }
    let d = diff as u64;
    *out = 1 ^ ((d | d.wrapping_neg()) >> 63);
}

/// `out = 1` when `1 <= a < n`, else `out = 0`.
///
/// Shim for `crate::scalar::ct_lt_n` and `crate::scalar::ct_is_zero`: a
/// borrow-propagating comparison against `n` and a difference accumulation
/// against zero.  The value is compared, never reduced, so `a >= n` gives 0
/// and `a = 0` gives 0.
///
/// Constant time.
pub fn p384_scalar_in_range(out: &mut u64, a: &[u8; 48]) {
    let l = scalar::limbs_from_bytes(a);
    *out = scalar::ct_lt_n(&l) & (1 ^ scalar::ct_is_zero(&l));
}

/// `out = 1` when `p` satisfies the curve equation and is not the identity,
/// else `out = 0`.
///
/// Shim for the fiat-crypto field operations `fp_square`, `fp_mul` and
/// `fp_add` exposed by `p384`, over the projective coordinates
/// `point_from_bytes` decodes.  The homogeneous curve equation
/// `Y^2 Z = X^3 + a X Z^2 + b Z^3` is evaluated with the Montgomery
/// constants `A_MONT` and `B_MONT`, and the result is `and`-ed with
/// `Z != 0`, which rejects the identity and every other `Z = 0` encoding.
/// The affine `g1_is_on_curve_affine` is not used, because reaching affine
/// coordinates needs the variable-time `g1_to_affine`.
///
/// The three coordinates are taken to be canonical Montgomery values below
/// `p`, which is what the point ABI carries; the fiat field operations
/// require that of their inputs, so a 144-byte string with a coordinate
/// limb at or above `p` is outside the domain of this check.
///
/// Constant time: straight-line field arithmetic and two mask comparisons,
/// with no inversion and no branch.
pub fn p384_point_valid(out: &mut u64, p: &[u8; 144]) {
    let pt = point_from_bytes(p);

    let mut y2 = Fp([0u64; 6]);
    fp_square(&mut y2, &pt.y);
    let mut lhs = Fp([0u64; 6]);
    fp_mul(&mut lhs, &y2, &pt.z);

    let mut x2 = Fp([0u64; 6]);
    fp_square(&mut x2, &pt.x);
    let mut x3 = Fp([0u64; 6]);
    fp_mul(&mut x3, &x2, &pt.x);

    let mut z2 = Fp([0u64; 6]);
    fp_square(&mut z2, &pt.z);
    let mut z3 = Fp([0u64; 6]);
    fp_mul(&mut z3, &z2, &pt.z);

    let mut ax = Fp([0u64; 6]);
    fp_mul(&mut ax, &A_MONT, &pt.x);
    let mut axz2 = Fp([0u64; 6]);
    fp_mul(&mut axz2, &ax, &z2);
    let mut bz3 = Fp([0u64; 6]);
    fp_mul(&mut bz3, &B_MONT, &z3);

    let mut rhs = Fp([0u64; 6]);
    fp_add(&mut rhs, &x3, &axz2);
    let mut rhs_all = Fp([0u64; 6]);
    fp_add(&mut rhs_all, &rhs, &bz3);

    let on_curve = scalar::ct_eq_limbs(&lhs.0, &rhs_all.0);
    let not_identity = 1 ^ scalar::ct_is_zero(&pt.z.0);
    *out = on_curve & not_identity;
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

use p384::group::{G1, ONE_MONT};

use crate::sec1;

/// Canonical affine `(x, y)` of `p` as limbs, and `(0, 0)` for any `Z = 0`
/// encoding, including the identity.
///
/// One `fp_inv` (the Bernstein-Yang divstep inverse) and two `fp_mul`, then
/// the result is masked with `Z != 0`, so there is no branch on `Z`.
fn affine_canonical_ct(p: &G1) -> ([u64; 6], [u64; 6]) {
    let mut zi = Fp([0u64; 6]);
    p384::fp_inv(&mut zi, &p.z);
    let mut xm = Fp([0u64; 6]);
    let mut ym = Fp([0u64; 6]);
    fp_mul(&mut xm, &p.x, &zi);
    fp_mul(&mut ym, &p.y, &zi);
    let mut x = FpRaw([0u64; 6]);
    let mut y = FpRaw([0u64; 6]);
    fp_from_montgomery(&mut x, &xm);
    fp_from_montgomery(&mut y, &ym);
    let keep = (1 ^ scalar::ct_is_zero(&p.z.0)).wrapping_neg();
    let mut xo = [0u64; 6];
    let mut yo = [0u64; 6];
    for i in 0..6 {
        xo[i] = x.0[i] & keep;
        yo[i] = y.0[i] & keep;
    }
    (xo, yo)
}

/// `P = (x : y : 1)` for the SEC1 string `s = 0x04 || X || Y`.
///
/// Shim for `fiat_p384_to_montgomery` on each coordinate and
/// `point_to_bytes`.  The prefix is not inspected and nothing is validated;
/// [`p384_sec1_valid`] is the check, and a kernel ands its flag into `ok`.
/// A coordinate at or above `p` is outside the domain of the Montgomery
/// conversion and yields an unspecified point, never a panic.
///
/// Constant time.
pub fn p384_sec1_decode(out: &mut [u8; 144], s: &[u8; 97]) {
    let (x, y) = sec1::coords(s);
    let mut xm = Fp([0u64; 6]);
    let mut ym = Fp([0u64; 6]);
    p384::fp_to_montgomery(&mut xm, &FpRaw(x));
    p384::fp_to_montgomery(&mut ym, &FpRaw(y));
    *out = point_to_bytes(&G1 { x: xm, y: ym, z: ONE_MONT });
}

/// `f = 1` when `s` is a valid P-384 public key in the RFC 9180 sense:
/// prefix `0x04`, both coordinates below `p`, and the point on the curve.
/// Else `f = 0`.
///
/// The syntactic checks are `sec1::ct_well_formed`; the curve equation is
/// [`p384_point_valid`] on the decoded point, whose `Z = 1` makes its
/// identity test vacuous here.  An affine point cannot be the identity, and
/// `0x04 || 0^96` fails the curve equation because `b != 0`.
///
/// Constant time.
pub fn p384_sec1_valid(f: &mut u64, s: &[u8; 97]) {
    let mut pt = [0u8; 144];
    p384_sec1_decode(&mut pt, s);
    let mut on_curve = 0u64;
    p384_point_valid(&mut on_curve, &pt);
    *f = sec1::ct_well_formed(s) & on_curve;
}

/// `s = 0x04 || be(x) || be(y)` for the affine point of `P`, and
/// `s = 0x04 || 0^96` when `P` has `Z = 0`.
///
/// Constant time: the inverse is the divstep `fp_inv` and the identity case
/// is a mask, see `affine_canonical_ct`.
pub fn p384_sec1_encode(s: &mut [u8; 97], point: &[u8; 144]) {
    let (x, y) = affine_canonical_ct(&point_from_bytes(point));
    sec1::encode(s, &x, &y);
}

/// `d = be(x)`, the affine x-coordinate of `P` as 48 big-endian bytes, the
/// Diffie-Hellman output of RFC 9180 §7.1.1; zero when `P` has `Z = 0`.
///
/// Constant time, unlike [`p384_point_affine_x`], which branches on `Z`.
pub fn p384_dh_x_be(d: &mut [u8; 48], point: &[u8; 144]) {
    let (x, _) = affine_canonical_ct(&point_from_bytes(point));
    sec1::be_from_limbs(d, &x);
}
