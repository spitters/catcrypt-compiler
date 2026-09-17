//! The P-384 scalar field, mod
//! `n = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973`.
//!
//! Multiplication, squaring and the Montgomery conversions are
//! `fiat_p384_scalar_*` from `fiat-crypto/fiat-rust/src/p384_scalar_64.rs`.
//! The divstep inverse is `safegcd::safegcd_p384_order`.  Addition mod n,
//! reduction mod n of a full 384-bit input, and the Fermat inverse chain
//! are written here.
//!
//! A scalar is carried as `[u8; 48]`: the canonical integer in `[0, n)`,
//! little-endian, *not* in the Montgomery domain.  `reduce` is the one
//! entry point that accepts an arbitrary 384-bit input.

use fiat_crypto::p384_scalar_64::{
    fiat_p384_scalar_from_bytes, fiat_p384_scalar_from_montgomery,
    fiat_p384_scalar_montgomery_domain_field_element as Mont,
    fiat_p384_scalar_non_montgomery_domain_field_element as NonMont, fiat_p384_scalar_mul,
    fiat_p384_scalar_set_one, fiat_p384_scalar_square, fiat_p384_scalar_to_bytes,
};

/// The group order, canonical little-endian u64 limbs.
pub use p384::group::N_CANON as N;

/// Limbs of `n - 2`, the Fermat exponent.
pub const N_MINUS_2: [u64; 6] = {
    let mut e = N;
    e[0] -= 2;
    e
};

// ---------------------------------------------------------------------------
// Limb-level helpers
// ---------------------------------------------------------------------------

/// `a + b + carry_in`, returning the sum limb and the carry out.
#[inline]
fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let (t, c1) = a.overflowing_add(b);
    let (t2, c2) = t.overflowing_add(carry);
    (t2, (c1 as u64) | (c2 as u64))
}

/// `a - b - borrow_in`, returning the difference limb and the borrow out.
#[inline]
fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let (t, b1) = a.overflowing_sub(b);
    let (t2, b2) = t.overflowing_sub(borrow);
    (t2, (b1 as u64) | (b2 as u64))
}

/// All-ones when `bit` is 1, all-zeros when it is 0.
#[inline]
fn mask_of(bit: u64) -> u64 {
    0u64.wrapping_sub(bit)
}

/// Subtracts `n` from `a` when `carry` is 1 or when `a >= n`, keeping `a`
/// otherwise.  `carry` is the carry out of the operation that produced `a`,
/// so the value being reduced is `carry * 2^384 + a`, known to be `< 2n`.
/// The select is a mask, so the same instructions run either way.
#[inline]
fn cond_sub_n(a: &mut [u64; 6], carry: u64) {
    let mut diff = [0u64; 6];
    let mut borrow = 0u64;
    for i in 0..6 {
        let (v, b) = sbb(a[i], N[i], borrow);
        diff[i] = v;
        borrow = b;
    }
    let take = carry | (1 ^ borrow);
    let m = mask_of(take);
    for i in 0..6 {
        a[i] = (a[i] & !m) | (diff[i] & m);
    }
}

/// `a += b mod n`, for `a, b < n`.
#[inline]
fn add_mod_n(a: &mut [u64; 6], b: &[u64; 6]) {
    let mut carry = 0u64;
    for i in 0..6 {
        let (v, c) = adc(a[i], b[i], carry);
        a[i] = v;
        carry = c;
    }
    cond_sub_n(a, carry);
}

/// `a = 2a mod n`, for `a < n`.
#[inline]
fn dbl_mod_n(a: &mut [u64; 6]) {
    let mut carry = 0u64;
    for i in 0..6 {
        let out = a[i] >> 63;
        a[i] = (a[i] << 1) | carry;
        carry = out;
    }
    cond_sub_n(a, carry);
}

// ---------------------------------------------------------------------------
// Byte <-> limb
// ---------------------------------------------------------------------------

/// Reads 48 little-endian bytes as 6 little-endian u64 limbs.
#[inline]
pub fn limbs_from_bytes(b: &[u8; 48]) -> [u64; 6] {
    let mut out = [0u64; 6];
    fiat_p384_scalar_from_bytes(&mut out, b);
    out
}

/// Writes 6 little-endian u64 limbs as 48 little-endian bytes.
#[inline]
pub fn bytes_from_limbs(out: &mut [u8; 48], l: &[u64; 6]) {
    fiat_p384_scalar_to_bytes(out, l);
}

// ---------------------------------------------------------------------------
// Field operations on canonical limbs
// ---------------------------------------------------------------------------

/// `a * b mod n`, for `a, b < n`.  Two Montgomery conversions around
/// `fiat_p384_scalar_mul`.
pub fn mul(a: &[u64; 6], b: &[u64; 6]) -> [u64; 6] {
    let mut am = Mont([0u64; 6]);
    let mut bm = Mont([0u64; 6]);
    fiat_p384_scalar_to_montgomery_pub(&mut am, a);
    fiat_p384_scalar_to_montgomery_pub(&mut bm, b);
    let mut pm = Mont([0u64; 6]);
    fiat_p384_scalar_mul(&mut pm, &am, &bm);
    let mut out = NonMont([0u64; 6]);
    fiat_p384_scalar_from_montgomery(&mut out, &pm);
    out.0
}

/// `a + b mod n`, for `a, b < n`.
pub fn add(a: &[u64; 6], b: &[u64; 6]) -> [u64; 6] {
    let mut out = *a;
    add_mod_n(&mut out, b);
    out
}

/// `m mod n` for an arbitrary `m < 2^384`.
///
/// Most-significant-bit-first double-and-add: the accumulator is doubled
/// mod n and the next bit of `m` is added, 384 times.  Every iteration runs
/// the same instructions; the conditional subtractions are mask selects.
pub fn reduce(m: &[u64; 6]) -> [u64; 6] {
    let mut acc = [0u64; 6];
    let mut i = 384;
    while i > 0 {
        i -= 1;
        dbl_mod_n(&mut acc);
        let bit = (m[i / 64] >> (i % 64)) & 1;
        let mut addend = [0u64; 6];
        addend[0] = bit;
        add_mod_n(&mut acc, &addend);
    }
    acc
}

/// Number of squarings in [`inv`]: one per exponent bit below the top.
pub const INV_SQUARINGS: u32 = 383;

/// Number of multiplications in [`inv`]: one per set exponent bit below the
/// top.  `tests/cost.rs` checks this against `popcount(n - 2) - 1`.
pub const INV_MULTIPLICATIONS: u32 = 287;

/// `a^(n-2) mod n`, which is `a^-1` for `a != 0` and `0` for `a = 0`.
///
/// Left-to-right square-and-multiply over the bits of the public constant
/// `n - 2`, starting from the top bit, which is set.  The exponent is a
/// compile-time constant, so the operation sequence does not depend on `a`;
/// the fiat multiplication and squaring are themselves constant-time.
/// The cost is [`INV_SQUARINGS`] squarings and [`INV_MULTIPLICATIONS`]
/// multiplications.
pub fn inv(a: &[u64; 6]) -> [u64; 6] {
    let mut base = Mont([0u64; 6]);
    fiat_p384_scalar_to_montgomery_pub(&mut base, a);

    // Bit 383 of n - 2 is set, so the accumulator starts at `base`.
    let mut acc = base;
    let mut sq = Mont([0u64; 6]);
    let mut pr = Mont([0u64; 6]);
    let mut i = 383;
    while i > 0 {
        i -= 1;
        fiat_p384_scalar_square(&mut sq, &acc);
        acc = sq;
        if (N_MINUS_2[i / 64] >> (i % 64)) & 1 == 1 {
            fiat_p384_scalar_mul(&mut pr, &acc, &base);
            acc = pr;
        }
    }

    let mut out = NonMont([0u64; 6]);
    fiat_p384_scalar_from_montgomery(&mut out, &acc);
    out.0
}

/// `a^-1 mod n`, and `0` for `a = 0`, by the Bernstein-Yang divstep
/// inversion of `safegcd::safegcd_p384_order`.
///
/// 15 outer iterations of 59 divsteps, against [`inv`]'s 383 squarings and
/// 287 multiplications.
///
/// The divstep inverter's domain is `[0, n)`, so an input at or above `n`
/// is brought into range first.  `n > 2^383`, so a 384-bit value is below
/// `2n` and one conditional subtraction is enough; [`cond_sub_n`] does it
/// with a mask select, which keeps the reduction on the same footing as
/// the rest of the leaf. [`inv`] reduces such an input too, through the
/// Montgomery conversion, so the two agree on all of `[0, 2^384)`.
///
/// Constant time: the divstep iteration count is the compile-time constant
/// `outer_iters`, and every step is a masked select.
pub fn inv_divstep(a: &[u64; 6]) -> [u64; 6] {
    let mut reduced = *a;
    cond_sub_n(&mut reduced, 0);
    let mut out = [0u64; 6];
    safegcd::safegcd_p384_order::p384_order_invert_divstep_sat(&mut out, &reduced);
    out
}

/// `1`, as canonical limbs.
pub fn one() -> [u64; 6] {
    let mut m = Mont([0u64; 6]);
    fiat_p384_scalar_set_one(&mut m);
    let mut out = NonMont([0u64; 6]);
    fiat_p384_scalar_from_montgomery(&mut out, &m);
    out.0
}

/// `a == b`, with no early exit.
#[inline]
pub fn ct_eq_limbs(a: &[u64; 6], b: &[u64; 6]) -> u64 {
    let mut diff = 0u64;
    for i in 0..6 {
        diff |= a[i] ^ b[i];
    }
    // 1 when diff == 0.
    1 ^ ((diff | diff.wrapping_neg()) >> 63)
}

/// `a == 0`, with no early exit.
#[inline]
pub fn ct_is_zero(a: &[u64; 6]) -> u64 {
    ct_eq_limbs(a, &[0u64; 6])
}

/// `a < n`, with no early exit.
#[inline]
pub fn ct_lt_n(a: &[u64; 6]) -> u64 {
    let mut borrow = 0u64;
    for i in 0..6 {
        let (_, b) = sbb(a[i], N[i], borrow);
        borrow = b;
    }
    borrow
}

// ---------------------------------------------------------------------------
// Montgomery conversion wrapper
// ---------------------------------------------------------------------------

/// `fiat_p384_scalar_to_montgomery` taking canonical limbs rather than the
/// non-Montgomery newtype.
#[inline]
fn fiat_p384_scalar_to_montgomery_pub(out: &mut Mont, a: &[u64; 6]) {
    fiat_crypto::p384_scalar_64::fiat_p384_scalar_to_montgomery(out, &NonMont(*a));
}
