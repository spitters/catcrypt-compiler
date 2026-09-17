//! The SEC1 uncompressed point encoding, `0x04 || X || Y` with `X` and `Y`
//! 48-byte big-endian field elements, as RFC 9180 §7.1.1 fixes it for
//! `SerializePublicKey` on P-384; and the constant-time checks the DHKEM
//! validity leaves share.
//!
//! Every function here reads or writes bytes and limbs only; the field and
//! group arithmetic is in the backend leaves.

/// The field prime `p = 2^384 - 2^128 - 2^96 + 2^32 - 1`, canonical
/// little-endian limbs.
pub const P: [u64; 6] = [
    0x0000_0000_ffff_ffff,
    0xffff_ffff_0000_0000,
    0xffff_ffff_ffff_fffe,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
];

/// The SEC1 prefix of an uncompressed point.
pub const UNCOMPRESSED: u8 = 0x04;

/// Six little-endian limbs from 48 big-endian bytes.
#[inline]
pub fn limbs_from_be(b: &[u8]) -> [u64; 6] {
    debug_assert_eq!(b.len(), 48);
    let mut out = [0u64; 6];
    for (i, w) in out.iter_mut().enumerate() {
        let mut t = [0u8; 8];
        t.copy_from_slice(&b[40 - 8 * i..48 - 8 * i]);
        *w = u64::from_be_bytes(t);
    }
    out
}

/// 48 big-endian bytes from six little-endian limbs.
#[inline]
pub fn be_from_limbs(out: &mut [u8], l: &[u64; 6]) {
    debug_assert_eq!(out.len(), 48);
    for (i, w) in l.iter().enumerate() {
        out[40 - 8 * i..48 - 8 * i].copy_from_slice(&w.to_be_bytes());
    }
}

/// The two coordinates of an encoded point as canonical-candidate limbs.
/// The prefix is not inspected.
#[inline]
pub fn coords(s: &[u8; 97]) -> ([u64; 6], [u64; 6]) {
    (limbs_from_be(&s[1..49]), limbs_from_be(&s[49..97]))
}

/// `0x04 || be(x) || be(y)`.
#[inline]
pub fn encode(s: &mut [u8; 97], x: &[u64; 6], y: &[u64; 6]) {
    s[0] = UNCOMPRESSED;
    be_from_limbs(&mut s[1..49], x);
    be_from_limbs(&mut s[49..97], y);
}

/// `1` when `a < p`, else `0`, by borrow propagation with no early exit.
#[inline]
pub fn ct_lt_p(a: &[u64; 6]) -> u64 {
    let mut borrow = 0u64;
    for i in 0..6 {
        let (d1, b1) = a[i].overflowing_sub(P[i]);
        let (_, b2) = d1.overflowing_sub(borrow);
        borrow = (b1 | b2) as u64;
    }
    borrow
}

/// `1` when `b == 0x04`, else `0`, with no branch.
#[inline]
pub fn ct_is_uncompressed(b: u8) -> u64 {
    let d = (b ^ UNCOMPRESSED) as u64;
    1 ^ ((d | d.wrapping_neg()) >> 63)
}

/// `1` when the prefix is `0x04` and both coordinates are below `p`: the
/// syntactic half of public-key validation.  The on-curve half is the
/// backend's.
#[inline]
pub fn ct_well_formed(s: &[u8; 97]) -> u64 {
    let (x, y) = coords(s);
    ct_is_uncompressed(s[0]) & ct_lt_p(&x) & ct_lt_p(&y)
}

/// The 48-byte big-endian form of a canonical field element, the output
/// convention of `p384_dh_x_be`.
#[inline]
pub fn be48(l: &[u64; 6]) -> [u8; 48] {
    let mut out = [0u8; 48];
    be_from_limbs(&mut out, l);
    out
}
