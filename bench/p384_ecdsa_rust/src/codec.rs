//! Conversions between the byte ABI and the `p384-safe-rust` types.

use p384::group::G1;
use p384::wnaf::{point_from_bytes, point_to_bytes};

/// A scalar or digest: canonical little-endian integer in `[0, n)`.
pub type ScalarBytes = [u8; 48];

/// A projective point: `X || Y || Z`, 48 little-endian Montgomery bytes each.
pub type PointBytes = [u8; 144];

/// Canonical limbs from scalar bytes.
#[inline]
pub fn limbs(b: &ScalarBytes) -> [u64; 6] {
    crate::scalar::limbs_from_bytes(b)
}

/// Scalar bytes from canonical limbs.
#[inline]
pub fn bytes(l: &[u64; 6]) -> ScalarBytes {
    let mut out = [0u8; 48];
    crate::scalar::bytes_from_limbs(&mut out, l);
    out
}

/// `p384::wnaf::point_to_bytes`.
#[inline]
pub fn point_bytes(p: &G1) -> PointBytes {
    point_to_bytes(p)
}

/// `p384::wnaf::point_from_bytes`.
#[inline]
pub fn point(b: &PointBytes) -> G1 {
    point_from_bytes(b)
}

/// Canonical limbs from a big-endian hex string of exactly 96 digits.
///
/// Test vectors are published big-endian; the ABI is little-endian.
pub fn limbs_from_be_hex(hex: &str) -> [u64; 6] {
    assert_eq!(hex.len(), 96, "expected 96 hex digits, got {}", hex.len());
    let mut be = [0u8; 48];
    for i in 0..48 {
        be[i] = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16)
            .unwrap_or_else(|_| panic!("non-hex digit in {hex}"));
    }
    let mut le = [0u8; 48];
    for i in 0..48 {
        le[i] = be[47 - i];
    }
    let mut out = [0u64; 6];
    for i in 0..6 {
        let mut w = [0u8; 8];
        w.copy_from_slice(&le[8 * i..8 * i + 8]);
        out[i] = u64::from_le_bytes(w);
    }
    out
}

/// Scalar bytes from a big-endian hex string of exactly 96 digits.
pub fn scalar_from_be_hex(hex: &str) -> ScalarBytes {
    bytes(&limbs_from_be_hex(hex))
}
