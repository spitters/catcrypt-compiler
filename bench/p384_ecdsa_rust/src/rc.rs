//! Bridge to the RustCrypto `p384` / `ecdsa` crates: the differential
//! opponent and the benchmark baseline.
//!
//! RustCrypto scalars and field elements are big-endian 48-byte
//! `FieldBytes`; this crate's ABI is little-endian.  Every conversion goes
//! through [`be_from_limbs`] / [`limbs_from_be`].
//!
//! Signing is driven through `ecdsa::hazmat::SignPrimitive::try_sign_prehashed`
//! with an explicit nonce, not through RFC 6979, because the emitted kernel
//! takes `k` as an input and the two sides must use the same one.

// `GenericArray::clone_from_slice` / `as_slice` carry deprecation warnings pointing to
// generic-array 1.x, which this pinned dependency set predates.
#![allow(deprecated)]

use ecdsa::hazmat::{SignPrimitive, VerifyPrimitive};
use elliptic_curve::ops::{Invert, MulByGenerator as _, Reduce};
use elliptic_curve::point::AffineCoordinates as _;
use elliptic_curve::sec1::FromEncodedPoint;
use elliptic_curve::subtle::CtOption;
use elliptic_curve::PrimeField;
use p384_rc::ecdsa::Signature;
use p384_rc::{AffinePoint, EncodedPoint, FieldBytes, ProjectivePoint, Scalar, U384};

/// A nonce for `try_sign_prehashed`, which needs `AsRef<Scalar>` together
/// with an `Invert` producing `CtOption<Scalar>`; `NonZeroScalar` inverts to
/// itself, so it does not fit the bound.
struct Nonce(Scalar);

impl AsRef<Scalar> for Nonce {
    fn as_ref(&self) -> &Scalar {
        &self.0
    }
}

impl Invert for Nonce {
    type Output = CtOption<Scalar>;
    fn invert(&self) -> CtOption<Scalar> {
        Invert::invert(&self.0)
    }
}

/// Big-endian 48 bytes from canonical little-endian limbs.
pub fn be_from_limbs(l: &[u64; 6]) -> [u8; 48] {
    let mut out = [0u8; 48];
    for i in 0..6 {
        out[40 - 8 * i..48 - 8 * i].copy_from_slice(&l[i].to_be_bytes());
    }
    out
}

/// Canonical little-endian limbs from big-endian 48 bytes.
pub fn limbs_from_be(b: &[u8; 48]) -> [u64; 6] {
    let mut out = [0u64; 6];
    for i in 0..6 {
        let mut w = [0u8; 8];
        w.copy_from_slice(&b[40 - 8 * i..48 - 8 * i]);
        out[i] = u64::from_be_bytes(w);
    }
    out
}

/// A `FieldBytes` from canonical limbs.
pub fn field_bytes(l: &[u64; 6]) -> FieldBytes {
    FieldBytes::clone_from_slice(&be_from_limbs(l))
}

/// A RustCrypto scalar, or `None` when the value is not below `n`.
pub fn scalar(l: &[u64; 6]) -> Option<Scalar> {
    Option::from(Scalar::from_repr(field_bytes(l)))
}

/// A RustCrypto scalar by reduction mod `n`, for any 384-bit value.
pub fn scalar_reduced(l: &[u64; 6]) -> Scalar {
    <Scalar as Reduce<U384>>::reduce_bytes(&field_bytes(l))
}

/// Canonical limbs of a RustCrypto scalar.
pub fn scalar_limbs(s: &Scalar) -> [u64; 6] {
    let mut b = [0u8; 48];
    b.copy_from_slice(s.to_repr().as_slice());
    limbs_from_be(&b)
}

/// `d * G` as a RustCrypto point.
pub fn public_point(d: &Scalar) -> ProjectivePoint {
    ProjectivePoint::mul_by_generator(d)
}

/// A RustCrypto affine point from canonical affine coordinates, or `None`
/// when the coordinates are not on the curve.
pub fn affine_from_coords(x: &[u64; 6], y: &[u64; 6]) -> Option<AffinePoint> {
    let enc = EncodedPoint::from_affine_coordinates(
        &FieldBytes::clone_from_slice(&be_from_limbs(x)),
        &FieldBytes::clone_from_slice(&be_from_limbs(y)),
        false,
    );
    Option::from(AffinePoint::from_encoded_point(&enc))
}

/// The affine x-coordinate of a point, as canonical limbs.
pub fn affine_x(p: &ProjectivePoint) -> [u64; 6] {
    let mut b = [0u8; 48];
    b.copy_from_slice(p.to_affine().x().as_slice());
    limbs_from_be(&b)
}

/// `(r, s)` for digest `e`, private scalar `d` and nonce `k`, all canonical
/// limbs below `n`.  `None` when RustCrypto refuses the inputs, which it
/// does for `k = 0` and for a zero `r` or `s`.
pub fn sign(e: &[u64; 6], d: &[u64; 6], k: &[u64; 6]) -> Option<([u64; 6], [u64; 6])> {
    let ds = scalar(d)?;
    let ks = scalar(k)?;
    let (sig, _) = ds.try_sign_prehashed(Nonce(ks), &field_bytes(e)).ok()?;
    let (r, s) = sig.split_scalars();
    Some((scalar_limbs(&r), scalar_limbs(&s)))
}

/// Whether RustCrypto accepts `(r, s)` on digest `e` under public point `q`.
///
/// `false` covers both a failed signature-structure check (a zero or
/// out-of-range `r` or `s`) and a failed verification.
pub fn verify(e: &[u64; 6], r: &[u64; 6], s: &[u64; 6], q: &AffinePoint) -> bool {
    let (rs, ss) = match (scalar(r), scalar(s)) {
        (Some(a), Some(b)) => (a, b),
        _ => return false,
    };
    let sig = match Signature::from_scalars(rs, ss) {
        Ok(sig) => sig,
        Err(_) => return false,
    };
    q.verify_prehashed(&field_bytes(e), &sig).is_ok()
}
