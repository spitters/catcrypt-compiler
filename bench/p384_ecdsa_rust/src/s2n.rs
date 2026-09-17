//! The s2n-bignum x86-64 assembly this crate's third leaf backend runs on.
//!
//! s2n-bignum is AWS's, machine-checked in HOL Light, and external to us in
//! exactly the sense fiat-crypto and CryptOpt are.  Nothing here implements
//! arithmetic: this module declares the archive's entry points, wraps each
//! one so that no call aliases its output with an input, and supplies the
//! curve constants and the byte conversions the backend above it needs.
//!
//! # What is linked
//!
//! `build.rs` links `x86/libs2nbignum.a` from the s2n-bignum checkout named
//! by `S2N_BIGNUM_DIR` when the `s2n` feature is on; the default is the
//! checkout in the sibling SSProve-lean tree, see `build.rs`.  The archive is built from the
//! `x86_att/` sources; every routine below has its argument order and its
//! Montgomery-domain convention taken from the header comment of its own
//! `.S` file, and the ABI is System V (`RDI`, `RSI`, `RDX`, `RCX`, `R8`),
//! pointer arguments throughout.
//!
//! # Representations
//!
//! * [`Fe`] — a field element mod `p_384`, six little-endian `u64` limbs.
//!   Montgomery domain unless a name says otherwise: `x' = 2^384 x mod p`.
//! * [`Jac`] — a **Jacobian** point, `X || Y || Z` as eighteen limbs, each
//!   coordinate Montgomery.  `(X, Y, Z)` with `Z != 0` is the affine point
//!   `(X/Z^2, Y/Z^3)`; `Z = 0` is the identity.  This is *not* the
//!   homogeneous projective triple the `p384-safe-rust` backend uses, and
//!   the two are not interchangeable — see the module header of
//!   [`crate::leaves_s2n`].
//! * [`Aff`] — an affine point, `X || Y` as twelve Montgomery limbs.  The
//!   second argument of `p384_montjmixadd`, which takes `Z = 1` implicitly.
//! * scalar — six little-endian `u64` limbs, the canonical integer, not in
//!   any Montgomery domain.
//!
//! # Domain conditions
//!
//! The field routines require reduced inputs (`< p_384`), and the generic
//! `bignum_montmul` requires `x * y <= 2^384 * m`, which holds when both
//! arguments are below the modulus.  `p384_montjadd` and `p384_montjmixadd`
//! handle a zero `Z` on their first argument but not the case where the two
//! arguments are equal or mutually inverse; [`crate::lincomb_s2n`] is where
//! that case is detected and repaired, and [`crate::comb_s2n`] is where it
//! is excluded by an argument about the partial sums.

#![allow(dead_code)]

use std::sync::LazyLock;

/// A field element mod `p_384`: six little-endian `u64` limbs.
pub type Fe = [u64; 6];

/// A Jacobian point, `X || Y || Z`, each coordinate Montgomery.
pub type Jac = [u64; 18];

/// An affine point, `X || Y`, each coordinate Montgomery.
pub type Aff = [u64; 12];

/// The 144-byte point ABI, which in this backend carries a [`Jac`].
pub type PointBytes = [u8; 144];

// ---------------------------------------------------------------------------
// The archive
// ---------------------------------------------------------------------------

extern "C" {
    fn bignum_montmul_p384(z: *mut u64, x: *const u64, y: *const u64);
    fn bignum_montsqr_p384(z: *mut u64, x: *const u64);
    fn bignum_montinv_p384(z: *mut u64, x: *const u64);
    fn bignum_tomont_p384(z: *mut u64, x: *const u64);
    fn bignum_deamont_p384(z: *mut u64, x: *const u64);
    fn bignum_add_p384(z: *mut u64, x: *const u64, y: *const u64);
    fn bignum_sub_p384(z: *mut u64, x: *const u64, y: *const u64);
    fn bignum_optneg_p384(z: *mut u64, p: u64, x: *const u64);
    fn bignum_mux_6(p: u64, z: *mut u64, x: *const u64, y: *const u64);

    fn bignum_mod_n384_6(z: *mut u64, x: *const u64);
    fn bignum_montmul(k: u64, z: *mut u64, x: *const u64, y: *const u64, m: *const u64);
    fn bignum_modadd(k: u64, z: *mut u64, x: *const u64, y: *const u64, m: *const u64);
    fn bignum_montifier(k: u64, z: *mut u64, m: *const u64, t: *mut u64);
    fn bignum_modinv(k: u64, z: *mut u64, a: *const u64, b: *const u64, t: *mut u64);
    fn bignum_lt(m: u64, x: *const u64, n: u64, y: *const u64) -> u64;
    fn bignum_eq(m: u64, x: *const u64, n: u64, y: *const u64) -> u64;
    fn bignum_iszero(k: u64, x: *const u64) -> u64;

    fn p384_montjadd(p3: *mut u64, p1: *const u64, p2: *const u64);
    fn p384_montjdouble(p3: *mut u64, p1: *const u64);
    fn p384_montjmixadd(p3: *mut u64, p1: *const u64, p2: *const u64);
    fn p384_montjscalarmul(res: *mut u64, scalar: *const u64, point: *const u64);
}

// ---------------------------------------------------------------------------
// Field arithmetic mod p_384
// ---------------------------------------------------------------------------

/// `x * y / 2^384 mod p`, the Montgomery product.
#[inline]
pub fn montmul(x: &Fe, y: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_montmul_p384(z.as_mut_ptr(), x.as_ptr(), y.as_ptr()) };
    z
}

/// `x^2 / 2^384 mod p`, the Montgomery square.
#[inline]
pub fn montsqr(x: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_montsqr_p384(z.as_mut_ptr(), x.as_ptr()) };
    z
}

/// The Montgomery inverse: `z` with `x * z == 2^768 mod p`, and `0` for a
/// multiple of `p`.  Montgomery form in, Montgomery form out.
#[inline]
pub fn montinv(x: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_montinv_p384(z.as_mut_ptr(), x.as_ptr()) };
    z
}

/// `2^384 x mod p`: canonical to Montgomery.
#[inline]
pub fn tomont(x: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_tomont_p384(z.as_mut_ptr(), x.as_ptr()) };
    z
}

/// `x / 2^384 mod p`: Montgomery to canonical, for any six-limb input.
#[inline]
pub fn deamont(x: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_deamont_p384(z.as_mut_ptr(), x.as_ptr()) };
    z
}

/// `x + y mod p`, for reduced `x` and `y`.
#[inline]
pub fn fadd(x: &Fe, y: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_add_p384(z.as_mut_ptr(), x.as_ptr(), y.as_ptr()) };
    z
}

/// `x - y mod p`, for reduced `x` and `y`.
#[inline]
pub fn fsub(x: &Fe, y: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_sub_p384(z.as_mut_ptr(), x.as_ptr(), y.as_ptr()) };
    z
}

/// `-x mod p` when `neg` is non-zero, `x` when it is zero.  A mask select
/// inside the assembly, with no branch.
#[inline]
pub fn optneg(neg: u64, x: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_optneg_p384(z.as_mut_ptr(), neg, x.as_ptr()) };
    z
}

/// `x` when `p` is non-zero, `y` when it is zero, by `cmov`.
#[inline]
pub fn mux(p: u64, x: &Fe, y: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_mux_6(p, z.as_mut_ptr(), x.as_ptr(), y.as_ptr()) };
    z
}

// ---------------------------------------------------------------------------
// The scalar field mod n_384
// ---------------------------------------------------------------------------

/// The group order, canonical little-endian limbs.
pub const N: Fe = crate::scalar::N;

/// `2^768 mod n`, the montifier for the scalar field.
///
/// s2n-bignum has no `bignum_tomont_n384`, so the constant that maps a
/// canonical scalar into the Montgomery domain of the generic
/// `bignum_montmul` is computed once, by the archive's own
/// `bignum_montifier`, rather than transcribed.  `tests/s2n.rs` checks it
/// against `2^768 mod n` computed by repeated doubling.
pub static R2_N: LazyLock<Fe> = LazyLock::new(|| {
    let mut z = [0u64; 6];
    let mut t = [0u64; 6];
    unsafe { bignum_montifier(6, z.as_mut_ptr(), N.as_ptr(), t.as_mut_ptr()) };
    z
});

/// `x mod n` for any six-limb `x`.
#[inline]
pub fn mod_n(x: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_mod_n384_6(z.as_mut_ptr(), x.as_ptr()) };
    z
}

/// `x * y / 2^384 mod n`, the generic Montgomery product at the group
/// order.  Both arguments must be below `n`.
#[inline]
pub fn montmul_n(x: &Fe, y: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_montmul(6, z.as_mut_ptr(), x.as_ptr(), y.as_ptr(), N.as_ptr()) };
    z
}

/// `x * y mod n`, for canonical `x` and `y` below `n`: one generic
/// Montgomery product to enter the domain and one to leave it.
#[inline]
pub fn mul_n(x: &Fe, y: &Fe) -> Fe {
    let xm = montmul_n(x, &R2_N);
    montmul_n(&xm, y)
}

/// `x + y mod n`, for reduced `x` and `y`.
#[inline]
pub fn add_n(x: &Fe, y: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_modadd(6, z.as_mut_ptr(), x.as_ptr(), y.as_ptr(), N.as_ptr()) };
    z
}

/// `a^-1 mod n` by the archive's generic modular inverse, which requires an
/// odd modulus above one and an argument coprime to it.
///
/// Not used by the leaves: s2n-bignum has no `bignum_inv_n384`, and this
/// generic routine is measured against the crate's divstep inverse in the
/// benchmark rather than substituted for it.
pub fn modinv_n(a: &Fe) -> Fe {
    let mut z = [0u64; 6];
    let mut t = [0u64; 3 * 6];
    unsafe { bignum_modinv(6, z.as_mut_ptr(), a.as_ptr(), N.as_ptr(), t.as_mut_ptr()) };
    z
}

/// `1` when `x < y`, else `0`, with no early exit.
#[inline]
pub fn lt(x: &Fe, y: &Fe) -> u64 {
    unsafe { bignum_lt(6, x.as_ptr(), 6, y.as_ptr()) }
}

/// `1` when `x == y`, else `0`, with no early exit.
#[inline]
pub fn eq(x: &Fe, y: &Fe) -> u64 {
    unsafe { bignum_eq(6, x.as_ptr(), 6, y.as_ptr()) }
}

/// `1` when `x == 0`, else `0`, with no early exit.
#[inline]
pub fn iszero(x: &Fe) -> u64 {
    unsafe { bignum_iszero(6, x.as_ptr()) }
}

// ---------------------------------------------------------------------------
// The group
// ---------------------------------------------------------------------------

/// `p1 + p2` in Jacobian coordinates.
///
/// Correct when the two arguments are distinct and not mutually inverse, and
/// when either has `Z = 0`.  Equal arguments give the identity rather than
/// the double; callers either exclude that case or detect and repair it.
#[inline]
pub fn jadd(p1: &Jac, p2: &Jac) -> Jac {
    let mut z = [0u64; 18];
    unsafe { p384_montjadd(z.as_mut_ptr(), p1.as_ptr(), p2.as_ptr()) };
    z
}

/// `2 * p1` in Jacobian coordinates.
#[inline]
pub fn jdouble(p1: &Jac) -> Jac {
    let mut z = [0u64; 18];
    unsafe { p384_montjdouble(z.as_mut_ptr(), p1.as_ptr()) };
    z
}

/// `p1 + p2` with `p2` affine, the mixed addition a comb wants.
///
/// The same domain as [`jadd`]: `Z1 = 0` is handled and returns `p2`, equal
/// or mutually inverse arguments are not.
#[inline]
pub fn jmixadd(p1: &Jac, p2: &Aff) -> Jac {
    let mut z = [0u64; 18];
    unsafe { p384_montjmixadd(z.as_mut_ptr(), p1.as_ptr(), p2.as_ptr()) };
    z
}

/// `scalar * point`, a complete constant-time scalar multiplication.
///
/// The archive's own routine: it reduces the scalar mod `n`, builds a
/// sixteen-entry table of multiples of the point, recodes the scalar into
/// signed five-bit digits, and runs seventy-six window steps of five
/// doublings and one addition.  The identity is produced with `Z = 0` when
/// the result is the identity.
#[inline]
pub fn jscalarmul(scalar: &Fe, point: &Jac) -> Jac {
    let mut z = [0u64; 18];
    unsafe { p384_montjscalarmul(z.as_mut_ptr(), scalar.as_ptr(), point.as_ptr()) };
    z
}

// ---------------------------------------------------------------------------
// Curve constants
// ---------------------------------------------------------------------------

/// `b` of `y^2 = x^3 - 3x + b`, canonical limbs.  FIPS 186-4 D.1.2.4.
pub const B_CANON: Fe = [
    0x2a85c8edd3ec2aef,
    0xc656398d8a2ed19d,
    0x0314088f5013875a,
    0x181d9c6efe814112,
    0x988e056be3f82d19,
    0xb3312fa7e23ee7e4,
];

/// `G_x`, canonical limbs.
pub const GX_CANON: Fe = [
    0x3a545e3872760ab7,
    0x5502f25dbf55296c,
    0x59f741e082542a38,
    0x6e1d3b628ba79b98,
    0x8eb1c71ef320ad74,
    0xaa87ca22be8b0537,
];

/// `G_y`, canonical limbs.
pub const GY_CANON: Fe = [
    0x7a431d7c90ea0e5f,
    0x0a60b1ce1d7e819d,
    0xe9da3113b5f0b8c0,
    0xf8f41dbd289a147c,
    0x5d9e98bf9292dc29,
    0x3617de4a96262c6f,
];

/// `1` in the Montgomery domain, `2^384 mod p`.  The `Z` of an affine point
/// lifted to Jacobian coordinates.
pub static ONE_MONT: LazyLock<Fe> = LazyLock::new(|| {
    let mut one = [0u64; 6];
    one[0] = 1;
    tomont(&one)
});

/// `b` in the Montgomery domain.
pub static B_MONT: LazyLock<Fe> = LazyLock::new(|| tomont(&B_CANON));

/// The standard base point in affine Montgomery coordinates.
pub static G_AFF: LazyLock<Aff> = LazyLock::new(|| {
    let mut a = [0u64; 12];
    a[..6].copy_from_slice(&tomont(&GX_CANON));
    a[6..].copy_from_slice(&tomont(&GY_CANON));
    a
});

/// The standard base point in Jacobian Montgomery coordinates.
pub static G_JAC: LazyLock<Jac> = LazyLock::new(|| aff_to_jac(&G_AFF));

// ---------------------------------------------------------------------------
// Point plumbing
// ---------------------------------------------------------------------------

/// The identity, `Z = 0`.
#[inline]
pub fn identity() -> Jac {
    [0u64; 18]
}

/// The `X`, `Y` and `Z` coordinates of a Jacobian point.
#[inline]
pub fn jx(p: &Jac) -> Fe {
    let mut z = [0u64; 6];
    z.copy_from_slice(&p[..6]);
    z
}

/// See [`jx`].
#[inline]
pub fn jy(p: &Jac) -> Fe {
    let mut z = [0u64; 6];
    z.copy_from_slice(&p[6..12]);
    z
}

/// See [`jx`].
#[inline]
pub fn jz(p: &Jac) -> Fe {
    let mut z = [0u64; 6];
    z.copy_from_slice(&p[12..]);
    z
}

/// A Jacobian point from its three coordinates.
#[inline]
pub fn jac(x: &Fe, y: &Fe, z: &Fe) -> Jac {
    let mut p = [0u64; 18];
    p[..6].copy_from_slice(x);
    p[6..12].copy_from_slice(y);
    p[12..].copy_from_slice(z);
    p
}

/// An affine point lifted to Jacobian coordinates with `Z = 1`.
#[inline]
pub fn aff_to_jac(a: &Aff) -> Jac {
    let mut p = [0u64; 18];
    p[..12].copy_from_slice(a);
    p[12..].copy_from_slice(&*ONE_MONT);
    p
}

/// Whether `p` is the identity.
#[inline]
pub fn is_identity(p: &Jac) -> bool {
    p[12..].iter().all(|&w| w == 0)
}

/// `-p`, by negating `Y`.
#[inline]
pub fn jneg(p: &Jac) -> Jac {
    jac(&jx(p), &optneg(1, &jy(p)), &jz(p))
}

/// `-a`, for an affine point.
#[inline]
pub fn aneg(a: &Aff) -> Aff {
    let mut out = *a;
    let mut y = [0u64; 6];
    y.copy_from_slice(&a[6..]);
    out[6..].copy_from_slice(&optneg(1, &y));
    out
}

/// The canonical affine coordinates of `p`, or `None` for the identity.
///
/// One Montgomery inverse of `Z`, two squarings and three multiplications.
pub fn to_affine(p: &Jac) -> Option<(Fe, Fe)> {
    let z = jz(p);
    if iszero(&z) == 1 {
        return None;
    }
    let zi = montinv(&z);
    let zi2 = montsqr(&zi);
    let zi3 = montmul(&zi2, &zi);
    Some((
        deamont(&montmul(&jx(p), &zi2)),
        deamont(&montmul(&jy(p), &zi3)),
    ))
}

/// A Jacobian point from canonical affine coordinates, with `Z = 1`.
pub fn from_canonical_affine(x: &Fe, y: &Fe) -> Jac {
    jac(&tomont(x), &tomont(y), &ONE_MONT)
}

/// The 144-byte point string this backend uses for canonical affine
/// coordinates.
pub fn point_bytes_from_canonical_affine(x: &Fe, y: &Fe) -> PointBytes {
    point_to_bytes(&from_canonical_affine(x, y))
}

/// The 144-byte point string of the identity: `Z = 0`, hence all zeros.
pub fn identity_bytes() -> PointBytes {
    [0u8; 144]
}

/// The 144-byte point string of the standard base point.
pub fn generator_bytes() -> PointBytes {
    point_to_bytes(&G_JAC)
}

/// Whether two Jacobian points are the same point of the curve.
///
/// `X1 Z2^2 == X2 Z1^2` and `Y1 Z2^3 == Y2 Z1^3`, which is projective
/// equality without an inversion.  Two identities compare equal.
pub fn same_point(p: &Jac, q: &Jac) -> bool {
    let (z1, z2) = (jz(p), jz(q));
    if iszero(&z1) == 1 || iszero(&z2) == 1 {
        return iszero(&z1) == iszero(&z2);
    }
    let z1s = montsqr(&z1);
    let z2s = montsqr(&z2);
    if eq(&montmul(&jx(p), &z2s), &montmul(&jx(q), &z1s)) == 0 {
        return false;
    }
    let z1c = montmul(&z1s, &z1);
    let z2c = montmul(&z2s, &z2);
    eq(&montmul(&jy(p), &z2c), &montmul(&jy(q), &z1c)) == 1
}

// ---------------------------------------------------------------------------
// The byte ABI
// ---------------------------------------------------------------------------

/// Six limbs from 48 little-endian bytes.
#[inline]
pub fn fe_from_bytes(b: &[u8; 48]) -> Fe {
    let mut out = [0u64; 6];
    for (i, w) in out.iter_mut().enumerate() {
        let mut t = [0u8; 8];
        t.copy_from_slice(&b[8 * i..8 * i + 8]);
        *w = u64::from_le_bytes(t);
    }
    out
}

/// 48 little-endian bytes from six limbs.
#[inline]
pub fn fe_to_bytes(out: &mut [u8; 48], x: &Fe) {
    for (i, w) in x.iter().enumerate() {
        out[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
}

/// A Jacobian point from the 144-byte ABI.
#[inline]
pub fn point_from_bytes(b: &PointBytes) -> Jac {
    let mut out = [0u64; 18];
    for (i, w) in out.iter_mut().enumerate() {
        let mut t = [0u8; 8];
        t.copy_from_slice(&b[8 * i..8 * i + 8]);
        *w = u64::from_le_bytes(t);
    }
    out
}

/// The 144-byte ABI from a Jacobian point.
#[inline]
pub fn point_to_bytes(p: &Jac) -> PointBytes {
    let mut out = [0u8; 144];
    for (i, w) in p.iter().enumerate() {
        out[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    out
}
