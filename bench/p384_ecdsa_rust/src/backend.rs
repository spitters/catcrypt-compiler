//! The leaf backends the emitted orchestration runs over, as a table the
//! tests and the benchmark iterate.
//!
//! The emitted sources in `gen/` are included once per backend (see
//! [`crate::generated`]), so every backend runs the same orchestration over
//! a different set of leaves.  What differs between them is the arithmetic
//! and, with it, the meaning of the 144 bytes:
//!
//! | backend | field and group | point ABI |
//! |---|---|---|
//! | `aucurves` | AUCurves `p384-safe-rust` over fiat-crypto, with the CryptOpt assembly when it is linked | homogeneous projective `(X : Y : Z)`, affine `(X/Z, Y/Z)` |
//! | `s2n` | AWS s2n-bignum x86-64 assembly | Jacobian `(X, Y, Z)`, affine `(X/Z^2, Y/Z^3)` |
//!
//! A point string is therefore not portable between backends, and every
//! caller builds one through [`Backend::point_from_affine`],
//! [`Backend::identity`] or [`Backend::generator`] rather than through
//! `codec::point_bytes`.  The two places where the backends must agree are
//! [`Backend::affine_x`], which must give the same canonical `x`, and the
//! identity and validity semantics the kernels apply to a public key;
//! `tests/s2n.rs` checks both directly.
//!
//! `aucurves` is the configuration in which the group law is ours; `s2n` is
//! the configuration in which the arithmetic is the same as Graviola's and
//! only the orchestration differs.  Neither replaces the other.

/// One leaf backend: the three emitted entry points over it, and the point
/// encodings its leaves expect.
pub struct Backend {
    /// Short name, used in test and benchmark output.
    pub name: &'static str,
    /// What is under the leaves, for a one-line report.
    pub arithmetic: &'static str,
    /// `p384_ecdsa_sign(e, d, k, r, s, ok)`.
    pub sign: fn(&[u8; 48], &[u8; 48], &[u8; 48], &mut [u8; 48], &mut [u8; 48], &mut u64),
    /// `p384_ecdsa_verify(e, r, s, Q, ok)`.
    pub verify: fn(&[u8; 48], &[u8; 48], &[u8; 48], &[u8; 144], &mut u64),
    /// `p384_ecdsa_verify_msm(u1, G, u2, Q, result)`.
    pub verify_msm: fn(&[u8; 48], &[u8; 144], &[u8; 48], &[u8; 144], &mut [u8; 144]),
    /// `p384_dhkem_encap(skE, pkR, enc, ss, ok)`, DHKEM(P-384, HKDF-SHA384).
    pub dhkem_encap: fn(&[u8; 48], &[u8; 97], &mut [u8; 97], &mut [u8; 48], &mut u64),
    /// `p384_dhkem_decap(enc, skR, pkR, ss, ok)`.
    pub dhkem_decap: fn(&[u8; 97], &[u8; 48], &[u8; 97], &mut [u8; 48], &mut u64),
    /// The point string for canonical affine coordinates.
    pub point_from_affine: fn(&[u64; 6], &[u64; 6]) -> [u8; 144],
    /// The point string for the identity.
    pub identity: fn() -> [u8; 144],
    /// The point string for the standard base point.
    pub generator: fn() -> [u8; 144],
    /// The canonical affine `x` of a point string, zero for the identity.
    pub affine_x: fn(&[u8; 144]) -> [u64; 6],
    /// The canonical affine coordinates of a point string, `None` for the
    /// identity.
    pub affine: fn(&[u8; 144]) -> Option<([u64; 6], [u64; 6])>,
    /// Builds any precomputed table, so a first timed iteration does not.
    pub warm: fn(),
}

fn aucurves_point_from_affine(x: &[u64; 6], y: &[u64; 6]) -> [u8; 144] {
    crate::codec::point_bytes(&crate::reference::point_from_canonical_affine(x, y))
}

fn aucurves_identity() -> [u8; 144] {
    crate::codec::point_bytes(&p384::group::g1_identity())
}

fn aucurves_generator() -> [u8; 144] {
    crate::codec::point_bytes(&crate::reference::generator())
}

fn aucurves_affine_x(b: &[u8; 144]) -> [u64; 6] {
    crate::reference::affine_x(&crate::codec::point(b))
}

fn aucurves_affine(b: &[u8; 144]) -> Option<([u64; 6], [u64; 6])> {
    let p = crate::codec::point(b);
    let (x, y) = p384::group::g1_to_affine(&p)?;
    let mut xr = p384::FpRaw([0u64; 6]);
    let mut yr = p384::FpRaw([0u64; 6]);
    p384::fp_from_montgomery(&mut xr, &x);
    p384::fp_from_montgomery(&mut yr, &y);
    Some((xr.0, yr.0))
}

/// The AUCurves backend: `src/leaves.rs` over `p384-safe-rust`.
pub const AUCURVES: Backend = Backend {
    name: "aucurves",
    arithmetic: "AUCurves p384-safe-rust over fiat-crypto (RCB complete formulas, projective)",
    sign: crate::generated::p384_ecdsa_sign,
    verify: crate::generated::p384_ecdsa_verify,
    verify_msm: crate::generated::p384_ecdsa_verify_msm,
    dhkem_encap: crate::generated::p384_dhkem_encap,
    dhkem_decap: crate::generated::p384_dhkem_decap,
    point_from_affine: aucurves_point_from_affine,
    identity: aucurves_identity,
    generator: aucurves_generator,
    affine_x: aucurves_affine_x,
    affine: aucurves_affine,
    warm: || {},
};

#[cfg(feature = "s2n")]
fn s2n_point_from_affine(x: &[u64; 6], y: &[u64; 6]) -> [u8; 144] {
    crate::s2n::point_bytes_from_canonical_affine(x, y)
}

#[cfg(feature = "s2n")]
fn s2n_affine_x(b: &[u8; 144]) -> [u64; 6] {
    let mut out = [0u8; 48];
    crate::leaves_s2n::p384_point_affine_x(&mut out, b);
    crate::s2n::fe_from_bytes(&out)
}

#[cfg(feature = "s2n")]
fn s2n_affine(b: &[u8; 144]) -> Option<([u64; 6], [u64; 6])> {
    crate::s2n::to_affine(&crate::s2n::point_from_bytes(b))
}

/// The s2n-bignum backend: `src/leaves_s2n.rs` over `libs2nbignum.a`.
#[cfg(feature = "s2n")]
pub const S2N: Backend = Backend {
    name: "s2n",
    arithmetic: "AWS s2n-bignum x86-64 assembly (Montgomery-Jacobian)",
    sign: crate::generated::s2n_kernel::p384_ecdsa_sign,
    verify: crate::generated::s2n_kernel::p384_ecdsa_verify,
    verify_msm: crate::generated::s2n_kernel::p384_ecdsa_verify_msm,
    dhkem_encap: crate::generated::s2n_kernel::p384_dhkem_encap,
    dhkem_decap: crate::generated::s2n_kernel::p384_dhkem_decap,
    point_from_affine: s2n_point_from_affine,
    identity: crate::s2n::identity_bytes,
    generator: crate::s2n::generator_bytes,
    affine_x: s2n_affine_x,
    affine: s2n_affine,
    warm: crate::comb_s2n::warm,
};

/// Every backend this binary was built with, the default one first.
pub fn all() -> &'static [Backend] {
    #[cfg(feature = "s2n")]
    {
        static ALL: [Backend; 2] = [AUCURVES, S2N];
        &ALL
    }
    #[cfg(not(feature = "s2n"))]
    {
        static ALL: [Backend; 1] = [AUCURVES];
        &ALL
    }
}
