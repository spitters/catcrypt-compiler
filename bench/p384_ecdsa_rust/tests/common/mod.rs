//! Shared test helpers: a deterministic PRNG, scalar sampling, and the
//! per-backend point encodings.
//!
//! Every test that drives a kernel runs once per entry of
//! [`p384_ecdsa_rust::backend::all`], because the emitted orchestration is
//! compiled over each leaf backend and the batteries score all of them.  A
//! point string is backend-specific — projective in one, Jacobian in the
//! other — so a test never builds one directly and always goes through
//! [`pub_key`], [`Backend::identity`] or [`Backend::generator`].
//!
//! Each integration test binary compiles this module separately, so items
//! one of them does not use are not dead code.

#![allow(dead_code, unused_imports)]

pub use p384_ecdsa_rust::backend::{self, Backend};

/// SplitMix64, seeded per test so a failure is reproducible from the seed
/// printed in the assertion message.
pub struct Rng(pub u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A uniform 384-bit value, which may exceed `n`.
    pub fn limbs384(&mut self) -> [u64; 6] {
        let mut out = [0u64; 6];
        for w in out.iter_mut() {
            *w = self.next_u64();
        }
        out
    }

    /// A non-zero scalar in `[1, n)`, by rejection.
    pub fn scalar(&mut self) -> [u64; 6] {
        loop {
            let c = self.limbs384();
            if p384_ecdsa_rust::scalar::ct_lt_n(&c) == 1 && c.iter().any(|&w| w != 0) {
                return c;
            }
        }
    }
}

/// Scalar bytes from canonical limbs.
pub fn sb(l: &[u64; 6]) -> [u8; 48] {
    p384_ecdsa_rust::codec::bytes(l)
}

/// Canonical limbs from scalar bytes.
pub fn sl(b: &[u8; 48]) -> [u64; 6] {
    p384_ecdsa_rust::codec::limbs(b)
}

/// The canonical affine coordinates of `k * G`.
///
/// Computed once, with `p384-safe-rust`, and then encoded per backend; the
/// s2n-bignum backend's own base-point multiplication is checked against
/// this one in `tests/s2n.rs`, so using it here does not make the
/// comparison circular.
pub fn affine_base(k: &[u64; 6]) -> ([u64; 6], [u64; 6]) {
    let p = p384::group::g1_scalar_mul_base(k);
    let (x, y) = p384::group::g1_to_affine(&p).expect("k*G is not the identity");
    let mut xr = p384::FpRaw([0u64; 6]);
    let mut yr = p384::FpRaw([0u64; 6]);
    p384::fp_from_montgomery(&mut xr, &x);
    p384::fp_from_montgomery(&mut yr, &y);
    (xr.0, yr.0)
}

/// `a^((p+1)/4) mod p`, a square root of `a` when one exists
/// (`p = 3 mod 4`), computed with the AUCurves field.  With `a = b` it gives
/// the `y` of the curve point `(0, y)`, which the DHKEM rejection tests
/// encode with the non-canonical `x = p`.
pub fn sqrt_candidate(a: &[u64; 6]) -> [u64; 6] {
    use p384::{fp_from_montgomery, fp_mul, fp_square, fp_to_montgomery, Fp, FpRaw};
    // (p + 1) / 4; p + 1 does not carry out of the low limb.
    let mut e = p384_ecdsa_rust::sec1::P;
    e[0] += 1;
    for i in 0..6 {
        e[i] = (e[i] >> 2) | if i < 5 { e[i + 1] << 62 } else { 0 };
    }
    let mut base = Fp([0; 6]);
    fp_to_montgomery(&mut base, &FpRaw(*a));
    let mut acc = Fp([0; 6]);
    fp_to_montgomery(&mut acc, &FpRaw([1, 0, 0, 0, 0, 0]));
    for i in (0..384).rev() {
        let mut t = Fp([0; 6]);
        fp_square(&mut t, &acc);
        acc = t;
        if (e[i / 64] >> (i % 64)) & 1 == 1 {
            let mut t = Fp([0; 6]);
            fp_mul(&mut t, &acc, &base);
            acc = t;
        }
    }
    let mut out = FpRaw([0; 6]);
    fp_from_montgomery(&mut out, &acc);
    out.0
}

/// The public key `d * G` as a point string in `b`'s encoding.
pub fn pub_key(b: &Backend, d: &[u64; 6]) -> [u8; 144] {
    let (x, y) = affine_base(d);
    (b.point_from_affine)(&x, &y)
}
