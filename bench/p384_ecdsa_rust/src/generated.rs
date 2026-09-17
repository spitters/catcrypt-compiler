//! The three top-level ECDSA-P-384 entry points and the two DHKEM(P-384)
//! entry points the harness drives, once per leaf backend.
//!
//! Each DHKEM entry point falls back to its transcription
//! (the `dhkem_transcription` macro) on its own when `gen/` does not define it; see
//! `build.rs`.
//!
//! When `gen/` holds compiler-emitted Rust, `build.rs` sets
//! `cfg(p384_emitted)` and those files are included here, with a leaf
//! backend in scope.  Otherwise the [`transcription`] macro below supplies a
//! hand-written transcription of the same three call sequences, so the
//! harness builds and the tests run before the emitted sources land.
//!
//! [`EMITTED`] reports which path this binary was built with.
//!
//! The same emitted sources are included twice when the `s2n` feature is on:
//! once over [`crate::leaves`] and once over [`crate::leaves_s2n`].  The
//! orchestration is identical in both modules — it is the same generated
//! text — and only the leaves under it differ, which is what makes the
//! backends comparable.
//!
//! The emitted entry points take their inputs first and their outputs last,
//! which is `ppRustFunction`'s order; the leaves take the destination first.

/// Whether the three ECDSA entry points re-exported here come from `gen/`.
pub const EMITTED: bool = cfg!(p384_ecdsa_emitted);

/// Whether `p384_dhkem_encap` comes from `gen/`.
pub const DHKEM_ENCAP_EMITTED: bool = cfg!(p384_dhkem_encap_emitted);

/// Whether `p384_dhkem_decap` comes from `gen/`.
pub const DHKEM_DECAP_EMITTED: bool = cfg!(p384_dhkem_decap_emitted);

#[cfg(p384_emitted)]
#[allow(
    dead_code,
    non_snake_case,
    unused_mut,
    unused_parens,
    unused_variables,
    clippy::all,
    clippy::needless_borrow
)]
pub mod emitted {
    use crate::leaves::*;
    include!(concat!(env!("OUT_DIR"), "/emitted_includes.rs"));
}

/// Every entry point `gen/` defines, including any beyond the three the
/// harness names.
#[cfg(p384_emitted)]
pub use emitted::*;

#[cfg(not(p384_ecdsa_emitted))]
pub use fallback::{p384_ecdsa_sign, p384_ecdsa_verify, p384_ecdsa_verify_msm};

#[cfg(not(p384_dhkem_encap_emitted))]
pub use fallback::p384_dhkem_encap;

#[cfg(not(p384_dhkem_decap_emitted))]
pub use fallback::p384_dhkem_decap;

/// The two DHKEM(P-384, HKDF-SHA384) call sequences of RFC 9180 §4.1, in
/// the order the Lean front emits them: eleven leaf calls for `Encap`, nine
/// for `Decap`.
///
/// Scalars are the ABI's six little-endian limbs, not the 48 big-endian
/// bytes of RFC 9180 §7.1.2; callers convert with
/// `crate::dhkem_kdf::sk_le_from_be`.  `enc` and `pkR` are SEC1
/// uncompressed, `0x04 || X || Y`, as the RFC fixes them.
///
/// There is no leaf that tests the Diffie-Hellman output for the identity.
/// P-384 has prime order and cofactor one, so a scalar in `[1, n)` times a
/// valid affine point is never the identity; the two validity flags in
/// `ok` are what exclude it.
macro_rules! dhkem_transcription {
    () => {
        /// `Encap(pkR)` with the ephemeral private key `skE` supplied:
        /// `enc = SerializePublicKey(skE*G)`, `ss = ExtractAndExpand(
        /// x(skE*pkR), enc || pkR)`, and `ok = 1` iff `skE` is in `[1, n)`
        /// and `pkR` is a valid public key.  `enc` and `ss` are written
        /// whatever `ok` is; a caller discards them when `ok = 0`.
        pub fn p384_dhkem_encap(
            skE: &[u8; 48],
            pkR: &[u8; 97],
            enc: &mut [u8; 97],
            ss: &mut [u8; 48],
            ok: &mut u64,
        ) {
            let mut vs = 0u64;
            p384_scalar_in_range(&mut vs, skE);
            let mut vk = 0u64;
            p384_sec1_valid(&mut vk, pkR);
            let mut Q = [0u8; 144];
            p384_sec1_decode(&mut Q, pkR);
            let mut E = [0u8; 144];
            p384_scalar_mul_base(&mut E, skE);
            p384_sec1_encode(enc, &E);
            let mut Z = [0u8; 144];
            p384_scalar_mul(&mut Z, skE, &Q);
            let mut dh = [0u8; 48];
            p384_dh_x_be(&mut dh, &Z);
            let mut ctx = [0u8; 194];
            p384_kem_context(&mut ctx, &enc, pkR);
            let mut prk = [0u8; 48];
            dhkem_p384_extract(&mut prk, &dh);
            dhkem_p384_expand(ss, &prk, &ctx);
            p384_flag_and(ok, &vs, &vk);
        }

        /// `Decap(enc, skR)` with the receiver's public key `pkR` supplied
        /// rather than recomputed: `ss = ExtractAndExpand(x(skR*pkE),
        /// enc || pkR)`, and `ok = 1` iff `enc` is a valid public key and
        /// `skR` is in `[1, n)`.  `pkR` is trusted to be `skR*G`.
        pub fn p384_dhkem_decap(
            enc: &[u8; 97],
            skR: &[u8; 48],
            pkR: &[u8; 97],
            ss: &mut [u8; 48],
            ok: &mut u64,
        ) {
            let mut ve = 0u64;
            p384_sec1_valid(&mut ve, enc);
            let mut vs = 0u64;
            p384_scalar_in_range(&mut vs, skR);
            let mut E = [0u8; 144];
            p384_sec1_decode(&mut E, enc);
            let mut Z = [0u8; 144];
            p384_scalar_mul(&mut Z, skR, &E);
            let mut dh = [0u8; 48];
            p384_dh_x_be(&mut dh, &Z);
            let mut ctx = [0u8; 194];
            p384_kem_context(&mut ctx, enc, pkR);
            let mut prk = [0u8; 48];
            dhkem_p384_extract(&mut prk, &dh);
            dhkem_p384_expand(ss, &prk, &ctx);
            p384_flag_and(ok, &ve, &vs);
        }
    };
}

/// The three call sequences, written by hand in the shape the compiler
/// emits: straight-line leaf calls, destination-first, no control flow and
/// no arithmetic outside a leaf.
///
/// Expanded once per backend, with that backend's leaves in scope.
macro_rules! transcription {
    () => {
        /// `ok = 1` iff `r` and `s` are in `[1, n)`, `Q` is a non-identity
        /// point on the curve, and `(x(u1*G + u2*Q) mod n) == r`, with
        /// `u1 = e * s^-1` and `u2 = r * s^-1`.
        ///
        /// Thirteen leaf calls, the sequence of `gen/p384_ecdsa_verify.rs`.
        /// The two-term multiplication `u1*G + u2*Q` is the single leaf
        /// `p384_lincomb`, which carries the base point, so there is no `G`
        /// parameter.
        pub fn p384_ecdsa_verify(
            e: &[u8; 48],
            r: &[u8; 48],
            s: &[u8; 48],
            Q: &[u8; 144],
            ok: &mut u64,
        ) {
            let mut vr = 0u64;
            p384_scalar_in_range(&mut vr, r);
            let mut vs = 0u64;
            p384_scalar_in_range(&mut vs, s);
            let mut vq = 0u64;
            p384_point_valid(&mut vq, Q);
            let mut sinv = [0u8; 48];
            p384_scalar_inv(&mut sinv, s);
            let mut u1 = [0u8; 48];
            p384_scalar_muln(&mut u1, e, &sinv);
            let mut u2 = [0u8; 48];
            p384_scalar_muln(&mut u2, r, &sinv);
            let mut rpoint = [0u8; 144];
            p384_lincomb(&mut rpoint, &u1, &u2, Q);
            let mut x = [0u8; 48];
            p384_point_affine_x(&mut x, &rpoint);
            let mut xn = [0u8; 48];
            p384_scalar_reduce(&mut xn, &x);
            let mut eq = 0u64;
            p384_scalar_is_eq(&mut eq, &xn, r);
            let mut c1 = 0u64;
            p384_flag_and(&mut c1, &vr, &vs);
            let mut c2 = 0u64;
            p384_flag_and(&mut c2, &c1, &vq);
            p384_flag_and(ok, &c2, &eq);
        }

        /// `r = x(k*G) mod n`, `s = k^-1 * (e + r*d) mod n`, and
        /// `ok = 1` iff both outputs are in `[1, n)`.
        ///
        /// Ten leaf calls, the sequence of `gen/p384_ecdsa_sign.rs`.  `k` is
        /// an input, so a zero `k` is the caller's to resample: it drives
        /// `r` to zero, which `ok` reports.
        pub fn p384_ecdsa_sign(
            e: &[u8; 48],
            d: &[u8; 48],
            k: &[u8; 48],
            r: &mut [u8; 48],
            s: &mut [u8; 48],
            ok: &mut u64,
        ) {
            let mut rpoint = [0u8; 144];
            p384_scalar_mul_base(&mut rpoint, k);
            let mut x = [0u8; 48];
            p384_point_affine_x(&mut x, &rpoint);
            p384_scalar_reduce(r, &x);
            let mut kinv = [0u8; 48];
            p384_scalar_inv(&mut kinv, k);
            let mut rd = [0u8; 48];
            p384_scalar_muln(&mut rd, r, d);
            let mut erd = [0u8; 48];
            p384_scalar_addn(&mut erd, e, &rd);
            p384_scalar_muln(s, &kinv, &erd);
            let mut vr = 0u64;
            p384_scalar_in_range(&mut vr, r);
            let mut vs = 0u64;
            p384_scalar_in_range(&mut vs, s);
            p384_flag_and(ok, &vr, &vs);
        }

        /// `result = u1*G + u2*Q`, the two-term multi-scalar multiplication
        /// inside verification.
        pub fn p384_ecdsa_verify_msm(
            u1: &[u8; 48],
            G: &[u8; 144],
            u2: &[u8; 48],
            Q: &[u8; 144],
            result: &mut [u8; 144],
        ) {
            let mut t1 = [0u8; 144];
            p384_scalar_mul(&mut t1, u1, G);
            let mut t2 = [0u8; 144];
            p384_scalar_mul(&mut t2, u2, Q);
            p384_point_add(result, &t1, &t2);
        }
    };
}

/// The transcription over the `p384-safe-rust` leaves.
///
/// This module is always compiled, so the emitted code and the
/// transcription can be compared in one binary.
#[allow(non_snake_case)]
pub mod fallback {
    use crate::leaves::*;
    transcription!();
    dhkem_transcription!();
}

/// The transcription over the s2n-bignum leaves.
#[cfg(feature = "s2n")]
#[allow(non_snake_case)]
pub mod fallback_s2n {
    use crate::leaves_s2n::*;
    transcription!();
    dhkem_transcription!();
}

/// The same three entry points over the s2n-bignum leaves.
///
/// The emitted sources when `gen/` holds them, the transcription otherwise
/// — the same choice [`EMITTED`] reports for the default backend, because
/// both modules include the same files.
#[cfg(feature = "s2n")]
pub mod s2n_kernel {
    #[cfg(p384_emitted)]
    #[allow(
        dead_code,
        non_snake_case,
        unused_mut,
        unused_parens,
        unused_variables,
        clippy::all,
        clippy::needless_borrow
    )]
    mod emitted_s2n {
        use crate::leaves_s2n::*;
        include!(concat!(env!("OUT_DIR"), "/emitted_includes.rs"));
    }

    #[cfg(p384_emitted)]
    pub use emitted_s2n::*;

    #[cfg(not(p384_ecdsa_emitted))]
    pub use crate::generated::fallback_s2n::{
        p384_ecdsa_sign, p384_ecdsa_verify, p384_ecdsa_verify_msm,
    };

    #[cfg(not(p384_dhkem_encap_emitted))]
    pub use crate::generated::fallback_s2n::p384_dhkem_encap;

    #[cfg(not(p384_dhkem_decap_emitted))]
    pub use crate::generated::fallback_s2n::p384_dhkem_decap;
}
