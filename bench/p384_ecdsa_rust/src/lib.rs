//! Leaf shims and a differential harness for the CatCrypt compiler's
//! emitted P-384 ECDSA source.
//!
//! * [`leaves`] — the thirteen leaf functions the emitted code calls, each
//!   a shim over `p384-safe-rust`, `safegcd`, `fiat-crypto` or, for
//!   [`lincomb`], this crate.
//! * [`lincomb`] — `u1*G + u2*Q` by Shamir's trick, the callee of the
//!   `p384_lincomb` leaf.
//! * [`generated`] — the three top-level entry points, from `gen/` when the
//!   emitted sources are present and from a hand-written transcription of
//!   the same call sequences otherwise.  [`generated::EMITTED`] says which.
//! * [`backend`] — the leaf backends the same emitted orchestration is
//!   compiled over, as a table the tests and the benchmark iterate.
//!
//! Under `--features s2n` a second backend is present: [`s2n`] declares the
//! vendored AWS s2n-bignum assembly, [`leaves_s2n`] is the same thirteen
//! leaves over it, and [`comb_s2n`] and [`lincomb_s2n`] are the two
//! orchestration routines — a fixed-base comb and an interleaved two-term
//! multiply — that the arithmetic is shared with Graviola to isolate.  In
//! that backend the 144-byte point is a **Jacobian** triple rather than a
//! homogeneous projective one; [`leaves_s2n`]'s module header says what
//! follows from that.
//! * [`reference`] — a second sign and verify written against the same
//!   libraries but not against the leaves.
//! * [`rc`] — the bridge to RustCrypto `p384` / `ecdsa`, the first
//!   differential opponent and benchmark baseline.
//! * [`grav`] — the bridge to Graviola, the second, whose P-384 arithmetic
//!   is s2n-bignum assembly rather than fiat-crypto Rust.
//! * [`bssl`] and [`ossl`], under `--features production` — BoringSSL and
//!   OpenSSL 3.0 `libcrypto`, the ECDSA a TLS stack runs, through their C
//!   APIs; and [`awslc`], AWS-LC's `libcrypto.so` loaded at run time, whose
//!   P-384 field is s2n-bignum assembly.
//! * [`scalar`] — the mod-`n` field the scalar leaves use.
//! * [`codec`] — conversions between the byte ABI and the library types.
//! * [`vectors`] — FIPS 186-4 CAVP P-384/SHA-384 signature-generation
//!   vectors.
//!
//! DHKEM(P-384, HKDF-SHA384), RFC 9180 KEM id `0x0011`, `Encap` and
//! `Decap` only:
//!
//! * [`generated::p384_dhkem_encap`] and [`generated::p384_dhkem_decap`] —
//!   emitted when `gen/` defines them, transcribed otherwise, over every
//!   backend; seven more leaves in [`leaves`] and [`leaves_s2n`].
//! * [`dhkem_kdf`] — the three leaves without curve arithmetic, and the
//!   big-endian / little-endian private-key conversion.
//! * [`sec1`] — the SEC1 uncompressed encoding and its syntactic checks.
//! * [`dhkem_ref`] — an independent DHKEM over RustCrypto `p384` ECDH and
//!   `hkdf`.
//! * [`hpke_rs`] — hpke-rs 0.7.0 over its RustCrypto provider, the native
//!   HPKE opponent; DHKEM reconstructions over Graviola in [`grav`], over
//!   BoringSSL in [`bssl`], over AWS-LC in [`awslc`], and over OpenSSL in
//!   [`ossl_kem`].
//!
//! The ABI: scalars and digests are `[u8; 48]`, canonical little-endian
//! integers in `[0, n)`; points are `[u8; 144]`, projective `X || Y || Z`
//! with 48 little-endian Montgomery bytes each; flags are `u64`.

pub mod backend;
pub mod codec;
pub mod dhkem_kdf;
pub mod dhkem_ref;
pub mod generated;
pub mod grav;
pub mod hpke_rs;
pub mod leaves;
pub mod lincomb;
pub mod rc;
pub mod reference;
pub mod scalar;
pub mod sec1;
pub mod vectors;

#[cfg(feature = "s2n")]
pub mod comb_s2n;
#[cfg(feature = "s2n")]
pub mod leaves_s2n;
#[cfg(feature = "s2n")]
pub mod lincomb_s2n;
#[cfg(feature = "s2n")]
pub mod s2n;

// The production TLS-stack opponents: BoringSSL linked statically, OpenSSL
// 3.0 loaded from the system `libcrypto.so.3`, AWS-LC loaded from its build
// tree.  Off by default; see `build.rs` and the module headers.
#[cfg(feature = "production")]
pub mod awslc;
#[cfg(feature = "production")]
pub mod bssl;
#[cfg(feature = "production")]
pub mod ossl;
#[cfg(feature = "production")]
pub mod ossl_kem;

pub use generated::{p384_ecdsa_sign, p384_ecdsa_verify, p384_ecdsa_verify_msm, EMITTED};
pub use generated::{p384_dhkem_decap, p384_dhkem_encap, DHKEM_DECAP_EMITTED, DHKEM_ENCAP_EMITTED};
