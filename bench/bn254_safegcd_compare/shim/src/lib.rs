//! C-linkable shim re-exporting AUCurves' safegcd_bn254 BY-inversion leaf.
//!
//! Mirrors `../SSProve-lean/bench/p256_safegcd_compare/shim/src/lib.rs`: we include AUCurves'
//! generic divstep core `safegcd.rs` and the BN254 wrapper `safegcd_bn254.rs`
//! by `#[path]` (no FFI, pure Rust), and re-export the single inversion entry
//! point under the C symbol `safegcd_bn254_invert` (matching the leaf name the
//! verified-front emit produces in
//! `gen_com/bn254_safegcd_invert_from_rustcmd_link.jazz`).
//!
//! Provenance (read live from the AUCurves tree at build time, unmodified):
//!
//! * `safegcd.rs`        → AUCurves `curve25519-jasmin-rs/src/safegcd.rs`
//!   (generic const-N Bernstein-Yang divstep core; Rust port of
//!   libsecp256k1 `secp256k1_modinv64.c`, Pieter Dettman 2020, MIT).
//! * `safegcd_bn254.rs`  → AUCurves `curve25519-jasmin-rs/src/safegcd_bn254.rs`
//!   (`ModInfo<5>` over the BN254 base prime
//!   `p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`
//!   + `bn254_invert_divstep_sat`; KAT-tested in-tree via the schoolbook
//!   `x · x^{-1} ≡ 1 (mod p)` round-trip reference).
//!
//! This shim adds NO axioms beyond `AUCurves_safegcd_bn254_invert_*`
//! declared in `CatCrypt/Crypto/Vale/SafegcdBN254.lean`.  It is a pure
//! ABI bridge.

#![allow(non_camel_case_types)]
#![allow(clippy::needless_range_loop)]

#[path = "../../../../../BLS/AUCurves/curve25519-jasmin-rs/src/safegcd.rs"]
pub mod safegcd;

#[path = "../../../../../BLS/AUCurves/curve25519-jasmin-rs/src/safegcd_bn254.rs"]
pub mod safegcd_bn254;

/// Compute `out = x^-1 mod p_{BN254}` on 4×u64 saturated input.
///
/// ABI: `out` and `x` are non-aliasing pointers to 32-byte (4×u64 LE)
/// buffers.  Matches the leaf C signature declared in
/// `CatCrypt/Crypto/Vale/SafegcdBN254.lean`.
///
/// # Safety
///
/// `out` must be a writable 4-u64 array; `x` a readable 4-u64 array; the
/// two must not alias and must be 8-byte aligned (Rust `[u64; 4]`).  The
/// verified-front reg-ptr ABI satisfies these by construction.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn safegcd_bn254_invert(out: *mut u64, x: *const u64) {
    let x_arr: &[u64; 4] = unsafe { &*(x as *const [u64; 4]) };
    let out_arr: &mut [u64; 4] = unsafe { &mut *(out as *mut [u64; 4]) };
    safegcd_bn254::bn254_invert_divstep_sat(out_arr, x_arr);
}
