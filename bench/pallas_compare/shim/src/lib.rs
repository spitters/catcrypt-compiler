//! C-linkable shim re-exporting AUCurves' safegcd_pallas BY-inversion leaf.
//!
//! The parent crate `curve25519-jasmin` (at
//! `~/Claude/BLS/AUCurves/curve25519-jasmin-rs/`) ships as an rlib and
//! does NOT export C-callable symbols.  This shim is a `staticlib` that
//! re-exports `safegcd_pallas::pallas_invert_divstep_sat` under the
//! C symbol `pallas_invert_divstep_sat` so the verified-front emitted
//! `.jazz` (and the bench harness) can call it.
//!
//! The wrapped Rust function is:
//!
//! ```rust,ignore
//! pub fn pallas_invert_divstep_sat(out: &mut [u64; 4], x: &[u64; 4]);
//! ```
//!
//! Computes constant-time modular inversion mod the Pallas base
//! prime `p = 2^254 + 45560315531419706090280762371685220353` on a
//! 4×u64 saturated little-endian input.  10 outer iterations × 59
//! inner divsteps = 590 total divsteps (Bernstein-Yang δ₀ = 1/2;
//! ≥ paper Theorem 1 bound 588 for `b = 255`).  The shared kernel
//! `safegcd::invert` operates on 5-limb Signed62 internally.
//!
//! Verification chain (AUCurves):
//!
//! * `safegcd::invert` correctness via the Bernstein-Yang divstep
//!   convergence lemma (eprint 2019/266 + Pornin 2020 refinement
//!   eprint 2020/972).
//! * In-tree KAT vs schoolbook 4×4 → 8-limb mul-mod reference
//!   (`safegcd_pallas.rs::tests::pallas_invert_times_self_is_one`).
//! * CI valgrind/crabgrind CT verification on the compiled binary
//!   (data-independent branches and memory accesses).
//!
//! This shim adds NO axioms beyond `Safegcd_Pallas_invert_*` declared
//! in `CatCrypt/Crypto/Vale/Pallas.lean`.  It is a pure ABI bridge.

use curve25519_jasmin::safegcd_pallas::pallas_invert_divstep_sat as inner;

/// Compute `out = x^-1 mod p_{Pallas}` on 4×u64 saturated input.
///
/// ABI: `out` and `x` are non-aliasing pointers to 32-byte (4×u64 LE)
/// buffers.  Matches the leaf C signature declared in
/// `CatCrypt/Crypto/Vale/Pallas.lean` §1.
///
/// # Safety
///
/// `out` must be a writable pointer to a 4-u64 array; `x` must be a
/// readable pointer to a 4-u64 array.  `out` and `x` must not alias.
/// The pointers must be 8-byte aligned (Rust's standard `[u64; 4]`
/// requirement).  Callers in the verified-front pipeline satisfy
/// these preconditions: the typed reg-ptr ABI emits aligned non-
/// aliasing reg-ptr arguments by construction.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn pallas_invert_divstep_sat(out: *mut u64, x: *const u64) {
    // SAFETY: the caller guarantees out and x are 4-u64 aligned and
    // non-aliasing per the precondition above.  We turn the raw
    // pointers into references to fixed-length arrays, which is the
    // safe-Rust shape AUCurves' pallas_invert_divstep_sat takes.
    let x_arr: &[u64; 4] = unsafe { &*(x as *const [u64; 4]) };
    let out_arr: &mut [u64; 4] = unsafe { &mut *(out as *mut [u64; 4]) };
    inner(out_arr, x_arr);
}
