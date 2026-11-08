//! # catcrypt-mpn
//!
//! GMP-style multi-precision natural-number (`mpn`) limb operations over
//! kernels **emitted by the CatCrypt compiler**: the equal-length limb loops
//! `mpn_{add,sub,and,ior,xor}_n` (`MpnLoopFrontEmit.lean`), the shift funnel
//! `mpn_shift_rt` (`MpnShiftFrontEmit.lean`), the constant-time comparison
//! `mpn_cmp_ct` (`MpnCmpFrontEmit.lean`) and the schoolbook product
//! `mpn_mul_basecase_rt` (`MpnMulBasecaseFrontEmit.lean`), all front-compiled
//! `LowCT` loop bodies with no hand-authored IR.
//!
//! ## Layers
//!
//! - `mpn_ffi` (**generated** by `MpnCrateEmit.lean`, do not edit):
//!   the `extern "C"` declarations and safe equal-length slice wrappers
//!   ([`mpn_add_n`], [`mpn_sub_n`], [`mpn_and_n`], [`mpn_ior_n`],
//!   [`mpn_xor_n`]). `unsafe` is confined to the wrapper bodies; slice
//!   distinctness (the kernels' verified state model has no aliasing) is
//!   enforced by the borrow checker.
//! - `rt_ffi` (**hand-written**): the same for the three runtime-trip
//!   kernels ([`mpn_shift_n`], [`mpn_cmp_n`], [`mpn_mul_basecase`]), with
//!   the kernels' range and length preconditions checked.
//! - [`seam`] (**hand-written, safe**): the variable-length add/sub bridge
//!   (zero-extension packing, the (m+1)-limb carry capture, the
//!   normalization scan) and the u32-surface bitwise, compare, shift and
//!   multiply operations over caller-provided u64 scratch, one function per
//!   step so a later verified replacement swaps one call site.
//! - [`cabi`] (**hand-written**, an `unsafe` island): `#[no_mangle]
//!   extern "C"` entry points over u32 digit arrays (`mpn_*_oc_32`, which
//!   also provide the seam's scratch: stack, or libc heap for large
//!   operands) and u64 limb arrays (`mpn_*_n_oc_64`). Building this crate as a
//!   `staticlib` yields an archive with these entries and the raw kernel
//!   symbols, for C callers with 32-bit digits.
//!
//! The Lean runtime of the CatCrypt lean4 branch `catcrypt-mpn-4.35.0` links this archive
//! and calls the kernels on its own 64-bit digit arrays.
//!
//! ## Trust boundary
//!
//! - **Verified in Lean (CatCrypt):** the kernels, within the scope each
//!   emitting module states. The five equal-length loops are encoded to
//!   object bytes by the translation-validated encoder, and the extern
//!   signatures of `mpn_ffi` are derived from the same `Lprog` values. The
//!   three runtime-trip kernels are encoded by the same encoder.
//! - **Trusted (TCB):** the linker; `rustc` (for the glue in this
//!   crate); the `extern "C"` boundary; the hand-written `rt_ffi`
//!   declarations; and the seam and C-ABI glue (differential- and
//!   vector-tested in `tests/kat.rs` and `tests/seam_diff.rs`).
//!
//! ## Safety
//!
//! `#![deny(unsafe_code)]` crate-wide; the `mpn_ffi` and `rt_ffi` kernel
//! modules and the `cabi` export module are the only opt-ins.

// `no_std` for the staticlib (built with `--no-default-features`), so the
// archive is self-contained — only the verified kernels, the safe seam, and
// this crate's panic-abort handler, pulling none of the Rust std runtime into
// the final link. The default `std` feature keeps the crate on std for the
// `cargo test` KAT harness.
#![cfg_attr(not(feature = "std"), no_std)]
#![deny(unsafe_code)]

// A length-check bound was violated. Abort — no unwinding across the C ABI. `panic = "abort"` (Cargo.toml release profile) makes this terminal.
#[cfg(not(feature = "std"))]
#[panic_handler]
#[allow(unsafe_code)]
fn panic(_info: &core::panic::PanicInfo<'_>) -> ! {
    extern "C" {
        fn abort() -> !;
    }
    unsafe { abort() }
}

// The precompiled `core` objects carry unwind tables that name
// `rust_eh_personality`. With `panic = "abort"` nothing unwinds, so the routine
// is never called; this definition only resolves the symbol for the C++ link.
#[cfg(not(feature = "std"))]
#[no_mangle]
#[allow(unsafe_code)]
pub extern "C" fn rust_eh_personality() {}

mod mpn_ffi;

pub use mpn_ffi::{mpn_add_n, mpn_and_n, mpn_ior_n, mpn_sub_n, mpn_xor_n};
pub use rt_ffi::{mpn_cmp_n, mpn_mul_basecase, mpn_shift_n};

#[allow(unsafe_code)]
mod rt_ffi {
    //! Extern declarations and safe wrappers for the runtime-trip kernels
    //! `mpn_shift_rt` (`MpnShiftFrontEmit.lean`), `mpn_cmp_ct`
    //! (`MpnCmpFrontEmit.lean`) and `mpn_mul_basecase_rt`
    //! (`MpnMulBasecaseFrontEmit.lean`) of the CatCrypt compiler. Hand-written:
    //! `MpnCrateEmit.lean` generates `mpn_ffi` for the five equal-length loops
    //! only.
    //!
    //! The kernels use SysV x86-64 argument registers and BMI2 (`shlx`,
    //! `shrx`, `mulx`). Their result is written through `rp`; the value left in
    //! `RAX` is the final loop index, not a pointer, so the declarations below
    //! return nothing. Each kernel writes below its own adjusted `%rsp`, inside
    //! the SysV red zone, which is legal for a leaf function.

    extern "C" {
        /// SysV: rp=RDI, up=RSI, n=RDX, sh=RCX. `rp` holds `n + 1` words.
        fn mpn_shift_rt(rp: *mut u64, up: *const u64, n: u64, sh: u64);
        /// SysV: rp=RDI, ap=RSI, bp=RDX, n=RCX. `rp` holds one word.
        fn mpn_cmp_ct(rp: *mut u64, ap: *const u64, bp: *const u64, n: u64);
        /// SysV: rp=RDI, up=RSI, vp=RDX, un=RCX, vn=R8. `rp` holds
        /// `un + vn + 1` words.
        fn mpn_mul_basecase_rt(rp: *mut u64, up: *const u64, vp: *const u64, un: u64, vn: u64);
    }

    /// The shift funnel: with `n = up.len()` and `rp.len() == n + 1`, sets
    /// `value(rp[0..=n]) = value(up) * 2^sh + s`, where `s` is the value of
    /// `rp[0]` on entry (the spill-in, required below `2^sh`).
    ///
    /// Left shift by `cnt` is `sh = cnt` with `rp[0] = 0`: `rp[0..n]` is the
    /// shifted value mod `2^(64 n)` and `rp[n]` the bits shifted out. Right
    /// shift by `cnt` is `sh = 64 - cnt` with `rp[0] = 0`: `rp[1..=n]` is
    /// `value(up) >> cnt` and `rp[0]` the bits shifted out at the bottom.
    ///
    /// Panics unless `1 <= sh <= 63`, `rp.len() == up.len() + 1` and
    /// `rp[0] < 2^sh`. (`sh = 64` is excluded: the machine masks the
    /// complementary count `64 - sh = 0` differently from the word model.)
    pub fn mpn_shift_n(rp: &mut [u64], up: &[u64], sh: u32) {
        let n = up.len();
        assert!((1..=63).contains(&sh));
        assert_eq!(rp.len(), n + 1);
        assert_eq!(rp[0] >> sh, 0);
        // SAFETY: the slices are distinct (borrow-checked); the kernel reads
        // up[0..n) and rp[0..n), writes rp[0..=n], and retains no pointer.
        unsafe { mpn_shift_rt(rp.as_mut_ptr(), up.as_ptr(), n as u64, sh as u64) }
    }

    /// Constant-time comparison of two equal-length little-endian values:
    /// `1` if `ap > bp`, `-1` if `ap < bp`, `0` if equal. The trip count is
    /// `ap.len()`, independent of the contents.
    ///
    /// Panics if the lengths differ, or if the kernel's result cell holds a
    /// value other than `0`, `1` or `2^64 - 1`.
    pub fn mpn_cmp_n(ap: &[u64], bp: &[u64]) -> i32 {
        let n = ap.len();
        assert_eq!(bp.len(), n);
        let mut cell = [0u64; 1];
        // SAFETY: `cell` is a distinct one-word buffer; the kernel reads
        // ap[0..n), bp[0..n), reads and writes cell[0], retains no pointer.
        unsafe { mpn_cmp_ct(cell.as_mut_ptr(), ap.as_ptr(), bp.as_ptr(), n as u64) }
        match cell[0] {
            0 => 0,
            1 => 1,
            u64::MAX => -1,
            _ => panic!("mpn_cmp_ct: result cell out of range"),
        }
    }

    /// Schoolbook product: with `un = up.len()`, `vn = vp.len()` and
    /// `rp.len() == un + vn + 1`, sets `value(rp[0..un+vn)) = value(up) *
    /// value(vp)` and `rp[un+vn] = 0`. `rp` is zeroed before the call (the
    /// kernel's entry condition). `up` and `vp` may be the same slice.
    ///
    /// Panics if `up` or `vp` is empty (the kernel's flush trip reads
    /// `up[0]`) or if `rp` has the wrong length.
    pub fn mpn_mul_basecase(rp: &mut [u64], up: &[u64], vp: &[u64]) {
        let (un, vn) = (up.len(), vp.len());
        assert!(un >= 1 && vn >= 1);
        assert_eq!(rp.len(), un + vn + 1);
        rp.fill(0);
        // SAFETY: `rp` is distinct from `up`/`vp` (borrow-checked); the kernel
        // reads up[0..un), vp[0..vn), reads and writes rp[0..=un+vn], and
        // retains no pointer. `up`/`vp` are only read, so they may alias.
        unsafe {
            mpn_mul_basecase_rt(
                rp.as_mut_ptr(),
                up.as_ptr(),
                vp.as_ptr(),
                un as u64,
                vn as u64,
            )
        }
        assert_eq!(rp[un + vn], 0);
    }
}

pub mod seam {
    //! Variable-length → equal-length seam over the verified kernels
    //! (safe Rust; mirrors the dev repository's `bench/integration_owned/lean_mpn_adapter_u32.c`
    //! and the `lean::mpn_add`/`mpn_sub` semantics of the Lean runtime).
    //!
    //! One function per algorithmic step — packing, kernel call, unpack,
    //! normalization — so each step can be individually replaced by a
    //! verified kernel later.

    use crate::mpn_ffi;

    /// Stack scratch capacity in u32 limbs of [`add_vl_u32`],
    /// [`sub_vl_u32`], [`add_vl_u64`] and [`sub_vl_u64`]; longer inputs
    /// panic. The Lean runtime does not call these four (it calls the
    /// `cabi` entries, which have no length bound).
    pub const MAX_LIMBS_U32: usize = 4096;
    /// Scratch capacity in u64 limbs.
    const MAX64: usize = MAX_LIMBS_U32 / 2;

    /// Step: zero-extension packing. Write `src`'s u32 limbs into the low
    /// half-words of `dst` (little-endian pairing
    /// `dst[i/2] |= src[i] << 32*(i%2)`), zeroing the first
    /// `m32/2` u64 limbs first. `m32` must be even and `>= src.len()`.
    fn pack_ext(dst: &mut [u64], src: &[u32], m32: usize) {
        debug_assert!(m32 % 2 == 0 && src.len() <= m32);
        let n64 = m32 / 2;
        for limb in dst[..n64].iter_mut() {
            *limb = 0;
        }
        for (i, &w) in src.iter().enumerate() {
            dst[i / 2] |= (w as u64) << (32 * (i % 2));
        }
    }

    /// Step: unpack the low `dst.len()` u32 limbs out of the u64 limbs of
    /// `src`.
    fn unpack_low(dst: &mut [u32], src: &[u64]) {
        for (i, w) in dst.iter_mut().enumerate() {
            *w = (src[i / 2] >> (32 * (i % 2))) as u32;
        }
    }

    /// Step: normalization scan — the length of `c` with trailing zero
    /// limbs trimmed, floored at 1 (the `lean::mpn_add` `*plngc`
    /// convention).
    fn normalized_len(c: &[u32]) -> usize {
        let mut os = c.len();
        while os > 1 && c[os - 1] == 0 {
            os -= 1;
        }
        os
    }

    /// u32 limb `i` of a little-endian u64 limb array.
    fn u32_limb(src: &[u64], i: usize) -> u32 {
        (src[i / 2] >> (32 * (i % 2))) as u32
    }

    /// Variable-length add with the `lean::mpn_add` surface: writes
    /// `max(a.len(), b.len()) + 1` u32 limbs to `c` and returns the
    /// normalized length. The carry is captured by the (m+1)-limb trick:
    /// both operands are zero-extended one limb past the longer one, so
    /// the equal-length kernel sum holds the carry in the top limb and no
    /// scalar carry return is needed.
    ///
    /// Panics if `c` is shorter than `max + 1` limbs or the extended
    /// length exceeds [`MAX_LIMBS_U32`].
    pub fn add_vl_u32(a: &[u32], b: &[u32], c: &mut [u32]) -> usize {
        let len = a.len().max(b.len());
        let ext = len + 1; // the carry lands in u32 limb [len]
        let ext2 = ext + (ext & 1); // whole u64 limbs for the kernel
        assert!(ext2 <= MAX_LIMBS_U32);
        assert!(c.len() >= ext);
        let n64 = ext2 / 2;
        let mut ea = [0u64; MAX64];
        let mut eb = [0u64; MAX64];
        let mut er = [0u64; MAX64];
        pack_ext(&mut ea, a, ext2);
        pack_ext(&mut eb, b, ext2);
        let _ = mpn_ffi::mpn_add_n(&mut er[..n64], &ea[..n64], &eb[..n64]);
        // sum < 2^(32*ext), so u32 limbs [ext, ext2) of er are zero
        unpack_low(&mut c[..ext], &er[..n64]);
        normalized_len(&c[..ext])
    }

    /// Variable-length sub with the `lean::mpn_sub` surface: writes
    /// `max(a.len(), b.len())` u32 limbs of `a - b` (mod `2^(32 max)`)
    /// to `c` and returns the borrow (0 or 1). `a < b` wraps, making the
    /// extension limb of the kernel result non-zero, which is how the
    /// borrow is recovered.
    ///
    /// Panics if `c` is shorter than `max` limbs or the extended length
    /// exceeds [`MAX_LIMBS_U32`].
    pub fn sub_vl_u32(a: &[u32], b: &[u32], c: &mut [u32]) -> u32 {
        let len = a.len().max(b.len());
        let ext = len + 1;
        let ext2 = ext + (ext & 1);
        assert!(ext2 <= MAX_LIMBS_U32);
        assert!(c.len() >= len);
        let n64 = ext2 / 2;
        let mut ea = [0u64; MAX64];
        let mut eb = [0u64; MAX64];
        let mut er = [0u64; MAX64];
        pack_ext(&mut ea, a, ext2);
        pack_ext(&mut eb, b, ext2);
        let _ = mpn_ffi::mpn_sub_n(&mut er[..n64], &ea[..n64], &eb[..n64]);
        unpack_low(&mut c[..len], &er[..n64]);
        if u32_limb(&er[..n64], len) != 0 {
            1
        } else {
            0
        }
    }

    /// Variable-length u64 add (same surface as [`add_vl_u32`], u64
    /// digits): writes `max + 1` limbs to `c`, returns the normalized
    /// length.
    pub fn add_vl_u64(a: &[u64], b: &[u64], c: &mut [u64]) -> usize {
        let len = a.len().max(b.len());
        let ext = len + 1;
        assert!(ext <= MAX64);
        assert!(c.len() >= ext);
        let mut ea = [0u64; MAX64];
        let mut eb = [0u64; MAX64];
        ea[..a.len()].copy_from_slice(a);
        eb[..b.len()].copy_from_slice(b);
        let _ = mpn_ffi::mpn_add_n(&mut c[..ext], &ea[..ext], &eb[..ext]);
        let mut os = ext;
        while os > 1 && c[os - 1] == 0 {
            os -= 1;
        }
        os
    }

    /// Variable-length u64 sub (same surface as [`sub_vl_u32`], u64
    /// digits): writes `max` limbs to `c`, returns the borrow.
    pub fn sub_vl_u64(a: &[u64], b: &[u64], c: &mut [u64]) -> u64 {
        let len = a.len().max(b.len());
        let ext = len + 1;
        assert!(ext <= MAX64);
        assert!(c.len() >= len);
        let mut ea = [0u64; MAX64];
        let mut eb = [0u64; MAX64];
        let mut er = [0u64; MAX64];
        ea[..a.len()].copy_from_slice(a);
        eb[..b.len()].copy_from_slice(b);
        let _ = mpn_ffi::mpn_sub_n(&mut er[..ext], &ea[..ext], &eb[..ext]);
        c[..len].copy_from_slice(&er[..len]);
        if er[len] != 0 {
            1
        } else {
            0
        }
    }

    // ---------------------------------------------------------------------
    // u32-surface operations over the runtime-trip and bitwise kernels.
    //
    // Each function packs its u32 operands into u64 limbs held in a
    // caller-provided `scratch` slice (a 2p-limb u32 array is the p-limb u64
    // array over the same bytes; an odd length is padded with a zero u32),
    // calls one kernel, and unpacks the low u32 limbs of the result. The
    // `*_scratch_len` functions give the scratch length each operation
    // requires; a shorter slice panics. No operation has a length bound.
    // ---------------------------------------------------------------------

    /// Number of u64 limbs holding `n32` u32 limbs.
    const fn pairs(n32: usize) -> usize {
        n32 / 2 + n32 % 2
    }

    /// Scratch length (u64 limbs) of [`and_n_u32`], [`ior_n_u32`] and
    /// [`xor_n_u32`] over `n` u32 limbs.
    pub const fn bitop_scratch_len(n: usize) -> usize {
        3 * pairs(n)
    }

    /// Step: one equal-length u64 bitwise kernel over packed operands.
    fn bitop_u32(
        a: &[u32],
        b: &[u32],
        c: &mut [u32],
        scratch: &mut [u64],
        kernel: fn(&mut [u64], &[u64], &[u64]),
    ) {
        let n = a.len();
        assert_eq!(b.len(), n);
        assert!(c.len() >= n);
        if n == 0 {
            return;
        }
        let p = pairs(n);
        let (ua, rest) = scratch.split_at_mut(p);
        let (ub, rest) = rest.split_at_mut(p);
        let r = &mut rest[..p];
        pack_ext(ua, a, 2 * p);
        pack_ext(ub, b, 2 * p);
        kernel(r, ua, ub);
        unpack_low(&mut c[..n], r);
    }

    /// `c[i] = a[i] & b[i]` for `i < n`, `n = a.len() = b.len()`.
    /// Panics if `b.len() != n`, `c.len() < n` or
    /// `scratch.len() < bitop_scratch_len(n)`.
    pub fn and_n_u32(a: &[u32], b: &[u32], c: &mut [u32], scratch: &mut [u64]) {
        bitop_u32(a, b, c, scratch, mpn_ffi::mpn_and_n)
    }

    /// `c[i] = a[i] | b[i]`; contract as [`and_n_u32`].
    pub fn ior_n_u32(a: &[u32], b: &[u32], c: &mut [u32], scratch: &mut [u64]) {
        bitop_u32(a, b, c, scratch, mpn_ffi::mpn_ior_n)
    }

    /// `c[i] = a[i] ^ b[i]`; contract as [`and_n_u32`].
    pub fn xor_n_u32(a: &[u32], b: &[u32], c: &mut [u32], scratch: &mut [u64]) {
        bitop_u32(a, b, c, scratch, mpn_ffi::mpn_xor_n)
    }

    /// Scratch length (u64 limbs) of [`cmp_u32`] for operands of `la` and
    /// `lb` u32 limbs.
    pub const fn cmp_scratch_len(la: usize, lb: usize) -> usize {
        let m = if la < lb { la } else { lb };
        2 * pairs(m)
    }

    /// Whether `x` is a normalized `mpz` digit array: at least one limb, and
    /// a nonzero top limb unless `x` is the single limb `0`.
    fn is_normalized(x: &[u32]) -> bool {
        match x.last() {
            None => false,
            Some(&top) => x.len() == 1 || top != 0,
        }
    }

    /// Three-way comparison of the values of `a` and `b` (little-endian):
    /// `1`, `0` or `-1`, as the Lean runtime's `mpn_compare`.
    ///
    /// Both operands must be normalized (`is_normalized`), the invariant the
    /// runtime's `mpz` keeps for every digit array it passes; a violation
    /// panics. Normalized operands of different lengths are ordered by
    /// length, and equal lengths are compared by the constant-time kernel.
    pub fn cmp_u32(a: &[u32], b: &[u32], scratch: &mut [u64]) -> i32 {
        assert!(is_normalized(a) && is_normalized(b));
        if a.len() != b.len() {
            return if a.len() > b.len() { 1 } else { -1 };
        }
        let m = a.len();
        let p = pairs(m);
        let (ua, rest) = scratch.split_at_mut(p);
        let ub = &mut rest[..p];
        pack_ext(ua, &a[..m], 2 * p);
        pack_ext(ub, &b[..m], 2 * p);
        crate::mpn_cmp_n(ua, ub)
    }

    /// Scratch length (u64 limbs) of [`lshift_u32`] and [`rshift_u32`] for
    /// an operand of `la` u32 limbs.
    pub const fn shift_scratch_len(la: usize) -> usize {
        2 * pairs(la) + 1
    }

    /// Output length of [`lshift_u32`]: `la + k / 32 + 1`.
    ///
    /// Panics if the length does not fit in `usize`.
    pub fn lshift_out_len(la: usize, k: u64) -> usize {
        let w = usize::try_from(k / 32).expect("shift count too large");
        la.checked_add(w)
            .and_then(|x| x.checked_add(1))
            .expect("shift count too large")
    }

    /// Output length of [`rshift_u32`]: `la - k / 32`, or `0` when
    /// `k / 32 >= la`.
    pub fn rshift_out_len(la: usize, k: u64) -> usize {
        let w = k / 32;
        if w >= la as u64 {
            0
        } else {
            la - w as usize
        }
    }

    /// Left shift by `k` bits: writes `value(a) * 2^k` to
    /// `c[0..lshift_out_len(a.len(), k))`. The whole-limb part `k / 32` is
    /// a zero fill, the sub-limb part `k % 32` is the shift kernel with
    /// `sh = k % 32` (a copy when `k % 32 = 0`). The top output limb holds
    /// the bits shifted out of `a`'s top limb and may be zero; the output is
    /// not normalized.
    ///
    /// Panics if `c` is shorter than the output length or `scratch` shorter
    /// than [`shift_scratch_len`]`(a.len())`.
    pub fn lshift_u32(a: &[u32], k: u64, c: &mut [u32], scratch: &mut [u64]) {
        let la = a.len();
        let out = lshift_out_len(la, k);
        assert!(c.len() >= out);
        let w = out - la - 1;
        let bits = (k % 32) as u32;
        c[..w].fill(0);
        let dst = &mut c[w..out];
        if bits == 0 || la == 0 {
            dst[..la].copy_from_slice(a);
            dst[la] = 0;
            return;
        }
        let p = pairs(la);
        let (u, rest) = scratch.split_at_mut(p);
        let r = &mut rest[..p + 1];
        pack_ext(u, a, 2 * p);
        r[0] = 0;
        crate::mpn_shift_n(r, u, bits);
        // value(a) * 2^bits < 2^(32 (la + 1)), so the u32 limbs of r above
        // index la are zero.
        unpack_low(dst, r);
    }

    /// Right shift by `k` bits: writes `floor(value(a) / 2^k)` to
    /// `c[0..rshift_out_len(a.len(), k))`. The whole-limb part `k / 32`
    /// drops low limbs, the sub-limb part `k % 32` is the shift kernel with
    /// `sh = 64 - k % 32` (a copy when `k % 32 = 0`). The output is not
    /// normalized.
    ///
    /// Panics if `c` is shorter than the output length or `scratch` shorter
    /// than [`shift_scratch_len`]`(a.len())`.
    pub fn rshift_u32(a: &[u32], k: u64, c: &mut [u32], scratch: &mut [u64]) {
        let m = rshift_out_len(a.len(), k);
        assert!(c.len() >= m);
        if m == 0 {
            return;
        }
        let src = &a[a.len() - m..];
        let dst = &mut c[..m];
        let bits = (k % 32) as u32;
        if bits == 0 {
            dst.copy_from_slice(src);
            return;
        }
        let p = pairs(m);
        let (u, rest) = scratch.split_at_mut(p);
        let r = &mut rest[..p + 1];
        pack_ext(u, src, 2 * p);
        r[0] = 0;
        crate::mpn_shift_n(r, u, 64 - bits);
        // r[1..=p] holds floor(value(src) / 2^bits); r[0] the dropped bits.
        unpack_low(dst, &r[1..]);
    }

    /// Scratch length (u64 limbs) of [`mul_u32`] for operands of `la` and
    /// `lb` u32 limbs.
    pub const fn mul_scratch_len(la: usize, lb: usize) -> usize {
        2 * (pairs(la) + pairs(lb)) + 1
    }

    /// Full product: writes `value(a) * value(b)` to
    /// `c[0..a.len() + b.len())`, unnormalized, as the Lean runtime's
    /// `mpn_mul`. If either operand is empty the output is all zero. `a` and
    /// `b` may be the same slice.
    ///
    /// Panics if `c` is shorter than `a.len() + b.len()` or `scratch`
    /// shorter than [`mul_scratch_len`].
    pub fn mul_u32(a: &[u32], b: &[u32], c: &mut [u32], scratch: &mut [u64]) {
        let (la, lb) = (a.len(), b.len());
        let out = la.checked_add(lb).expect("operand lengths overflow");
        assert!(c.len() >= out);
        if la == 0 || lb == 0 {
            c[..out].fill(0);
            return;
        }
        let (pa, pb) = (pairs(la), pairs(lb));
        let (ua, rest) = scratch.split_at_mut(pa);
        let (ub, rest) = rest.split_at_mut(pb);
        let r = &mut rest[..pa + pb + 1];
        pack_ext(ua, a, 2 * pa);
        pack_ext(ub, b, 2 * pb);
        crate::mpn_mul_basecase(r, ua, ub);
        // the product is below 2^(32 (la + lb)), so higher u32 limbs are zero
        unpack_low(&mut c[..out], r);
    }
}

#[allow(unsafe_code)]
pub mod cabi {
    //! `#[no_mangle] extern "C"` entry points for the Lean 4 runtime
    //! (`src/runtime/mpn.cpp` of the CatCrypt lean4 fork) and other C
    //! callers. Built as a `staticlib`, this crate provides these symbols
    //! plus the raw `mpn_*_loop_owned` kernels from `obj/`.
    //!
    //! The u32 entries keep the fork's digit width
    //! (`lean::mpn_digit = unsigned int`): on little-endian x86-64 the
    //! 2k-limb u32 array and the k-limb u64 array over the same bytes
    //! denote the same natural number, so the u64 kernel computes the low
    //! `2*(n/2)` u32 limbs directly on the caller's buffers (the kernels
    //! load/store with `movq`, which has no alignment requirement), and an
    //! odd top limb is finished by a scalar step seeded with the kernel's
    //! carry/borrow return.

    use crate::mpn_ffi;

    /// Equal-length u32 add mod `2^(32 n)`: `op[0..n] = ap + bp`, carry
    /// beyond limb `n-1` dropped (callers capture it by pre-extending, as
    /// `lean::mpn_add` does).
    ///
    /// # Safety
    /// `op`, `ap`, `bp` must be valid for `n` u32 limbs, `op` writable,
    /// and `op` must not overlap `ap` or `bp`.
    #[no_mangle]
    pub unsafe extern "C" fn mpn_add_n_oc_32(
        op: *mut u32,
        ap: *const u32,
        bp: *const u32,
        n: u64,
    ) {
        let n32 = n as usize;
        let pairs = (n32 / 2) as u64;
        let cy = mpn_ffi::mpn_add_n_loop_owned(
            op as *mut u64,
            ap as *const u64,
            bp as *const u64,
            pairs,
        );
        if n32 % 2 == 1 {
            let i = n32 - 1;
            let s = (*ap.add(i) as u64) + (*bp.add(i) as u64) + cy;
            *op.add(i) = s as u32;
        }
    }

    /// Equal-length u32 sub mod `2^(32 n)`: `op[0..n] = ap - bp`, borrow
    /// beyond limb `n-1` dropped (callers recover it by pre-extending, as
    /// `lean::mpn_sub` does).
    ///
    /// # Safety
    /// Same contract as [`mpn_add_n_oc_32`].
    #[no_mangle]
    pub unsafe extern "C" fn mpn_sub_n_oc_32(
        op: *mut u32,
        ap: *const u32,
        bp: *const u32,
        n: u64,
    ) {
        let n32 = n as usize;
        let pairs = (n32 / 2) as u64;
        let bw = mpn_ffi::mpn_sub_n_loop_owned(
            op as *mut u64,
            ap as *const u64,
            bp as *const u64,
            pairs,
        );
        if n32 % 2 == 1 {
            let i = n32 - 1;
            let d = (*ap.add(i) as u64)
                .wrapping_sub(*bp.add(i) as u64)
                .wrapping_sub(bw);
            *op.add(i) = d as u32;
        }
    }

    /// Equal-length u64 add mod `2^(64 n)`; returns the carry limb.
    ///
    /// # Safety
    /// `rp`, `ap`, `bp` must be valid for `n` u64 limbs, `rp` writable,
    /// and `rp` must not overlap `ap` or `bp`.
    #[no_mangle]
    pub unsafe extern "C" fn mpn_add_n_oc_64(
        rp: *mut u64,
        ap: *const u64,
        bp: *const u64,
        n: u64,
    ) -> u64 {
        mpn_ffi::mpn_add_n_loop_owned(rp, ap, bp, n)
    }

    /// Equal-length u64 sub mod `2^(64 n)`; returns the borrow limb.
    ///
    /// # Safety
    /// Same contract as [`mpn_add_n_oc_64`].
    #[no_mangle]
    pub unsafe extern "C" fn mpn_sub_n_oc_64(
        rp: *mut u64,
        ap: *const u64,
        bp: *const u64,
        n: u64,
    ) -> u64 {
        mpn_ffi::mpn_sub_n_loop_owned(rp, ap, bp, n)
    }

    /// Limbwise u64 AND.
    ///
    /// # Safety
    /// Same contract as [`mpn_add_n_oc_64`].
    #[no_mangle]
    pub unsafe extern "C" fn mpn_and_n_oc_64(
        rp: *mut u64,
        ap: *const u64,
        bp: *const u64,
        n: u64,
    ) {
        let _ = mpn_ffi::mpn_and_n_loop_owned(rp, ap, bp, n);
    }

    /// Limbwise u64 OR.
    ///
    /// # Safety
    /// Same contract as [`mpn_add_n_oc_64`].
    #[no_mangle]
    pub unsafe extern "C" fn mpn_ior_n_oc_64(
        rp: *mut u64,
        ap: *const u64,
        bp: *const u64,
        n: u64,
    ) {
        let _ = mpn_ffi::mpn_ior_n_loop_owned(rp, ap, bp, n);
    }

    /// Limbwise u64 XOR.
    ///
    /// # Safety
    /// Same contract as [`mpn_add_n_oc_64`].
    #[no_mangle]
    pub unsafe extern "C" fn mpn_xor_n_oc_64(
        rp: *mut u64,
        ap: *const u64,
        bp: *const u64,
        n: u64,
    ) {
        let _ = mpn_ffi::mpn_xor_n_loop_owned(rp, ap, bp, n);
    }

    // ---------------------------------------------------------------------
    // u32 entries over the `seam` operations. Each entry forms slices from
    // the caller's pointers, obtains the seam's u64 scratch (on the stack up
    // to `STACK_SCRATCH` limbs, from libc `malloc` above that), and calls one
    // safe seam function. Output buffers are zeroed through the raw pointer
    // before a slice is formed over them, so they may be uninitialized on
    // entry. There is no length bound.
    //
    // Common caller obligations: every pointer is valid for the stated
    // number of u32 limbs (a null or dangling pointer is allowed only for a
    // zero length); the output does not overlap any input; inputs may
    // overlap each other.
    // ---------------------------------------------------------------------

    use crate::seam;
    use core::mem::MaybeUninit;

    extern "C" {
        fn malloc(size: usize) -> *mut u8;
        fn free(ptr: *mut u8);
        fn abort() -> !;
    }

    /// Scratch limbs held on the stack before falling back to `malloc`.
    const STACK_SCRATCH: usize = 512;

    /// Run `f` on a zeroed scratch slice of `n` u64 limbs.
    fn with_scratch<R>(n: usize, f: impl FnOnce(&mut [u64]) -> R) -> R {
        if n <= STACK_SCRATCH {
            let mut buf = [MaybeUninit::<u64>::uninit(); STACK_SCRATCH];
            for w in &mut buf[..n] {
                w.write(0);
            }
            // SAFETY: the first n elements were initialized just above.
            let s = unsafe { core::slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut u64, n) };
            f(s)
        } else {
            let bytes = match n.checked_mul(core::mem::size_of::<u64>()) {
                Some(b) => b,
                // SAFETY: abort has no preconditions.
                None => unsafe { abort() },
            };
            // SAFETY: malloc has no preconditions; a null result aborts.
            let p = unsafe { malloc(bytes) } as *mut u64;
            if p.is_null() {
                // SAFETY: as above.
                unsafe { abort() }
            }
            // SAFETY: p is a fresh allocation of n u64 limbs (malloc's result
            // is aligned for any fundamental type); it is zeroed before the
            // slice is formed and freed after its last use.
            let r = unsafe {
                core::ptr::write_bytes(p, 0, n);
                f(core::slice::from_raw_parts_mut(p, n))
            };
            // SAFETY: p came from malloc and is not used afterwards.
            unsafe { free(p as *mut u8) };
            r
        }
    }

    /// Shared slice over `n` u32 limbs at `p` (empty when `n == 0`).
    ///
    /// # Safety
    /// `p` valid for reads of `n` u32 limbs, not written while the slice
    /// lives.
    unsafe fn in_slice<'a>(p: *const u32, n: usize) -> &'a [u32] {
        if n == 0 {
            &[]
        } else {
            core::slice::from_raw_parts(p, n)
        }
    }

    /// Zero `n` u32 limbs at `p` and return the exclusive slice over them.
    ///
    /// # Safety
    /// `p` valid for writes of `n` u32 limbs, aligned, not aliased while the
    /// slice lives.
    unsafe fn out_slice<'a>(p: *mut u32, n: usize) -> &'a mut [u32] {
        if n == 0 {
            &mut []
        } else {
            core::ptr::write_bytes(p, 0, n);
            core::slice::from_raw_parts_mut(p, n)
        }
    }

    fn usize_of(n: u64) -> usize {
        match usize::try_from(n) {
            Ok(v) => v,
            // SAFETY: abort has no preconditions.
            Err(_) => unsafe { abort() },
        }
    }

    /// `op[i] = ap[i] & bp[i]` for `i < n` (u32 limbs).
    ///
    /// # Safety
    /// Common caller obligations above; `op`, `ap`, `bp` hold `n` limbs.
    #[no_mangle]
    pub unsafe extern "C" fn mpn_and_n_oc_32(op: *mut u32, ap: *const u32, bp: *const u32, n: u64) {
        let n = usize_of(n);
        let (a, b, c) = (in_slice(ap, n), in_slice(bp, n), out_slice(op, n));
        with_scratch(seam::bitop_scratch_len(n), |s| seam::and_n_u32(a, b, c, s))
    }

    /// `op[i] = ap[i] | bp[i]` for `i < n` (u32 limbs).
    ///
    /// # Safety
    /// As [`mpn_and_n_oc_32`].
    #[no_mangle]
    pub unsafe extern "C" fn mpn_ior_n_oc_32(op: *mut u32, ap: *const u32, bp: *const u32, n: u64) {
        let n = usize_of(n);
        let (a, b, c) = (in_slice(ap, n), in_slice(bp, n), out_slice(op, n));
        with_scratch(seam::bitop_scratch_len(n), |s| seam::ior_n_u32(a, b, c, s))
    }

    /// `op[i] = ap[i] ^ bp[i]` for `i < n` (u32 limbs).
    ///
    /// # Safety
    /// As [`mpn_and_n_oc_32`].
    #[no_mangle]
    pub unsafe extern "C" fn mpn_xor_n_oc_32(op: *mut u32, ap: *const u32, bp: *const u32, n: u64) {
        let n = usize_of(n);
        let (a, b, c) = (in_slice(ap, n), in_slice(bp, n), out_slice(op, n));
        with_scratch(seam::bitop_scratch_len(n), |s| seam::xor_n_u32(a, b, c, s))
    }

    /// Three-way comparison of `ap[0..an)` and `bp[0..bn)` as values:
    /// returns `1`, `0` or `-1` (the `lean::mpn_compare` contract).
    ///
    /// # Safety
    /// Common caller obligations above.
    #[no_mangle]
    pub unsafe extern "C" fn mpn_cmp_oc_32(ap: *const u32, an: u64, bp: *const u32, bn: u64) -> i32 {
        let (an, bn) = (usize_of(an), usize_of(bn));
        let (a, b) = (in_slice(ap, an), in_slice(bp, bn));
        with_scratch(seam::cmp_scratch_len(an, bn), |s| seam::cmp_u32(a, b, s))
    }

    /// Writes `ap[0..an) * 2^k` to `rp[0 .. an + k/32 + 1)`, unnormalized.
    ///
    /// # Safety
    /// Common caller obligations above; `rp` holds `an + k/32 + 1` limbs.
    #[no_mangle]
    pub unsafe extern "C" fn mpn_lshift_oc_32(rp: *mut u32, ap: *const u32, an: u64, k: u64) {
        let an = usize_of(an);
        let out = seam::lshift_out_len(an, k);
        let (a, c) = (in_slice(ap, an), out_slice(rp, out));
        with_scratch(seam::shift_scratch_len(an), |s| seam::lshift_u32(a, k, c, s))
    }

    /// Writes `floor(ap[0..an) / 2^k)` to `rp[0 .. an - k/32)` (nothing
    /// when `k/32 >= an`), unnormalized.
    ///
    /// # Safety
    /// Common caller obligations above; `rp` holds `an - k/32` limbs when
    /// that is positive.
    #[no_mangle]
    pub unsafe extern "C" fn mpn_rshift_oc_32(rp: *mut u32, ap: *const u32, an: u64, k: u64) {
        let an = usize_of(an);
        let out = seam::rshift_out_len(an, k);
        let (a, c) = (in_slice(ap, an), out_slice(rp, out));
        with_scratch(seam::shift_scratch_len(out), |s| seam::rshift_u32(a, k, c, s))
    }

    /// Writes `ap[0..an) * bp[0..bn)` to `rp[0 .. an + bn)`, unnormalized
    /// (the `lean::mpn_mul` contract).
    ///
    /// # Safety
    /// Common caller obligations above; `rp` holds `an + bn` limbs.
    #[no_mangle]
    pub unsafe extern "C" fn mpn_mul_oc_32(
        rp: *mut u32,
        ap: *const u32,
        an: u64,
        bp: *const u32,
        bn: u64,
    ) {
        let (an, bn) = (usize_of(an), usize_of(bn));
        let out = match an.checked_add(bn) {
            Some(v) => v,
            // SAFETY: abort has no preconditions.
            None => abort(),
        };
        let (a, b, c) = (in_slice(ap, an), in_slice(bp, bn), out_slice(rp, out));
        with_scratch(seam::mul_scratch_len(an, bn), |s| seam::mul_u32(a, b, c, s))
    }
}
