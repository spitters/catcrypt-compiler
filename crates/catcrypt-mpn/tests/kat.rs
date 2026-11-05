//! Known-answer and differential tests for the verified mpn kernels, the
//! variable-length seam, and the C-ABI entries.
//!
//! The equal-length wrappers are checked against fixed carry/borrow-chain
//! vectors and a deterministic differential sweep (xorshift64 inputs, sizes
//! 1..=40 limbs) against in-test schoolbook references. The seam functions
//! are checked for the `lean::mpn_add`/`mpn_sub` surface semantics
//! (normalized length, borrow recovery) on mixed-length inputs, and the u32
//! C-ABI entries are exercised over both parities of the limb count. The
//! same kernels are differential-tested against libgmp by
//! `bench/integration/Makefile.loop_owned` in the dev repository.

use catcrypt_mpn::seam::{add_vl_u32, add_vl_u64, sub_vl_u32, sub_vl_u64};
use catcrypt_mpn::{mpn_add_n, mpn_and_n, mpn_ior_n, mpn_sub_n, mpn_xor_n};

/// Deterministic xorshift64 stream for the differential sweeps.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn limbs64(&mut self, n: usize) -> Vec<u64> {
        (0..n).map(|_| self.next()).collect()
    }
    fn limbs32(&mut self, n: usize) -> Vec<u32> {
        (0..n).map(|_| self.next() as u32).collect()
    }
}

/// Schoolbook equal-length u64 add; returns (sum limbs, carry).
fn ref_add_u64(a: &[u64], b: &[u64]) -> (Vec<u64>, u64) {
    let mut cy = 0u64;
    let mut out = Vec::with_capacity(a.len());
    for (&x, &y) in a.iter().zip(b) {
        let s = (x as u128) + (y as u128) + (cy as u128);
        out.push(s as u64);
        cy = (s >> 64) as u64;
    }
    (out, cy)
}

/// Schoolbook equal-length u64 sub; returns (difference limbs, borrow).
fn ref_sub_u64(a: &[u64], b: &[u64]) -> (Vec<u64>, u64) {
    let mut bw = 0u64;
    let mut out = Vec::with_capacity(a.len());
    for (&x, &y) in a.iter().zip(b) {
        let d = (x as u128).wrapping_sub(y as u128).wrapping_sub(bw as u128);
        out.push(d as u64);
        bw = ((d >> 64) as u64) & 1;
    }
    (out, bw)
}

/// Schoolbook equal-length u32 add; returns (sum limbs, carry).
fn ref_add_u32(a: &[u32], b: &[u32]) -> (Vec<u32>, u32) {
    let mut cy = 0u64;
    let mut out = Vec::with_capacity(a.len());
    for (&x, &y) in a.iter().zip(b) {
        let s = (x as u64) + (y as u64) + cy;
        out.push(s as u32);
        cy = s >> 32;
    }
    (out, cy as u32)
}

/// Schoolbook equal-length u32 sub; returns (difference limbs, borrow).
fn ref_sub_u32(a: &[u32], b: &[u32]) -> (Vec<u32>, u32) {
    let mut bw = 0u64;
    let mut out = Vec::with_capacity(a.len());
    for (&x, &y) in a.iter().zip(b) {
        let d = (x as u64).wrapping_sub(y as u64).wrapping_sub(bw);
        out.push(d as u32);
        bw = (d >> 32) & 1;
    }
    (out, bw as u32)
}

/// Full-length carry chain: (2^256 - 1) + 1 = 2^256.
#[test]
fn add_carry_chain() {
    let a = [u64::MAX; 4];
    let b = [1u64, 0, 0, 0];
    let mut r = [0u64; 4];
    let cy = mpn_add_n(&mut r, &a, &b);
    assert_eq!(r, [0, 0, 0, 0]);
    assert_eq!(cy, 1);
}

/// Full-length borrow chain: 0 - 1 wraps to 2^128 - 1 with borrow 1.
#[test]
fn sub_borrow_chain() {
    let a = [0u64, 0];
    let b = [1u64, 0];
    let mut r = [0u64; 2];
    let bw = mpn_sub_n(&mut r, &a, &b);
    assert_eq!(r, [u64::MAX, u64::MAX]);
    assert_eq!(bw, 1);
}

/// Bitwise identities: x & x = x, x | 0 = x, x ^ x = 0.
#[test]
fn bitwise_identities() {
    let x = [0xdead_beef_0123_4567u64, 0x8899_aabb_ccdd_eeffu64, 5u64];
    let z = [0u64; 3];
    let mut r = [0u64; 3];
    mpn_and_n(&mut r, &x, &x);
    assert_eq!(r, x);
    mpn_ior_n(&mut r, &x, &z);
    assert_eq!(r, x);
    mpn_xor_n(&mut r, &x, &x);
    assert_eq!(r, z);
}

/// Differential sweep of the five equal-length wrappers against the
/// schoolbook references, sizes 1..=40 (both parities), 4 trials each.
#[test]
fn differential_equal_length() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for n in 1..=40usize {
        for _ in 0..4 {
            let a = rng.limbs64(n);
            let b = rng.limbs64(n);
            let mut r = vec![0u64; n];

            let cy = mpn_add_n(&mut r, &a, &b);
            let (want, want_cy) = ref_add_u64(&a, &b);
            assert_eq!((r.clone(), cy), (want, want_cy), "add n={n}");

            let bw = mpn_sub_n(&mut r, &a, &b);
            let (want, want_bw) = ref_sub_u64(&a, &b);
            assert_eq!((r.clone(), bw), (want, want_bw), "sub n={n}");

            mpn_and_n(&mut r, &a, &b);
            let want: Vec<u64> = a.iter().zip(&b).map(|(x, y)| x & y).collect();
            assert_eq!(r, want, "and n={n}");

            mpn_ior_n(&mut r, &a, &b);
            let want: Vec<u64> = a.iter().zip(&b).map(|(x, y)| x | y).collect();
            assert_eq!(r, want, "ior n={n}");

            mpn_xor_n(&mut r, &a, &b);
            let want: Vec<u64> = a.iter().zip(&b).map(|(x, y)| x ^ y).collect();
            assert_eq!(r, want, "xor n={n}");
        }
    }
}

/// Mismatched slice lengths must panic, not truncate.
#[test]
#[should_panic]
fn length_mismatch_panics() {
    let a = [1u64, 2];
    let b = [3u64];
    let mut r = [0u64; 2];
    let _ = mpn_add_n(&mut r, &a, &b);
}

/// `add_vl_u32` against the schoolbook reference over mixed lengths,
/// including the carry into the extension limb and the normalized length.
#[test]
fn seam_add_vl_u32() {
    let mut rng = Rng(0xc0ff_ee00_dead_10cc);
    for la in [1usize, 2, 3, 7, 8, 33] {
        for lb in [1usize, 2, 5, 8, 32, 33] {
            let a = rng.limbs32(la);
            let b = rng.limbs32(lb);
            let len = la.max(lb);
            let mut c = vec![0u32; len + 1];
            let os = add_vl_u32(&a, &b, &mut c);

            // reference: zero-extend both to len+1, schoolbook add
            let mut ea = a.clone();
            ea.resize(len + 1, 0);
            let mut eb = b.clone();
            eb.resize(len + 1, 0);
            let (want, _) = ref_add_u32(&ea, &eb);
            assert_eq!(c, want, "la={la} lb={lb}");
            let mut want_os = len + 1;
            while want_os > 1 && want[want_os - 1] == 0 {
                want_os -= 1;
            }
            assert_eq!(os, want_os, "normalized length la={la} lb={lb}");
        }
    }
    // 1 + (2^32 - 1): the carry must land in the extension limb.
    let mut c = vec![0u32; 2];
    let os = add_vl_u32(&[1], &[u32::MAX], &mut c);
    assert_eq!((c, os), (vec![0, 1], 2));
}

/// `sub_vl_u32` against the schoolbook reference, both borrow polarities.
#[test]
fn seam_sub_vl_u32() {
    let mut rng = Rng(0x0123_4567_89ab_cdef);
    for la in [1usize, 2, 3, 8, 33] {
        for lb in [1usize, 2, 7, 8, 33] {
            let a = rng.limbs32(la);
            let b = rng.limbs32(lb);
            let len = la.max(lb);
            let mut c = vec![0u32; len];
            let bw = sub_vl_u32(&a, &b, &mut c);

            let mut ea = a.clone();
            ea.resize(len, 0);
            let mut eb = b.clone();
            eb.resize(len, 0);
            let (want, want_bw) = ref_sub_u32(&ea, &eb);
            assert_eq!((c, bw), (want, want_bw), "la={la} lb={lb}");
        }
    }
    // 1 - 2 wraps with borrow.
    let mut c = vec![0u32; 1];
    let bw = sub_vl_u32(&[1], &[2], &mut c);
    assert_eq!((c, bw), (vec![u32::MAX], 1));
}

/// The u64 seam pair on mixed lengths.
#[test]
fn seam_vl_u64() {
    let a = [u64::MAX, u64::MAX];
    let b = [1u64];
    let mut c = [0u64; 3];
    let os = add_vl_u64(&a, &b, &mut c);
    assert_eq!((c, os), ([0, 0, 1], 3));

    let mut d = [0u64; 2];
    let bw = sub_vl_u64(&b, &a, &mut d);
    assert_eq!((d, bw), ([2, 0], 1));
}

/// The u32 C-ABI entries over both limb-count parities (the odd case takes
/// the scalar-tail path), against the schoolbook reference.
#[test]
fn cabi_u32_entries() {
    use catcrypt_mpn::cabi::{mpn_add_n_oc_32, mpn_sub_n_oc_32};
    let mut rng = Rng(0xfeed_face_cafe_beef);
    for n in 1..=17usize {
        let a = rng.limbs32(n);
        let b = rng.limbs32(n);
        let mut r = vec![0u32; n];
        // SAFETY: distinct buffers of n u32 limbs each.
        unsafe {
            mpn_add_n_oc_32(r.as_mut_ptr(), a.as_ptr(), b.as_ptr(), n as u64);
        }
        let (want, _) = ref_add_u32(&a, &b);
        assert_eq!(r, want, "oc32 add n={n}");
        // SAFETY: as above.
        unsafe {
            mpn_sub_n_oc_32(r.as_mut_ptr(), a.as_ptr(), b.as_ptr(), n as u64);
        }
        let (want, _) = ref_sub_u32(&a, &b);
        assert_eq!(r, want, "oc32 sub n={n}");
    }
}
