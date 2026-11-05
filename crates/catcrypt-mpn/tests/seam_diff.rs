//! Differential tests of the u32-surface operations (bitwise, compare,
//! shifts, multiply) against schoolbook references over `Vec<u32>`.
//!
//! Every operation is driven through its C-ABI entry (`cabi::mpn_*_oc_32`),
//! which is the path the Lean runtime calls and which exercises the seam
//! function and its scratch sizing. Operand lengths are drawn from 0..=300
//! u32 limbs (both parities), with limb patterns random, all-zero, all-ones
//! and sparse; a smaller sweep uses lengths up to 6000 limbs so that the
//! `malloc` scratch path and operands above 4096 limbs are covered. Output
//! buffers carry sentinel limbs past the contracted output length, and the
//! tests check that those limbs are left untouched.

use catcrypt_mpn::cabi::{
    mpn_and_n_oc_32, mpn_cmp_oc_32, mpn_ior_n_oc_32, mpn_lshift_oc_32, mpn_mul_oc_32,
    mpn_rshift_oc_32, mpn_xor_n_oc_32,
};
use catcrypt_mpn::seam;
use std::cmp::Ordering;

const SENTINEL: u32 = 0xA5A5_5A5A;
const PAD: usize = 3;

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
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    /// A limb vector of length `n` in one of four patterns.
    fn limbs(&mut self, n: usize) -> Vec<u32> {
        match self.below(8) {
            0 => vec![0; n],
            1 => vec![u32::MAX; n],
            2 => (0..n)
                .map(|_| if self.below(10) == 0 { self.next() as u32 } else { 0 })
                .collect(),
            3 => (0..n)
                .map(|_| if self.below(2) == 0 { u32::MAX } else { 0 })
                .collect(),
            _ => (0..n).map(|_| self.next() as u32).collect(),
        }
    }
    fn len(&mut self, max: usize) -> usize {
        self.below(max as u64 + 1) as usize
    }
    fn shift(&mut self) -> u64 {
        const FIXED: [u64; 8] = [0, 1, 31, 32, 33, 63, 64, 65];
        if self.below(2) == 0 {
            FIXED[self.below(8) as usize]
        } else {
            self.below(20001)
        }
    }
}

/// Output buffer of `n` garbage limbs followed by `PAD` sentinels.
fn out_buf(n: usize) -> Vec<u32> {
    let mut v = vec![0xDEAD_BEEF; n];
    v.extend_from_slice(&[SENTINEL; PAD]);
    v
}

fn check_pad(buf: &[u32], n: usize, what: &str) {
    assert_eq!(&buf[n..], &[SENTINEL; PAD], "{what}: wrote past the output length");
}

fn trimmed(a: &[u32]) -> &[u32] {
    let mut n = a.len();
    while n > 0 && a[n - 1] == 0 {
        n -= 1;
    }
    &a[..n]
}

/// The normalized `mpz` form of `a`: leading zero limbs removed, and the
/// single limb `0` for the value zero. `mpn_cmp_oc_32` requires it.
fn norm(a: &[u32]) -> Vec<u32> {
    let t = trimmed(a);
    if t.is_empty() { vec![0] } else { t.to_vec() }
}

fn ref_cmp(a: &[u32], b: &[u32]) -> i32 {
    let (a, b) = (trimmed(a), trimmed(b));
    let ord = a
        .len()
        .cmp(&b.len())
        .then_with(|| a.iter().rev().cmp(b.iter().rev()));
    match ord {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}

fn ref_lshift(a: &[u32], k: u64) -> Vec<u32> {
    let w = (k / 32) as usize;
    let bits = (k % 32) as u32;
    let mut out = vec![0u32; a.len() + w + 1];
    for (i, &x) in a.iter().enumerate() {
        let v = (x as u64) << bits;
        out[i + w] |= v as u32;
        out[i + w + 1] |= (v >> 32) as u32;
    }
    out
}

fn ref_rshift(a: &[u32], k: u64) -> Vec<u32> {
    let w = k / 32;
    if w >= a.len() as u64 {
        return Vec::new();
    }
    let w = w as usize;
    let bits = (k % 32) as u32;
    (0..a.len() - w)
        .map(|i| {
            let lo = a[i + w] as u64;
            let hi = a.get(i + w + 1).copied().unwrap_or(0) as u64;
            (((hi << 32) | lo) >> bits) as u32
        })
        .collect()
}

fn ref_mul(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = vec![0u32; a.len() + b.len()];
    for (j, &y) in b.iter().enumerate() {
        let mut k = 0u64;
        for (i, &x) in a.iter().enumerate() {
            let t = (x as u64) * (y as u64) + out[i + j] as u64 + k;
            out[i + j] = t as u32;
            k = t >> 32;
        }
        out[j + a.len()] = k as u32;
    }
    out
}

fn run_bitops(rng: &mut Rng, cases: usize, max_len: usize) -> usize {
    type Entry = unsafe extern "C" fn(*mut u32, *const u32, *const u32, u64);
    let ops: [(&str, Entry, fn(u32, u32) -> u32); 3] = [
        ("and", mpn_and_n_oc_32, |x, y| x & y),
        ("ior", mpn_ior_n_oc_32, |x, y| x | y),
        ("xor", mpn_xor_n_oc_32, |x, y| x ^ y),
    ];
    let mut count = 0;
    for _ in 0..cases {
        let n = rng.len(max_len);
        let a = rng.limbs(n);
        let b = if rng.below(8) == 0 { a.clone() } else { rng.limbs(n) };
        for (name, entry, f) in ops {
            let mut c = out_buf(n);
            // SAFETY: a, b hold n limbs; c holds n + PAD limbs, distinct.
            unsafe { entry(c.as_mut_ptr(), a.as_ptr(), b.as_ptr(), n as u64) };
            let want: Vec<u32> = a.iter().zip(&b).map(|(&x, &y)| f(x, y)).collect();
            assert_eq!(&c[..n], &want[..], "{name} n={n}");
            check_pad(&c, n, name);
            count += 1;
        }
    }
    count
}

fn run_cmp(rng: &mut Rng, cases: usize, max_len: usize) -> usize {
    for _ in 0..cases {
        let la = rng.len(max_len);
        let a = norm(&rng.limbs(la));
        let b = match rng.below(4) {
            // equal values
            0 => a.clone(),
            // equal except one limb, same length when that limb stays nonzero
            1 => {
                let mut b = a.clone();
                let i = rng.below(a.len() as u64) as usize;
                b[i] = rng.next() as u32;
                norm(&b)
            }
            _ => {
                let lb = rng.len(max_len);
                norm(&rng.limbs(lb))
            }
        };
        // SAFETY: a and b hold a.len() and b.len() limbs.
        let got = unsafe { mpn_cmp_oc_32(a.as_ptr(), a.len() as u64, b.as_ptr(), b.len() as u64) };
        assert_eq!(got, ref_cmp(&a, &b), "cmp la={} lb={}", a.len(), b.len());
    }
    cases
}

fn run_shifts(rng: &mut Rng, cases: usize, max_len: usize) -> usize {
    for _ in 0..cases {
        let la = rng.len(max_len);
        let a = rng.limbs(la);
        let k = rng.shift();

        let want = ref_lshift(&a, k);
        let n = seam::lshift_out_len(la, k);
        assert_eq!(n, want.len());
        let mut c = out_buf(n);
        // SAFETY: a holds la limbs; c holds n + PAD limbs, distinct.
        unsafe { mpn_lshift_oc_32(c.as_mut_ptr(), a.as_ptr(), la as u64, k) };
        assert_eq!(&c[..n], &want[..], "lshift la={la} k={k}");
        check_pad(&c, n, "lshift");

        let want = ref_rshift(&a, k);
        let n = seam::rshift_out_len(la, k);
        assert_eq!(n, want.len());
        let mut c = out_buf(n);
        // SAFETY: as above.
        unsafe { mpn_rshift_oc_32(c.as_mut_ptr(), a.as_ptr(), la as u64, k) };
        assert_eq!(&c[..n], &want[..], "rshift la={la} k={k}");
        check_pad(&c, n, "rshift");
    }
    2 * cases
}

fn run_mul(rng: &mut Rng, cases: usize, max_len: usize) -> usize {
    for _ in 0..cases {
        // bias towards short operands, where most runtime products are
        let la = if rng.below(2) == 0 { rng.len(8) } else { rng.len(max_len) };
        let lb = if rng.below(2) == 0 { rng.len(8) } else { rng.len(max_len) };
        let a = rng.limbs(la);
        let sq = rng.below(8) == 0;
        let b = if sq { a.clone() } else { rng.limbs(lb) };
        let n = la + b.len();
        let mut c = out_buf(n);
        // SAFETY: a, b hold la, b.len() limbs; c holds n + PAD limbs.
        unsafe { mpn_mul_oc_32(c.as_mut_ptr(), a.as_ptr(), la as u64, b.as_ptr(), b.len() as u64) };
        assert_eq!(&c[..n], &ref_mul(&a, &b)[..], "mul la={la} lb={}", b.len());
        check_pad(&c, n, "mul");
    }
    cases
}

#[test]
fn diff_bitops() {
    let mut rng = Rng(0x1234_5678_9abc_def1);
    let n = run_bitops(&mut rng, 20_000, 300);
    eprintln!("bitops: {n} cases");
}

#[test]
fn diff_cmp() {
    let mut rng = Rng(0x0fed_cba9_8765_4321);
    let n = run_cmp(&mut rng, 60_000, 300);
    eprintln!("cmp: {n} cases");
}

#[test]
fn diff_shifts() {
    let mut rng = Rng(0x5555_aaaa_3333_cccc);
    let n = run_shifts(&mut rng, 30_000, 300);
    eprintln!("shifts: {n} cases");
}

#[test]
fn diff_mul() {
    let mut rng = Rng(0x7777_1111_9999_2222);
    let n = run_mul(&mut rng, 30_000, 300);
    eprintln!("mul: {n} cases");
}

/// Operands up to 6000 limbs: the heap scratch path and lengths above the
/// former 4096-limb stack bound.
#[test]
fn diff_large() {
    let mut rng = Rng(0xabcd_ef01_2345_6789);
    let mut n = 0;
    n += run_bitops(&mut rng, 40, 6000);
    n += run_cmp(&mut rng, 200, 6000);
    n += run_shifts(&mut rng, 200, 6000);
    n += run_mul(&mut rng, 12, 6000);
    eprintln!("large: {n} cases");
}

/// Exhaustive small cases: every length pair up to 6 limbs, every shift
/// count 0..=200, limbs drawn from {0, 1, 2^31, 2^32 - 1}.
#[test]
fn edge_small() {
    let vals = [0u32, 1, 0x8000_0000, u32::MAX];
    let mut rng = Rng(0x2468_ace0_1357_9bdf);
    let mut count = 0;
    for la in 0..=6usize {
        for _ in 0..40 {
            let a: Vec<u32> = (0..la).map(|_| vals[rng.below(4) as usize]).collect();
            for k in 0..=200u64 {
                let mut c = out_buf(la + (k / 32) as usize + 1);
                unsafe { mpn_lshift_oc_32(c.as_mut_ptr(), a.as_ptr(), la as u64, k) };
                let want = ref_lshift(&a, k);
                assert_eq!(&c[..want.len()], &want[..], "lshift {a:?} k={k}");
                check_pad(&c, want.len(), "lshift");
                let want = ref_rshift(&a, k);
                let mut c = out_buf(want.len());
                unsafe { mpn_rshift_oc_32(c.as_mut_ptr(), a.as_ptr(), la as u64, k) };
                assert_eq!(&c[..want.len()], &want[..], "rshift {a:?} k={k}");
                check_pad(&c, want.len(), "rshift");
                count += 2;
            }
            for lb in 0..=6usize {
                let b: Vec<u32> = (0..lb).map(|_| vals[rng.below(4) as usize]).collect();
                let mut c = out_buf(la + lb);
                unsafe { mpn_mul_oc_32(c.as_mut_ptr(), a.as_ptr(), la as u64, b.as_ptr(), lb as u64) };
                assert_eq!(&c[..la + lb], &ref_mul(&a, &b)[..], "mul {a:?} {b:?}");
                check_pad(&c, la + lb, "mul");
                let (na, nb) = (norm(&a), norm(&b));
                let got = unsafe {
                    mpn_cmp_oc_32(na.as_ptr(), na.len() as u64, nb.as_ptr(), nb.len() as u64)
                };
                assert_eq!(got, ref_cmp(&a, &b), "cmp {a:?} {b:?}");
                count += 2;
            }
        }
    }
    // Null pointers with zero lengths are accepted.
    unsafe {
        mpn_mul_oc_32(std::ptr::null_mut(), std::ptr::null(), 0, std::ptr::null(), 0);
        mpn_and_n_oc_32(std::ptr::null_mut(), std::ptr::null(), std::ptr::null(), 0);
        mpn_rshift_oc_32(std::ptr::null_mut(), std::ptr::null(), 0, 5);
    }
    eprintln!("edge: {count} cases");
}

/// The seam functions reject a short scratch slice and a short output.
#[test]
#[should_panic]
fn seam_short_scratch_panics() {
    let a = [1u32, 2, 3];
    let mut c = [0u32; 6];
    let mut s = vec![0u64; seam::mul_scratch_len(3, 3) - 1];
    seam::mul_u32(&a, &a, &mut c, &mut s);
}

#[test]
#[should_panic]
fn seam_short_output_panics() {
    let a = [1u32, 2, 3];
    let mut c = [0u32; 4];
    let mut s = vec![0u64; seam::shift_scratch_len(3)];
    seam::lshift_u32(&a, 40, &mut c, &mut s);
}

/// The kernel wrappers: the shift funnel with a nonzero spill-in, and the
/// out-of-range shift count.
#[test]
fn kernel_shift_spill_in() {
    let up = [u64::MAX, 0x0123_4567_89ab_cdef];
    let mut rp = [5u64, 0, 0];
    catcrypt_mpn::mpn_shift_n(&mut rp, &up, 4);
    // value(up) * 16 + 5
    let v = ((up[1] as u128) << 64 | up[0] as u128) * 16 + 5;
    assert_eq!(rp[0], v as u64);
    assert_eq!(rp[1], (v >> 64) as u64);
    assert_eq!(rp[2], up[1] >> 60);
}

#[test]
#[should_panic]
fn kernel_shift_rejects_64() {
    let up = [1u64];
    let mut rp = [0u64; 2];
    catcrypt_mpn::mpn_shift_n(&mut rp, &up, 64);
}

/// The compare rejects operands that are not normalized: a leading zero limb
/// or an empty array.
#[test]
#[should_panic]
fn cmp_rejects_leading_zero() {
    let mut s = vec![0u64; seam::cmp_scratch_len(2, 1)];
    seam::cmp_u32(&[5, 0], &[5], &mut s);
}

#[test]
#[should_panic]
fn cmp_rejects_empty() {
    let mut s = vec![0u64; seam::cmp_scratch_len(0, 1)];
    seam::cmp_u32(&[], &[0], &mut s);
}
