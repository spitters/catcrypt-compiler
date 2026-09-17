//! A fixed-base comb for the generator over `p384_montjmixadd`.
//!
//! `k * G` with no doublings at all: every multiple the pass needs is in a
//! table, so the seventy-seven window steps are seventy-seven mixed
//! Jacobian-plus-affine additions and nothing else.  Graviola, whose
//! arithmetic this backend shares, runs its base-point multiplication on the
//! same five-bit window it uses for a variable point — three hundred and
//! eighty-four doublings and seventy-seven additions — and its README says
//! so, which is what this module is here to measure against.
//!
//! # The table
//!
//! [`WINDOWS`] windows of [`W`] bits cover a 384-bit scalar.  Entry
//! `(i, d)` is the affine point `d * 2^(W*i) * G` for `d` in
//! `1 ..= ENTRIES`, so
//!
//! ```text
//! k * G  =  sum_i  d_i * 2^(W*i) * G,    d_i = (k >> W*i) & (2^W - 1)
//! ```
//!
//! is a sum of table entries.  [`TABLE_BYTES`] of affine Montgomery
//! coordinates, built once on first use from the generator by
//! [`build_table`], with a single Montgomery batch inversion for the whole
//! affine conversion.
//!
//! # Why the mixed addition is in its domain
//!
//! `p384_montjmixadd` is correct when its accumulator is the identity, and
//! when the two arguments are neither equal nor mutually inverse.  Both
//! excluded cases are impossible here, by an argument about integers rather
//! than about points.  Let the windows be processed in increasing `i`, and
//! write `m` for the integer the accumulator represents and `a` for the one
//! the addend does.  Before step `i`,
//!
//! ```text
//! m  =  sum_{j < i} d_j 2^(W j)  <  2^(W i)   and   a  =  d_i 2^(W i) >= 2^(W i),
//! ```
//!
//! so `m < a` and in particular `m != a`.  And `m + a` is the partial sum of
//! the digits of `k`, which never exceeds `k < n`, so `m + a != 0 mod n` and
//! the two are not mutually inverse either.  The accumulator is the identity
//! only while every digit so far is zero, which the assembly handles.
//!
//! # Constant time
//!
//! The window count and the entry count are compile-time constants, the
//! table lookup is a full linear scan of all [`ENTRIES`] entries with a mask
//! select, and the zero digit is handled by adding a dummy entry and then
//! mask-selecting the accumulator back.  No branch and no address depends on
//! the scalar.  The scan is the price of that: [`TABLE_BYTES`] of table are
//! read per multiplication, which the benchmark's comb row includes.

use std::sync::LazyLock;

use crate::s2n::{self, Aff, Fe, Jac};

/// Window width in bits.
pub const W: usize = 5;

/// Windows needed for a 384-bit scalar.
pub const WINDOWS: usize = 384_usize.div_ceil(W);

/// Non-zero digits per window, `2^W - 1`.
pub const ENTRIES: usize = (1 << W) - 1;

/// Size of the precomputed table in bytes.
pub const TABLE_BYTES: usize = WINDOWS * ENTRIES * 12 * 8;

/// Odd multiples of `G` held for the two-term multiply, `1G, 3G, ..., 15G`.
pub const WNAF_TABLE_LEN: usize = 8;

/// `[i][d - 1] = d * 2^(W*i) * G`, affine Montgomery, flattened.
struct Table {
    comb: Vec<Aff>,
    wnaf: [Aff; WNAF_TABLE_LEN],
}

static TABLE: LazyLock<Table> = LazyLock::new(build_table);

/// Montgomery batch inversion: `zs[j]^-1` for every `j`, in one
/// [`s2n::montinv`] and three multiplications per element.
///
/// Every `Z` here is the coordinate of a non-identity multiple of `G`, so
/// none is zero.
fn batch_invert(zs: &[Fe]) -> Vec<Fe> {
    let mut prefix = Vec::with_capacity(zs.len());
    let mut acc = *s2n::ONE_MONT;
    for z in zs {
        prefix.push(acc);
        acc = s2n::montmul(&acc, z);
    }
    let mut running = s2n::montinv(&acc);
    let mut out = vec![[0u64; 6]; zs.len()];
    for j in (0..zs.len()).rev() {
        out[j] = s2n::montmul(&prefix[j], &running);
        running = s2n::montmul(&running, &zs[j]);
    }
    out
}

/// The affine form of a list of Jacobian points, with one inversion for the
/// whole list.
fn to_affine_batch(points: &[Jac]) -> Vec<Aff> {
    let zs: Vec<Fe> = points.iter().map(s2n::jz).collect();
    let zis = batch_invert(&zs);
    points
        .iter()
        .zip(zis.iter())
        .map(|(p, zi)| {
            let zi2 = s2n::montsqr(zi);
            let zi3 = s2n::montmul(&zi2, zi);
            let mut a = [0u64; 12];
            a[..6].copy_from_slice(&s2n::montmul(&s2n::jx(p), &zi2));
            a[6..].copy_from_slice(&s2n::montmul(&s2n::jy(p), &zi3));
            a
        })
        .collect()
}

/// Builds both tables from the generator.
///
/// `WINDOWS * ENTRIES` Jacobian points, then one batch inversion.  The `d`
/// loop starts from an explicit doubling because `d = 2` is the one step
/// whose two addends would be equal, which `p384_montjadd` does not serve.
fn build_table() -> Table {
    let g = *s2n::G_JAC;

    let mut jac = Vec::with_capacity(WINDOWS * ENTRIES);
    let mut base = g;
    for _ in 0..WINDOWS {
        let mut e = base;
        jac.push(e);
        e = s2n::jdouble(&base);
        jac.push(e);
        for _ in 3..=ENTRIES {
            e = s2n::jadd(&e, &base);
            jac.push(e);
        }
        // 2^W * base, by W doublings.
        for _ in 0..W {
            base = s2n::jdouble(&base);
        }
    }
    let comb = to_affine_batch(&jac);

    let two = s2n::jdouble(&g);
    let mut odd = Vec::with_capacity(WNAF_TABLE_LEN);
    let mut e = g;
    odd.push(e);
    for _ in 1..WNAF_TABLE_LEN {
        e = s2n::jadd(&e, &two);
        odd.push(e);
    }
    let odd_aff = to_affine_batch(&odd);
    let mut wnaf = [[0u64; 12]; WNAF_TABLE_LEN];
    wnaf.copy_from_slice(&odd_aff);

    Table { comb, wnaf }
}

/// `1G, 3G, 5G, ..., 15G` in affine Montgomery coordinates, the generator
/// side of the interleaved two-term multiply.
pub fn generator_odd_multiples() -> &'static [Aff; WNAF_TABLE_LEN] {
    &TABLE.wnaf
}

/// Forces the tables to be built, so a benchmark's first timed iteration
/// does not pay for them.
pub fn warm() {
    let _ = TABLE.comb.len();
}

/// All-ones when `a == b`, all-zeros otherwise, with no branch.
#[inline]
fn mask_eq(a: u64, b: u64) -> u64 {
    let d = a ^ b;
    // 0 when d != 0, all ones when d == 0.
    ((d | d.wrapping_neg()) >> 63).wrapping_sub(1)
}

/// Entry `d` of window `i`, by a full linear scan with a mask select; a
/// zero `d` yields entry 1, the dummy the caller discards.
#[inline]
fn select(window: usize, d: u64) -> Aff {
    let base = window * ENTRIES;
    let mut out = [0u64; 12];
    for j in 0..ENTRIES {
        // Entry j serves digit j + 1, and also digit 0 when j is 0.
        let want = (j + 1) as u64;
        let m = mask_eq(d, want) | if j == 0 { mask_eq(d, 0) } else { 0 };
        let e = &TABLE.comb[base + j];
        for l in 0..12 {
            out[l] |= e[l] & m;
        }
    }
    out
}

/// `sel` when `take` is all-ones, `keep` when it is all-zeros.
#[inline]
fn select_jac(take: u64, sel: &Jac, keep: &Jac) -> Jac {
    let mut out = [0u64; 18];
    for l in 0..18 {
        out[l] = (sel[l] & take) | (keep[l] & !take);
    }
    out
}

/// `k * G`, for any six-limb `k`.
///
/// `k` is reduced mod `n` first, which is what `p384_montjscalarmul` does
/// with its own scalar and what the comb's domain argument needs.  The
/// result is a Jacobian point, the identity with `Z = 0` when `k == 0`.
pub fn scalar_mul_base(k: &Fe) -> Jac {
    let k = s2n::mod_n(k);

    let mut acc = s2n::identity();
    for i in 0..WINDOWS {
        let bit = W * i;
        let lo = bit / 64;
        let sh = bit % 64;
        let mut d = k[lo] >> sh;
        if sh + W > 64 && lo + 1 < 6 {
            d |= k[lo + 1] << (64 - sh);
        }
        d &= (1u64 << W) - 1;

        let entry = select(i, d);
        let sum = s2n::jmixadd(&acc, &entry);
        // A zero digit added the dummy entry; keep the accumulator instead.
        acc = select_jac(!mask_eq(d, 0), &sum, &acc);
    }
    acc
}
