//! The two CatCrypt-emitted P-384 field kernels against s2n-bignum's, with a
//! known-answer gate first.
//!
//! One question: on the P-384 Montgomery multiply, where both sides compute
//! exactly the same function on the same representation, is our emitted
//! kernel faster than AWS's hand-written, HOL-Light-checked assembly?
//! `bench/framework/geomean_ratios.tsv` holds no P-384 row at all, and
//! `bench/p384_fieldmul_compare/README.md`'s bench section is deferred, so
//! neither emitted kernel has been measured against s2n-bignum before.
//!
//! # The arms
//!
//! | arm | symbol | computes | source |
//! |---|---|---|---|
//! | `ours-montmul` | `p384_montmul_proven` | `x y R^-1 mod p`, `R = 2^384` | `bench/p384_compare/gen/p384_montmul_proven.s` |
//! | `s2n-montmul` | `bignum_montmul_p384` | `x y R^-1 mod p`, `R = 2^384` | `bench/reference_install/s2n-bignum/x86_att/p384/bignum_montmul_p384.S` |
//! | `ours-solinas` | `p384_mul_x86_from_lean` | `x y mod p`, ordinary domain | `bench/p384_fieldmul_compare/gen_com/p384_mul_x86_from_lean.s` |
//! | `aucurves-fp_mul` | `p384::fp_mul` | `x y R^-1 mod p` | fiat-crypto, or CryptOpt when linked |
//! | `s2n-reemitted` | `bignum_montmul_p384_reemitted` | `x y R^-1 mod p`, `R = 2^384` | `bench/s2n_import/gen/bignum_montmul_p384_reemitted.s` |
//! | `s2n-encoded` | `bignum_montmul_p384_encoded` | `x y R^-1 mod p`, `R = 2^384` | `bench/s2n_import/gen/bignum_montmul_p384_encoded.s` |
//! | `s2n-montsqr` | `bignum_montsqr_p384` | `x^2 R^-1 mod p`, `R = 2^384` | `bench/reference_install/s2n-bignum/x86_att/p384/bignum_montsqr_p384.S` |
//! | `s2n-sqr-reemitted` | `bignum_montsqr_p384_reemitted` | `x^2 R^-1 mod p`, `R = 2^384` | `bench/s2n_import/gen/bignum_montsqr_p384_reemitted.s` |
//! | `s2n-sqr-encoded` | `bignum_montsqr_p384_encoded` | `x^2 R^-1 mod p`, `R = 2^384` | `bench/s2n_import/gen/bignum_montsqr_p384_encoded.s` |
//!
//! The fifth arm is s2n-bignum's `bignum_montmul_p384` imported into
//! CatCrypt's `JInstr 64` IR by `bench/s2n_import/import_s2n.sh` and printed
//! back to AT&T assembly by CatCrypt's scalar printer (`bench/s2n_import/`
//! `reemit.lean`).  It is the same program as the second arm up to the
//! encoding of 29 instructions, which the importer widens from 32 to 64 bits,
//! so its row measures what the import and re-emission cost, not a
//! different algorithm.  Its `.s` is included with `global_asm!`, so this
//! binary does not compile until `make -C bench/s2n_import reemit` has
//! written it.
//!
//! The sixth arm is the same imported block encoded to machine code by
//! CatCrypt's scalar encoder (`ScalarEncoder.encodeJBlock`, driver
//! `bench/s2n_import/encode.lean`) and included as `.byte` directives inside
//! s2n-bignum's literal frame.  Those body bytes are the subject of
//! `S2nMontmulP384.s2nMontmulP384Bytes_correct`: they decode to the block, and
//! the block computes the Montgomery product under `JasminModel`.  The encoder
//! writes the 25 `adcq`/`sbbq $0` instructions in the `81 /digit imm32` form
//! where the assembler picks `83 /digit imm8`, so the body is 75 bytes longer
//! than the re-emitted one.  It does not compile until
//! `make -C bench/s2n_import encode` has written its `.s`.
//!
//! The last three arms are the Montgomery square.  `s2n-montsqr` is
//! s2n-bignum's `bignum_montsqr_p384`; the other two are its body imported by
//! the same importer (`import_s2n.sh bignum_montsqr_p384`) and emitted by the
//! printer (`reemit_montsqr.lean`) and by the encoder under the identity
//! allocation (`encode_montsqr.lean`), inside s2n-bignum's literal frame.  No
//! theorem is stated over the square's block or bytes.  The encoder writes 19
//! `adcq`/`sbbq $0` instructions in the 7-byte form, so the encoded body is 57
//! bytes longer than the re-emitted one.  The square arms take one operand;
//! their timing chain is `z <- f(z)`.  Their gate runs separately from the
//! multiply gate: on every corner operand and `KAT_RANDOM` random operands
//! below `p`, both imported arms agree with `bignum_montsqr_p384` and with
//! `bignum_montmul_p384(x, x)`.
//!
//! The first two are the like-for-like pair: same operation, same domain,
//! same six-limb layout, same System V signature.  The third is **not** a
//! like-for-like comparison with them — it is a 6x6 MULX/ADCX schoolbook
//! followed by a derived signed Solinas reduction, and it leaves the
//! Montgomery domain out of the picture entirely, so it does more of one
//! kind of work and none of another.  It is timed beside them because it is
//! the other emitted P-384 field kernel in the tree and because a field
//! multiply in the ordinary domain is what a Solinas-reduction group law
//! would call; it is not a substitute for the montmul row.  The fourth is
//! the field the `aucurves` ECDSA backend actually runs, for scale.
//!
//! # Provenance
//!
//! Both emitted `.s` files are untracked build output of their Lean
//! emitters, and this binary assembles whatever is on disk.  The header line
//! prints the size and modification time of each, so a recorded figure names
//! the bytes it measured.  Nothing here regenerates them.
//!
//! # Method
//!
//! A known-answer gate runs first and no timing is printed unless every arm
//! passes it: corner operands, all pairs, plus `KAT_RANDOM` random pairs
//! below `p`, byte-identical against a reference built from s2n-bignum
//! itself.  Then a serial dependent chain `z <- f(z, y)`, so each multiply
//! reads the previous one's stored result, with the arms interleaved in
//! rotating order within each sample round.  The figure is the minimum and
//! the median over the rounds, in invariant-TSC reference cycles and in
//! nanoseconds; both are taken from the same loop.

use std::hint::black_box;
use std::time::Instant;

use p384_ecdsa_rust::s2n::{self, Fe};

extern "C" {
    /// `z = x y R^-1 mod p`, `R = 2^384`.  System V: `rdi`, `rsi`, `rdx`.
    fn p384_montmul_proven(z: *mut u64, x: *const u64, y: *const u64);
    /// `z = x y mod p`, ordinary domain.  System V: `rdi`, `rsi`, `rdx`.
    fn p384_mul_x86_from_lean(z: *mut u64, x: *const u64, y: *const u64);
    /// `z = x y R^-1 mod p`, `R = 2^384`: s2n-bignum's block through the
    /// CatCrypt import and printer.  System V: `rdi`, `rsi`, `rdx`.
    fn bignum_montmul_p384_reemitted(z: *mut u64, x: *const u64, y: *const u64);
    /// `z = x y R^-1 mod p`, `R = 2^384`: s2n-bignum's block through the
    /// CatCrypt import and byte encoder.  System V: `rdi`, `rsi`, `rdx`.
    fn bignum_montmul_p384_encoded(z: *mut u64, x: *const u64, y: *const u64);
    /// `z = x^2 R^-1 mod p`, `R = 2^384`: s2n-bignum's square through the
    /// CatCrypt import and printer.  System V: `rdi`, `rsi`.
    fn bignum_montsqr_p384_reemitted(z: *mut u64, x: *const u64);
    /// `z = x^2 R^-1 mod p`, `R = 2^384`: s2n-bignum's square through the
    /// CatCrypt import and byte encoder.  System V: `rdi`, `rsi`.
    fn bignum_montsqr_p384_encoded(z: *mut u64, x: *const u64);
}

// The re-emitted s2n-bignum kernel, assembled by rustc's integrated assembler.
std::arch::global_asm!(
    include_str!("../../../s2n_import/gen/bignum_montmul_p384_reemitted.s"),
    options(att_syntax)
);

// The encoded s2n-bignum kernel: `.byte` directives inside a literal frame.
std::arch::global_asm!(
    include_str!("../../../s2n_import/gen/bignum_montmul_p384_encoded.s"),
    options(att_syntax)
);

// The re-emitted s2n-bignum square.
std::arch::global_asm!(
    include_str!("../../../s2n_import/gen/bignum_montsqr_p384_reemitted.s"),
    options(att_syntax)
);

// The encoded s2n-bignum square.
std::arch::global_asm!(
    include_str!("../../../s2n_import/gen/bignum_montsqr_p384_encoded.s"),
    options(att_syntax)
);

/// `p_384`, canonical little-endian limbs.
const P: Fe = [
    0x0000_0000_ffff_ffff,
    0xffff_ffff_0000_0000,
    0xffff_ffff_ffff_fffe,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
];

/// `z = x y R^-1 mod p` through the emitted kernel.
#[inline]
fn ours_montmul(x: &Fe, y: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { p384_montmul_proven(z.as_mut_ptr(), x.as_ptr(), y.as_ptr()) };
    z
}

/// `z = x y mod p` through the emitted Solinas kernel.
#[inline]
fn ours_solinas(x: &Fe, y: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { p384_mul_x86_from_lean(z.as_mut_ptr(), x.as_ptr(), y.as_ptr()) };
    z
}

/// `z = x y R^-1 mod p` through the re-emitted s2n-bignum block.
#[inline]
fn s2n_reemitted(x: &Fe, y: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_montmul_p384_reemitted(z.as_mut_ptr(), x.as_ptr(), y.as_ptr()) };
    z
}

/// `z = x y R^-1 mod p` through the encoded s2n-bignum block.
#[inline]
fn s2n_encoded(x: &Fe, y: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_montmul_p384_encoded(z.as_mut_ptr(), x.as_ptr(), y.as_ptr()) };
    z
}

/// `z = x^2 R^-1 mod p` through the re-emitted s2n-bignum square.
#[inline]
fn s2n_sqr_reemitted(x: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_montsqr_p384_reemitted(z.as_mut_ptr(), x.as_ptr()) };
    z
}

/// `z = x^2 R^-1 mod p` through the encoded s2n-bignum square.
#[inline]
fn s2n_sqr_encoded(x: &Fe) -> Fe {
    let mut z = [0u64; 6];
    unsafe { bignum_montsqr_p384_encoded(z.as_mut_ptr(), x.as_ptr()) };
    z
}

/// The square arms in the two-operand shape of [`Arm`]; `y` is unused.
fn arm_s2n_montsqr(x: &Fe, _y: &Fe) -> Fe {
    s2n::montsqr(x)
}

fn arm_s2n_sqr_reemitted(x: &Fe, _y: &Fe) -> Fe {
    s2n_sqr_reemitted(x)
}

fn arm_s2n_sqr_encoded(x: &Fe, _y: &Fe) -> Fe {
    s2n_sqr_encoded(x)
}

/// `z = x y R^-1 mod p` through AUCurves' field multiply.
#[inline]
fn aucurves_fp_mul(x: &Fe, y: &Fe) -> Fe {
    let mut z = p384::Fp([0u64; 6]);
    p384::fp_mul(&mut z, &p384::Fp(*x), &p384::Fp(*y));
    z.0
}

/// SplitMix64, so the operands are the same on every run.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A uniform element of `[0, p)`, by rejection.
    fn fe(&mut self) -> Fe {
        loop {
            let mut c = [0u64; 6];
            for w in c.iter_mut() {
                *w = self.next_u64();
            }
            if lt(&c, &P) {
                return c;
            }
        }
    }
}

fn lt(a: &Fe, b: &Fe) -> bool {
    for i in (0..6).rev() {
        if a[i] != b[i] {
            return a[i] < b[i];
        }
    }
    false
}

/// `2^768 mod p`, so `montmul(montmul(x, y), R2) = x y mod p`.
fn r2_mod_p() -> Fe {
    let mut one = [0u64; 6];
    one[0] = 1;
    s2n::tomont(&s2n::tomont(&one))
}

/// Operands that have exercised limb boundaries and reduction corners.
fn corners() -> Vec<Fe> {
    let mut one = [0u64; 6];
    one[0] = 1;
    let mut two = [0u64; 6];
    two[0] = 2;
    let p_minus_1 = {
        let mut v = P;
        v[0] -= 1;
        v
    };
    let p_minus_2 = {
        let mut v = P;
        v[0] -= 2;
        v
    };
    let mut out = vec![
        [0u64; 6],
        one,
        two,
        p_minus_1,
        p_minus_2,
        s2n::tomont(&one),
        r2_mod_p(),
    ];
    for i in 0..6 {
        let mut v = [0u64; 6];
        v[i] = 1;
        out.push(v);
        let mut w = [0u64; 6];
        w[i] = u64::MAX;
        out.push(w);
    }
    out
}

/// The known-answer gate.  Returns the number of pairs checked per arm.
fn gate(random: usize) -> usize {
    let r2 = r2_mod_p();
    let mut checked = 0usize;

    let mut check = |x: &Fe, y: &Fe| {
        let want_mont = s2n::montmul(x, y);
        let want_ord = s2n::montmul(&want_mont, &r2);

        let got_mont = ours_montmul(x, y);
        assert_eq!(
            got_mont, want_mont,
            "p384_montmul_proven differs from bignum_montmul_p384 at x = {x:?}, y = {y:?}"
        );
        assert!(lt(&got_mont, &P), "p384_montmul_proven returned a value at or above p");

        let got_ord = ours_solinas(x, y);
        assert_eq!(
            got_ord, want_ord,
            "p384_mul_x86_from_lean differs from the reference at x = {x:?}, y = {y:?}"
        );
        assert!(lt(&got_ord, &P), "p384_mul_x86_from_lean returned a value at or above p");

        assert_eq!(
            aucurves_fp_mul(x, y),
            want_mont,
            "p384::fp_mul differs from bignum_montmul_p384 at x = {x:?}, y = {y:?}"
        );

        assert_eq!(
            s2n_reemitted(x, y),
            want_mont,
            "bignum_montmul_p384_reemitted differs from bignum_montmul_p384 at x = {x:?}, y = {y:?}"
        );

        assert_eq!(
            s2n_encoded(x, y),
            want_mont,
            "bignum_montmul_p384_encoded differs from bignum_montmul_p384 at x = {x:?}, y = {y:?}"
        );
        checked += 1;
    };

    let cs = corners();
    for x in &cs {
        for y in &cs {
            check(x, y);
        }
    }
    let mut rng = Rng(0xc0ff_ee12_3456_789a);
    for _ in 0..random {
        let x = rng.fe();
        let y = rng.fe();
        check(&x, &y);
    }
    checked
}

/// The known-answer gate for the square.  Returns the number of operands
/// checked per arm.
fn gate_sqr(random: usize) -> usize {
    let mut checked = 0usize;

    let mut check = |x: &Fe| {
        let want = s2n::montsqr(x);
        assert_eq!(
            s2n::montmul(x, x),
            want,
            "bignum_montsqr_p384 differs from bignum_montmul_p384(x, x) at x = {x:?}"
        );
        assert!(lt(&want, &P), "bignum_montsqr_p384 returned a value at or above p");
        assert_eq!(
            s2n_sqr_reemitted(x),
            want,
            "bignum_montsqr_p384_reemitted differs from bignum_montsqr_p384 at x = {x:?}"
        );
        assert_eq!(
            s2n_sqr_encoded(x),
            want,
            "bignum_montsqr_p384_encoded differs from bignum_montsqr_p384 at x = {x:?}"
        );
        checked += 1;
    };

    for x in &corners() {
        check(x);
    }
    let mut rng = Rng(0x5a17_5eed_0bad_cafe);
    for _ in 0..random {
        check(&rng.fe());
    }
    checked
}

/// A serialised invariant-TSC read.
#[inline]
fn tsc() -> u64 {
    unsafe {
        std::arch::x86_64::_mm_lfence();
        let t = std::arch::x86_64::_rdtsc();
        std::arch::x86_64::_mm_lfence();
        t
    }
}

struct Arm {
    name: &'static str,
    note: &'static str,
    f: fn(&Fe, &Fe) -> Fe,
    cycles: Vec<f64>,
    nanos: Vec<f64>,
    end: Fe,
}

impl Arm {
    fn new(name: &'static str, note: &'static str, f: fn(&Fe, &Fe) -> Fe) -> Self {
        Arm {
            name,
            note,
            f,
            cycles: Vec::new(),
            nanos: Vec::new(),
            end: [0u64; 6],
        }
    }
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = v.len();
    if n % 2 == 1 {
        v[n / 2]
    } else {
        0.5 * (v[n / 2 - 1] + v[n / 2])
    }
}

fn minimum(v: &[f64]) -> f64 {
    v.iter().copied().fold(f64::INFINITY, f64::min)
}

fn main() {
    let samples: usize = std::env::var("FIELD_SAMPLES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(301);
    let inner: usize = std::env::var("FIELD_INNER")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(2000);
    let kat_random: usize = std::env::var("KAT_RANDOM")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(100_000);

    println!("# P-384 field multiply: CatCrypt emitted kernels against s2n-bignum");
    for (label, path) in [
        ("ours-montmul", "../p384_compare/gen/p384_montmul_proven.s"),
        (
            "ours-solinas",
            "../p384_fieldmul_compare/gen_com/p384_mul_x86_from_lean.s",
        ),
        (
            "s2n-reemitted",
            "../s2n_import/gen/bignum_montmul_p384_reemitted.s",
        ),
        (
            "s2n-encoded",
            "../s2n_import/gen/bignum_montmul_p384_encoded.s",
        ),
        (
            "s2n-sqr-reemitted",
            "../s2n_import/gen/bignum_montsqr_p384_reemitted.s",
        ),
        (
            "s2n-sqr-encoded",
            "../s2n_import/gen/bignum_montsqr_p384_encoded.s",
        ),
    ] {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(path);
        match std::fs::metadata(&p) {
            Ok(m) => println!(
                "# {label:<17} {} bytes, mtime {:?}, {}",
                m.len(),
                m.modified().ok(),
                p.display()
            ),
            Err(e) => println!("# {label:<17} {} ({e})", p.display()),
        }
    }
    println!(
        "# aucurves field = {}",
        if p384::CRYPTOPT_ASM {
            "CryptOpt assembly"
        } else {
            "fiat-crypto Rust"
        }
    );
    println!();

    let checked = gate(kat_random);
    println!("# KAT: {checked} operand pairs per arm, byte-identical to the reference");
    println!("#   reference = bignum_montmul_p384, and for the ordinary-domain arm");
    println!("#   montmul(montmul(x, y), 2^768 mod p), which is x*y mod p.");
    let checked_sqr = gate_sqr(kat_random);
    println!("# KAT (square): {checked_sqr} operands per arm, byte-identical to");
    println!("#   bignum_montsqr_p384, which equals bignum_montmul_p384(x, x) on each.");
    println!();

    let mut rng = Rng(0x5eed_0f1e_1d5a_b1e0);
    let pool: Vec<(Fe, Fe)> = (0..16).map(|_| (rng.fe(), rng.fe())).collect();

    let mut arms = [
        Arm::new("ours-montmul (emitted)", "x*y*R^-1 mod p", ours_montmul),
        Arm::new("s2n-bignum montmul_p384", "x*y*R^-1 mod p", s2n::montmul),
        Arm::new("aucurves fp_mul", "x*y*R^-1 mod p", aucurves_fp_mul),
        Arm::new("ours-solinas (emitted)", "x*y mod p, other shape", ours_solinas),
        Arm::new("s2n re-emitted (import)", "x*y*R^-1 mod p", s2n_reemitted),
        Arm::new("s2n encoded (proved)", "x*y*R^-1 mod p", s2n_encoded),
        Arm::new("s2n-bignum montsqr_p384", "x^2*R^-1 mod p", arm_s2n_montsqr),
        Arm::new("s2n sqr re-emitted", "x^2*R^-1 mod p", arm_s2n_sqr_reemitted),
        Arm::new("s2n sqr encoded", "x^2*R^-1 mod p", arm_s2n_sqr_encoded),
    ];

    // Warm-up, outside the measured region.
    for arm in arms.iter_mut() {
        let (mut z, y) = pool[0];
        for _ in 0..inner {
            z = (arm.f)(&z, &y);
        }
        arm.end = z;
    }

    for round in 0..samples {
        let (z0, y) = pool[round % pool.len()];
        for arm in arms.iter_mut() {
            let mut z = z0;
            let t0 = tsc();
            let w0 = Instant::now();
            for _ in 0..inner {
                z = (arm.f)(black_box(&z), black_box(&y));
            }
            let w = w0.elapsed().as_nanos() as f64;
            let t = (tsc() - t0) as f64;
            arm.end = black_box(z);
            arm.cycles.push(t / inner as f64);
            arm.nanos.push(w / inner as f64);
        }
    }

    println!("# serial dependent chain, samples={samples} inner={inner}, arms interleaved");
    println!("# cycles are invariant-TSC reference cycles, not retired core cycles");
    println!();
    println!(
        "{:<26} {:<22} {:>9} {:>9} {:>9} {:>9}",
        "arm", "computes", "min cyc", "med cyc", "min ns", "med ns"
    );
    let mut mins = Vec::new();
    for arm in arms.iter() {
        let mc = minimum(&arm.cycles);
        mins.push(mc);
        println!(
            "{:<26} {:<22} {mc:>9.1} {:>9.1} {:>9.2} {:>9.2}",
            arm.name,
            arm.note,
            median(arm.cycles.clone()),
            minimum(&arm.nanos),
            median(arm.nanos.clone()),
        );
    }
    println!();
    println!("# the like-for-like row: ours-montmul / s2n-bignum montmul_p384");
    println!(
        "#   on the minima, {:.3}; on the medians, {:.3}.",
        mins[0] / mins[1],
        median(arms[0].cycles.clone()) / median(arms[1].cycles.clone())
    );
    println!("#   above 1.000 means our emitted kernel is slower.");
    println!();
    println!("# for scale, against the same denominator:");
    for (i, arm) in arms.iter().enumerate().take(6).skip(2) {
        println!("#   {:<26} {:.3}", arm.name, mins[i] / mins[1]);
    }
    println!("# the solinas row computes a different function (ordinary domain, a");
    println!("#   derived signed Solinas reduction rather than a Montgomery one), so");
    println!("#   its ratio against a montmul is a shape comparison, not a like-for-");
    println!("#   like one.");
    println!();
    println!("# the import row: s2n re-emitted / s2n-bignum montmul_p384, the same");
    println!("#   program up to the encoding of 29 widened instructions:");
    println!(
        "#   on the minima, {:.3}; on the medians, {:.3}.",
        mins[4] / mins[1],
        median(arms[4].cycles.clone()) / median(arms[1].cycles.clone())
    );
    println!("# ours-montmul / s2n re-emitted:");
    println!(
        "#   on the minima, {:.3}; on the medians, {:.3}.",
        mins[0] / mins[4],
        median(arms[0].cycles.clone()) / median(arms[4].cycles.clone())
    );
    println!("# the encoded row: s2n encoded / s2n-bignum montmul_p384, the bytes");
    println!("#   S2nMontmulP384.s2nMontmulP384Bytes_correct is stated over:");
    println!(
        "#   on the minima, {:.3}; on the medians, {:.3}.",
        mins[5] / mins[1],
        median(arms[5].cycles.clone()) / median(arms[1].cycles.clone())
    );
    println!();
    println!("# the square rows, against s2n-bignum montsqr_p384 (chain z <- f(z)):");
    for i in [7, 8] {
        println!(
            "#   {:<26} on the minima, {:.3}; on the medians, {:.3}.",
            arms[i].name,
            mins[i] / mins[6],
            median(arms[i].cycles.clone()) / median(arms[6].cycles.clone())
        );
    }
}
