//! Known-answer test for the emitted BN254 `Fp2` (quadratic-twist field) multiply.
//!
//! CONN-3i lands the first level of the pairing tower: the abstract
//! `Fp2 = Fp[u]/(u²+1)` over the CONN-3e-realized base field, with the emitted
//! `Fp2` multiply a COMPOSITION over the verified base-field leaves — the
//! schoolbook `(a+bu)(c+du) = (ac−bd) + (ad+bc)u` reduction over `u² = −1`
//! (`Pairing/Fp2Tower.lean`, `BaseSubstrate.emittedFp2Mul`).  There is no opaque
//! `Fp2`-multiply leaf: the emitted `Fp2` mul is three base `fp_mul`s plus one
//! base `fp_add` and one base `fp_sub`.
//!
//! This KAT cross-checks that emitted schoolbook composition — built from the
//! SAME AUCurves verified base leaves (`fp_mul`/`fp_add`/`fp_sub`) — is
//! BYTE-IDENTICAL to the AUCurves verified `fp2_mul` (`bn254_Fp2_mul`, the
//! Karatsuba `v0/v1/v2` form, `generated/bn254_safe_tower.rs`) on fixed and
//! reproducible-random `Fp2` inputs in the BN254 Montgomery domain.
//!
//! No fabricated vectors: the reference is the AUCurves verified `fp2_mul`; the
//! inputs are the published generator coordinates (Montgomery form) plus an
//! LCG-reproducible random sweep over the base leaves.

use bn254::*;

/// The EMITTED `Fp2` multiply: the schoolbook `(ac−bd) + (ad+bc)u` reduction
/// (`u² = −1`) built from the verified base-field leaves, exactly as
/// `Fp2Tower.BaseSubstrate.emittedFp2Mul` prescribes — three `fp_mul`s, one
/// `fp_add`, one `fp_sub`.  No `fp2_mul` leaf is used here.
fn emitted_fp2_mul(x: &Fp2, y: &Fp2) -> Fp2 {
    let mut ac = Fp::zero();
    let mut bd = Fp::zero();
    let mut ad = Fp::zero();
    let mut bc = Fp::zero();
    fp_mul(&mut ac, &x.c0, &y.c0); // a·c
    fp_mul(&mut bd, &x.c1, &y.c1); // b·d
    fp_mul(&mut ad, &x.c0, &y.c1); // a·d
    fp_mul(&mut bc, &x.c1, &y.c0); // b·c
    let mut c0 = Fp::zero();
    let mut c1 = Fp::zero();
    fp_sub(&mut c0, &ac, &bd); // ac − bd
    fp_add(&mut c1, &ad, &bc); // ad + bc
    Fp2 { c0, c1 }
}

fn fp_eq(a: &Fp, b: &Fp) -> bool {
    a.0[0] == b.0[0] && a.0[1] == b.0[1] && a.0[2] == b.0[2] && a.0[3] == b.0[3]
}

fn fp2_eq(a: &Fp2, b: &Fp2) -> bool {
    fp_eq(&a.c0, &b.c0) && fp_eq(&a.c1, &b.c1)
}

// --- Published generator coordinates (Montgomery form), from bn254_kat.rs -----
const G1_X: Fp = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
const G1_Y: Fp = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);

fn g2_gen() -> (Fp2, Fp2) {
    let q_x = Fp2 {
        c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
        c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]),
    };
    let q_y = Fp2 {
        c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
        c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]),
    };
    (q_x, q_y)
}

/// Reproducible pseudo-random `Fp` via the base `fp_mul`/`fp_add` leaves applied
/// to a small LCG-seeded word, kept in the Montgomery domain so the inputs are
/// genuine field elements (no out-of-range words).
fn rand_fp(state: &mut u64) -> Fp {
    *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    let mut base = Fp::zero();
    fp_from_word(&mut base, *state);
    // Square a few times to spread bits across all limbs.
    let mut acc = base;
    for _ in 0..3 {
        let mut t = Fp::zero();
        fp_mul(&mut t, &acc, &acc);
        acc = t;
    }
    acc
}

fn rand_fp2(state: &mut u64) -> Fp2 {
    Fp2 { c0: rand_fp(state), c1: rand_fp(state) }
}

fn check(name: &str, x: &Fp2, y: &Fp2, fail: &mut i32) {
    let emitted = emitted_fp2_mul(x, y);
    let mut reference = Fp2::zero();
    fp2_mul(&mut reference, x, y); // AUCurves verified bn254_Fp2_mul
    if fp2_eq(&emitted, &reference) {
        println!("ok:   emitted Fp2 mul == AUCurves fp2_mul ({})", name);
    } else {
        println!("FAIL: emitted Fp2 mul != AUCurves fp2_mul ({})", name);
        *fail += 1;
    }
}

fn main() {
    let mut fail = 0;
    let (q_x, q_y) = g2_gen();

    // --- Fixed vectors: published G2 generator coordinates + a G1-lifted pair --
    check("G2_x · G2_y", &q_x, &q_y, &mut fail);
    check("G2_y · G2_x (comm)", &q_y, &q_x, &mut fail);
    let g1_lift = Fp2 { c0: G1_X, c1: G1_Y };
    check("G1-lift · G2_x", &g1_lift, &q_x, &mut fail);
    check("G2_x · G2_x (square shape)", &q_x, &q_x, &mut fail);
    // 1 + 0u  and  0 + 1u  (the unit and the generator u)
    let mut one = Fp::zero();
    fp_from_word(&mut one, 1);
    let fp2_one = Fp2 { c0: one, c1: Fp::zero() };
    let fp2_u = Fp2 { c0: Fp::zero(), c1: one };
    check("1 · G2_x (identity)", &fp2_one, &q_x, &mut fail);
    check("u · u (should be -1)", &fp2_u, &fp2_u, &mut fail);

    // --- Reproducible random sweep over the base leaves -----------------------
    let mut state: u64 = 0x9e3779b97f4a7c15;
    for i in 0..2000 {
        let x = rand_fp2(&mut state);
        let y = rand_fp2(&mut state);
        let emitted = emitted_fp2_mul(&x, &y);
        let mut reference = Fp2::zero();
        fp2_mul(&mut reference, &x, &y);
        if !fp2_eq(&emitted, &reference) {
            println!("FAIL: random vector {} mismatch", i);
            fail += 1;
            if fail > 5 { break; }
        }
    }
    if fail == 0 {
        println!("ok:   emitted Fp2 mul == AUCurves fp2_mul on 2000 reproducible-random vectors");
    }

    if fail == 0 {
        println!("KAT PASSED (emitted BN254 Fp2 multiply — schoolbook composition over the verified base leaves — is byte-identical to the AUCurves verified fp2_mul)");
    } else {
        println!("KAT FAILED ({} case(s))", fail);
        std::process::exit(1);
    }
}
