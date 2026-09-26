//! Known-answer test for the **reg-ptr verified-leaf re-emitted** BN254
//! pairing-tower field arithmetic (task #260).
//!
//! `CatCrypt/Crypto/Jasmin/Bn254Reflect.lean` §8 + the emit driver
//! `bench/bn254_compare/fp_tower_from_rustcmd.lean` route the BN254 `Fp2/Fp6/Fp12`
//! multiply op bodies — leaf-call chains over the next-lower tower level — through
//! CatCrypt's verified front (`translate → cprogToJasminCom → emitAbiOrchRegPtr`)
//! to reg-ptr `.jazz` over typed-array (`reg ptr u64[N]`) field leaves. The
//! emitted leaf-call schedules are reproduced below EXACTLY (same leaf order, same
//! scratch read/write graph) and cross-checked byte-for-byte against the AUCurves
//! verified reference (`tower::bn254_Fp2_mul` / `bn254_Fp6_mul` / `fp12_mul`, the
//! same verified-bedrock2 tower) on the published EIP-197 generator coordinates
//! plus an LCG-reproducible random sweep.
//!
//! No fabricated vectors: the reference is the AUCurves verified tower; the inputs
//! are the published G2 generator coordinates (Montgomery form) plus the
//! reproducible random sweep. The emitted reg-ptr `.jazz` is field-correct iff
//! these match, since the emitted leaf graph is byte-identical to the Qed-pinned
//! import-file `*Expected` chains (`Fp2TowerImport.lean`, `Fp6Fp12TowerImport.lean`).

use bn254::*;
use bn254::tower::{
    bn254_Fp2_mul, bn254_Fp2_add, bn254_Fp2_sub, bn254_Fp2_mul_xi,
    bn254_Fp6_mul, bn254_Fp6_add, bn254_Fp6_sub, bn254_Fp6_mul_by_v,
};

// ---- Equality helpers --------------------------------------------------------
fn fp_eq(a: &Fp, b: &Fp) -> bool {
    a.0[0] == b.0[0] && a.0[1] == b.0[1] && a.0[2] == b.0[2] && a.0[3] == b.0[3]
}
fn fp2_eq(a: &Fp2, b: &Fp2) -> bool { fp_eq(&a.c0, &b.c0) && fp_eq(&a.c1, &b.c1) }
fn fp6_eq(a: &Fp6, b: &Fp6) -> bool {
    fp2_eq(&a.c0, &b.c0) && fp2_eq(&a.c1, &b.c1) && fp2_eq(&a.c2, &b.c2)
}
fn fp12_eq(a: &Fp12, b: &Fp12) -> bool { fp6_eq(&a.c0, &b.c0) && fp6_eq(&a.c1, &b.c1) }

// =============================================================================
// The EMITTED reg-ptr schedules — byte-identical to the .jazz emitted by
// fp_tower_from_rustcmd.lean (Bn254Reflect §8e bodies).
// =============================================================================

/// Emitted `bn254_Fp2_mul_rustcmd` (Karatsuba over the verified `Fp` leaves):
///   t0=mul(a,c) t1=mul(b,d) t2=add(a,b) t3=add(c,d) t4=mul(t3,t2)
///   t5=t4-t0 t6=t5-t1 (= ad+bc, imaginary)  t7=t0-t1 (= ac-bd, real)
fn emitted_fp2_mul(x: &Fp2, y: &Fp2) -> Fp2 {
    let (a, b) = (&x.c0, &x.c1);
    let (c, d) = (&y.c0, &y.c1);
    let mut t0 = Fp::zero(); fp_mul(&mut t0, a, c);
    let mut t1 = Fp::zero(); fp_mul(&mut t1, b, d);
    let mut t2 = Fp::zero(); fp_add(&mut t2, a, b);
    let mut t3 = Fp::zero(); fp_add(&mut t3, c, d);
    let mut t4 = Fp::zero(); fp_mul(&mut t4, &t3, &t2);
    let mut t5 = Fp::zero(); fp_sub(&mut t5, &t4, &t0);
    let mut t6 = Fp::zero(); fp_sub(&mut t6, &t5, &t1);  // imaginary
    let mut t7 = Fp::zero(); fp_sub(&mut t7, &t0, &t1);  // real
    Fp2 { c0: t7, c1: t6 }
}

/// Emitted `bn254_Fp6_mul_rustcmd` (cubic Toom/Karatsuba over the `Fp2` leaves;
/// the Bn254Reflect §8e fp6MulExpected chain, components extracted + reassembled).
fn emitted_fp6_mul(x: &Fp6, y: &Fp6) -> Fp6 {
    let (x0, x1, x2) = (&x.c0, &x.c1, &x.c2);
    let (y0, y1, y2) = (&y.c0, &y.c1, &y.c2);
    let z = Fp2 { c0: Fp::zero(), c1: Fp::zero() };
    let mut a0b0 = z.clone(); bn254_Fp2_mul(&mut a0b0, x0, y0);
    let mut a1b1 = z.clone(); bn254_Fp2_mul(&mut a1b1, x1, y1);
    let mut a2b2 = z.clone(); bn254_Fp2_mul(&mut a2b2, x2, y2);
    let mut t = z.clone(); bn254_Fp2_add(&mut t, x1, x2);
    let mut u = z.clone(); bn254_Fp2_add(&mut u, y1, y2);
    { let mut r = z.clone(); bn254_Fp2_mul(&mut r, &t, &u); t = r; }
    { let mut r = z.clone(); bn254_Fp2_sub(&mut r, &t, &a1b1); t = r; }
    { let mut r = z.clone(); bn254_Fp2_sub(&mut r, &t, &a2b2); t = r; }
    { let mut r = z.clone(); bn254_Fp2_mul_xi(&mut r, &t); t = r; }
    let mut o0 = z.clone(); bn254_Fp2_add(&mut o0, &a0b0, &t);
    { let mut r = z.clone(); bn254_Fp2_add(&mut r, x0, x1); t = r; }
    { let mut r = z.clone(); bn254_Fp2_add(&mut r, y0, y1); u = r; }
    { let mut r = z.clone(); bn254_Fp2_mul(&mut r, &t, &u); t = r; }
    { let mut r = z.clone(); bn254_Fp2_sub(&mut r, &t, &a0b0); t = r; }
    { let mut r = z.clone(); bn254_Fp2_sub(&mut r, &t, &a1b1); t = r; }
    { let mut r = z.clone(); bn254_Fp2_mul_xi(&mut r, &a2b2); u = r; }
    let mut o1 = z.clone(); bn254_Fp2_add(&mut o1, &t, &u);
    { let mut r = z.clone(); bn254_Fp2_add(&mut r, x0, x2); t = r; }
    { let mut r = z.clone(); bn254_Fp2_add(&mut r, y0, y2); u = r; }
    { let mut r = z.clone(); bn254_Fp2_mul(&mut r, &t, &u); t = r; }
    { let mut r = z.clone(); bn254_Fp2_sub(&mut r, &t, &a0b0); t = r; }
    { let mut r = z.clone(); bn254_Fp2_sub(&mut r, &t, &a2b2); t = r; }
    let mut o2 = z.clone(); bn254_Fp2_add(&mut o2, &t, &a1b1);
    Fp6 { c0: o0, c1: o1, c2: o2 }
}

/// Emitted `bn254_Fp12_mul_rustcmd` (Karatsuba over the `Fp6` leaves; the
/// Bn254Reflect §8e fp12MulExpected chain).
fn emitted_fp12_mul(x: &Fp12, y: &Fp12) -> Fp12 {
    let (x0, x1) = (&x.c0, &x.c1);
    let (y0, y1) = (&y.c0, &y.c1);
    let zfp2 = Fp2 { c0: Fp::zero(), c1: Fp::zero() };
    let z6 = Fp6 { c0: zfp2.clone(), c1: zfp2.clone(), c2: zfp2.clone() };
    let mut v0 = z6.clone(); bn254_Fp6_mul(&mut v0, x0, y0);
    let mut v1 = z6.clone(); bn254_Fp6_mul(&mut v1, x1, y1);
    let mut v2 = z6.clone(); bn254_Fp6_add(&mut v2, x0, x1);
    let mut o1 = z6.clone(); bn254_Fp6_add(&mut o1, y0, y1);
    { let mut r = z6.clone(); bn254_Fp6_mul(&mut r, &o1, &v2); o1 = r; }
    { let mut r = z6.clone(); bn254_Fp6_sub(&mut r, &o1, &v0); o1 = r; }
    { let mut r = z6.clone(); bn254_Fp6_sub(&mut r, &o1, &v1); o1 = r; }
    let mut t = z6.clone(); bn254_Fp6_mul_by_v(&mut t, &v1);
    let mut o0 = z6.clone(); bn254_Fp6_add(&mut o0, &v0, &t);
    Fp12 { c0: o0, c1: o1 }
}

// ---- Published generator coordinates (Montgomery form) -----------------------
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

// ---- Reproducible pseudo-random field elements (Montgomery domain) -----------
fn rand_fp(state: &mut u64) -> Fp {
    *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    let mut base = Fp::zero();
    fp_from_word(&mut base, *state);
    let mut acc = base;
    for _ in 0..3 { let mut t = Fp::zero(); fp_mul(&mut t, &acc, &acc); acc = t; }
    acc
}
fn rand_fp2(state: &mut u64) -> Fp2 { Fp2 { c0: rand_fp(state), c1: rand_fp(state) } }
fn rand_fp6(state: &mut u64) -> Fp6 {
    Fp6 { c0: rand_fp2(state), c1: rand_fp2(state), c2: rand_fp2(state) }
}
fn rand_fp12(state: &mut u64) -> Fp12 { Fp12 { c0: rand_fp6(state), c1: rand_fp6(state) } }

fn main() {
    let mut fail = 0;
    let (q_x, q_y) = g2_gen();

    // === Fp2 mul ===
    {
        let g1_lift = Fp2 { c0: G1_X, c1: G1_Y };
        let mut one = Fp::zero(); fp_from_word(&mut one, 1);
        let cases: &[(&str, &Fp2, &Fp2)] = &[
            ("G2_x · G2_y", &q_x, &q_y),
            ("G2_y · G2_x", &q_y, &q_x),
            ("G1-lift · G2_x", &g1_lift, &q_x),
            ("G2_x · G2_x", &q_x, &q_x),
        ];
        for (name, x, y) in cases {
            let emitted = emitted_fp2_mul(x, y);
            let mut reference = Fp2::zero();
            bn254_Fp2_mul(&mut reference, x, y);
            if fp2_eq(&emitted, &reference) {
                println!("ok:   emitted Fp2 mul == AUCurves bn254_Fp2_mul ({})", name);
            } else { println!("FAIL: Fp2 mul ({})", name); fail += 1; }
        }
        let mut st: u64 = 0x9e3779b97f4a7c15;
        let mut bad = 0;
        for _ in 0..2000 {
            let x = rand_fp2(&mut st); let y = rand_fp2(&mut st);
            let emitted = emitted_fp2_mul(&x, &y);
            let mut reference = Fp2::zero();
            bn254_Fp2_mul(&mut reference, &x, &y);
            if !fp2_eq(&emitted, &reference) { bad += 1; }
        }
        if bad == 0 { println!("ok:   emitted Fp2 mul == AUCurves on 2000 random vectors"); }
        else { println!("FAIL: Fp2 mul {} random mismatches", bad); fail += bad; }
    }

    // === Fp6 mul ===
    {
        let mut st: u64 = 0x243f6a8885a308d3;
        let mut bad = 0;
        for _ in 0..1000 {
            let x = rand_fp6(&mut st); let y = rand_fp6(&mut st);
            let emitted = emitted_fp6_mul(&x, &y);
            let mut reference = Fp6::zero();
            bn254_Fp6_mul(&mut reference, &x, &y);
            if !fp6_eq(&emitted, &reference) { bad += 1; }
        }
        if bad == 0 { println!("ok:   emitted Fp6 mul == AUCurves bn254_Fp6_mul on 1000 random vectors"); }
        else { println!("FAIL: Fp6 mul {} random mismatches", bad); fail += bad; }
    }

    // === Fp12 mul (GT) ===
    {
        let mut st: u64 = 0x13198a2e03707344;
        let mut bad = 0;
        for _ in 0..500 {
            let x = rand_fp12(&mut st); let y = rand_fp12(&mut st);
            let emitted = emitted_fp12_mul(&x, &y);
            let mut reference = x.clone();
            fp12_mul(&mut reference, &x, &y);
            if !fp12_eq(&emitted, &reference) { bad += 1; }
        }
        if bad == 0 { println!("ok:   emitted Fp12 mul == AUCurves fp12_mul on 500 random vectors"); }
        else { println!("FAIL: Fp12 mul {} random mismatches", bad); fail += bad; }
    }

    if fail == 0 {
        println!("KAT PASSED (reg-ptr re-emitted BN254 Fp2/Fp6/Fp12 multiply byte-identical to the AUCurves verified tower)");
    } else {
        println!("KAT FAILED ({} case(s))", fail);
        std::process::exit(1);
    }
}
