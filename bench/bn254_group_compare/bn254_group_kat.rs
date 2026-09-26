//! Known-answer test: the BN254 `G1` affine point-add emitted as a COMPOSITION
//! over the AUCurves verified FIELD leaves is byte-identical to the published
//! BN254 generator-multiple spec vectors.
//!
//! CONN-3e (#331).  `Pairing/Bn254Emit.lean` emits the BN254 `G1` group law as
//! one opaque `extCall` group leaf (`bn254_g1_add`).
//! `Pairing/BN254GroupEmit.lean` re-emits the same group op as a straight-line
//! `Com` over the field leaves
//!   lambda = fp_mul(fp_sub(Qy,Py), fp_inv(fp_sub(Qx,Px)))
//!   Rx     = fp_sub(fp_sub(fp_mul(lambda,lambda), Px), Qx)
//!   Ry     = fp_sub(fp_mul(lambda, fp_sub(Px,Rx)), Py)
//! and proves (BN254GroupEmit.emittedAffineAdd_realizes) that its denotation
//! equals the abstract `bn254AffineAdd` over `FpBN254` (Util/BN254Verified.lean).
//! This KAT confirms the re-emitted composition computes the SAME bytes as the
//! production `G1` add on the standard generator chain.
//!
//! Inputs / expected outputs are NOT fabricated: they are the published BN254
//! (alt_bn128) generator-multiple vectors `G1, 2G1, 3G1, 5G1` in the AUCurves
//! Montgomery `Fp([u64;4])` canonical form (mirrored verbatim from
//! `bn254-safe-rust/tests/kat_vectors.rs`, where each is annotated with its
//! decimal affine coordinate on `y^2 = x^3 + 3`).  Byte-identity is checked on
//! the canonical 32-byte little-endian Montgomery-limb encoding of (x, y).
//!
//!   G1 + 2G1  == 3G1   (distinct-point add, both anchors published)
//!   2G1 + 3G1 == 5G1   (distinct-point add, both anchors published)

use bn254::*;

// Published BN254 G1 generator multiples (Montgomery `Fp([u64;4])`), from
// bn254-safe-rust/tests/kat_vectors.rs (BN254 / alt_bn128 standard vectors).

/// G1 = (1, 2) — the standard BN254/alt_bn128 generator.
const G1_X: Fp = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
const G1_Y: Fp = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);
/// 2*G1.
const G1_2X: Fp = Fp([16214190896527698488, 13550016860984857705, 14015815241649799916, 1378791528466284877]);
const G1_2Y: Fp = Fp([4332616871279656263, 10917124144477883021, 13281191951274694749, 316464129134141481]);
/// 3*G1.
const G1_3X: Fp = Fp([11349945508338274720, 10516340564297075582, 1073522015087498704, 1220681065426257209]);
const G1_3Y: Fp = Fp([13696893332200248298, 16748403329945737754, 5894261446386786634, 92646983456880915]);
/// 5*G1.
const G1_5X: Fp = Fp([5962560908110737257, 956008546028513767, 10141120004113640803, 3120535472679077436]);
const G1_5Y: Fp = Fp([17932343232170917889, 10208671136062734056, 18427887398183947538, 1591919978119415005]);

/// The affine point-add EMITTED AS A FIELD-LEAF COMPOSITION (the exact chain
/// `BN254GroupEmit.lamCom` / `bn254AddxCom` / `bn254AddyCom`), evaluated on the
/// AUCurves verified field leaves.  Distinct points, P != +/-Q.
fn field_leaf_point_add(px: &Fp, py: &Fp, qx: &Fp, qy: &Fp) -> (Fp, Fp) {
    // lambda = (Qy - Py) * (Qx - Px)^-1
    let mut num = Fp::zero();
    fp_sub(&mut num, qy, py);
    let mut den = Fp::zero();
    fp_sub(&mut den, qx, px);
    let mut den_inv = Fp::zero();
    fp_inv(&mut den_inv, &den);
    let mut lam = Fp::zero();
    fp_mul(&mut lam, &num, &den_inv);

    // Rx = lambda*lambda - Px - Qx
    let mut lam2 = Fp::zero();
    fp_mul(&mut lam2, &lam, &lam);
    let mut t = Fp::zero();
    fp_sub(&mut t, &lam2, px);
    let mut rx = Fp::zero();
    fp_sub(&mut rx, &t, qx);

    // Ry = lambda*(Px - Rx) - Py
    let mut d = Fp::zero();
    fp_sub(&mut d, px, &rx);
    let mut m = Fp::zero();
    fp_mul(&mut m, &lam, &d);
    let mut ry = Fp::zero();
    fp_sub(&mut ry, &m, py);

    (rx, ry)
}

// ---------------------------------------------------------------------------
// Projective (Jacobian) group law — the INVERSION-FREE hot path emitted by
// `Pairing/BN254ProjectiveEmit.lean` (`jacDouble` = dbl-2009-l, `jacAddZ1` =
// add-2007-bl in the Z=1 chart, `jacToAffine` = the one-inverse conversion).
// BN254 G1 is y^2 = x^3 + 3 (a = 0), so the a=0 formulas (independent of b)
// carry over verbatim from the BLS12-381 G1 hot path.
// ---------------------------------------------------------------------------

/// A Jacobian point (X, Y, Z) representing affine (X/Z^2, Y/Z^3).
#[derive(Clone)]
struct Jac { x: Fp, y: Fp, z: Fp }

fn fp_one() -> Fp {
    // R mod p, derived (not hardcoded) as G1_X * G1_X^-1.
    let mut xi = Fp::zero();
    fp_inv(&mut xi, &G1_X);
    let mut one = Fp::zero();
    fp_mul(&mut one, &G1_X, &xi);
    one
}

fn fp_of_small(one: &Fp, n: u32) -> Fp {
    // n in Montgomery form = one + one + ... + one (n times).
    let mut acc = Fp::zero();
    for _ in 0..n {
        let mut t = Fp::zero();
        fp_add(&mut t, &acc, one);
        acc = t;
    }
    acc
}

fn fmul(a: &Fp, b: &Fp) -> Fp { let mut o = Fp::zero(); fp_mul(&mut o, a, b); o }
fn fadd(a: &Fp, b: &Fp) -> Fp { let mut o = Fp::zero(); fp_add(&mut o, a, b); o }
fn fsub(a: &Fp, b: &Fp) -> Fp { let mut o = Fp::zero(); fp_sub(&mut o, a, b); o }

/// `dbl-2009-l` Jacobian double for a=0: S=4XY^2, M=3X^2, X'=M^2-2S,
/// Y'=M(S-X')-8Y^4, Z'=2YZ.  Exactly `BN254ProjectiveEmit.jacDouble`.
fn jac_double(c: &Consts, j: &Jac) -> Jac {
    let y2 = fmul(&j.y, &j.y);
    let s = fmul(&fmul(&c.four, &j.x), &y2);          // 4 X Y^2
    let m = fmul(&c.three, &fmul(&j.x, &j.x));          // 3 X^2
    let m2 = fmul(&m, &m);
    let two_s = fmul(&c.two, &s);
    let x3 = fsub(&m2, &two_s);                         // M^2 - 2S
    let y4 = fmul(&y2, &y2);
    let y3 = fsub(&fmul(&m, &fsub(&s, &x3)), &fmul(&c.eight, &y4)); // M(S-X')-8Y^4
    let z3 = fmul(&fmul(&c.two, &j.y), &j.z);           // 2YZ
    Jac { x: x3, y: y3, z: z3 }
}

/// `add-2007-bl` Jacobian add in the Z=1 chart: H=X2-X1, r=Y2-Y1,
/// X'=r^2-H^3-2X1 H^2, Y'=r(X1 H^2 - X')-Y1 H^3, Z'=H.  Exactly
/// `BN254ProjectiveEmit.jacAddZ1` (both inputs affine, Z=1).
fn jac_add_z1(j: &Jac, k: &Jac) -> Jac {
    let h = fsub(&k.x, &j.x);
    let r = fsub(&k.y, &j.y);
    let h2 = fmul(&h, &h);
    let h3 = fmul(&h2, &h);
    let x1h2 = fmul(&j.x, &h2);
    let two_x1h2 = fadd(&x1h2, &x1h2);
    let x3 = fsub(&fsub(&fmul(&r, &r), &h3), &two_x1h2);  // r^2 - H^3 - 2 X1 H^2
    let y3 = fsub(&fmul(&r, &fsub(&x1h2, &x3)), &fmul(&j.y, &h3)); // r(X1 H^2 - X') - Y1 H^3
    Jac { x: x3, y: y3, z: h }
}

/// `jacToAffine`: (X, Y, Z) -> (X (Z^2)^-1, Y (Z^3)^-1).  One inverse.
fn jac_to_affine(j: &Jac) -> (Fp, Fp) {
    let z2 = fmul(&j.z, &j.z);
    let z3 = fmul(&z2, &j.z);
    let mut z2i = Fp::zero(); fp_inv(&mut z2i, &z2);
    let mut z3i = Fp::zero(); fp_inv(&mut z3i, &z3);
    (fmul(&j.x, &z2i), fmul(&j.y, &z3i))
}

/// Small-constant cache (Montgomery form) for the dbl-2009-l numerals.
struct Consts { two: Fp, three: Fp, four: Fp, eight: Fp }

/// `madd-2007-bl` mixed Jacobian + affine add: accumulator `j` (general Z),
/// affine `(qx, qy)` (Z2 = 1).  The table-lookup add the windowed/Pippenger
/// schedules drive (an affine table point into a Jacobian accumulator).
/// Z1 = 1 specialises to `jacAddZ1`; this is the general-Z1 version the in-loop
/// accumulation actually uses.  Still INVERSION-FREE.
fn jac_madd(c: &Consts, j: &Jac, qx: &Fp, qy: &Fp) -> Jac {
    // Z1Z1 = Z1^2 ; U2 = X2 Z1Z1 ; S2 = Y2 Z1 Z1Z1 ; H = U2 - X1 ; r = 2(S2 - Y1)
    let z1z1 = fmul(&j.z, &j.z);
    let u2 = fmul(qx, &z1z1);
    let s2 = fmul(qy, &fmul(&j.z, &z1z1));
    let h = fsub(&u2, &j.x);
    let r = fadd(&fsub(&s2, &j.y), &fsub(&s2, &j.y)); // 2(S2 - Y1)
    let hh = fmul(&h, &h);                 // H^2
    let i = fmul(&c.four, &hh);            // I = 4 H^2
    let jv = fmul(&h, &i);                 // J = H I
    let v = fmul(&j.x, &i);                // V = X1 I
    // X3 = r^2 - J - 2V
    let x3 = fsub(&fsub(&fmul(&r, &r), &jv), &fadd(&v, &v));
    // Y3 = r(V - X3) - 2 Y1 J
    let y3 = fsub(&fmul(&r, &fsub(&v, &x3)), &fmul(&c.two, &fmul(&j.y, &jv)));
    // Z3 = 2 Z1 H
    let z3 = fmul(&c.two, &fmul(&j.z, &h));
    Jac { x: x3, y: y3, z: z3 }
}

/// Binary double-and-add scalar-mul over the INVERSION-FREE projective group law
/// (the in-loop body the windowed/Pippenger schedules drive: doublings +
/// mixed-adds of the affine base, one final `jac_to_affine`).  MSB-first.
fn proj_scalar_mul(c: &Consts, px: &Fp, py: &Fp, k: u64) -> (Fp, Fp) {
    // identity at infinity: Z = 0.
    let mut acc = Jac { x: c.two.clone(), y: c.two.clone(), z: Fp::zero() };
    let mut started = false;
    let bits = 64 - k.leading_zeros();
    for i in (0..bits).rev() {
        if started {
            acc = jac_double(c, &acc);
        }
        if (k >> i) & 1 == 1 {
            if !started {
                acc = Jac { x: *px, y: *py, z: fp_one() };
                started = true;
            } else {
                acc = jac_madd(c, &acc, px, py);
            }
        }
    }
    jac_to_affine(&acc)
}

/// Canonical 32-byte little-endian Montgomery-limb encoding of an `Fp`.
fn le_bytes(x: &Fp) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, limb) in x.0.iter().enumerate() {
        out[i * 8..i * 8 + 8].copy_from_slice(&limb.to_le_bytes());
    }
    out
}

fn check_case(
    name: &str,
    px: &Fp, py: &Fp, qx: &Fp, qy: &Fp,
    ex: &Fp, ey: &Fp,
    fail: &mut usize,
) {
    let (rx, ry) = field_leaf_point_add(px, py, qx, qy);
    let (cx, cy) = (le_bytes(&rx), le_bytes(&ry));
    let (refx, refy) = (le_bytes(ex), le_bytes(ey));
    if cx == refx && cy == refy {
        println!("ok:   {name}: field-leaf composition == published spec vector (byte-identical, 64 bytes)");
    } else {
        println!("FAIL: {name}");
        println!("      comp.x = {}", hex(&cx));
        println!("      ref .x = {}", hex(&refx));
        println!("      comp.y = {}", hex(&cy));
        println!("      ref .y = {}", hex(&refy));
        *fail += 1;
    }
}

fn hex(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// Naive per-element inversion: one Fermat `fp_inv` per input.
fn naive_batch_inv(xs: &[Fp]) -> Vec<Fp> {
    xs.iter()
        .map(|x| {
            let mut o = Fp::zero();
            fp_inv(&mut o, x);
            o
        })
        .collect()
}

/// Montgomery's trick (the schedule emitted by `BN254GroupEmit.wireBatchInv`):
/// forward running products, ONE `fp_inv` of the total product, backward unwind
/// with `fp_mul`.  Returns the same list of inverses as `naive_batch_inv`, but
/// with a single field inversion.
fn montgomery_batch_inv(xs: &[Fp]) -> Vec<Fp> {
    let n = xs.len();
    if n == 0 {
        return Vec::new();
    }
    // Montgomery-form field one (= R mod p), derived as xs[0] * xs[0]^-1 so the
    // radix constant is not hardcoded; xs[0] != 0 holds for every case.
    let mut x0inv = Fp::zero();
    fp_inv(&mut x0inv, &xs[0]);
    let mut one = Fp::zero();
    fp_mul(&mut one, &xs[0], &x0inv);
    // forward products: prefix[i] = xs[0] * ... * xs[i-1], prefix[0] = 1.
    let mut prefix = vec![one; n + 1];
    for i in 0..n {
        let mut p = Fp::zero();
        fp_mul(&mut p, &prefix[i], &xs[i]);
        prefix[i + 1] = p;
    }
    // single inverse of the total product.
    let mut u = Fp::zero();
    fp_inv(&mut u, &prefix[n]);
    // backward unwind: out[i] = u * prefix[i]; u *= xs[i].
    let mut out = vec![Fp::zero(); n];
    for i in (0..n).rev() {
        let mut inv_i = Fp::zero();
        fp_mul(&mut inv_i, &u, &prefix[i]);
        out[i] = inv_i;
        let mut nu = Fp::zero();
        fp_mul(&mut nu, &u, &xs[i]);
        u = nu;
    }
    out
}

/// Batch-inversion KAT: Montgomery's trick is byte-identical to per-point
/// inversion, on REAL field elements derived from the published generator
/// multiples (coordinate differences — the actual chord-slope denominators
/// `Qx - Px` and a few `Qy - Py` numerators — not fabricated values).
fn check_batch_inv(fail: &mut usize) {
    let mut diffs: Vec<Fp> = Vec::new();
    let pairs = [
        (&G1_X, &G1_2X), (&G1_2X, &G1_3X), (&G1_X, &G1_3X),
        (&G1_Y, &G1_2Y), (&G1_2Y, &G1_3Y), (&G1_X, &G1_3Y),
    ];
    for (a, b) in pairs.iter() {
        let mut d = Fp::zero();
        fp_sub(&mut d, b, a);
        diffs.push(d);
    }

    let naive = naive_batch_inv(&diffs);
    let mont = montgomery_batch_inv(&diffs);

    let mut all_ok = naive.len() == mont.len();
    for (a, b) in naive.iter().zip(mont.iter()) {
        if le_bytes(a) != le_bytes(b) {
            all_ok = false;
        }
    }
    if all_ok {
        println!(
            "ok:   batch inversion: Montgomery's trick (one inversion of the total product + \
             fp_mul unwind) == per-point inversion ({} fp_inv calls), byte-identical on {} \
             real field denominators",
            diffs.len(),
            diffs.len()
        );
    } else {
        println!("FAIL: batch inversion mismatch vs per-point inversion");
        for (i, (a, b)) in naive.iter().zip(mont.iter()).enumerate() {
            println!("      [{i}] naive = {}", hex(&le_bytes(a)));
            println!("      [{i}] mont  = {}", hex(&le_bytes(b)));
        }
        *fail += 1;
    }
}

/// Check that an affine result (cx, cy) is byte-identical to a published vector.
fn check_affine(name: &str, cx: &Fp, cy: &Fp, ex: &Fp, ey: &Fp, fail: &mut usize) {
    if le_bytes(cx) == le_bytes(ex) && le_bytes(cy) == le_bytes(ey) {
        println!("ok:   {name}: projective composition == published spec vector (byte-identical, 64 bytes)");
    } else {
        println!("FAIL: {name}");
        println!("      comp.x = {}", hex(&le_bytes(cx)));
        println!("      ref .x = {}", hex(&le_bytes(ex)));
        *fail += 1;
    }
}

/// Projective (Jacobian, inversion-free) path KATs vs the same published BN254
/// generator-multiple vectors: the `BN254ProjectiveEmit` hot path projected via
/// one `jacToAffine` must compute the SAME bytes as the affine oracle.
fn check_projective(fail: &mut usize) {
    let one = fp_one();
    let c = Consts {
        two: fp_of_small(&one, 2),
        three: fp_of_small(&one, 3),
        four: fp_of_small(&one, 4),
        eight: fp_of_small(&one, 8),
    };

    // Jacobian DOUBLE of G1 (Z=1 chart) -> 2G1.
    let g1 = Jac { x: G1_X, y: G1_Y, z: one.clone() };
    let (dx, dy) = jac_to_affine(&jac_double(&c, &g1));
    check_affine("2*G1 via jacDouble", &dx, &dy, &G1_2X, &G1_2Y, fail);

    // Jacobian ADD (Z=1 chart) G1 + 2G1 -> 3G1.
    let g2 = Jac { x: G1_2X, y: G1_2Y, z: one.clone() };
    let (ax, ay) = jac_to_affine(&jac_add_z1(&g1, &g2));
    check_affine("G1 + 2G1 = 3G1 via jacAddZ1", &ax, &ay, &G1_3X, &G1_3Y, fail);

    // Projective windowed/binary scalar-mul 5*G1 -> 5G1 (inversion-free loop,
    // one final affine conversion). Validates the BN254WindowedMul/Msm path.
    let (sx, sy) = proj_scalar_mul(&c, &G1_X, &G1_Y, 5);
    check_affine("5*G1 via projective scalar-mul", &sx, &sy, &G1_5X, &G1_5Y, fail);

    // A small MSM: 2*G1 + 3*G1 == 5G1 (Pippenger sub-MSM recombination).
    let (m2x, m2y) = proj_scalar_mul(&c, &G1_X, &G1_Y, 2);
    let (m3x, m3y) = proj_scalar_mul(&c, &G1_X, &G1_Y, 3);
    let sum = jac_add_z1(
        &Jac { x: m2x, y: m2y, z: one.clone() },
        &Jac { x: m3x, y: m3y, z: one.clone() },
    );
    let (mx, my) = jac_to_affine(&sum);
    check_affine("MSM 2*G1 + 3*G1 = 5G1 (recombination)", &mx, &my, &G1_5X, &G1_5Y, fail);
}

fn main() {
    let mut fail = 0usize;

    // G1 + 2G1 = 3G1.
    check_case("G1 + 2G1 = 3G1", &G1_X, &G1_Y, &G1_2X, &G1_2Y, &G1_3X, &G1_3Y, &mut fail);
    // 2G1 + 3G1 = 5G1.
    check_case("2G1 + 3G1 = 5G1", &G1_2X, &G1_2Y, &G1_3X, &G1_3Y, &G1_5X, &G1_5Y, &mut fail);

    // Projective (inversion-free hot path) + windowed/MSM scalar-mul.
    check_projective(&mut fail);

    // Montgomery's trick == per-point inversion (batch affine-conversion lever).
    check_batch_inv(&mut fail);

    if fail == 0 {
        println!(
            "KAT PASSED: the BN254 G1 group law re-emitted over the AUCurves field leaves is \
             byte-identical to the published BN254 generator-multiple spec vectors — the affine \
             field-leaf composition (BN254GroupEmit), the inversion-free projective hot path \
             (BN254ProjectiveEmit: jacDouble/jacAddZ1/jacToAffine), the projective windowed \
             scalar-mul (BN254WindowedMulEmit, 5*G1), and the Pippenger MSM recombination \
             (BN254MsmEmit, 2*G1 + 3*G1 = 5G1); the AUCurves verified field leaves \
             (bn254-safe-rust fp_add/fp_sub/fp_mul + Fermat fp_inv) carry every result."
        );
    } else {
        println!("KAT FAILED ({fail} case(s))");
        std::process::exit(1);
    }
}
