//! KAT (#222): the OWNED front-emitted BN254 Fp2 tower leaves, byte-identical
//! to the AUCurves verified-bedrock2 Rust tower on published EIP-197 vectors.
//!
//! The j_bn254_Fp2_* leaves are front-compiled and rendered through CatCrypt's
//! own x86 backend (Bn254TowerFrontEmit.lean: LowCT carry-chain bodies ->
//! translateDialectControl -> Com catCryptDialect -> cryptoDialectToJasminCom
//! -> Com.toLprogPhysAbi -> renderLprogAtt; no jasminc, no hand Com/Lcmd).
//! The Rust `tower::bn254_Fp2_*` reference is the AUCurves verified-bedrock2
//! pretty-print; this KAT confirms the owned leaves agree byte-for-byte with
//! it on real inputs. No fabricated vectors: the inputs are the published
//! BN254 G2 generator coordinates (EIP-197), in Montgomery form.

use bn254::tower::{self, Fp, Fp2};

// owned tower exports (u64 byte-pointer ABI: out, x, y over 64-byte Fp2),
// named j_* to avoid colliding with tower::bn254_Fp2_*.
unsafe extern "C" {
    fn j_bn254_Fp2_add(out: *mut u64, x: *const u64, y: *const u64);
    fn j_bn254_Fp2_sub(out: *mut u64, x: *const u64, y: *const u64);
    fn j_bn254_Fp2_felem_copy(out: *mut u64, x: *const u64);
}

// Published BN254 G2 generator (Montgomery form) — the EIP-197 anchor.
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

fn as_bytes(a: &Fp2) -> [u64; 8] {
    let mut o = [0u64; 8];
    o[..4].copy_from_slice(&a.c0.0);
    o[4..].copy_from_slice(&a.c1.0);
    o
}

fn owned_fp2_add(x: &Fp2, y: &Fp2) -> Fp2 {
    let (xb, yb) = (as_bytes(x), as_bytes(y));
    let mut ob = [0u64; 8];
    unsafe { j_bn254_Fp2_add(ob.as_mut_ptr(), xb.as_ptr(), yb.as_ptr()); }
    Fp2 { c0: Fp([ob[0], ob[1], ob[2], ob[3]]), c1: Fp([ob[4], ob[5], ob[6], ob[7]]) }
}
fn owned_fp2_sub(x: &Fp2, y: &Fp2) -> Fp2 {
    let (xb, yb) = (as_bytes(x), as_bytes(y));
    let mut ob = [0u64; 8];
    unsafe { j_bn254_Fp2_sub(ob.as_mut_ptr(), xb.as_ptr(), yb.as_ptr()); }
    Fp2 { c0: Fp([ob[0], ob[1], ob[2], ob[3]]), c1: Fp([ob[4], ob[5], ob[6], ob[7]]) }
}
fn owned_fp2_copy(x: &Fp2) -> Fp2 {
    let xb = as_bytes(x);
    let mut ob = [0u64; 8];
    unsafe { j_bn254_Fp2_felem_copy(ob.as_mut_ptr(), xb.as_ptr()); }
    Fp2 { c0: Fp([ob[0], ob[1], ob[2], ob[3]]), c1: Fp([ob[4], ob[5], ob[6], ob[7]]) }
}

fn main() {
    let (qx, qy) = g2_gen();
    let mut fails = 0u32;

    // 1. Fp2_add: owned vs Rust tower, byte-for-byte.
    let mut r_add = Fp2::zero();
    tower::bn254_Fp2_add(&mut r_add, &qx, &qy);
    let j_add = owned_fp2_add(&qx, &qy);
    if as_bytes(&j_add) == as_bytes(&r_add) {
        println!("PASS Fp2_add  (Qx + Qy): owned == Rust tower (byte-identical)");
    } else {
        println!("FAIL Fp2_add: owned {:?} != Rust {:?}", as_bytes(&j_add), as_bytes(&r_add));
        fails += 1;
    }

    // 2. Fp2_sub: owned vs Rust tower.
    let mut r_sub = Fp2::zero();
    tower::bn254_Fp2_sub(&mut r_sub, &qx, &qy);
    let j_sub = owned_fp2_sub(&qx, &qy);
    if as_bytes(&j_sub) == as_bytes(&r_sub) {
        println!("PASS Fp2_sub  (Qx - Qy): owned == Rust tower (byte-identical)");
    } else {
        println!("FAIL Fp2_sub: owned {:?} != Rust {:?}", as_bytes(&j_sub), as_bytes(&r_sub));
        fails += 1;
    }

    // 3. Fp2_felem_copy: owned vs Rust tower.
    let mut r_cp = Fp2::zero();
    tower::bn254_Fp2_felem_copy(&mut r_cp, &qx);
    let j_cp = owned_fp2_copy(&qx);
    if as_bytes(&j_cp) == as_bytes(&r_cp) && as_bytes(&j_cp) == as_bytes(&qx) {
        println!("PASS Fp2_copy (Qx):      owned == Rust tower == Qx (byte-identical)");
    } else {
        println!("FAIL Fp2_copy: owned {:?} != Rust {:?}", as_bytes(&j_cp), as_bytes(&r_cp));
        fails += 1;
    }

    // 4. additive round-trip on the generator: (Qx + Qy) - Qy == Qx, via the owned leaves only.
    let s = owned_fp2_add(&qx, &qy);
    let back = owned_fp2_sub(&s, &qy);
    if as_bytes(&back) == as_bytes(&qx) {
        println!("PASS Fp2 add/sub round-trip (owned): (Qx+Qy)-Qy == Qx");
    } else {
        println!("FAIL Fp2 round-trip: {:?} != {:?}", as_bytes(&back), as_bytes(&qx));
        fails += 1;
    }

    if fails == 0 {
        println!("\nKAT OK: owned front-emitted BN254 Fp2 leaves are byte-identical to the Rust tower.");
    } else {
        eprintln!("\nKAT FAILED: {fails} mismatch(es).");
        std::process::exit(1);
    }
}
