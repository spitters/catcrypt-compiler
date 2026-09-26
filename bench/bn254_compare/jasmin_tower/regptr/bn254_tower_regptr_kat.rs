//! KAT (#227): the reg-ptr-emitted BN254 tower subset, byte-identical to the
//! Rust tower on published EIP-197 vectors.
//!
//! The reg-ptr tower is emitted by AUCurves `ExtractBN254TowerJasmin.v` via the
//! verified `tr_func_sized 4` / `pp_module_regptr` path — the SAME jasmin_func
//! AST that `pp_module` (the #222 baseline) renders, re-rendered under the
//! `reg ptr u64[N]` convention. So `j_bn254_Fp2_felem_copy` and the Rust
//! `tower::bn254_Fp2_felem_copy` are two pretty-prints of one verified bedrock2
//! program (the reg-ptr emit is faithful by `pp_module_regptr_same_inputs` +
//! `tr_cmd_correct`).
//!
//! Scope of the byte-identity check: the reg-ptr `.jazz` links STRUCTURAL leaf
//! stubs (the `inline fn bn254_add/mul/...` in the emitted module are copy
//! shells, not the verified Montgomery arithmetic — the real leaves use the
//! reg-u64 mem-pointer convention and cannot be passed a reg-ptr argument
//! without a #219 reg-ptr leaf re-emit, which is out of #227 scope). The one
//! leaf whose stub realises its TRUE semantics is `bn254_felem_copy` (copy
//! a -> o), so the reg-ptr `Fp2_felem_copy` is genuinely byte-identical to the
//! Rust tower's copy. That is the byte-exact assertion here. Fp2_mul/add/sub
//! byte-identity needs the reg-ptr verified leaves; this KAT does NOT fabricate
//! those vectors. The #227 advance over #222 is that Fp2_mul/square/inv now
//! COMPILE to x86-64 at all (see `make structural-check`).
//!
//! No fabricated vectors: the input is the published BN254 G2 generator
//! coordinate (EIP-197), in Montgomery form.

use bn254::tower::{self, Fp, Fp2};

unsafe extern "C" {
    // reg ptr u64[8] out, reg const ptr u64[8] x — same C pointer ABI as reg u64.
    fn j_bn254_Fp2_felem_copy(out: *mut u64, x: *const u64) -> *mut u64;
}

// Published BN254 G2 generator x-coordinate (Montgomery form) — EIP-197 anchor.
fn g2_gen_x() -> Fp2 {
    Fp2 {
        c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
        c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]),
    }
}

fn as_bytes(a: &Fp2) -> [u64; 8] {
    let mut o = [0u64; 8];
    o[..4].copy_from_slice(&a.c0.0);
    o[4..].copy_from_slice(&a.c1.0);
    o
}

fn jasmin_fp2_copy(x: &Fp2) -> Fp2 {
    let xb = as_bytes(x);
    let mut ob = [0u64; 8];
    unsafe { j_bn254_Fp2_felem_copy(ob.as_mut_ptr(), xb.as_ptr()); }
    Fp2 { c0: Fp([ob[0], ob[1], ob[2], ob[3]]), c1: Fp([ob[4], ob[5], ob[6], ob[7]]) }
}

fn main() {
    let qx = g2_gen_x();
    let mut fails = 0u32;

    // reg-ptr Fp2_felem_copy vs Rust tower, byte-for-byte.
    let mut r_cp = Fp2::zero();
    tower::bn254_Fp2_felem_copy(&mut r_cp, &qx);
    let j_cp = jasmin_fp2_copy(&qx);
    if as_bytes(&j_cp) == as_bytes(&r_cp) && as_bytes(&j_cp) == as_bytes(&qx) {
        println!("PASS Fp2_copy (Qx): reg-ptr jasmin == Rust tower == Qx (byte-identical)");
    } else {
        println!("FAIL Fp2_copy: jasmin {:?} != Rust {:?}", as_bytes(&j_cp), as_bytes(&r_cp));
        fails += 1;
    }

    if fails == 0 {
        println!("\nKAT OK: reg-ptr-emitted BN254 Fp2_felem_copy is byte-identical to the Rust tower.");
        println!("(Fp2_mul/square/inv now COMPILE under the reg-ptr path — a #222 type error;");
        println!(" their byte-identity KAT awaits reg-ptr verified leaves, out of #227 scope.)");
    } else {
        eprintln!("\nKAT FAILED: {fails} mismatch(es).");
        std::process::exit(1);
    }
}
