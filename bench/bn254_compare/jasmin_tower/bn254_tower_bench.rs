//! Parity bench (#222): OWNED front-emitted BN254 Fp2 tower ops vs the Rust tower.
//!
//! The win in #222 is TRUST/composition, not speed; this confirms the owned
//! Fp2 ops are parity-or-close with the Rust tower. MIN-of-3 over the
//! rdtsc cycle counter; pin a core with `taskset -c <n>` (see Makefile $(PIN)).

use bn254::tower::{Fp, Fp2};
use std::arch::x86_64::_rdtsc;

unsafe extern "C" {
    fn j_bn254_Fp2_add(out: *mut u64, x: *const u64, y: *const u64);
}

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

const ITERS: u64 = 2_000_000;

fn main() {
    let (qx, qy) = g2_gen();
    let xb = as_bytes(&qx);
    let yb = as_bytes(&qy);

    // owned tower Fp2_add
    let mut owned = u64::MAX;
    for _ in 0..3 {
        let mut ob = [0u64; 8];
        let t0 = unsafe { _rdtsc() };
        for _ in 0..ITERS {
            unsafe { j_bn254_Fp2_add(ob.as_mut_ptr(), xb.as_ptr(), yb.as_ptr()); }
            std::hint::black_box(&ob);
        }
        let t1 = unsafe { _rdtsc() };
        owned = owned.min((t1 - t0) / ITERS);
    }

    // Rust tower Fp2_add
    let mut rust = u64::MAX;
    for _ in 0..3 {
        let mut out = Fp2::zero();
        let t0 = unsafe { _rdtsc() };
        for _ in 0..ITERS {
            bn254::tower::bn254_Fp2_add(&mut out, &qx, &qy);
            std::hint::black_box(&out);
        }
        let t1 = unsafe { _rdtsc() };
        rust = rust.min((t1 - t0) / ITERS);
    }

    println!("BN254 Fp2_add (MIN-of-3, cyc/op):");
    println!("  owned tower  : {owned}");
    println!("  Rust tower   : {rust}");
    println!("  ratio o/r    : {:.2}x", owned as f64 / rust as f64);
}
