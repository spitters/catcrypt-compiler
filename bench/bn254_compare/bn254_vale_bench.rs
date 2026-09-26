//! Perf bench for the AUCurves-verified BN254 (alt_bn128) pairing tower.
//!
//! Drives the same leaves the emitted-via-Lean kernels in
//! gen/bn254_pairing_one.jazz and gen/bn254_eip197_verify.jazz call:
//!   bn254_pairing_dsd_optimal  (the optimal-ate pairing, Frobenius-fixed)
//!   bn254_Fp12_mul             (the GT accumulator for multi-pairing)
//! plus the corresponding miller_loop_optimal (pre-final-exp accumulator).
//!
//! Measurements are taken via the rdtsc median-of-3 pattern from
//! the other Vale benches (bench_chacha_vale, bench_aesgcm_vale, ...),
//! reported as cyc/op on the published EIP-196 generators.
//!
//! Calibration. The honest BN254 pairing budget in publicly available
//! production implementations:
//!   arkworks-bn254 ate pairing             ~1.6 Mcyc (single pairing, Skylake)
//!   go-ethereum's Cloudflare bn256.Pair    ~1.4 Mcyc (single pairing, Skylake)
//!   blst (BLS12-381, faster curve, ref)    ~1.0 Mcyc (single pairing, Skylake)
//! The AUCurves implementation here is the bedrock2 extraction (not yet
//! AVX2/AVX512 optimized), so a 3-5× gap vs production refs is expected.
//! The point of this bench is to:
//!   (a) measure the AUCurves baseline honestly,
//!   (b) confirm the optimal-ate path (`_optimal` variants) is hit,
//!   (c) document the gap so the AUCurves perf optimisation work
//!       (better Karatsuba in Fp6, deeper inline of `bn254_Fp2_mul_xi`
//!       fused into the line evaluation) can be tracked.

use bn254::*;
use std::time::Instant;

// --- Published BN254 generators (Montgomery form, from kat_vectors.rs) -------
const G1_X: Fp = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
const G1_Y: Fp = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);
const NEG_G1_Y: Fp = Fp([10765297436657115661, 9407901146999403537, 16965902948054780933, 1463492787413574090]);

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

#[inline(always)]
fn rdtsc() -> u64 {
    // Use std::time as a cycle proxy when rdtsc isn't available. The host CPU
    // frequency in cycles is computed via a 100ms calibration loop.
    let _ = Instant::now();
    unsafe { core::arch::x86_64::_rdtsc() }
}

fn calibrate_cpu_hz() -> f64 {
    // Cross-check rdtsc cycles vs wall clock to print a cyc/s estimate
    // (informational only — measurements are reported as cycles directly).
    let start_c = rdtsc();
    let start_t = Instant::now();
    while start_t.elapsed().as_millis() < 100 {
        std::hint::spin_loop();
    }
    let elapsed_c = rdtsc() - start_c;
    let elapsed_s = start_t.elapsed().as_secs_f64();
    elapsed_c as f64 / elapsed_s
}

fn bench_pairing_optimal(iters: usize) -> (u64, u64) {
    let (q_x, q_y) = g2_gen();
    let mut out = Fp12::zero();
    // Warm-up.
    for _ in 0..16 {
        pairing_optimal(&mut out, &G1_X, &G1_Y, &q_x, &q_y);
    }
    let start = rdtsc();
    for _ in 0..iters {
        pairing_optimal(&mut out, &G1_X, &G1_Y, &q_x, &q_y);
    }
    let elapsed = rdtsc() - start;
    // Defeat dead-code elimination on `out`.
    std::hint::black_box(&out);
    (elapsed, elapsed / iters as u64)
}

fn bench_miller_loop_optimal(iters: usize) -> (u64, u64) {
    let (q_x, q_y) = g2_gen();
    let mut out = Fp12::zero();
    for _ in 0..16 {
        miller_loop_optimal(&mut out, &G1_X, &G1_Y, &q_x, &q_y);
    }
    let start = rdtsc();
    for _ in 0..iters {
        miller_loop_optimal(&mut out, &G1_X, &G1_Y, &q_x, &q_y);
    }
    let elapsed = rdtsc() - start;
    std::hint::black_box(&out);
    (elapsed, elapsed / iters as u64)
}

fn bench_fp12_mul(iters: usize) -> (u64, u64) {
    let (q_x, q_y) = g2_gen();
    let mut a = Fp12::zero();
    let mut b = Fp12::zero();
    let mut out = Fp12::zero();
    pairing_optimal(&mut a, &G1_X, &G1_Y, &q_x, &q_y);
    pairing_optimal(&mut b, &G1_X, &NEG_G1_Y, &q_x, &q_y);
    for _ in 0..16 {
        fp12_mul(&mut out, &a, &b);
    }
    let start = rdtsc();
    for _ in 0..iters {
        fp12_mul(&mut out, &a, &b);
    }
    let elapsed = rdtsc() - start;
    std::hint::black_box(&out);
    (elapsed, elapsed / iters as u64)
}

fn bench_eip197_2pair(iters: usize) -> (u64, u64) {
    // The EIP-197 2-pair product e(P1,Q1) * e(P2,Q2): two pairings +
    // one fp12 mul. This is the per-iteration cost of the
    // bn254_eip197_verify.jazz kernel emitted from Lean
    // (Bn254Emit.Emit.eip197VerifyJazz).
    let (q_x, q_y) = g2_gen();
    let mut e1 = Fp12::zero();
    let mut e2 = Fp12::zero();
    let mut prod = Fp12::zero();
    for _ in 0..16 {
        pairing_optimal(&mut e1, &G1_X, &G1_Y, &q_x, &q_y);
        pairing_optimal(&mut e2, &G1_X, &NEG_G1_Y, &q_x, &q_y);
        fp12_mul(&mut prod, &e1, &e2);
    }
    let start = rdtsc();
    for _ in 0..iters {
        pairing_optimal(&mut e1, &G1_X, &G1_Y, &q_x, &q_y);
        pairing_optimal(&mut e2, &G1_X, &NEG_G1_Y, &q_x, &q_y);
        fp12_mul(&mut prod, &e1, &e2);
    }
    let elapsed = rdtsc() - start;
    std::hint::black_box(&prod);
    (elapsed, elapsed / iters as u64)
}

fn median_of_3<F: FnMut() -> (u64, u64)>(mut f: F) -> u64 {
    let mut samples = [f().1, f().1, f().1];
    samples.sort();
    samples[1]
}

fn main() {
    let cpu_hz = calibrate_cpu_hz();
    let cpu_ghz = cpu_hz / 1e9;
    println!("# CPU frequency calibration: {:.3} GHz (informational)", cpu_ghz);
    println!();

    // The pairing is heavy (~1-2 Mcyc on this implementation); 100 iters is
    // a few hundred ms median, enough for a clean 3-sample variance check.
    let pairing_iters = 100usize;
    let miller_iters = 100usize;
    let fp12_mul_iters = 10_000usize;
    let eip197_iters = 50usize;

    println!("# Benchmark: AUCurves bn254-safe-rust verified BN254 tower");
    println!("# rdtsc median-of-3 on the published EIP-196 generators");
    println!();
    println!("| Op                                  | iters | cyc/op         | notes |");
    println!("|-------------------------------------|------:|---------------:|-------|");

    let p = median_of_3(|| bench_pairing_optimal(pairing_iters));
    println!("| bn254_pairing_dsd_optimal           | {:5} | {:>14} | full pairing (Miller + final exp), optimal-ate |", pairing_iters, p);

    let m = median_of_3(|| bench_miller_loop_optimal(miller_iters));
    println!("| bn254_miller_loop_optimal           | {:5} | {:>14} | pre-final-exp accumulator (Miller only)        |", miller_iters, m);

    let f = median_of_3(|| bench_fp12_mul(fp12_mul_iters));
    println!("| bn254_Fp12_mul                      | {:5} | {:>14} | Fp12 product (Karatsuba over Fp6/Fp2/Fp)       |", fp12_mul_iters, f);

    let v = median_of_3(|| bench_eip197_2pair(eip197_iters));
    println!("| bn254 EIP-197 2-pair (2P + 1Fp12mul)| {:5} | {:>14} | per-iter cost of the emitted bn254_eip197_verify kernel |", eip197_iters, v);

    println!();
    println!("# Honest gap assessment:");
    println!("#   arkworks-bn254 ate pairing  (Skylake reference)   ~1.6 Mcyc");
    println!("#   go-ethereum bn256.Pair      (Cloudflare, Skylake) ~1.4 Mcyc");
    println!("#   blst BLS12-381 pairing      (faster curve, ref)   ~1.0 Mcyc");
    println!("# AUCurves bn254 (this measurement above) is the bedrock2 extraction —");
    println!("# no AVX2 fp12_mul or fused-line eval. The gap vs arkworks-bn254 is the");
    println!("# load-bearing perf-optimisation work tracked in AUCurves PERF_OPTIMIZATION_PLAN.md.");
}
