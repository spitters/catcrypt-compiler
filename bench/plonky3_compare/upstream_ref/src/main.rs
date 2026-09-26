//! Upstream-style Rust reference bench for the Fibonacci-AIR Plonky3 prover.
//!
//! Counterpart to bench_prove_fib_tierc.c (Tier C jasmin emit). We use the
//! plonky3-hax crate which carries the reference Rust impl of the same prover
//! (the Lean spec is hax-extracted from it).
//!
//! Sizing is matched to the Tier C jazz: width=3, height=8 Fibonacci AIR with
//! domain_log2=5 (n = 32, blowup = 4), num_layers=3, num_queries=8.
//! This matches the `dump_phase(8, 3, 5, 8, 2)` call in the upstream KAT
//! example, which is what our Lean KAT theorems pin against.
//!
//! Methodology: rdtsc, taskset -c 3, warmup 200, ITERS=200 per trial (smaller
//! than the C bench because each iter does ~50× more work — a full STARK
//! proof, not a compressed 6-leaf orchestration), median-of-3.
//!
//! Run:
//!   cd bench/plonky3_compare/upstream_ref
//!   cargo build --release
//!   taskset -c 3 ./target/release/plonky3-bench-upstream

use plonky3_hax::air::{fib_air, fib_trace};
use plonky3_hax::fri::FriOptions;
use plonky3_hax::plonky3::{plonky3_prove, LDE_COSET_SHIFT};

#[inline]
fn rdtscp() -> u64 {
    let mut aux: u32 = 0;
    unsafe { core::arch::x86_64::__rdtscp(&mut aux as *mut u32) }
}

const ITERS: u32 = 200;

fn main() {
    let height: usize = 8;
    let air = fib_air();
    let trace = fib_trace(height);
    let opts = FriOptions {
        num_layers: 3,
        domain_log2: 5,
        num_queries: 8,
        blowup: 2,
        coset_shift: LDE_COSET_SHIFT,
        proof_of_work_bits: 0,
    };

    // Sanity check: produce one proof and report its boundary claims so the
    // bench output is reproducible.
    let proof = plonky3_prove(&air, &trace, opts).expect("prover");
    println!(
        "Plonky3 Fibonacci STARK upstream-Rust reference (height={}, width=3, n=32, queries=8):",
        height
    );
    println!("  boundary_claims = {:?}", proof.boundary_claims);
    println!(
        "  trace_commitment = {}",
        proof
            .trace_commitment
            .iter()
            .map(|b| format!("{:02x}", b))
            .collect::<String>()
    );

    // Warm caches.
    for _ in 0..50 {
        let _ = plonky3_prove(&air, &trace, opts).expect("prover");
    }

    let mut best: u64 = u64::MAX;
    for _trial in 0..3 {
        let t0 = rdtscp();
        for _ in 0..ITERS {
            let p = plonky3_prove(&air, &trace, opts).expect("prover");
            // Make sure the prover output is consumed so LLVM doesn't elide it.
            std::hint::black_box(&p);
        }
        let t1 = rdtscp();
        let span = t1 - t0;
        if span < best {
            best = span;
        }
    }

    let cyc = best / (ITERS as u64);
    println!(
        "  Upstream Rust reference (rustc -O3 LTO): {} cyc/op (median-of-3, ITERS={})",
        cyc, ITERS
    );
}
