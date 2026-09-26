//! Real upstream Plonky3 (`p3-*` 0.5.3) Fibonacci-AIR STARK prover reference.
//!
//! Counterpart to ../bench_prove_fib_tierc.c (the Jasmin Tier C emit). The AIR,
//! trace generator and the type aliases (BabyBear / Poseidon2-16 / Merkle MMCS /
//! TwoAdicFriPcs) are taken verbatim from the p3-uni-stark 0.5.3
//! `tests/fib_air.rs`, so this is the genuine upstream prover, not our hax
//! extraction.
//!
//! Circuit matched to the emitted prover:
//!   field   = BabyBear
//!   height  = 8  (1<<3)
//!   hash    = Poseidon2-BabyBear width 16
//!   FRI     = log_blowup 2 (blowup x4), num_queries 8
//!   pis     = [0, 1, 21]   (8th Fibonacci number is 21)
//!
//! Output:
//!   * KAT gate: prove -> verify must accept; a tampered public input must be
//!     rejected by verify.
//!   * Bench: rdtsc, min-of-3 trials, end-to-end `prove` time in cyc/op.
//!
//! Run (one core-pinned process at a time):
//!   cargo build --release
//!   taskset -c 3 ./target/release/p3-fib-ref

use core::borrow::Borrow;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{prove, verify, StarkConfig};
use rand::rngs::SmallRng;
use rand::SeedableRng;

// ---------------------------------------------------------------------------
// Fibonacci AIR (verbatim from p3-uni-stark 0.5.3 tests/fib_air.rs)
// ---------------------------------------------------------------------------

pub struct FibonacciAir {}

impl<F> BaseAir<F> for FibonacciAir {
    fn width(&self) -> usize {
        NUM_FIBONACCI_COLS
    }
    fn num_public_values(&self) -> usize {
        3
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }
}

impl<AB: AirBuilder> Air<AB> for FibonacciAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let pis = builder.public_values();
        let a = pis[0];
        let b = pis[1];
        let x = pis[2];

        let local: &FibonacciRow<AB::Var> = main.current_slice().borrow();
        let next: &FibonacciRow<AB::Var> = main.next_slice().borrow();

        let mut when_first_row = builder.when_first_row();
        when_first_row.assert_eq(local.left, a);
        when_first_row.assert_eq(local.right, b);

        let mut when_transition = builder.when_transition();
        when_transition.assert_eq(local.right, next.left);
        when_transition.assert_eq(local.left + local.right, next.right);

        builder.when_last_row().assert_eq(local.right, x);
    }
}

pub fn generate_trace_rows<F: PrimeField64>(a: u64, b: u64, n: usize) -> RowMajorMatrix<F> {
    assert!(n.is_power_of_two());
    let mut trace = RowMajorMatrix::new(F::zero_vec(n * NUM_FIBONACCI_COLS), NUM_FIBONACCI_COLS);
    let (prefix, rows, suffix) = unsafe { trace.values.align_to_mut::<FibonacciRow<F>>() };
    assert!(prefix.is_empty(), "Alignment should match");
    assert!(suffix.is_empty(), "Alignment should match");
    assert_eq!(rows.len(), n);
    rows[0] = FibonacciRow::new(F::from_u64(a), F::from_u64(b));
    for i in 1..n {
        rows[i].left = rows[i - 1].right;
        rows[i].right = rows[i - 1].left + rows[i - 1].right;
    }
    trace
}

const NUM_FIBONACCI_COLS: usize = 2;

pub struct FibonacciRow<F> {
    pub left: F,
    pub right: F,
}
impl<F> FibonacciRow<F> {
    const fn new(left: F, right: F) -> Self {
        Self { left, right }
    }
}
impl<F> Borrow<FibonacciRow<F>> for [F] {
    fn borrow(&self) -> &FibonacciRow<F> {
        debug_assert_eq!(self.len(), NUM_FIBONACCI_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to::<FibonacciRow<F>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &shorts[0]
    }
}

// ---------------------------------------------------------------------------
// Config: BabyBear / Poseidon2-16 / Merkle MMCS / TwoAdicFriPcs
// ---------------------------------------------------------------------------

type Val = BabyBear;
type Perm = Poseidon2BabyBear<16>;
type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
type ValMmcs =
    MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 2, 8>;
type Challenge = BinomialExtensionField<Val, 4>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
type Dft = Radix2DitParallel<Val>;
type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

/// FRI params matched to the emitted Tier C prover circuit:
/// log_blowup 2 (blowup x4), num_queries 8, height 8.
fn make_config() -> MyConfig {
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = FriParameters {
        log_blowup: 2,
        log_final_poly_len: 2,
        max_log_arity: 1,
        num_queries: 8,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(dft, val_mmcs, fri_params);
    let challenger = Challenger::new(perm);
    MyConfig::new(pcs, challenger)
}

#[inline]
fn rdtscp() -> u64 {
    let mut aux: u32 = 0;
    unsafe { core::arch::x86_64::__rdtscp(&mut aux as *mut u32) }
}

const HEIGHT: usize = 8;
const ITERS: u32 = 200;

fn main() {
    let config = make_config();
    let pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::from_u64(21)];

    println!(
        "Plonky3 Fibonacci STARK upstream-Rust reference (p3-* 0.5.3, height={}, width=2, blowup=4, queries=8):",
        HEIGHT
    );

    // ----- KAT gate: prove -> verify must accept -----
    let trace = generate_trace_rows::<Val>(0, 1, HEIGHT);
    let proof = prove(&config, &FibonacciAir {}, trace, &pis);
    match verify(&config, &FibonacciAir {}, &proof, &pis) {
        Ok(()) => println!("  KAT: verify ACCEPT on honest proof  [PASS]"),
        Err(e) => {
            println!("  KAT: verify REJECTED honest proof: {:?}  [FAIL]", e);
            std::process::exit(1);
        }
    }

    // ----- Soundness gate: tampered public input must be rejected -----
    let bad_pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::from_u64(22)];
    match verify(&config, &FibonacciAir {}, &proof, &bad_pis) {
        Err(_) => println!("  KAT: verify REJECT on tampered public input  [PASS]"),
        Ok(()) => {
            println!("  KAT: verify ACCEPTED tampered public input  [FAIL]");
            std::process::exit(1);
        }
    }

    // ----- Warm caches -----
    for _ in 0..50 {
        let t = generate_trace_rows::<Val>(0, 1, HEIGHT);
        let p = prove(&config, &FibonacciAir {}, t, &pis);
        std::hint::black_box(&p);
    }

    // ----- Bench: end-to-end prove, min-of-3 -----
    let mut best: u64 = u64::MAX;
    for _trial in 0..3 {
        let t0 = rdtscp();
        for _ in 0..ITERS {
            let t = generate_trace_rows::<Val>(0, 1, HEIGHT);
            let p = prove(&config, &FibonacciAir {}, t, &pis);
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
        "  Upstream p3-* prove (rustc -O3 LTO): {} cyc/op (min-of-3, ITERS={})",
        cyc, ITERS
    );
}
