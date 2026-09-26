//! p3-verifier-accepts interop harness (TASK #647, step 1).
//!
//! Goal: establish the exact bar an emitted prover must clear for the REAL
//! `p3-uni-stark` 0.5.3 verifier to accept its proof, and remove the single
//! biggest avoidable blocker — the round-constant mismatch.
//!
//! The bench reference (`src/main.rs`) seeds its Poseidon2 permutation from
//! `SmallRng::seed_from_u64(1)` (`new_from_rng_128`). That is an arbitrary
//! config choice; it makes p3's hash use random constants that NO emitted
//! prover can match. This harness instead builds the config from
//! `default_babybear_poseidon2_16()` — the canonical default BabyBear
//! Poseidon2 constants. Those are EXACTLY the constants the CatCrypt emitted
//! Poseidon2 leaf KAT-matches (`../SSProve-lean/bench/poseidon2_compare`,
//! `test_default_babybear_poseidon2_width_16`). So under this config p3's
//! hash == our emitted hash, byte-for-byte.
//!
//! What this binary proves concretely:
//!   1. `default`-constant config: real p3 prove -> verify ACCEPT.
//!   2. The proof serializes (serde + bincode) to a flat byte blob and
//!      DESERIALIZES back into a `Proof<MyConfig>` that the real p3 verifier
//!      still ACCEPTs. This is the serialization format an emitted prover
//!      must reproduce to be verifier-accepted.
//!   3. It dumps the serialized proof to `p3_default_proof.bin` and prints
//!      its structure (commitment digests, opened-value extension-field
//!      vectors, FRI commit-phase commitments, query count, final_poly),
//!      i.e. the exact wire format + transcript-derived shape.
//!
//! This is the FAEST-4506-grade bar made concrete: a real p3 verifier
//! accepting a deserialized proof over the default-constant Poseidon2 that
//! the emitted leaf computes. The remaining delta (an emitted prover writing
//! THESE bytes) is documented in FULL_PROVER_VS_P3.md.

use core::borrow::Borrow;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::{default_babybear_poseidon2_16, BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField64};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{prove, verify, Proof, StarkConfig};

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
// Config: BabyBear / Poseidon2-16 (DEFAULT constants) / Merkle MMCS / FriPcs
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

/// Config built from the DEFAULT BabyBear Poseidon2 constants — the exact
/// constants the CatCrypt emitted Poseidon2 leaf KAT-matches. This is what
/// makes p3's hash identical to the emitted hash.
fn make_default_config() -> MyConfig {
    let perm = default_babybear_poseidon2_16();
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

const HEIGHT: usize = 8;

fn main() {
    let config = make_default_config();
    let pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::from_u64(21)];

    println!("p3-verifier-accepts interop harness (p3-* 0.5.3, DEFAULT BabyBear Poseidon2 constants)");
    println!("  Challenge field = BinomialExtensionField<BabyBear,4>  (DIMENSION = {})", <Challenge as BasedVectorSpace<Val>>::DIMENSION);

    // (1) Prove and verify under the default-constant config.
    let trace = generate_trace_rows::<Val>(0, 1, HEIGHT);
    let proof: Proof<MyConfig> = prove(&config, &FibonacciAir {}, trace, &pis);
    match verify(&config, &FibonacciAir {}, &proof, &pis) {
        Ok(()) => println!("  (1) default-constant config: prove -> verify ACCEPT  [PASS]"),
        Err(e) => {
            println!("  (1) default-constant config: verify REJECTED honest proof: {:?}  [FAIL]", e);
            std::process::exit(1);
        }
    }

    // (2) Serialize the proof (the wire format an emitted prover must match),
    //     deserialize it back, and re-verify with the real p3 verifier.
    let bytes = bincode::serialize(&proof).expect("serialize proof");
    let proof2: Proof<MyConfig> = bincode::deserialize(&bytes).expect("deserialize proof");
    match verify(&config, &FibonacciAir {}, &proof2, &pis) {
        Ok(()) => println!(
            "  (2) serialize({} bytes) -> deserialize -> verify ACCEPT  [PASS]",
            bytes.len()
        ),
        Err(e) => {
            println!("  (2) deserialized proof REJECTED: {:?}  [FAIL]", e);
            std::process::exit(1);
        }
    }
    std::fs::write("p3_default_proof.bin", &bytes).expect("write proof");
    println!("  wrote p3_default_proof.bin ({} bytes)", bytes.len());

    // (3) Dump the proof structure — the exact shape an emitted prover must
    //     reproduce. This is the verifier-accepts wire spec.
    println!("\n--- proof structure (verifier-accepts wire spec) ---");
    println!("  degree_bits = {}", proof.degree_bits);
    // Commitments are MerkleCap wrappers; serialize each to expose the
    // 8-element BabyBear digest the verifier observes into the transcript.
    let trace_com_bytes = bincode::serialize(&proof.commitments.trace).unwrap();
    println!(
        "  commitments.trace        = {} serialized bytes (8-elt BabyBear Merkle root)",
        trace_com_bytes.len()
    );
    let q_com_bytes = bincode::serialize(&proof.commitments.quotient_chunks).unwrap();
    println!(
        "  commitments.quotient_chunks = {} serialized bytes (8-elt BabyBear Merkle root)",
        q_com_bytes.len()
    );
    println!(
        "  opened_values.trace_local                = {} ext-elts (each dim {})",
        proof.opened_values.trace_local.len(),
        <Challenge as BasedVectorSpace<Val>>::DIMENSION
    );
    println!(
        "  opened_values.trace_next                 = {}",
        proof
            .opened_values
            .trace_next
            .as_ref()
            .map(|v| format!("{} ext-elts", v.len()))
            .unwrap_or_else(|| "None".into())
    );
    println!(
        "  opened_values.quotient_chunks            = {} chunks x {} ext-elts",
        proof.opened_values.quotient_chunks.len(),
        proof
            .opened_values
            .quotient_chunks
            .first()
            .map(|c| c.len())
            .unwrap_or(0)
    );
    println!(
        "  opening_proof.commit_phase_commits       = {} FRI layer commitments",
        proof.opening_proof.commit_phase_commits.len()
    );
    println!(
        "  opening_proof.query_proofs               = {} queries",
        proof.opening_proof.query_proofs.len()
    );
    println!(
        "  opening_proof.final_poly                 = {} ext-elts",
        proof.opening_proof.final_poly.len()
    );
    println!("\nThis proof IS accepted by the real p3 verifier. The emitted prover must");
    println!("produce these same bytes (DEEP-quotient phase + degree-4 extension FRI +");
    println!("serde layout) to be p3-verifier-accepted. See FULL_PROVER_VS_P3.md.");
}
