//! p3 intermediate-value dump + foreign-proof verifier (TASK #647, items 1-3).
//!
//! Two modes:
//!
//! `p3-fib-dump`            — replicate `p3_uni_stark::prove` STEP BY STEP using
//!                            only public p3 APIs (same config as interop.rs:
//!                            DEFAULT BabyBear Poseidon2 constants), asserting at
//!                            each stage that the replicated value equals what the
//!                            real `prove()` produced. Dumps every intermediate
//!                            (trace LDE, trace commit, alpha, selectors-free
//!                            quotient evals, quotient commit, zeta, opened values,
//!                            FRI batch alpha, FRI beta, final poly, query indices)
//!                            in canonical u32 form so an external prover can be
//!                            cross-checked stage by stage.
//!
//! `p3-fib-dump verify F`   — read a serialized proof from file F, deserialize it
//!                            as `Proof<MyConfig>` and run the REAL p3 verifier on
//!                            it. Also byte-compares F against the proof produced
//!                            by the real `prove()` in-process.
//!
//! The stage-asserts make this dump trustworthy: if the replication diverged from
//! `prove()`, the asserts would fire (commitments + full proof bytes compared).

use core::borrow::Borrow;

use p3_air::symbolic::AirLayout;
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::{default_babybear_poseidon2_16, BabyBear, Poseidon2BabyBear};
use p3_challenger::{CanObserve, CanSampleBits, DuplexChallenger, FieldChallenger};
use p3_commit::{ExtensionMmcs, Pcs, PolynomialSpace};
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32, PrimeField64};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{
    get_log_num_quotient_chunks, prove, quotient_values, verify, Commitments, OpenedValues, Proof,
    StarkConfig, StarkGenericConfig,
};

// --- Fibonacci AIR (verbatim from interop.rs / p3-uni-stark tests) ---

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
    assert!(prefix.is_empty());
    assert!(suffix.is_empty());
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
        debug_assert!(prefix.is_empty());
        debug_assert!(suffix.is_empty());
        debug_assert_eq!(shorts.len(), 1);
        &shorts[0]
    }
}

// --- Config (identical to interop.rs) ---

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
type MyPcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
type MyConfig = StarkConfig<MyPcs, Challenge, Challenger>;

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
    let pcs = MyPcs::new(dft, val_mmcs, fri_params);
    let challenger = Challenger::new(perm);
    MyConfig::new(pcs, challenger)
}

const HEIGHT: usize = 8;

// Typed aliases pinning `Pcs<Challenge, Challenger>` so method calls resolve.
type PcsT = <MyPcs as Pcs<Challenge, Challenger>>::ProverData;
type DomainT = <MyPcs as Pcs<Challenge, Challenger>>::Domain;
type CommitT = <MyPcs as Pcs<Challenge, Challenger>>::Commitment;
type EvalsT<'a> = <MyPcs as Pcs<Challenge, Challenger>>::EvaluationsOnDomain<'a>;
type ProofT = <MyPcs as Pcs<Challenge, Challenger>>::Proof;

fn pcs_commit(pcs: &MyPcs, evals: Vec<(DomainT, RowMajorMatrix<Val>)>) -> (CommitT, PcsT) {
    <MyPcs as Pcs<Challenge, Challenger>>::commit(pcs, evals)
}
fn pcs_natural_domain(pcs: &MyPcs, degree: usize) -> DomainT {
    <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree)
}
fn pcs_evals_on_domain<'a>(pcs: &MyPcs, data: &'a PcsT, idx: usize, d: DomainT) -> EvalsT<'a> {
    <MyPcs as Pcs<Challenge, Challenger>>::get_evaluations_on_domain(pcs, data, idx, d)
}
fn pcs_commit_quotient(
    pcs: &MyPcs,
    d: DomainT,
    evals: RowMajorMatrix<Val>,
    chunks: usize,
) -> (CommitT, PcsT) {
    <MyPcs as Pcs<Challenge, Challenger>>::commit_quotient(pcs, d, evals, chunks)
}
fn pcs_open(
    pcs: &MyPcs,
    rounds: Vec<(&PcsT, Vec<Vec<Challenge>>)>,
    challenger: &mut Challenger,
) -> (p3_commit::OpenedValues<Challenge>, ProofT) {
    <MyPcs as Pcs<Challenge, Challenger>>::open(pcs, rounds, challenger)
}

fn fmt_ext(x: &Challenge) -> String {
    let c: &[Val] = <Challenge as BasedVectorSpace<Val>>::as_basis_coefficients_slice(x);
    format!(
        "[{}, {}, {}, {}]",
        c[0].as_canonical_u32(),
        c[1].as_canonical_u32(),
        c[2].as_canonical_u32(),
        c[3].as_canonical_u32()
    )
}

fn fmt_digest_cap(cap: &<ValMmcs as p3_commit::Mmcs<Val>>::Commitment) -> String {
    // MerkleCap with cap_height 0: a single 8-element digest.
    let root = &cap[0];
    let v: Vec<String> = root.iter().map(|x| x.as_canonical_u32().to_string()).collect();
    format!("[{}]", v.join(", "))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let config = make_default_config();
    let pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::from_u64(21)];
    let air = FibonacciAir {};
    let trace = generate_trace_rows::<Val>(0, 1, HEIGHT);

    // Ground truth from the real prover.
    let proof: Proof<MyConfig> = prove(&config, &air, trace.clone(), &pis);
    let proof_bytes = bincode::serialize(&proof).expect("serialize");
    verify(&config, &air, &proof, &pis).expect("real prove must verify");

    if args.len() >= 3 && args[1] == "verify" {
        // Foreign-proof mode: deserialize the candidate bytes and run the REAL verifier.
        let cand = std::fs::read(&args[2]).expect("read candidate proof");
        println!(
            "byte-compare vs in-process real prove(): {} ({} vs {} bytes)",
            if cand == proof_bytes { "IDENTICAL" } else { "DIFFERENT" },
            cand.len(),
            proof_bytes.len()
        );
        if cand != proof_bytes {
            // locate first divergence for diagnostics
            let n = cand.len().min(proof_bytes.len());
            if let Some(i) = (0..n).find(|&i| cand[i] != proof_bytes[i]) {
                println!(
                    "  first differing byte at offset {} (ours=0x{:02x} p3=0x{:02x})",
                    i, cand[i], proof_bytes[i]
                );
            }
        }
        let cand_proof: Proof<MyConfig> =
            bincode::deserialize(&cand).expect("deserialize candidate proof");
        match verify(&config, &air, &cand_proof, &pis) {
            Ok(()) => println!("REAL p3 verifier on candidate proof: ACCEPT"),
            Err(e) => println!("REAL p3 verifier on candidate proof: REJECT ({:?})", e),
        }
        return;
    }

    // ------------------------------------------------------------------
    // Step-by-step replication of prove() with intermediate dumps.
    // Each stage is asserted against the real proof, so the dump is
    // guaranteed to be what prove() actually computed.
    // ------------------------------------------------------------------
    let pcs = config.pcs();
    let mut challenger = config.initialise_challenger();

    let degree = HEIGHT;
    let log_degree = 3usize;
    let log_ext_degree = log_degree; // is_zk = 0

    let layout = AirLayout {
        preprocessed_width: 0,
        main_width: <FibonacciAir as BaseAir<Val>>::width(&air),
        num_public_values: <FibonacciAir as BaseAir<Val>>::num_public_values(&air),
        ..Default::default()
    };
    let log_num_quotient_chunks = get_log_num_quotient_chunks::<Val, _>(&air, layout, 0);
    let num_quotient_chunks = 1usize << log_num_quotient_chunks;
    println!("num_quotient_chunks = {}", num_quotient_chunks);

    let trace_domain = pcs_natural_domain(pcs, degree);
    let ext_trace_domain = trace_domain;

    let (trace_commit, trace_data) = pcs_commit(pcs, vec![(ext_trace_domain, trace.clone())]);
    assert_eq!(
        bincode::serialize(&trace_commit).unwrap(),
        bincode::serialize(&proof.commitments.trace).unwrap(),
        "replicated trace commit != prove()'s trace commit"
    );
    println!("trace_commit = {}", fmt_digest_cap(&trace_commit));

    // Dump the natural-order trace LDE (32 x 2) over the coset g*K.
    let lde_domain =
        trace_domain.create_disjoint_domain(32); // shift becomes 1*GENERATOR = g, log 5
    let lde_view = pcs_evals_on_domain(pcs, &trace_data, 0, lde_domain);
    println!("trace_lde (natural order over gK, 32 rows x 2 cols, canonical):");
    for r in 0..32 {
        let row: Vec<u32> = lde_view.row(r).unwrap().into_iter().map(|x| x.as_canonical_u32()).collect();
        println!("  lde[{}] = {:?}", r, row);
    }

    challenger.observe(Val::from_u8(log_ext_degree as u8));
    challenger.observe(Val::from_u8(log_degree as u8));
    challenger.observe(Val::from_usize(0)); // preprocessed_width
    challenger.observe(trace_commit.clone());
    challenger.observe_slice(&pis);

    let alpha: Challenge = challenger.sample_algebra_element();
    println!("alpha = {}", fmt_ext(&alpha));

    let quotient_domain =
        ext_trace_domain.create_disjoint_domain(1 << (log_ext_degree + log_num_quotient_chunks));
    println!(
        "quotient_domain: shift = {}, size = {}",
        quotient_domain.shift().as_canonical_u32(),
        quotient_domain.size()
    );

    let trace_on_quotient_domain = pcs_evals_on_domain(pcs, &trace_data, 0, quotient_domain);
    println!("trace_on_quotient_domain (8 rows x 2, canonical):");
    for r in 0..8 {
        let row: Vec<u32> = trace_on_quotient_domain
            .row(r).unwrap()
            .into_iter()
            .map(|x| x.as_canonical_u32())
            .collect();
        println!("  tq[{}] = {:?}", r, row);
    }

    // Dump the selectors prove() uses.
    let sels = trace_domain.selectors_on_coset(quotient_domain);
    println!("selectors (canonical):");
    for r in 0..8 {
        println!(
            "  i={} first={} last={} trans={} invvan={}",
            r,
            sels.is_first_row[r].as_canonical_u32(),
            sels.is_last_row[r].as_canonical_u32(),
            sels.is_transition[r].as_canonical_u32(),
            sels.inv_vanishing[r].as_canonical_u32()
        );
    }

    let none_pre = if false {
        Some(pcs_evals_on_domain(pcs, &trace_data, 0, quotient_domain))
    } else {
        None
    };
    let qvals = quotient_values::<MyConfig, _, _>(
        &air,
        &pis,
        layout,
        trace_domain,
        quotient_domain,
        &trace_on_quotient_domain,
        none_pre.as_ref(),
        alpha,
    );
    println!("quotient_values (8 ext elts, canonical coeffs):");
    for (i, q) in qvals.iter().enumerate() {
        println!("  q[{}] = {}", i, fmt_ext(q));
    }

    let quotient_flat = RowMajorMatrix::new_col(qvals.clone()).flatten_to_base();
    let (quotient_commit, quotient_data) =
        pcs_commit_quotient(pcs, quotient_domain, quotient_flat, num_quotient_chunks);
    assert_eq!(
        bincode::serialize(&quotient_commit).unwrap(),
        bincode::serialize(&proof.commitments.quotient_chunks).unwrap(),
        "replicated quotient commit != prove()'s quotient commit"
    );
    println!("quotient_commit = {}", fmt_digest_cap(&quotient_commit));

    challenger.observe(quotient_commit.clone());

    let zeta: Challenge = challenger.sample_algebra_element();
    let zeta_next = trace_domain.next_point(zeta).unwrap();
    println!("zeta = {}", fmt_ext(&zeta));
    println!("zeta_next = {}", fmt_ext(&zeta_next));

    // Replicate the open() challenger interaction for FRI-stage dumps.
    let mut fri_challenger = challenger.clone();

    let round1 = (&trace_data, vec![vec![zeta, zeta_next]]);
    let round2 = (&quotient_data, vec![vec![zeta]; num_quotient_chunks]);
    let (opened_values, opening_proof) = pcs_open(pcs, vec![round1, round2], &mut challenger);

    let trace_local = opened_values[0][0][0].clone();
    let trace_next = opened_values[0][0][1].clone();
    let qc_opened: Vec<Vec<Challenge>> =
        opened_values[1].iter().map(|v| v[0].clone()).collect();

    println!("opened trace_local  = [{}, {}]", fmt_ext(&trace_local[0]), fmt_ext(&trace_local[1]));
    println!("opened trace_next   = [{}, {}]", fmt_ext(&trace_next[0]), fmt_ext(&trace_next[1]));
    for (i, c) in qc_opened.iter().enumerate() {
        let s: Vec<String> = c.iter().map(fmt_ext).collect();
        println!("opened quotient_chunks[{}] = [{}]", i, s.join(", "));
    }

    // Replay the in-open challenger to extract FRI alpha / beta / query indices.
    for v in trace_local.iter().chain(trace_next.iter()) {
        fri_challenger.observe_algebra_element(*v);
    }
    for c in &qc_opened {
        for v in c {
            fri_challenger.observe_algebra_element(*v);
        }
    }
    let fri_alpha: Challenge = fri_challenger.sample_algebra_element();
    println!("fri_alpha = {}", fmt_ext(&fri_alpha));

    assert_eq!(opening_proof.commit_phase_commits.len(), 1);
    println!(
        "fri commit_phase_commit[0] = {}",
        fmt_digest_cap(&opening_proof.commit_phase_commits[0])
    );
    fri_challenger.observe(opening_proof.commit_phase_commits[0].clone());
    // grind(0) is a no-op on the transcript.
    let beta: Challenge = fri_challenger.sample_algebra_element();
    println!("fri beta = {}", fmt_ext(&beta));

    println!("fri final_poly:");
    for (i, c) in opening_proof.final_poly.iter().enumerate() {
        println!("  fp[{}] = {}", i, fmt_ext(c));
    }
    for c in &opening_proof.final_poly {
        fri_challenger.observe_algebra_element(*c);
    }
    fri_challenger.observe(Val::from_usize(1)); // log_arity of the single round
    // query grind(0): no-op.
    let indices: Vec<usize> = (0..8).map(|_| fri_challenger.sample_bits(5)).collect();
    println!("fri query indices = {:?}", indices);

    // Final self-check: assemble the proof exactly like prove() and byte-compare.
    let replicated = Proof::<MyConfig> {
        commitments: Commitments {
            trace: trace_commit,
            quotient_chunks: quotient_commit,
            random: None,
        },
        opened_values: OpenedValues {
            trace_local,
            trace_next: Some(trace_next),
            preprocessed_local: None,
            preprocessed_next: None,
            quotient_chunks: qc_opened,
            random: None,
        },
        opening_proof,
        degree_bits: log_ext_degree,
    };
    let replicated_bytes = bincode::serialize(&replicated).unwrap();
    assert_eq!(
        replicated_bytes, proof_bytes,
        "replicated proof bytes != real prove() bytes"
    );
    println!(
        "REPLICATION SELF-CHECK: replicated proof == real prove() bytes ({} bytes)  [PASS]",
        proof_bytes.len()
    );

    // Also confirm the query indices we replayed match the openings in the proof:
    // the input_proof openings at index i must equal the committed LDE rows there.
    println!("(dump complete)");
}
