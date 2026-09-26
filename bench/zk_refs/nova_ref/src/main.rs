// Reference bench: microsoft/Nova (nova-snark, full production folding prover).
// Workload: one Nova recursive folding step (prove_step) over the Pasta cycle
// (pallas/vesta), using TrivialTestCircuit for both primary and secondary.
// This times the Nova folding prover core (R1CS relaxation fold + commitment).
//
// NOTE: Nova is a FOLDING scheme; our emitted ZK prover set has NO direct
// Nova analogue (we emit Spartan/Jolt sum-check, Bulletproofs/Halo2 IPA,
// Marlin KZG). This row is a production-prover reference data point only,
// not an ours-vs-Nova comparison.

use ff::Field;
use nova_snark::{
    traits::{circuit::TrivialTestCircuit, Group},
    PublicParams, RecursiveSNARK,
};

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type C1 = TrivialTestCircuit<<G1 as Group>::Scalar>;
type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;

#[inline(always)]
fn rdtsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

fn main() {
    let circuit_primary = TrivialTestCircuit::default();
    let circuit_secondary = TrivialTestCircuit::default();

    let pp = PublicParams::<G1, G2, C1, C2>::setup(
        circuit_primary.clone(),
        circuit_secondary.clone(),
    );
    println!(
        "nova public params (Pasta cycle, trivial step) cons primary={}, secondary={}",
        pp.num_constraints().0,
        pp.num_constraints().1
    );

    let z0_primary = vec![<G1 as Group>::Scalar::zero()];
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    // correctness: a couple of folding steps
    let mut rs: RecursiveSNARK<G1, G2, C1, C2> = RecursiveSNARK::new(
        &pp, &circuit_primary, &circuit_secondary,
        z0_primary.clone(), z0_secondary.clone(),
    );
    let r = rs.prove_step(&pp, &circuit_primary, &circuit_secondary,
        z0_primary.clone(), z0_secondary.clone());
    assert!(r.is_ok());
    println!("nova prove_step correctness: PASS");

    // Honest measurement: fold many sequential steps on one running instance.
    // Use both rdtsc and steady-clock wall time (rdtsc alone proved too noisy
    // for this large-but-fast-returning call; wall time cross-checks it).
    use std::time::Instant;
    let reps = 100;
    let mut best = u64::MAX;
    let mut best_ns = u128::MAX;
    let mut rs2: RecursiveSNARK<G1, G2, C1, C2> = RecursiveSNARK::new(
        &pp, &circuit_primary, &circuit_secondary,
        z0_primary.clone(), z0_secondary.clone(),
    );
    for _ in 0..reps {
        let w = Instant::now();
        let s = rdtsc();
        let r = rs2.prove_step(&pp, &circuit_primary, &circuit_secondary,
            z0_primary.clone(), z0_secondary.clone());
        let e = rdtsc();
        let ns = w.elapsed().as_nanos();
        assert!(r.is_ok());
        let d = e.wrapping_sub(s);
        if d < best { best = d; }
        if ns < best_ns { best_ns = ns; }
    }
    println!("nova-snark prove_step (Pasta cycle folding core, ~10k-constraint trivial step): {} cyc / {} ns per step (min of {} sequential steps)", best, best_ns, reps);
}
