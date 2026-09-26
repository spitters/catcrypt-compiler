// Reference bench: microsoft/Spartan (libspartan, full production prover).
// Workload: NIZK proof of a synthetic R1CS instance over curve25519-dalek's
// Ristretto scalar field. Full Spartan prover = multilinear sum-check rounds
// + polynomial commitment (curve MSM) + Fiat-Shamir. Our emitted Spartan
// prover benches the sum-check field core (BabyBear Horner) + Poseidon2
// commit/squeeze leaves; the PCS curve MSM is the documented gap.

use libspartan::{Instance, NIZKGens, NIZK};
use merlin::Transcript;

#[inline(always)]
fn rdtsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

fn main() {
    // Smallest meaningful R1CS: num_cons constraints, num_vars variables.
    let num_vars = 16;
    let num_cons = 16;
    let num_inputs = 2;
    let (inst, vars, inputs) =
        Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    let gens = NIZKGens::new(num_cons, num_vars, num_inputs);

    // correctness
    let mut prover_t = Transcript::new(b"zkxcompare");
    let proof = NIZK::prove(&inst, vars.clone(), &inputs, &gens, &mut prover_t);
    let mut verifier_t = Transcript::new(b"zkxcompare");
    assert!(proof
        .verify(&inst, &inputs, &mut verifier_t, &gens)
        .is_ok());
    println!("spartan NIZK (cons={}, vars={}) correctness: PASS", num_cons, num_vars);

    let reps = 100;
    let mut best = u64::MAX;
    for _ in 0..reps {
        let mut prover_t = Transcript::new(b"zkxcompare");
        let s = rdtsc();
        let _proof = NIZK::prove(&inst, vars.clone(), &inputs, &gens, &mut prover_t);
        let e = rdtsc();
        let d = e.wrapping_sub(s);
        if d < best { best = d; }
    }
    println!("microsoft-spartan NIZK full prove (cons={}, vars={}, sum-check + PCS MSM + FS): {} cyc/prove (min of {} reps)", num_cons, num_vars, best, reps);
}
