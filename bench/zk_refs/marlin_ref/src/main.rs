// Reference bench: arkworks ark-marlin (full production prover).
// Workload: the crate's own R1CS test circuit proved with Marlin's KZG10
// polynomial commitment over BLS12-381 (full prover = AHP sum-check rounds +
// KZG commit (G1 MSM) + KZG opening + pairing-based verifier). This is the
// production analogue of our emitted Marlin prover, which benches the REAL
// verified BN254 optimal-ate pairing CHECK + the verified Fp sum-check round;
// the KZG-commit G1 MSM is our documented residual.
//
// NOTE on curve: ark-marlin here uses BLS12-381; our emitted prover's real
// pairing leaf is BN254. Same KZG-over-pairing structure, different pairing
// curve (documented in the cross-crate table).
//
// Circuit body copied verbatim from ark-marlin-0.3.0/src/test.rs.

use ark_ff::Field;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};

use ark_bls12_381::{Bls12_381, Fr};
use ark_ff::UniformRand;
use ark_marlin::Marlin;
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::marlin_pc::MarlinKZG10;
use ark_std::ops::MulAssign;
use blake2::Blake2s;

#[inline(always)]
fn rdtsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

#[derive(Copy, Clone)]
struct Circuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
    num_constraints: usize,
    num_variables: usize,
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit<ConstraintF> {
    fn generate_constraints(self, cs: ConstraintSystemRef<ConstraintF>) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
            a.mul_assign(&b);
            Ok(a)
        })?;
        let d = cs.new_input_variable(|| {
            let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
            a.mul_assign(&b);
            a.mul_assign(&b);
            Ok(a)
        })?;
        for _ in 0..(self.num_variables - 3) {
            let _ = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }
        for _ in 0..(self.num_constraints - 1) {
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        }
        cs.enforce_constraint(lc!() + c, lc!() + b, lc!() + d)?;
        Ok(())
    }
}

type MultiPC = MarlinKZG10<Bls12_381, DensePolynomial<Fr>>;
type MarlinInst = Marlin<Fr, MultiPC, Blake2s>;

fn main() {
    let num_constraints = 25;
    let num_variables = 25;
    let rng = &mut ark_std::test_rng();

    let universal_srs = MarlinInst::universal_setup(100, 25, 100, rng).unwrap();

    let a = Fr::rand(rng);
    let b = Fr::rand(rng);
    let mut c = a; c.mul_assign(&b);
    let mut d = c; d.mul_assign(&b);
    let circ = Circuit { a: Some(a), b: Some(b), num_constraints, num_variables };
    let (index_pk, index_vk) = MarlinInst::index(&universal_srs, circ.clone()).unwrap();

    // correctness
    let proof = MarlinInst::prove(&index_pk, circ, rng).unwrap();
    assert!(MarlinInst::verify(&index_vk, &[c, d], &proof, rng).unwrap());
    println!("ark-marlin (cons={}, vars={}, BLS12-381 KZG) correctness: PASS", num_constraints, num_variables);

    let reps = 100;
    let mut best = u64::MAX;
    for _ in 0..reps {
        let circ = Circuit { a: Some(a), b: Some(b), num_constraints, num_variables };
        let s = rdtsc();
        let _proof = MarlinInst::prove(&index_pk, circ, rng).unwrap();
        let e = rdtsc();
        let dd = e.wrapping_sub(s);
        if dd < best { best = dd; }
    }
    println!("ark-marlin full prove (cons={}, vars={}, AHP sum-check + KZG G1-MSM + opening): {} cyc/prove (min of {} reps)", num_constraints, num_variables, best, reps);

    // also time the verifier (pairing-based) for comparison to our pairing-check leaf
    let mut bestv = u64::MAX;
    for _ in 0..reps {
        let s = rdtsc();
        let ok = MarlinInst::verify(&index_vk, &[c, d], &proof, rng).unwrap();
        let e = rdtsc();
        assert!(ok);
        let dd = e.wrapping_sub(s);
        if dd < bestv { bestv = dd; }
    }
    println!("ark-marlin full verify (pairing-based KZG check): {} cyc/verify (min of {} reps)", bestv, reps);
}
