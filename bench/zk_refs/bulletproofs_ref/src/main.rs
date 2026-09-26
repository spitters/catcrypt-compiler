// Reference bench: dalek bulletproofs (full production prover).
// Workload: a single range proof over Ristretto255 (full Bulletproofs prover:
// vector Pedersen commitment via curve MSM + IPA fold recursion + Fiat-Shamir).
// This is the closest production analogue to our emitted Bulletproofs prover,
// whose field IPA recursion + Poseidon2 FS we bench separately; the dalek prover
// additionally performs the curve-MSM vector commitment (our documented gap).

use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use curve25519_dalek_ng::scalar::Scalar;
use merlin::Transcript;
use rand::rngs::OsRng;

#[inline(always)]
fn rdtsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

fn main() {
    let pc_gens = PedersenGens::default();
    // n = 32-bit range; 1 value. 32 generators -> 5 IPA rounds.
    let bp_gens = BulletproofGens::new(32, 1);
    let secret = 1037578891u64;
    let blinding = Scalar::random(&mut OsRng);

    // warmup + correctness
    let mut t = Transcript::new(b"zkxcompare");
    let (proof, _commit) = RangeProof::prove_single(
        &bp_gens, &pc_gens, &mut t, secret, &blinding, 32,
    )
    .expect("prove");
    let mut tv = Transcript::new(b"zkxcompare");
    let vc = pc_gens.commit(Scalar::from(secret), blinding).compress();
    assert!(proof.verify_single(&bp_gens, &pc_gens, &mut tv, &vc, 32).is_ok());
    println!("range-proof (n=32) correctness: PASS");

    let reps = 200;
    let mut best = u64::MAX;
    for _ in 0..reps {
        let blinding = Scalar::random(&mut OsRng);
        let mut t = Transcript::new(b"zkxcompare");
        let s = rdtsc();
        let (_proof, _commit) = RangeProof::prove_single(
            &bp_gens, &pc_gens, &mut t, secret, &blinding, 32,
        )
        .expect("prove");
        let e = rdtsc();
        let d = e.wrapping_sub(s);
        if d < best { best = d; }
    }
    println!("dalek-bulletproofs full prove (n=32 range, curve MSM + IPA + FS): {} cyc/prove (min of {} reps)", best, reps);
}
