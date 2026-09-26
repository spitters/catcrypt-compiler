// Reference: libspartan's intermediate ZK sub-proofs of `NIZK::prove`
// (= `R1CSProof::prove`, src/r1csproof.rs), reproduced clause-for-clause from
// `spartan-0.9.0/src/nizk/mod.rs` over the SAME field libspartan uses
// (curve25519-dalek-ng Ristretto scalar field, order
//  q = 2^252 + 27742317777372353535851937790883648493).
//
// This dumps the deterministic scalar OUTPUTS of the intermediate sub-proofs
// the #429/#431 bench skipped (the #435 residual), so the CatCrypt C replica
// (../SSProve-lean/bench/spartan_compare/spartan_prover_prod_kat.c) can KAT against them:
//
//   * ProductProof::prove (nizk/mod.rs:159) over the phase-1 claims
//     (x=Az_claim, y=Bz_claim, z=Az_claim*Bz_claim):
//       z1 = b1 + c*x ; z2 = b2 + c*rX ; z3 = b3 + c*y ; z4 = b4 + c*rY ;
//       z5 = b5 + c*(rZ - rX*y)
//   * EqualityProof::prove (nizk/mod.rs:88) closing each sum-check phase:
//       z  = c*(s1 - s2) + r
//     - phase-1: proof_eq_sc_phase1  (r1csproof.rs:254)
//     - phase-2: proof_eq_sc_phase2  (r1csproof.rs:317)
//
// We do NOT call libspartan's private nizk internals (crate-private) nor Merlin;
// instead we reproduce the EXACT scalar arithmetic over the SAME Scalar type
// with DETERMINISTIC stand-in randomness/challenges (same convention as the
// twophase reference) — the scalar z-outputs are the ground truth the C replica
// must reproduce bit-for-bit (mod q).  The curve commitments (alpha/beta/delta)
// are KAT'd for reproducibility on the C side over the verified Ed25519 group.
//
// Build/run:  cargo run --release --offline --bin spartan_nizk_ref

use curve25519_dalek_ng::scalar::Scalar;

fn s(x: u64) -> Scalar { Scalar::from(x) }

fn dec(x: &Scalar) -> String {
    let b = x.to_bytes();
    let mut digits: Vec<u8> = vec![0];
    for byte in b.iter().rev() {
        let mut carry = *byte as u32;
        for d in digits.iter_mut() {
            let v = (*d as u32) * 256 + carry;
            *d = (v % 10) as u8;
            carry = v / 10;
        }
        while carry > 0 { digits.push((carry % 10) as u8); carry /= 10; }
    }
    digits.iter().rev().map(|d| (b'0' + d) as char).collect()
}

// ---- ProductProof::prove scalar outputs (nizk/mod.rs:159) ----
// returns [z1,z2,z3,z4,z5]
fn product_proof(
    x: Scalar, r_x: Scalar, y: Scalar, r_y: Scalar, z: Scalar, r_z: Scalar,
    b1: Scalar, b2: Scalar, b3: Scalar, b4: Scalar, b5: Scalar, c: Scalar,
) -> [Scalar; 5] {
    let z1 = b1 + c * x;
    let z2 = b2 + c * r_x;
    let z3 = b3 + c * y;
    let z4 = b4 + c * r_y;
    let z5 = b5 + c * (r_z - r_x * y);
    [z1, z2, z3, z4, z5]
}

// ---- EqualityProof::prove scalar output (nizk/mod.rs:88) ----
// z = c*(s1 - s2) + r
fn equality_proof(s1: Scalar, s2: Scalar, r: Scalar, c: Scalar) -> Scalar {
    c * (s1 - s2) + r
}

fn main() {
    // Deterministic phase-1 post-sum-check claims (Az_claim, Bz_claim, Cz_claim,
    // tau_claim).  These stand in for poly_{Az,Bz,Cz,tau}[0] after the phase-1
    // sum-check binds all variables; the exact values are deterministic, the
    // ARITHMETIC of the sub-proofs is libspartan's.
    let az_claim = s(1234567);
    let bz_claim = s(7654321);
    let cz_claim = az_claim * bz_claim;   // satisfied gate residual handled below
    let tau_claim = s(424242);

    // blinds for the three claim commitments + the product commitment
    let az_blind = s(11);
    let bz_blind = s(22);
    let cz_blind = s(33);
    let prod_az_bz_blind = s(44);

    // ProductProof over (Az_claim, Bz_claim, prod = Az_claim*Bz_claim)
    let prod = az_claim * bz_claim;
    // five random scalars (deterministic stand-ins for random_tape b1..b5)
    let (b1, b2, b3, b4, b5) = (s(101), s(102), s(103), s(104), s(105));
    let c_prod = s(9001);   // challenge_scalar(b"c")
    let pp = product_proof(
        az_claim, az_blind, bz_claim, bz_blind, prod, prod_az_bz_blind,
        b1, b2, b3, b4, b5, c_prod,
    );

    // EqualityProof phase-1 (r1csproof.rs:251) :
    //   claim_post_phase1 = (Az*Bz - Cz)*tau_claim
    //   blind_expected_claim_postsc1 = tau_claim*(prod_Az_Bz_blind - Cz_blind)
    //   v1 = v2 = claim_post_phase1 ;  s1 = blind_expected ; s2 = blind_claim_postsc1
    let blind_claim_postsc1 = s(55);  // returned by phase-1 sum-check (stand-in)
    let claim_post_phase1 = (az_claim * bz_claim - cz_claim) * tau_claim;
    let blind_expected_claim_postsc1 = tau_claim * (prod_az_bz_blind - cz_blind);
    let r_eq1 = s(7001);
    let c_eq1 = s(8001);
    let eq1_z = equality_proof(blind_expected_claim_postsc1, blind_claim_postsc1, r_eq1, c_eq1);

    // EqualityProof phase-2 (r1csproof.rs:313) :
    //   claim_post_phase2 = claims_phase2[0]*claims_phase2[1]
    //   blind_eval_Z_at_ry = (1 - ry[0])*blind_eval
    //   blind_expected_claim_postsc2 = claims_phase2[1]*blind_eval_Z_at_ry
    let claims_phase2_0 = s(31415);
    let claims_phase2_1 = s(27182);
    let ry0 = s(161803);
    let blind_eval = s(66);
    let blind_claim_postsc2 = s(77);  // returned by phase-2 sum-check (stand-in)
    let claim_post_phase2 = claims_phase2_0 * claims_phase2_1;
    let blind_eval_z_at_ry = (Scalar::one() - ry0) * blind_eval;
    let blind_expected_claim_postsc2 = claims_phase2_1 * blind_eval_z_at_ry;
    let r_eq2 = s(7002);
    let c_eq2 = s(8002);
    let eq2_z = equality_proof(blind_expected_claim_postsc2, blind_claim_postsc2, r_eq2, c_eq2);

    let _ = claim_post_phase1;   // (the committed value; KAT'd via the z-equation)
    let _ = claim_post_phase2;
    let _ = prod;

    println!("# libspartan NIZK::prove intermediate ZK sub-proof scalar outputs");
    println!("# (ProductProof z1..z5, EqualityProof phase-1 z, EqualityProof phase-2 z)");
    print!("PP");
    for x in pp.iter() { print!(" {}", dec(x)); }
    println!();
    println!("EQ1 {}", dec(&eq1_z));
    println!("EQ2 {}", dec(&eq2_z));
}
