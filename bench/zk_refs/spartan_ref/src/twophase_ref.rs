// Reference: libspartan's TWO-PHASE R1CS sum-check prover transcript, reproduced
// clause-for-clause from `spartan-0.9.0/src/sumcheck.rs` + `src/r1csproof.rs`
// over the SAME field libspartan uses (curve25519-dalek-ng Ristretto scalar field,
// order q = 2^252 + 27742317777372353535851937790883648493).
//
// This dumps the deterministic prover transcript so the CatCrypt C replica (in
// ../SSProve-lean/bench/spartan_compare/spartan_prover_prod_kat.c) can KAT against it:
//   * phase-1: `num_rounds_x` rounds of `prove_cubic_with_additive_term` over the
//     combination eq(tau,x) * (Az(x)*Bz(x) - Cz(x))  (degree-3 round polys)
//   * phase-2: `num_rounds_y` rounds of `prove_quad` over Z(y) * ABC(y), with ABC
//     the random-linear-combination r_A*A + r_B*B + r_C*C  (degree-2 round polys)
//
// We do NOT call libspartan's private sum-check internals (they are crate-private);
// instead we reproduce their EXACT arithmetic here over the SAME Scalar type, which
// is the ground truth the C replica must reproduce bit-for-bit (mod q).
//
// Build/run:  cargo run --release --offline --bin spartan_twophase_ref

use curve25519_dalek_ng::scalar::Scalar;

fn s(x: u64) -> Scalar { Scalar::from(x) }

fn dec(x: &Scalar) -> String {
    // little-endian bytes -> decimal big-integer string
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

// ---- multilinear poly stored as evaluation table (DensePolynomial) ----
// bound_poly_var_top: src/dense_mlpoly.rs:215
fn bound_var_top(z: &mut Vec<Scalar>, r: &Scalar) {
    let n = z.len() / 2;
    for i in 0..n {
        z[i] = z[i] + r * (z[i + n] - z[i]);
    }
    z.truncate(n);
}

// EqPolynomial::evals  (src/dense_mlpoly.rs:68)
fn eq_evals(r: &[Scalar]) -> Vec<Scalar> {
    let ell = r.len();
    let mut evals = vec![Scalar::one(); 1usize << ell];
    let mut size = 1usize;
    for j in 0..ell {
        size *= 2;
        let mut i = size - 1;
        loop {
            let scalar = evals[i / 2];
            evals[i] = scalar * r[j];
            evals[i - 1] = scalar - evals[i];
            if i < 2 { break; }
            i -= 2;
        }
    }
    evals
}

// UniPoly::from_evals  (src/unipoly.rs:23) -- returns coeff vector
fn from_evals(evals: &[Scalar]) -> Vec<Scalar> {
    let two_inv = s(2).invert();
    if evals.len() == 3 {
        let c = evals[0];
        let a = two_inv * (evals[2] - evals[1] - evals[1] + c);
        let b = evals[1] - c - a;
        vec![c, b, a]
    } else {
        let six_inv = s(6).invert();
        let d = evals[0];
        let a = six_inv
            * (evals[3] - evals[2] - evals[2] - evals[2] + evals[1] + evals[1] + evals[1]
                - evals[0]);
        let b = two_inv
            * (evals[0] + evals[0] - evals[1] - evals[1] - evals[1] - evals[1] - evals[1]
                + evals[2] + evals[2] + evals[2] + evals[2] - evals[3]);
        let c = evals[1] - d - a - b;
        vec![d, c, b, a]
    }
}

fn poly_eval(coeffs: &[Scalar], r: &Scalar) -> Scalar {
    let mut eval = coeffs[0];
    let mut power = *r;
    for i in 1..coeffs.len() {
        eval += power * coeffs[i];
        power *= r;
    }
    eval
}

// ---- phase 1: prove_cubic_with_additive_term  (src/sumcheck.rs:588) ----
// comb_func(a,b,c,d) = a * (b*c - d)  (the R1CS gate, src/r1csproof.rs prove())
fn phase_one(
    num_rounds: usize,
    claim: Scalar,
    poly_tau: &mut Vec<Scalar>,
    poly_az: &mut Vec<Scalar>,
    poly_bz: &mut Vec<Scalar>,
    poly_cz: &mut Vec<Scalar>,
    challenges: &[Scalar],
) -> (Vec<Vec<Scalar>>, Vec<Scalar>) {
    let comb = |a: &Scalar, b: &Scalar, c: &Scalar, d: &Scalar| *a * (*b * *c - *d);
    let mut claim_per_round = claim;
    let mut transcript: Vec<Vec<Scalar>> = Vec::new();
    let mut rx: Vec<Scalar> = Vec::new();
    for j in 0..num_rounds {
        let mut e0 = Scalar::zero();
        let mut e2 = Scalar::zero();
        let mut e3 = Scalar::zero();
        let len = poly_tau.len() / 2;
        for i in 0..len {
            e0 += comb(&poly_tau[i], &poly_az[i], &poly_bz[i], &poly_cz[i]);
            let ta = poly_tau[len + i] + poly_tau[len + i] - poly_tau[i];
            let aa = poly_az[len + i] + poly_az[len + i] - poly_az[i];
            let ba = poly_bz[len + i] + poly_bz[len + i] - poly_bz[i];
            let ca = poly_cz[len + i] + poly_cz[len + i] - poly_cz[i];
            e2 += comb(&ta, &aa, &ba, &ca);
            let ta = ta + poly_tau[len + i] - poly_tau[i];
            let aa = aa + poly_az[len + i] - poly_az[i];
            let ba = ba + poly_bz[len + i] - poly_bz[i];
            let ca = ca + poly_cz[len + i] - poly_cz[i];
            e3 += comb(&ta, &aa, &ba, &ca);
        }
        let evals = vec![e0, claim_per_round - e0, e2, e3];
        let coeffs = from_evals(&evals);
        transcript.push(coeffs.clone());
        let r_j = challenges[j];
        bound_var_top(poly_tau, &r_j);
        bound_var_top(poly_az, &r_j);
        bound_var_top(poly_bz, &r_j);
        bound_var_top(poly_cz, &r_j);
        rx.push(r_j);
        claim_per_round = poly_eval(&coeffs, &r_j);
    }
    (transcript, rx)
}

// ---- phase 2: prove_quad  (src/sumcheck.rs:428) ----
// comb_func(a,b) = a * b   (Z(y) * ABC(y))
fn phase_two(
    num_rounds: usize,
    claim: Scalar,
    poly_z: &mut Vec<Scalar>,
    poly_abc: &mut Vec<Scalar>,
    challenges: &[Scalar],
) -> (Vec<Vec<Scalar>>, Vec<Scalar>) {
    let comb = |a: &Scalar, b: &Scalar| *a * *b;
    let mut claim_per_round = claim;
    let mut transcript: Vec<Vec<Scalar>> = Vec::new();
    let mut ry: Vec<Scalar> = Vec::new();
    for j in 0..num_rounds {
        let mut e0 = Scalar::zero();
        let mut e2 = Scalar::zero();
        let len = poly_z.len() / 2;
        for i in 0..len {
            e0 += comb(&poly_z[i], &poly_abc[i]);
            let za = poly_z[len + i] + poly_z[len + i] - poly_z[i];
            let aa = poly_abc[len + i] + poly_abc[len + i] - poly_abc[i];
            e2 += comb(&za, &aa);
        }
        let evals = vec![e0, claim_per_round - e0, e2];
        let coeffs = from_evals(&evals);
        transcript.push(coeffs.clone());
        let r_j = challenges[j];
        bound_var_top(poly_z, &r_j);
        bound_var_top(poly_abc, &r_j);
        ry.push(r_j);
        claim_per_round = poly_eval(&coeffs, &r_j);
    }
    (transcript, ry)
}

fn main() {
    // --- deterministic toy R1CS: num_cons = 16, num_vars = 16 (Z length 2*num_vars=32) ---
    // (matches the bench statement size; num_rounds_x = log2(16)=4, num_rounds_y = log2(32)=5)
    let num_cons = 16usize;
    let z_len = 32usize; // 2 * num_vars
    let nx = num_cons.trailing_zeros() as usize; // 4
    let ny = z_len.trailing_zeros() as usize;    // 5

    // satisfying assignment-shaped vectors: Az, Bz, Cz with Az.*Bz - Cz = 0 pointwise
    // (so the phase-1 claim is 0, exactly as in a satisfied R1CS).
    let mut az: Vec<Scalar> = (0..num_cons).map(|i| s((3 + i as u64) % 7 + 1)).collect();
    let mut bz: Vec<Scalar> = (0..num_cons).map(|i| s((5 + 2 * i as u64) % 11 + 1)).collect();
    let mut cz: Vec<Scalar> = (0..num_cons).map(|i| az[i] * bz[i]).collect();

    // tau: deterministic verifier challenge vector for R(tau, .)
    let tau: Vec<Scalar> = (0..nx).map(|i| s(7 + 3 * i as u64)).collect();
    let mut poly_tau = eq_evals(&tau);

    // deterministic per-round challenges (stand in for Fiat-Shamir squeezes)
    let chx: Vec<Scalar> = (0..nx).map(|i| s(11 + 5 * i as u64)).collect();
    let chy: Vec<Scalar> = (0..ny).map(|i| s(13 + 4 * i as u64)).collect();

    let claim1 = Scalar::zero();
    let (t1, _rx) = phase_one(nx, claim1, &mut poly_tau, &mut az, &mut bz, &mut cz, &chx);

    // phase-2: random linear combination r_A*Az + r_B*Bz + r_C*Cz at point rx, then
    // quad sum-check over Z(y) * ABC(y).  We use deterministic r_A,r_B,r_C and a
    // deterministic Z and ABC of length z_len (clause-for-clause shape; the exact
    // entries are deterministic stand-ins, the prover ARITHMETIC is libspartan's).
    let r_a = s(101); let r_b = s(103); let r_c = s(107);
    let claim2 = r_a * az[0] + r_b * bz[0] + r_c * cz[0]; // post-phase-1 bound claim
    let mut poly_z: Vec<Scalar> = (0..z_len).map(|i| s(2 + i as u64)).collect();
    let mut poly_abc: Vec<Scalar> =
        (0..z_len).map(|i| r_a * s(1 + i as u64) + r_b * s(2 + i as u64) + r_c * s(3 + i as u64)).collect();
    let (t2, _ry) = phase_two(ny, claim2, &mut poly_z, &mut poly_abc, &chy);

    // dump transcript: "P1 round j: coeff0 coeff1 ...", "P2 round j: ..."
    println!("# libspartan two-phase R1CS sum-check transcript (Ristretto scalar field)");
    println!("# num_cons={} z_len={} num_rounds_x={} num_rounds_y={}", num_cons, z_len, nx, ny);
    for (j, c) in t1.iter().enumerate() {
        print!("P1 {}", j);
        for x in c { print!(" {}", dec(x)); }
        println!();
    }
    for (j, c) in t2.iter().enumerate() {
        print!("P2 {}", j);
        for x in c { print!(" {}", dec(x)); }
        println!();
    }
}
