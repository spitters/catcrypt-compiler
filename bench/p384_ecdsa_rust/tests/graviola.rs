//! Cross-implementation interop between the emitted P-384 ECDSA kernel and
//! Graviola 0.4.1.
//!
//! Graviola is a second opponent of a different tier from RustCrypto: its
//! P-384 field, group and scalar arithmetic is s2n-bignum assembly,
//! machine-checked in HOL Light, where this crate and RustCrypto both run
//! fiat-crypto Rust under the group law.  Agreement with it is therefore a
//! check against an independently derived implementation, not against a
//! sibling of our own leaves.
//!
//! Three checks:
//!
//! 1. [`our_signature_verifies_under_graviola`] — the emitted kernel signs,
//!    Graviola verifies.  This exercises the marshalling in one direction:
//!    `(r, s)` from two canonical little-endian 48-byte integers to the
//!    fixed-length big-endian concatenation, and the public key from this
//!    crate's 144-byte projective form to X9.62 uncompressed.
//! 2. [`graviola_signature_verifies_under_our_kernel`] — Graviola signs, the
//!    emitted kernel verifies with `ok = 1`, marshalling the other way.
//! 3. The CAVP block — the vectors in `src/vectors.rs` against Graviola's
//!    arithmetic.
//!
//! On the interface each check uses.  Graviola's ECDSA API is
//! message-oriented: `verify` hashes the message itself and there is no
//! prehashed entry point, nor can one be built downstream (the `Hash`
//! parameter's `zeroed_block` returns a type no public path names).  Checks
//! 1 and 2 therefore run over a real message, with this crate's side taking
//! `e = SHA-384(message) mod n` computed with the `sha2` crate, so the two
//! sides derive the same scalar through two independent SHA-384
//! implementations.
//!
//! The CAVP vectors carry only the digest `m`, not the message it came from,
//! so no `(m, r, s)` triple can be put through Graviola's verify at all.
//! What is reachable is Graviola's base-point multiplication, and the CAVP
//! block uses it on both published scalars: `d` must give the published
//! public key, and `k` must give the published `r`.  Signing each vector's
//! `(d, k)` over a real message and having Graviola verify closes the loop
//! over the same key material.  The digest `m` and the component `s` are the
//! two published fields Graviola cannot be made to check.

mod common;
use common::{affine_base, backend, pub_key, sb, sl, Rng};

use sha2::{Digest, Sha384};

use p384_ecdsa_rust::codec::limbs_from_be_hex;
use p384_ecdsa_rust::{grav, rc, reference, scalar, vectors::CAVP};

/// The canonical affine coordinates of `d * G`, computed by this crate.
fn our_public_affine(d: &[u64; 6]) -> ([u64; 6], [u64; 6]) {
    affine_base(d)
}

/// `e = SHA-384(message) mod n`, the scalar the emitted kernel takes, with
/// the digest from the `sha2` crate rather than from Graviola.
fn digest_scalar(message: &[u8]) -> [u64; 6] {
    let mut d = [0u8; 48];
    d.copy_from_slice(&Sha384::digest(message));
    scalar::reduce(&rc::limbs_from_be(&d))
}

/// The two SHA-384 implementations in this binary agree, so a disagreement
/// later in the file is about the curve arithmetic and not about the digest.
#[test]
fn sha384_agrees_between_sha2_and_graviola() {
    let mut rng = Rng::new(60);
    for _ in 0..32 {
        let len = (rng.next_u64() % 200) as usize;
        let msg: Vec<u8> = (0..len).map(|_| rng.next_u64() as u8).collect();
        let mut theirs = [0u8; 48];
        theirs.copy_from_slice(&grav::sha384(&msg));
        let mut ours = [0u8; 48];
        ours.copy_from_slice(&Sha384::digest(&msg));
        assert_eq!(ours, theirs, "SHA-384 differs on a {len}-byte message");
    }
}

/// Graviola derives the same public key from a private scalar as this crate
/// does, in both directions of the encoding.
#[test]
fn public_keys_agree() {
    let mut rng = Rng::new(61);
    let mut agreed = 0;
    for _ in 0..32 {
        let d = rng.scalar();
        let (x, y) = our_public_affine(&d);
        let sk = grav::signing_key(&d).expect("Graviola refused a valid private scalar");
        assert_eq!(
            grav::public_key_bytes(&sk),
            grav::x962(&x, &y),
            "public keys differ for d = {d:?}"
        );
        assert!(
            grav::verifying_key_from_coords(&x, &y).is_some(),
            "Graviola rejects d*G as a public key"
        );
        agreed += 1;
    }
    println!("public key: {agreed}/32 agree");
}

/// Check 1: the emitted kernel signs, Graviola verifies.
#[test]
fn our_signature_verifies_under_graviola() {
    for b in backend::all() {
        let mut rng = Rng::new(62);
        let mut accepted = 0;
        let mut rejected_tampered = 0;

        for i in 0..32 {
            let d = rng.scalar();
            let k = rng.scalar();
            let message = format!("catcrypt p384 ecdsa interop vector {i}");
            let e = digest_scalar(message.as_bytes());

            let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
            let mut ok = 0u64;
            (b.sign)(&sb(&e), &sb(&d), &sb(&k), &mut r, &mut s, &mut ok);
            assert_eq!(ok, 1, "[{}] case {i}: out-of-range signature", b.name);

            let (x, y) = our_public_affine(&d);
            let vk = grav::verifying_key_from_coords(&x, &y).expect("Graviola rejects d*G");
            let sig = grav::signature(&sl(&r), &sl(&s));

            assert!(
                grav::verify_message(&vk, message.as_bytes(), &sig),
                "[{}] case {i}: Graviola rejects a signature the kernel produced",
                b.name
            );
            accepted += 1;

            // A flipped bit in `s` must be rejected, so acceptance above is
            // not an artefact of the harness accepting everything.
            let mut bad = sig;
            bad[grav::SIG_LEN - 1] ^= 1;
            assert!(
                !grav::verify_message(&vk, message.as_bytes(), &bad),
                "[{}] case {i}: Graviola accepts a tampered signature",
                b.name
            );
            rejected_tampered += 1;
        }

        println!(
            "ours -> graviola [{}]: {accepted}/32 accepted, {rejected_tampered}/32 tampered rejected",
            b.name
        );
    }
}

/// Check 2: Graviola signs, the emitted kernel verifies.
#[test]
fn graviola_signature_verifies_under_our_kernel() {
    for b in backend::all() {
        let mut rng = Rng::new(63);
        let mut accepted = 0;
        let mut rejected_tampered = 0;

        for i in 0..32 {
            let d = rng.scalar();
            let message = format!("graviola p384 ecdsa interop vector {i}");
            let e = digest_scalar(message.as_bytes());

            let sk = grav::signing_key(&d).expect("Graviola refused a valid private scalar");
            let sig = grav::sign_message(&sk, message.as_bytes());
            let (r, s) = grav::split_signature(&sig);

            let q = pub_key(b, &d);
            let mut ok = 0u64;
            (b.verify)(&sb(&e), &sb(&r), &sb(&s), &q, &mut ok);
            assert_eq!(
                ok, 1,
                "[{}] case {i}: the kernel rejects a Graviola signature (r = {r:?}, s = {s:?})",
                b.name
            );
            accepted += 1;

            let s_bad = reference::add_mod_n(&s, &scalar::one());
            let mut ok_bad = 0u64;
            (b.verify)(&sb(&e), &sb(&r), &sb(&s_bad), &q, &mut ok_bad);
            assert_eq!(ok_bad, 0, "[{}] case {i}: a tampered signature was accepted", b.name);
            rejected_tampered += 1;
        }

        println!(
            "graviola -> ours [{}]: {accepted}/32 accepted, {rejected_tampered}/32 tampered rejected",
            b.name
        );
    }
}

/// Check 3a: Graviola's base-point multiplication takes each CAVP `d` to the
/// vector's published public key.
#[test]
fn cavp_public_keys_agree_with_graviola() {
    let mut matched = 0;
    for (i, v) in CAVP.iter().enumerate() {
        let d = limbs_from_be_hex(v.d);
        let qx = limbs_from_be_hex(v.q_x);
        let qy = limbs_from_be_hex(v.q_y);
        let sk = grav::signing_key(&d).expect("Graviola refused a CAVP private scalar");
        assert_eq!(
            grav::public_key_bytes(&sk),
            grav::x962(&qx, &qy),
            "vector {i}: Graviola's d*G is not the published (Qx, Qy)"
        );
        matched += 1;
    }
    assert_eq!(matched, CAVP.len());
    println!("CAVP d*G under graviola: {matched}/{} match", CAVP.len());
}

/// Check 3b: Graviola's base-point multiplication takes each CAVP `k` to a
/// point whose affine `x` reduces to the vector's published `r`.
#[test]
fn cavp_r_is_x_of_k_times_g_under_graviola() {
    let mut matched = 0;
    for (i, v) in CAVP.iter().enumerate() {
        let k = limbs_from_be_hex(v.k);
        let want_r = limbs_from_be_hex(v.r);
        let sk = grav::signing_key(&k).expect("Graviola refused a CAVP nonce");
        let encoded = grav::public_key_bytes(&sk);
        let mut x = [0u8; grav::SCALAR_LEN];
        x.copy_from_slice(&encoded[1..1 + grav::SCALAR_LEN]);
        assert_eq!(
            scalar::reduce(&grav::from_be48(&x)),
            want_r,
            "vector {i}: x(k*G) mod n under Graviola is not the published r"
        );
        matched += 1;
    }
    assert_eq!(matched, CAVP.len());
    println!("CAVP r = x(k*G) under graviola: {matched}/{} match", CAVP.len());
}

/// Check 3c: signing a real message with each CAVP `(d, k)` through the
/// emitted kernel produces a signature Graviola accepts under the vector's
/// published public key, with the same `r` the vector publishes.
///
/// `r` depends only on `k`, so it is the vector's; `s` is not, because the
/// digest is this message's and not the vector's unpublished one.
#[test]
fn cavp_keys_sign_and_graviola_verifies() {
    for b in backend::all() {
        let mut accepted = 0;
        for (i, v) in CAVP.iter().enumerate() {
            let d = limbs_from_be_hex(v.d);
            let k = limbs_from_be_hex(v.k);
            let qx = limbs_from_be_hex(v.q_x);
            let qy = limbs_from_be_hex(v.q_y);
            let want_r = limbs_from_be_hex(v.r);

            let message = format!("catcrypt cavp key reuse {i}");
            let e = digest_scalar(message.as_bytes());

            let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
            let mut ok = 0u64;
            (b.sign)(&sb(&e), &sb(&d), &sb(&k), &mut r, &mut s, &mut ok);
            assert_eq!(ok, 1, "[{}] vector {i}: out-of-range output", b.name);
            assert_eq!(sl(&r), want_r, "[{}] vector {i}: r is not the published r", b.name);

            let vk = grav::verifying_key_from_coords(&qx, &qy)
                .expect("Graviola rejects a CAVP public key");
            let sig = grav::signature(&sl(&r), &sl(&s));
            assert!(
                grav::verify_message(&vk, message.as_bytes(), &sig),
                "[{}] vector {i}: Graviola rejects a signature under the published key",
                b.name
            );
            accepted += 1;
        }
        assert_eq!(accepted, CAVP.len());
        println!(
            "CAVP (d, k) signed and verified by graviola [{}]: {accepted}/{}",
            b.name,
            CAVP.len()
        );
    }
}

/// The HMAC_DRBG reconstruction in `grav::drbg_nonce_path` produces a nonce
/// in range, which is what the benchmark's signing-component row times.
///
/// It cannot be checked against Graviola's own `sign`, whose sixteen bytes of
/// added randomness are read inside the call and never returned.  What is
/// checked here is that the reconstruction runs the HMAC chain it claims to
/// and lands on a usable scalar, so the timed work is the real work.
#[test]
fn drbg_reconstruction_yields_a_usable_nonce() {
    let mut rng = Rng::new(64);
    let mut usable = 0;
    for _ in 0..16 {
        let d = grav::be48(&rng.scalar());
        let e = grav::be48(&rng.scalar());
        let random: [u8; 16] = std::array::from_fn(|_| rng.next_u64() as u8);
        let candidate = grav::drbg_nonce_path(&d, &e, &random);
        let k = grav::from_be48(&candidate);
        assert_eq!(scalar::ct_lt_n(&k), 1, "the DRBG nonce is not below n");
        assert!(grav::signing_key(&k).is_some(), "Graviola refuses the DRBG nonce");
        usable += 1;
    }
    println!("drbg reconstruction: {usable}/16 nonces in range");
}
