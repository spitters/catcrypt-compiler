//! The emitted entry points against RustCrypto `p384` 0.13.1 / `ecdsa`
//! 0.16.9, once per leaf backend.
//!
//! Signing is driven with an explicit nonce on both sides
//! (`SignPrimitive::try_sign_prehashed`), not RFC 6979, because the emitted
//! kernel takes `k` as an input.
//!
//! The emitted kernel range-checks `r` and `s`, validates `Q`, and reports
//! an out-of-range signing output through `ok`, so it should agree with
//! RustCrypto on every input.  `historical_divergences_are_now_rejected`
//! holds the four inputs on which the previous kernel accepted and
//! RustCrypto rejected; each is asserted rejected, alongside the fact that
//! the underlying arithmetic relation still holds, which is what made the
//! acceptance possible.

mod common;
use common::{backend, pub_key, sb, sl, Backend, Rng};

use p384::group::g1_scalar_mul_base;
use p384_ecdsa_rust::{rc, reference, scalar};

/// The RustCrypto affine point for `d * G`.
fn rc_public(d: &[u64; 6]) -> p384_rc::AffinePoint {
    let (x, y) = common::affine_base(d);
    rc::affine_from_coords(&x, &y).expect("d*G is on the curve")
}

#[cfg(not(feature = "force-fallback"))]
#[test]
fn built_against_the_emitted_sources() {
    assert!(p384_ecdsa_rust::EMITTED, "gen/ holds no emitted source");
}

#[test]
fn sign_matches_rustcrypto() {
    for b in backend::all() {
        let mut rng = Rng::new(30);
        let mut matched = 0;
        for _ in 0..64 {
            let e = rng.scalar();
            let d = rng.scalar();
            let k = rng.scalar();

            let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
            let mut ok = 0u64;
            (b.sign)(&sb(&e), &sb(&d), &sb(&k), &mut r, &mut s, &mut ok);

            let (rr, rs) = rc::sign(&e, &d, &k).expect("RustCrypto refused a valid input");
            assert_eq!(sl(&r), rr, "{}: r differs for k = {k:?}", b.name);
            assert_eq!(sl(&s), rs, "{}: s differs for k = {k:?}", b.name);
            assert_eq!(ok, 1, "{}: sign reported out of range for k = {k:?}", b.name);
            matched += 1;
        }
        println!("sign [{}]: {matched}/64 identical (r, s)", b.name);
    }
}

#[test]
fn verify_matches_rustcrypto_on_valid_and_tampered_signatures() {
    for b in backend::all() {
        let mut rng = Rng::new(31);
        let mut agreed = 0;
        let mut cases = 0;
        for _ in 0..32 {
            let e = rng.scalar();
            let d = rng.scalar();
            let k = rng.scalar();
            let q = pub_key(b, &d);
            let qrc = rc_public(&d);

            let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
            let mut signed = 0u64;
            (b.sign)(&sb(&e), &sb(&d), &sb(&k), &mut r, &mut s, &mut signed);
            assert_eq!(signed, 1, "{}", b.name);

            let variants: [([u64; 6], [u64; 6], [u64; 6]); 4] = [
                (e, sl(&r), sl(&s)),
                (scalar::add(&e, &scalar::one()), sl(&r), sl(&s)),
                (e, scalar::add(&sl(&r), &scalar::one()), sl(&s)),
                (e, sl(&r), scalar::add(&sl(&s), &scalar::one())),
            ];
            for (ev, rv, sv) in variants {
                let mut ok = 0u64;
                (b.verify)(&sb(&ev), &sb(&rv), &sb(&sv), &q, &mut ok);
                let rc_ok = rc::verify(&ev, &rv, &sv, &qrc);
                assert_eq!(
                    ok == 1,
                    rc_ok,
                    "{}: verdicts differ: e = {ev:?}, r = {rv:?}, s = {sv:?}",
                    b.name
                );
                agreed += 1;
                cases += 1;
            }
        }
        println!("verify [{}]: {agreed}/{cases} verdicts agree", b.name);
    }
}

#[test]
fn verify_matches_rustcrypto_on_a_wrong_public_key() {
    for b in backend::all() {
        let mut rng = Rng::new(32);
        for _ in 0..16 {
            let e = rng.scalar();
            let d = rng.scalar();
            let other = rng.scalar();
            let k = rng.scalar();

            let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
            let mut signed = 0u64;
            (b.sign)(&sb(&e), &sb(&d), &sb(&k), &mut r, &mut s, &mut signed);
            assert_eq!(signed, 1, "{}", b.name);

            let mut ok = 0u64;
            (b.verify)(&sb(&e), &r, &s, &pub_key(b, &other), &mut ok);
            assert_eq!(ok, 0, "{}", b.name);
            assert!(!rc::verify(&e, &sl(&r), &sl(&s), &rc_public(&other)));
        }
    }
}

/// `-a mod n`, for `a` in `[1, n)`.
fn neg_mod_n(a: &[u64; 6]) -> [u64; 6] {
    reference::sub_mod_n(&[0u64; 6], a)
}

/// The four inputs on which the previous emitted kernel accepted and
/// RustCrypto rejected.  In each, the ECDSA arithmetic relation genuinely
/// holds — `reference::verify_core` is asserted true — and the acceptance
/// came from the kernel computing that relation and nothing else.  The
/// current kernel rejects all four through `p384_scalar_in_range` and
/// `p384_point_valid`, in every backend.
fn historical_divergences(b: &Backend) -> Vec<&'static str> {
    let mut rng = Rng::new(33);
    let zero = [0u64; 6];
    let one = scalar::one();
    let d = rng.scalar();
    let q = pub_key(b, &d);
    let qref = g1_scalar_mul_base(&d);
    let qrc = rc_public(&d);

    let mut closed = Vec::new();

    // D1: e = 0, r = 0, s = 1.  u1 = u2 = 0, so R is the identity, x(R) is
    // taken as 0, and 0 == r.  RustCrypto rejects r = 0; so now does the
    // emitted kernel, on the range check for r.
    {
        let mut ok = 0u64;
        (b.verify)(&sb(&zero), &sb(&zero), &sb(&one), &q, &mut ok);
        assert!(reference::verify_core(&zero, &zero, &one, &qref));
        assert_eq!((ok, rc::verify(&zero, &zero, &one, &qrc)), (0, false));
        closed.push("D1 e=0, r=0, s=1: relation holds, kernel rejects (r out of range)");
    }

    // D2: r = 0, s = 0, any e.  inv(0) = 0, so u1 = u2 = 0 and the same
    // path is taken.  Both range checks fail now.
    {
        let e = rng.scalar();
        let mut ok = 0u64;
        (b.verify)(&sb(&e), &sb(&zero), &sb(&zero), &q, &mut ok);
        assert!(reference::verify_core(&e, &zero, &zero, &qref));
        assert_eq!((ok, rc::verify(&e, &zero, &zero, &qrc)), (0, false));
        closed.push("D2 r=0, s=0: relation holds, kernel rejects (r and s out of range)");
    }

    // D3: a scalar at or above n, taken mod n by the scalar leaves.  A
    // signature is built with a small `s` by solving for the digest
    // (`e = s*k - r*d mod n`), so that `s + n` is still below 2^384 and is
    // a legal 48-byte input.  Wycheproof tcId 165 is this case end to end.
    {
        let k = rng.scalar();
        let r = reference::reduce_once(&reference::affine_x(&g1_scalar_mul_base(&k)));
        let mut s_small = [0u64; 6];
        s_small[0] = 0x0000_0000_0001_3579;
        let e = reference::add_mod_n(
            &scalar::mul(&s_small, &k),
            &neg_mod_n(&scalar::mul(&r, &d)),
        );

        // The in-range signature verifies on both sides.
        let mut ok = 0u64;
        (b.verify)(&sb(&e), &sb(&r), &sb(&s_small), &q, &mut ok);
        assert_eq!(ok, 1, "{}: the constructed signature does not verify", b.name);
        assert!(rc::verify(&e, &r, &s_small, &qrc));

        // s + n is the same scalar mod n and fits in 384 bits.
        let mut s_plus_n = s_small;
        let mut carry = false;
        for i in 0..6 {
            let (t, c1) = s_plus_n[i].overflowing_add(scalar::N[i]);
            let (t2, c2) = t.overflowing_add(carry as u64);
            s_plus_n[i] = t2;
            carry = c1 | c2;
        }
        assert!(!carry, "s + n overflowed 384 bits");

        let mut ok2 = 0u64;
        (b.verify)(&sb(&e), &sb(&r), &sb(&s_plus_n), &q, &mut ok2);
        assert!(reference::verify_core(&e, &r, &s_plus_n, &qref));
        assert_eq!((ok2, rc::verify(&e, &r, &s_plus_n, &qrc)), (0, false));
        closed.push("D3 s >= n with s = s0 + n: relation holds, kernel rejects (s out of range)");
    }

    // D4: Q = the point at infinity, s = 1, r = x(e*G) mod n.  u2*Q is the
    // identity whatever u2 is, so the relation holds for a forged pair with
    // no private key.  The point check rejects the identity.
    {
        let e = rng.scalar();
        let r = reference::reduce_once(&reference::affine_x(&g1_scalar_mul_base(&e)));
        let id = p384::group::g1_identity();
        let mut ok = 0u64;
        (b.verify)(&sb(&e), &sb(&r), &sb(&one), &(b.identity)(), &mut ok);
        assert!(reference::verify_core(&e, &r, &one, &id));
        assert_eq!(ok, 0, "{}: the emitted kernel accepted a key-free forgery", b.name);
        // The identity has no affine encoding, so RustCrypto has no such
        // public key at all.
        assert!(rc::affine_from_coords(&zero, &zero).is_none());
        closed.push("D4 Q = infinity, s=1, r=x(e*G): relation holds, kernel rejects (Q invalid)");
    }

    closed
}

#[test]
fn historical_divergences_are_now_rejected() {
    for b in backend::all() {
        let closed = historical_divergences(b);
        for line in &closed {
            println!("closed [{}]: {line}", b.name);
        }
        assert_eq!(closed.len(), 4);
    }
}

/// `r` or `s` at or above `n` is outside the encoding both sides expect.
/// RustCrypto refuses the signature; the emitted kernel rejects it on the
/// range check.
#[test]
fn out_of_range_r_and_s_are_rejected_by_both() {
    for b in backend::all() {
        let mut rng = Rng::new(34);
        let d = rng.scalar();
        let q = pub_key(b, &d);
        let qrc = rc_public(&d);
        let e = rng.scalar();
        let one = scalar::one();

        for bad in [scalar::N, [u64::MAX; 6]] {
            let mut ok = 0u64;
            (b.verify)(&sb(&e), &sb(&bad), &sb(&one), &q, &mut ok);
            assert_eq!(ok, 0, "{}", b.name);
            assert!(!rc::verify(&e, &bad, &one, &qrc));

            (b.verify)(&sb(&e), &sb(&one), &sb(&bad), &q, &mut ok);
            assert_eq!(ok, 0, "{}", b.name);
            assert!(!rc::verify(&e, &one, &bad, &qrc));
        }
    }
}
