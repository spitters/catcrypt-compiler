//! Cross-implementation interop between the emitted P-384 ECDSA kernel and
//! four production libraries, BoringSSL, OpenSSL 3.0, AWS-LC and Microsoft
//! SymCrypt, run once per leaf backend.  The AWS-LC and SymCrypt suites print
//! a `SKIP:` line and pass when their library is absent
//! (`P384_AWSLC_LIBCRYPTO`, `P384_SYMCRYPT_LIB`).
//!
//! The first three take a prehashed digest and can be driven with a
//! caller-supplied nonce (`src/bssl.rs`, `src/ossl.rs`, `src/awslc.rs`), so unlike the
//! Graviola suite every published field of a CAVP vector — `m`, `r` and `s`
//! included — is checked through each of them.  SymCrypt's module exports no
//! nonce-supplied signing entry point (`src/symcrypt.rs`), so its suite has
//! checks 1 and 2 and a CAVP check without the signing half; see
//! `mod symcrypt_suite`.
//!
//! Per library:
//!
//! 1. `ours_verifies_under_lib` — the emitted kernel signs, the library's
//!    `ECDSA_do_verify` accepts; the signature with one bit of `s` flipped
//!    is rejected.
//! 2. `lib_signature_verifies_under_ours` — the library's own `ECDSA_do_sign`
//!    (its nonce) signs, the emitted `p384_ecdsa_verify` returns `ok = 1`;
//!    `s + 1 mod n` returns `ok = 0`.
//! 3. `nonce_supplied_signatures_agree` — the library signs with the nonce
//!    the kernel is given, and the two `(r, s)` are byte-identical.
//! 4. `cavp_reproduces_r_and_s` — each CAVP `(d, Q, k, m)` signed by the
//!    library with the nonce supplied gives the published `(r, s)`, which
//!    the library then verifies under the published `Q`, and rejects with a
//!    bit of `s` flipped.
//!
//! Only `#[cfg(feature = "production")]` builds contain these tests.

#![cfg(feature = "production")]

mod common;
use common::{affine_base, backend, pub_key, sb, sl, Rng};

use p384_ecdsa_rust::codec::limbs_from_be_hex;
use p384_ecdsa_rust::rc::{be_from_limbs, limbs_from_be};
use p384_ecdsa_rust::{reference, scalar, vectors::CAVP};

/// Random signing inputs: a digest scalar `e`, a private `d` and a nonce
/// `k`, each in `[1, n)`.
fn inputs(rng: &mut Rng) -> ([u64; 6], [u64; 6], [u64; 6]) {
    (rng.scalar(), rng.scalar(), rng.scalar())
}

/// Whether the AWS-LC library is present; prints a `SKIP:` line when not.
fn awslc_ready() -> bool {
    let ok = p384_ecdsa_rust::awslc::available();
    if !ok {
        println!("SKIP: no AWS-LC libcrypto at {}", p384_ecdsa_rust::awslc::library_path());
    }
    ok
}

/// Whether the SymCrypt module is present; prints a `SKIP:` line when not.
fn symcrypt_ready() -> bool {
    let ok = p384_ecdsa_rust::symcrypt::available();
    if !ok {
        println!("SKIP: no SymCrypt module at {}", p384_ecdsa_rust::symcrypt::library_path());
    }
    ok
}

/// `keys`, check 1 and check 2, for a module that has `use ... as lib`, a
/// `ready()` function, and `use super::*`.  Neither check needs a supplied
/// nonce.
macro_rules! interop_tests {
    ($label:literal) => {
        fn keys(d: &[u64; 6]) -> (lib::Key, lib::Key) {
            let (x, y) = affine_base(d);
            let (xb, yb) = (be_from_limbs(&x), be_from_limbs(&y));
            let sk = lib::signing_key(&be_from_limbs(d), &xb, &yb)
                .expect(concat!($label, " refused a valid private key"));
            let vk = lib::verifying_key(&xb, &yb)
                .expect(concat!($label, " rejected d*G as a public key"));
            (sk, vk)
        }

        #[test]
        fn ours_verifies_under_lib() {
            if !ready() {
                return;
            }
            for b in backend::all() {
                let mut rng = Rng::new(70);
                let (mut accepted, mut rejected) = (0, 0);
                for i in 0..32 {
                    let (e, d, k) = inputs(&mut rng);
                    let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
                    let mut ok = 0u64;
                    (b.sign)(&sb(&e), &sb(&d), &sb(&k), &mut r, &mut s, &mut ok);
                    assert_eq!(ok, 1, "[{}] case {i}: out-of-range signature", b.name);

                    let (_, vk) = keys(&d);
                    let digest = be_from_limbs(&e);
                    let (rb, sbe) = (be_from_limbs(&sl(&r)), be_from_limbs(&sl(&s)));
                    assert!(
                        lib::verify(&vk, &digest, &lib::sig(&rb, &sbe)),
                        "[{}] case {i}: {} rejects a signature the kernel produced",
                        b.name,
                        $label
                    );
                    accepted += 1;

                    let mut bad = sbe;
                    bad[47] ^= 1;
                    assert!(
                        !lib::verify(&vk, &digest, &lib::sig(&rb, &bad)),
                        "[{}] case {i}: {} accepts a tampered signature",
                        b.name,
                        $label
                    );
                    rejected += 1;
                }
                println!(
                    "ours -> {} [{}]: {accepted}/32 accepted, {rejected}/32 tampered rejected",
                    $label, b.name
                );
            }
        }

        #[test]
        fn lib_signature_verifies_under_ours() {
            if !ready() {
                return;
            }
            for b in backend::all() {
                let mut rng = Rng::new(71);
                let (mut accepted, mut rejected) = (0, 0);
                for i in 0..32 {
                    let (e, d, _) = inputs(&mut rng);
                    let (sk, _) = keys(&d);
                    let (rb, sbe) = lib::sign(&sk, &be_from_limbs(&e));
                    let (r, s) = (limbs_from_be(&rb), limbs_from_be(&sbe));

                    let q = pub_key(b, &d);
                    let mut ok = 0u64;
                    (b.verify)(&sb(&e), &sb(&r), &sb(&s), &q, &mut ok);
                    assert_eq!(
                        ok, 1,
                        "[{}] case {i}: the kernel rejects a {} signature (r = {r:?}, s = {s:?})",
                        b.name, $label
                    );
                    accepted += 1;

                    let s_bad = reference::add_mod_n(&s, &scalar::one());
                    let mut ok_bad = 0u64;
                    (b.verify)(&sb(&e), &sb(&r), &sb(&s_bad), &q, &mut ok_bad);
                    assert_eq!(ok_bad, 0, "[{}] case {i}: a tampered signature was accepted", b.name);
                    rejected += 1;
                }
                println!(
                    "{} -> ours [{}]: {accepted}/32 accepted, {rejected}/32 tampered rejected",
                    $label, b.name
                );
            }
        }
    };
}

macro_rules! suite {
    ($modname:ident, $lib:ident, $label:literal, $ready:expr) => {
        mod $modname {
            use super::*;
            use p384_ecdsa_rust::$lib as lib;

            fn ready() -> bool {
                $ready
            }

            interop_tests!($label);

            #[test]
            fn nonce_supplied_signatures_agree() {
                if !ready() {
                    return;
                }
                for b in backend::all() {
                    let mut rng = Rng::new(72);
                    let mut agreed = 0;
                    for i in 0..32 {
                        let (e, d, k) = inputs(&mut rng);
                        let (mut r, mut s) = ([0u8; 48], [0u8; 48]);
                        let mut ok = 0u64;
                        (b.sign)(&sb(&e), &sb(&d), &sb(&k), &mut r, &mut s, &mut ok);
                        assert_eq!(ok, 1, "[{}] case {i}: out-of-range signature", b.name);

                        let (sk, _) = keys(&d);
                        let (rb, sbe) = lib::sign_with_nonce(&sk, &be_from_limbs(&e), &be_from_limbs(&k))
                            .expect(concat!($label, " refused a nonce-supplied signature"));
                        assert_eq!(
                            (limbs_from_be(&rb), limbs_from_be(&sbe)),
                            (sl(&r), sl(&s)),
                            "[{}] case {i}: (r, s) differ between the kernel and {}",
                            b.name,
                            $label
                        );
                        agreed += 1;
                    }
                    println!("nonce-supplied (r, s), ours vs {} [{}]: {agreed}/32 identical", $label, b.name);
                }
            }

            #[test]
            fn cavp_reproduces_r_and_s() {
                if !ready() {
                    return;
                }
                let (mut reproduced, mut verified, mut rejected) = (0, 0, 0);
                for (i, v) in CAVP.iter().enumerate() {
                    let hex = |h: &str| be_from_limbs(&limbs_from_be_hex(h));
                    let (d, qx, qy, k, m) = (hex(v.d), hex(v.q_x), hex(v.q_y), hex(v.k), hex(v.m));
                    let (want_r, want_s) = (hex(v.r), hex(v.s));

                    let sk = lib::signing_key(&d, &qx, &qy)
                        .expect(concat!($label, " refused a CAVP key pair"));
                    let (r, s) = lib::sign_with_nonce(&sk, &m, &k)
                        .expect(concat!($label, " refused a CAVP nonce"));
                    assert_eq!(r, want_r, "vector {i}: {} r is not the published r", $label);
                    assert_eq!(s, want_s, "vector {i}: {} s is not the published s", $label);
                    reproduced += 1;

                    let vk = lib::verifying_key(&qx, &qy).expect(concat!($label, " rejected a CAVP Q"));
                    assert!(
                        lib::verify(&vk, &m, &lib::sig(&want_r, &want_s)),
                        "vector {i}: {} rejects the published signature",
                        $label
                    );
                    verified += 1;

                    let mut bad = want_s;
                    bad[47] ^= 1;
                    assert!(
                        !lib::verify(&vk, &m, &lib::sig(&want_r, &bad)),
                        "vector {i}: {} accepts a tampered published signature",
                        $label
                    );
                    rejected += 1;
                }
                assert_eq!(reproduced, CAVP.len());
                println!(
                    "CAVP under {}: {reproduced}/{n} (r, s) reproduced with k supplied, {verified}/{n} verified, {rejected}/{n} tampered rejected",
                    $label,
                    n = CAVP.len()
                );
            }
        }
    };
}

suite!(boringssl, bssl, "BoringSSL", true);
suite!(openssl, ossl, "OpenSSL", true);
suite!(aws_lc, awslc, "AWS-LC", awslc_ready());

/// SymCrypt: checks 1 and 2 as above, then what can be checked without a
/// supplied nonce.
mod symcrypt_suite {
    use super::*;
    use p384_ecdsa_rust::symcrypt as lib;

    fn ready() -> bool {
        symcrypt_ready()
    }

    interop_tests!("SymCrypt");

    /// 4'. Each CAVP key pair `(d, Q)` passes SymCrypt's pairwise import
    /// check; the published `(m, r, s)` verifies under the published `Q`,
    /// and a flipped bit of `s` is rejected; a SymCrypt signature of `m`
    /// under `d` verifies under SymCrypt and under the kernel.  The
    /// published `(r, s)` cannot be reproduced: `k` cannot be supplied.
    #[test]
    fn cavp_verifies_and_signs() {
        if !ready() {
            return;
        }
        let (mut verified, mut rejected, mut own) = (0, 0, 0);
        for (i, v) in CAVP.iter().enumerate() {
            let hex = |h: &str| be_from_limbs(&limbs_from_be_hex(h));
            let (d, qx, qy, m) = (hex(v.d), hex(v.q_x), hex(v.q_y), hex(v.m));
            let (want_r, want_s) = (hex(v.r), hex(v.s));

            let sk = lib::signing_key(&d, &qx, &qy).expect("SymCrypt refused a CAVP key pair");
            let vk = lib::verifying_key(&qx, &qy).expect("SymCrypt rejected a CAVP Q");
            assert!(lib::verify(&vk, &m, &lib::sig(&want_r, &want_s)), "vector {i}: published signature rejected");
            verified += 1;
            let mut bad = want_s;
            bad[47] ^= 1;
            assert!(!lib::verify(&vk, &m, &lib::sig(&want_r, &bad)), "vector {i}: tampered signature accepted");
            rejected += 1;

            let (r, s) = lib::sign(&sk, &m);
            assert!(lib::verify(&vk, &m, &lib::sig(&r, &s)), "vector {i}: SymCrypt rejects its own signature");
            // The CAVP digests are 48 bytes, so `m` is the digest scalar;
            // reduce it for the kernel's `e < n` input.
            let e = scalar::reduce(&limbs_from_be(&m));
            for b in backend::all() {
                let q = (b.point_from_affine)(&limbs_from_be(&qx), &limbs_from_be(&qy));
                let mut ok = 0u64;
                (b.verify)(&sb(&e), &sb(&limbs_from_be(&r)), &sb(&limbs_from_be(&s)), &q, &mut ok);
                assert_eq!(ok, 1, "[{}] vector {i}: the kernel rejects SymCrypt's signature", b.name);
            }
            own += 1;
        }
        assert_eq!(verified, CAVP.len());
        println!(
            "CAVP under SymCrypt: {verified}/{n} verified, {rejected}/{n} tampered rejected, \
             {own}/{n} SymCrypt signatures accepted by the kernel on every backend",
            n = CAVP.len()
        );
    }

    /// Two signatures of the same digest under the same key differ, and
    /// both verify: `SymCryptEcDsaSign` draws a fresh nonce on every call.
    #[test]
    fn full_api_nonce_is_fresh() {
        if !ready() {
            return;
        }
        let mut rng = Rng::new(75);
        let (e, d, _) = inputs(&mut rng);
        let (sk, vk) = keys(&d);
        let digest = be_from_limbs(&e);
        let (r1, s1) = lib::sign(&sk, &digest);
        let (r2, s2) = lib::sign(&sk, &digest);
        assert_ne!(r1, r2, "two SymCrypt signatures share r");
        assert!(lib::verify(&vk, &digest, &lib::sig(&r1, &s1)));
        assert!(lib::verify(&vk, &digest, &lib::sig(&r2, &s2)));
        println!("SymCrypt: two signatures of one digest differ in r; both verify");
    }

    /// SymCrypt's key import rejects a public point off the curve, a
    /// coordinate equal to `p`, a signing key whose `Q` is not `d*G`, and
    /// the private keys `0` and `n`, under the default validation.
    #[test]
    fn key_import_rejects_invalid_keys() {
        if !ready() {
            return;
        }
        let mut rng = Rng::new(76);
        let (_, d, _) = inputs(&mut rng);
        let (x, y) = affine_base(&d);
        let (xb, yb) = (be_from_limbs(&x), be_from_limbs(&y));
        let mut off = yb;
        off[47] ^= 1;
        assert!(lib::verifying_key(&xb, &off).is_none(), "off-curve point accepted");
        let p_be = p384_ecdsa_rust::sec1::be48(&p384_ecdsa_rust::sec1::P);
        assert!(lib::verifying_key(&p_be, &yb).is_none(), "x = p accepted");
        assert!(lib::verifying_key(&xb, &p_be).is_none(), "y = p accepted");
        let d1 = reference::add_mod_n(&d, &scalar::one());
        assert!(lib::signing_key(&be_from_limbs(&d1), &xb, &yb).is_none(), "mismatched key pair accepted");
        assert!(lib::signing_key(&[0u8; 48], &xb, &yb).is_none(), "d = 0 accepted");
        assert!(lib::signing_key(&be_from_limbs(&scalar::N), &xb, &yb).is_none(), "d = n accepted");
        println!("SymCrypt key import: off-curve, x = p, y = p, mismatched pair, d = 0, d = n rejected");
    }
}

/// The SymCrypt module accepts the API version the bridge was written
/// against and refuses a later minor version and another API number.
#[test]
fn symcrypt_is_103_13() {
    if !symcrypt_ready() {
        return;
    }
    use p384_ecdsa_rust::symcrypt;
    let (api_v, minor) = symcrypt::API_VERSION;
    assert!(symcrypt::accepts_version(api_v, minor));
    assert!(!symcrypt::accepts_version(api_v, minor + 1), "the module is newer than 103.13");
    assert!(!symcrypt::accepts_version(api_v + 1, 0));
    println!(
        "SymCrypt loaded from {}: SymCryptModuleInitEx accepts {api_v}.{minor}, refuses {api_v}.{} and {}.0",
        symcrypt::library_path(),
        minor + 1,
        api_v + 1
    );
}

/// The SymCrypt RNG arm the benchmark times returns 48 bytes, not all equal
/// across sixteen calls.
#[test]
fn symcrypt_random_draw_runs() {
    if !symcrypt_ready() {
        return;
    }
    let mut seen = std::collections::HashSet::new();
    for _ in 0..16 {
        let mut b = [0u8; 48];
        p384_ecdsa_rust::symcrypt::random48(&mut b);
        seen.insert(b);
    }
    assert_eq!(seen.len(), 16, "SymCryptRandom repeated a 48-byte output");
    println!("SymCrypt SymCryptRandom(48): 16/16 distinct");
}

/// The library loaded as AWS-LC reports itself as AWS-LC.
#[test]
fn awslc_is_aws_lc() {
    if !awslc_ready() {
        return;
    }
    let (num, api_num, text) = p384_ecdsa_rust::awslc::version();
    println!(
        "AWS-LC loaded from {}: {text} (OpenSSL_version_num 0x{num:08x}, awslc_api_version_num {api_num})",
        p384_ecdsa_rust::awslc::library_path()
    );
    assert!(text.contains("AWS-LC"), "expected AWS-LC, loaded {text}");
}

/// The AWS-LC nonce-derivation arm the benchmark times runs to completion
/// (`BN_rand_range_ex` returns one) on sixteen keys.
#[test]
fn awslc_nonce_parts_run() {
    if !awslc_ready() {
        return;
    }
    use p384_ecdsa_rust::awslc;
    let mut rng = Rng::new(74);
    let mut st = awslc::NonceState::new();
    for _ in 0..16 {
        let (e, d, _) = inputs(&mut rng);
        let (x, y) = affine_base(&d);
        let sk = awslc::signing_key(&be_from_limbs(&d), &be_from_limbs(&x), &be_from_limbs(&y))
            .expect("AWS-LC refused a valid private key");
        awslc::nonce_parts(&sk, &sb(&d), &be_from_limbs(&e), &mut st);
    }
    println!("AWS-LC SHA512 + BN_rand_range_ex(1, n): 16/16 ran");
}

/// The loaded OpenSSL is the 3.0 series the module header describes.
#[test]
fn openssl_is_the_3_0_series() {
    let (num, text) = p384_ecdsa_rust::ossl::version();
    println!("OpenSSL loaded from {}: {text} (0x{num:08x})", p384_ecdsa_rust::ossl::library_path());
    assert_eq!(num >> 20, 0x300, "expected OpenSSL 3.0.x, loaded {text}");
}

/// The OpenSSL nonce derivation the benchmark times separately yields a
/// nonce below `n`, so the timed work is the real work.
#[test]
fn openssl_dsa_nonce_is_in_range() {
    let mut rng = Rng::new(73);
    let mut st = p384_ecdsa_rust::ossl::NonceState::new();
    let mut usable = 0;
    for _ in 0..16 {
        let (e, d, _) = inputs(&mut rng);
        let (x, y) = affine_base(&d);
        let sk = p384_ecdsa_rust::ossl::signing_key(&be_from_limbs(&d), &be_from_limbs(&x), &be_from_limbs(&y))
            .expect("OpenSSL refused a valid private key");
        let k = limbs_from_be(&p384_ecdsa_rust::ossl::dsa_nonce(&sk, &be_from_limbs(&e), &mut st));
        assert_eq!(scalar::ct_lt_n(&k), 1, "BN_generate_dsa_nonce returned a value not below n");
        usable += 1;
    }
    println!("OpenSSL BN_generate_dsa_nonce: {usable}/16 nonces below n");
}
