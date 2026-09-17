//! Wall-clock comparison of the emitted P-384 ECDSA sign and verify, over
//! every leaf backend this binary was built with, against RustCrypto `p384`
//! 0.13.1 / `ecdsa` 0.16.9 and Graviola 0.4.1.
//!
//! Every side runs in this process, on the same inputs, interleaved
//! round-robin: one repetition of every variant, then the next repetition.
//! A sequential sweep is not used because on this machine the clock drifts
//! by more over a sweep than the variants differ from each other
//! (`p384-safe-rust/build.sh` records the measurement that established
//! this).
//!
//! The CryptOpt assembly is a compile-time choice of `p384-safe-rust`, so
//! the two AUCurves configurations cannot be interleaved in one process.
//! Run the binary twice, once with `P384_NO_CRYPTOPT=1`, and report the two
//! as separate rows.  [`p384::CRYPTOPT_ASM`] says which one a given binary
//! is, and the header line prints it.  The s2n-bignum backend is unaffected
//! by that choice and appears in both processes, which makes its two rows a
//! check on the run-to-run drift.
//!
//! What each side is, in the terms of `bench/AGENTS.md`:
//!
//! * ours, `aucurves` — the orchestration is the CatCrypt compiler's
//!   emitted Rust (`gen/*.rs`, `EMITTED == true`) over the leaf shims in
//!   `src/leaves.rs`; the group law is AUCurves `p384-safe-rust`
//!   (Rocq-emitted RCB formulas, adopted verified leaf) and the base field
//!   is fiat-crypto, with the CryptOpt assembly on top when it is linked.
//! * ours, `s2n` — the same emitted orchestration over `src/leaves_s2n.rs`,
//!   whose arithmetic is AWS s2n-bignum assembly, machine-checked in HOL
//!   Light and external to us exactly as fiat-crypto and CryptOpt are.
//!   This is the row that is same-tier with Graviola *and* runs the same
//!   arithmetic, so the difference is orchestration alone.
//! * RustCrypto `p384` — an unverified production implementation over
//!   fiat-crypto Rust.  Same tier as the pure-Rust AUCurves row.
//! * Graviola 0.4.1 — a production implementation whose P-384 field, group
//!   and scalar arithmetic is the same s2n-bignum assembly the `s2n` row
//!   runs.
//!
//! What each signing side includes is not the same, and the ratio must be
//! read with that in mind.  Our kernels and RustCrypto's
//! `try_sign_prehashed` all take a digest and a nonce and do only the
//! arithmetic.  Graviola's `sign` is the whole API: SHA-384 of the message,
//! sixteen bytes from the system RNG, an RFC 6979 HMAC_DRBG nonce
//! derivation, then the arithmetic.  `rfc6979_sign_with_random` is private
//! and the `Hash` parameter cannot be instantiated downstream, so there is
//! no way to call the arithmetic alone.  The signing-decomposition block
//! times the three components separately and prints the resulting upper
//! bound on Graviola's arithmetic-only cost.
//!
//! Verification is the fair row: Graviola's `verify` takes no RNG and no
//! DRBG, and differs from our kernels only by hashing the message.
//!
//! Under `--features production` two more columns join the same
//! round-robin: OpenSSL 3.0 (`src/ossl.rs`) and BoringSSL (`src/bssl.rs`),
//! the ECDSA of the two production TLS stacks.  Both take the digest, and
//! both are signed with the kernel's nonce: BoringSSL through its
//! nonce-supplied testing entry point, which reaches the production
//! `ecdsa_sign_impl`; OpenSSL through a public-API reconstruction of
//! `ecdsa_sign_setup` followed by `ECDSA_do_sign_ex`.  Verification is
//! `ECDSA_do_verify` on a pre-built `ECDSA_SIG`.  A second block times each
//! library's full `ECDSA_do_sign`, which derives its own nonce, and
//! OpenSSL's `BN_generate_dsa_nonce` on its own.  AWS-LC (`src/awslc.rs`)
//! joins as a third column when its shared library is present; it is
//! driven as BoringSSL is, and its P-384 field is s2n-bignum assembly.
//!
//! Three micro-benchmarks run first, in the same round-robin style, because
//! the whole-operation rows are the sum of many parts and a change to one of
//! them is not attributable from them alone:
//!
//! * the scalar inverse — the Fermat chain `a^(n-2)` against the
//!   Bernstein-Yang divstep inversion, with the base-field `fp_inv` for
//!   scale and, when the `s2n` feature is on, s2n-bignum's generic
//!   `bignum_modinv` at the group order;
//! * the base-point multiply — the two orchestrations of `k*G` over
//!   identical s2n-bignum arithmetic: our fixed-base comb against the
//!   archive's own windowed multiplication, which is the route Graviola
//!   takes for its base point;
//! * the two-term multiply — the interleaved pass against the three-leaf
//!   route it replaced, on each backend.

use std::hint::black_box;
use std::time::Instant;

use p384_ecdsa_rust::backend::{self, Backend};
use p384_ecdsa_rust::scalar;
use p384_ecdsa_rust::{grav, rc};
#[cfg(feature = "production")]
use p384_ecdsa_rust::{awslc, bssl, ossl};

/// The production-library state the benchmark arms borrow.  AWS-LC is
/// loaded at run time and is `None` when its library is absent.
#[cfg(feature = "production")]
struct Prod {
    digest: [u8; 48],
    kbe: [u8; 48],
    bs_sk: bssl::Key,
    bs_vk: bssl::Key,
    bs_sig: bssl::Sig,
    os_sk: ossl::Key,
    os_vk: ossl::Key,
    os_sig: ossl::Sig,
    aw: Option<(awslc::Key, awslc::Key, awslc::Sig)>,
}

/// One line naming the AWS-LC library the benchmark loaded, or its absence.
#[cfg(feature = "production")]
fn awslc_banner() -> String {
    if awslc::available() {
        let (_, api_num, text) = awslc::version();
        format!(
            "{text} (api {api_num}) from {}, EC_GFp_nistp384, s2n-bignum field",
            awslc::library_path()
        )
    } else {
        format!("absent at {}", awslc::library_path())
    }
}

/// `"openssl M.m"` for a loaded OpenSSL 3.2+ library.
#[cfg(feature = "production")]
fn openssl_label(lib: &p384_ecdsa_rust::ossl_kem::Lib) -> String {
    let (num, _, _) = lib.version();
    format!("openssl {}.{}", num >> 28, (num >> 20) & 0xff)
}

/// The message the Graviola arms sign and verify.  Short, so the SHA-384 it
/// includes is a small and measurable fraction of the whole.
const MESSAGE: &[u8] = b"catcrypt p384 ecdsa bench";

/// SplitMix64, so the inputs are the same on every run.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn scalar(&mut self) -> [u64; 6] {
        loop {
            let mut c = [0u64; 6];
            for w in c.iter_mut() {
                *w = self.next_u64();
            }
            if p384_ecdsa_rust::scalar::ct_lt_n(&c) == 1 && c.iter().any(|&w| w != 0) {
                return c;
            }
        }
    }
}

fn sb(l: &[u64; 6]) -> [u8; 48] {
    p384_ecdsa_rust::codec::bytes(l)
}

/// Median of the per-repetition ns/op.
fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = v.len();
    if n % 2 == 1 {
        v[n / 2]
    } else {
        0.5 * (v[n / 2 - 1] + v[n / 2])
    }
}

/// Iterations per repetition for the micro-benchmarks, which measure
/// operations three orders of magnitude cheaper than a whole signature.
fn micro_iters() -> usize {
    std::env::var("BENCH_MICRO_ITERS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(4000)
}

/// One timed arm: a name and a closure, timed once per repetition in a
/// fixed order alongside the others.
struct Arm<'a> {
    name: String,
    run: Box<dyn FnMut() + 'a>,
    times: Vec<f64>,
}

impl<'a> Arm<'a> {
    fn new(name: impl Into<String>, run: impl FnMut() + 'a) -> Self {
        Arm {
            name: name.into(),
            run: Box::new(run),
            times: Vec::new(),
        }
    }
}

/// Runs every arm once per repetition, in the given order, after a warm-up
/// pass.  Returns the median ns/op of each, in the same order.
fn round_robin(arms: &mut [Arm], reps: usize, iters: usize) -> Vec<f64> {
    for arm in arms.iter_mut() {
        for _ in 0..iters.min(64) {
            (arm.run)();
        }
    }
    for _ in 0..reps {
        for arm in arms.iter_mut() {
            let t = Instant::now();
            for _ in 0..iters {
                (arm.run)();
            }
            arm.times.push(t.elapsed().as_nanos() as f64 / iters as f64);
        }
    }
    arms.iter()
        .map(|a| median(a.times.clone()))
        .collect()
}

/// The scalar inverse alone: Fermat against divstep, with the base-field
/// divstep inverse for scale and s2n-bignum's generic modular inverse where
/// it is linked.
fn micro_inverse(reps: usize, a: &[u64; 6]) {
    let iters = micro_iters();

    let mut fp_in = p384::Fp([0u64; 6]);
    p384::fp_to_montgomery(&mut fp_in, &p384::FpRaw(*a));

    let mut arms = vec![
        Arm::new("Fermat a^(n-2), 383 S + 287 M", || {
            black_box(scalar::inv(black_box(a)));
        }),
        Arm::new("divstep, 15 x 59 (safegcd)", || {
            black_box(scalar::inv_divstep(black_box(a)));
        }),
        Arm::new("base-field fp_inv, for scale", || {
            let mut out = p384::Fp([0u64; 6]);
            p384::fp_inv(&mut out, black_box(&fp_in));
            black_box(out);
        }),
    ];
    #[cfg(feature = "s2n")]
    arms.push(Arm::new("s2n-bignum generic bignum_modinv", || {
        black_box(p384_ecdsa_rust::s2n::modinv_n(black_box(a)));
    }));

    let names: Vec<String> = arms.iter().map(|a| a.name.clone()).collect();
    let out = round_robin(&mut arms, reps, iters);
    let base = out[0];

    println!("# scalar inverse mod n, reps={reps} iters={iters}, round-robin, median ns/op");
    println!();
    println!("{:<36} {:>12} {:>10}", "inverse", "ns/op", "vs Fermat");
    for (name, v) in names.iter().zip(out.iter()) {
        println!("{name:<36} {v:>12.0} {:>10.2}", v / base);
    }
    println!();
}

/// The base-point multiply, over identical s2n-bignum arithmetic: our
/// fixed-base comb against the archive's own windowed multiplication.
///
/// The second arm is what Graviola does for its base point — its README
/// says it uses the same five-bit window as for a variable point — so the
/// ratio between the two arms is the orchestration lever in isolation, with
/// no arithmetic difference between them at all.  The AUCurves comb is
/// shown for scale; it is a different group law and a different field.
#[cfg(feature = "s2n")]
fn micro_base_multiply(reps: usize, k: &[u8; 48]) {
    use p384_ecdsa_rust::s2n;

    let iters = (micro_iters() / 20).max(20);
    let kl = s2n::fe_from_bytes(k);
    let g = s2n::point_from_bytes(&s2n::generator_bytes());
    p384_ecdsa_rust::comb_s2n::warm();

    let mut arms = vec![
        Arm::new("s2n: montjscalarmul on G (as GV)", || {
            black_box(s2n::jscalarmul(black_box(&kl), black_box(&g)));
        }),
        Arm::new("s2n: fixed-base comb, w = 5", || {
            black_box(p384_ecdsa_rust::comb_s2n::scalar_mul_base(black_box(&kl)));
        }),
        Arm::new("aucurves: fixed-base comb, w = 5", || {
            let mut out = [0u8; 144];
            p384_ecdsa_rust::leaves::p384_scalar_mul_base(&mut out, black_box(k));
            black_box(out);
        }),
    ];

    let names: Vec<String> = arms.iter().map(|a| a.name.clone()).collect();
    let out = round_robin(&mut arms, reps, iters);
    let base = out[0];

    println!("# base-point multiply k*G, reps={reps} iters={iters}, round-robin, median ns/op");
    println!();
    println!("{:<36} {:>12} {:>10}", "route", "ns/op", "ratio");
    for (name, v) in names.iter().zip(out.iter()) {
        println!("{name:<36} {v:>12.0} {:>10.2}", v / base);
    }
    println!();
    println!("# the first two rows run the same s2n-bignum field and point");
    println!("#   operations; they differ only in how the multiplication is");
    println!("#   organised, so the ratio is the comb's alone.");
    println!();
}

/// The two-term multiply on each backend: the interleaved leaf against the
/// three leaves it replaced.
fn micro_lincomb(reps: usize, u1: &[u8; 48], u2: &[u8; 48], qs: &[[u8; 144]]) {
    let iters = (micro_iters() / 20).max(20);
    let backends = backend::all();

    let mut arms: Vec<Arm> = Vec::new();
    for (b, q) in backends.iter().zip(qs.iter()) {
        let msm = b.verify_msm;
        let gen = (b.generator)();
        arms.push(Arm::new(
            format!("{}: mul_base + mul + add", b.name),
            move || {
                let mut out = [0u8; 144];
                msm(black_box(u1), black_box(&gen), black_box(u2), black_box(q), &mut out);
                black_box(out);
            },
        ));
        let lc = lincomb_of(b);
        arms.push(Arm::new(
            format!("{}: interleaved, w = 5", b.name),
            move || {
                let mut out = [0u8; 144];
                lc(black_box(u1), black_box(u2), black_box(q), &mut out);
                black_box(out);
            },
        ));
    }

    let names: Vec<String> = arms.iter().map(|a| a.name.clone()).collect();
    let out = round_robin(&mut arms, reps, iters);

    println!("# two-term multiply u1*G + u2*Q, reps={reps} iters={iters}, round-robin, median ns/op");
    println!();
    println!("{:<36} {:>12} {:>10}", "route", "ns/op", "ratio");
    for (i, (name, v)) in names.iter().zip(out.iter()).enumerate() {
        // Each backend's pair is scored against its own split route.
        let base = out[i - i % 2];
        println!("{name:<36} {v:>12.0} {:>10.2}", v / base);
    }
    println!();
}

/// The `p384_lincomb` leaf of a backend, as a function over the byte ABI.
fn lincomb_of(b: &Backend) -> fn(&[u8; 48], &[u8; 48], &[u8; 144], &mut [u8; 144]) {
    fn aucurves(u1: &[u8; 48], u2: &[u8; 48], q: &[u8; 144], out: &mut [u8; 144]) {
        p384_ecdsa_rust::leaves::p384_lincomb(out, u1, u2, q);
    }
    #[cfg(feature = "s2n")]
    fn s2n(u1: &[u8; 48], u2: &[u8; 48], q: &[u8; 144], out: &mut [u8; 144]) {
        p384_ecdsa_rust::leaves_s2n::p384_lincomb(out, u1, u2, q);
    }
    match b.name {
        #[cfg(feature = "s2n")]
        "s2n" => s2n,
        _ => aucurves,
    }
}

/// Whether `BENCH_SECTIONS` (comma-separated, default `ecdsa,dhkem`) names
/// `section`.
fn section_enabled(section: &str) -> bool {
    std::env::var("BENCH_SECTIONS")
        .unwrap_or_else(|_| "ecdsa,dhkem".to_string())
        .split(',')
        .any(|s| s.trim() == section)
}

/// One DHKEM arm: its row name, what kind of entry point it is, and the
/// arithmetic under it.
struct KemRow {
    op: &'static str,
    name: String,
    kind: &'static str,
    tier: String,
}

/// DHKEM(P-384, HKDF-SHA384) `Encap` and `Decap`, every backend of ours
/// against every opponent that works, interleaved round-robin with the same
/// reps and iters as the ECDSA table, followed by the HKDF share of each and
/// the adjustments that make the native-API rows comparable.
fn dhkem_section(reps: usize, iters: usize, field_config: &str) {
    use p384_ecdsa_rust::dhkem_kdf::{
        dhkem_p384_expand, dhkem_p384_extract, p384_kem_context, sk_be_from_le,
    };
    use p384_ecdsa_rust::{dhkem_ref, hpke_rs};

    let backends = backend::all();
    let mut rng = Rng(0xd4e4_5eed_0384_0011);
    let r_le = sb(&rng.scalar());
    let r_be = sk_be_from_le(&r_le);
    let e_le = sb(&rng.scalar());
    let e_be = sk_be_from_le(&e_le);
    let pk_r = dhkem_ref::public_key(&r_be).expect("valid skR");
    let ikme: [u8; 48] = sb(&rng.scalar());

    // One encapsulation, checked by every side before timing.
    let (mut enc, mut ss, mut ok) = ([0u8; 97], [0u8; 48], 0u64);
    (backends[0].dhkem_encap)(&e_le, &pk_r, &mut enc, &mut ss, &mut ok);
    assert_eq!(ok, 1);
    assert_eq!(dhkem_ref::encap(&e_be, &pk_r), Some((enc, ss)), "reference disagrees");
    for b in backends {
        let (mut enc0, mut ss0, mut ok0) = ([0u8; 97], [0u8; 48], 0u64);
        (b.dhkem_encap)(&e_le, &pk_r, &mut enc0, &mut ss0, &mut ok0);
        assert_eq!((enc0, ss0, ok0), (enc, ss, 1), "backend {} encapsulates differently", b.name);
        let mut ok1 = 0u64;
        (b.dhkem_decap)(&enc, &r_le, &pk_r, &mut ss0, &mut ok1);
        assert_eq!((ss0, ok1), (ss, 1), "backend {} decapsulates differently", b.name);
    }
    let mut hpke = hpke_rs::new();
    assert_eq!(hpke_rs::prims_encap(&e_be, &pk_r), Some((enc, ss)));
    assert_eq!(grav::dhkem_encap(&e_be, &pk_r), Some((enc, ss)));
    let (enc_h, ctx_h) = hpke_rs::setup_sender(&mut hpke, &pk_r, &ikme).expect("hpke-rs sender");
    let (dkp_sk, _) = hpke_rs::derive_key_pair(&hpke, &ikme);
    let (mut enc2, mut ss2, mut ok2) = ([0u8; 97], [0u8; 48], 0u64);
    (backends[0].dhkem_encap)(
        &p384_ecdsa_rust::dhkem_kdf::sk_le_from_be(&dkp_sk),
        &pk_r,
        &mut enc2,
        &mut ss2,
        &mut ok2,
    );
    assert_eq!(enc2, enc_h);
    assert_eq!(hpke_rs::export_for_shared_secret(&hpke, &ss2), hpke_rs::export(&ctx_h));

    #[cfg(feature = "production")]
    let (sys, v36) = {
        use p384_ecdsa_rust::ossl_kem;
        let sys = ossl_kem::system();
        let mut s = sys.scratch();
        assert_eq!(sys.recon_encap(&mut s, &e_be, &pk_r), Some((enc, ss)));
        assert_eq!(
            bssl::dhkem_encap(&mut bssl::KemState::new(), &e_be, &pk_r),
            Some((enc, ss))
        );
        let v36 = ossl_kem::v36();
        if let Some(lib) = v36 {
            let mut s = lib.scratch();
            assert_eq!(lib.recon_encap(&mut s, &e_be, &pk_r), Some((enc, ss)));
            let recip = lib.public_pkey(&pk_r).unwrap();
            let (nenc, nss) = lib.native_encap(&recip, &ikme).expect("native encap");
            assert_eq!((nenc, nss), (enc2, ss2), "OpenSSL native DHKEM disagrees");
        }
        if awslc::available() {
            let mut st = awslc::KemState::new();
            assert_eq!(awslc::dhkem_encap(&mut st, &e_be, &pk_r), Some((enc, ss)), "AWS-LC encap disagrees");
            assert_eq!(awslc::dhkem_decap(&mut st, &enc, &r_be, &pk_r), Some(ss), "AWS-LC decap disagrees");
        }
        (sys, v36)
    };

    let mut rows: Vec<KemRow> = Vec::new();
    let mut arms: Vec<Arm> = Vec::new();
    let ours_tier = |b: &Backend| match b.name {
        "s2n" => "s2n-bignum x86-64 asm (Jacobian)".to_string(),
        _ => format!("AUCurves RCB, field: {field_config}"),
    };

    for op in ["encap", "decap"] {
        for b in backends {
            rows.push(KemRow {
                op,
                name: format!("ours/{}", b.name),
                kind: if (op == "encap" && p384_ecdsa_rust::DHKEM_ENCAP_EMITTED)
                    || (op == "decap" && p384_ecdsa_rust::DHKEM_DECAP_EMITTED)
                {
                    "emitted kernel"
                } else {
                    "transcription"
                },
                tier: ours_tier(b),
            });
            if op == "encap" {
                let f = b.dhkem_encap;
                arms.push(Arm::new("", move || {
                    let (mut enc0, mut ss0, mut ok0) = ([0u8; 97], [0u8; 48], 0u64);
                    f(black_box(&e_le), black_box(&pk_r), &mut enc0, &mut ss0, &mut ok0);
                    black_box((enc0, ss0, ok0));
                }));
            } else {
                let f = b.dhkem_decap;
                arms.push(Arm::new("", move || {
                    let (mut ss0, mut ok0) = ([0u8; 48], 0u64);
                    f(black_box(&enc), black_box(&r_le), black_box(&pk_r), &mut ss0, &mut ok0);
                    black_box((ss0, ok0));
                }));
            }
        }
    }

    macro_rules! row {
        ($op:expr, $name:expr, $kind:expr, $tier:expr, $body:expr) => {{
            rows.push(KemRow { op: $op, name: $name.to_string(), kind: $kind, tier: $tier.to_string() });
            arms.push(Arm::new("", $body));
        }};
    }

    let rc_tier = "RustCrypto p384 0.13.1, fiat-crypto Rust";
    row!("encap", "reference", "reconstruction", rc_tier, move || {
        black_box(dhkem_ref::encap(black_box(&e_be), black_box(&pk_r)));
    });
    row!("decap", "reference", "reconstruction", rc_tier, move || {
        black_box(dhkem_ref::decap_with_pk(black_box(&enc), black_box(&r_be), black_box(&pk_r)));
    });
    let hpke_ref = std::cell::RefCell::new(hpke_rs::new());
    row!("encap", "hpke-rs", "native API (+DKP, +key schedule)", rc_tier, move || {
        let mut h = hpke_ref.borrow_mut();
        black_box(hpke_rs::setup_sender(&mut h, black_box(&pk_r), black_box(&ikme)));
    });
    let hpke_r = hpke_rs::new();
    row!("decap", "hpke-rs", "native API (+pk(skR), +key schedule)", rc_tier, move || {
        black_box(hpke_rs::setup_receiver(&hpke_r, black_box(&enc), black_box(&r_be)));
    });
    row!("encap", "hpke-rs provider", "reconstruction", rc_tier, move || {
        black_box(hpke_rs::prims_encap(black_box(&e_be), black_box(&pk_r)));
    });
    row!("decap", "hpke-rs provider", "reconstruction", rc_tier, move || {
        black_box(hpke_rs::prims_decap(black_box(&enc), black_box(&r_be), black_box(&pk_r)));
    });
    let gv_tier = "Graviola 0.4.1, s2n-bignum x86-64 asm";
    row!("encap", "graviola", "reconstruction", gv_tier, move || {
        black_box(grav::dhkem_encap(black_box(&e_be), black_box(&pk_r)));
    });
    row!("decap", "graviola", "reconstruction", gv_tier, move || {
        black_box(grav::dhkem_decap(black_box(&enc), black_box(&r_be), black_box(&pk_r)));
    });

    #[cfg(feature = "production")]
    {
        let bs_tier = "BoringSSL EC_GFp_mont, bn_mul_mont_nohw";
        let bst_e = std::cell::RefCell::new(bssl::KemState::new());
        let bst_d = std::cell::RefCell::new(bssl::KemState::new());
        row!("encap", "boringssl", "reconstruction", bs_tier, move || {
            black_box(bssl::dhkem_encap(&mut bst_e.borrow_mut(), black_box(&e_be), black_box(&pk_r)));
        });
        row!("decap", "boringssl", "reconstruction", bs_tier, move || {
            black_box(bssl::dhkem_decap(&mut bst_d.borrow_mut(), black_box(&enc), black_box(&r_be), black_box(&pk_r)));
        });
        let os_tier = "OpenSSL 3.0.13 EC_GFp_mont, x86_64-mont";
        let sys_s = std::cell::RefCell::new(sys.scratch());
        row!("encap", "openssl 3.0", "reconstruction", os_tier, move || {
            black_box(sys.recon_encap(&mut sys_s.borrow_mut(), black_box(&e_be), black_box(&pk_r)));
        });
        row!("decap", "openssl 3.0", "reconstruction", os_tier, move || {
            black_box(sys.recon_decap(black_box(&enc), black_box(&r_be), black_box(&pk_r)));
        });
        if awslc::available() {
            let aw_tier = "AWS-LC nistp384, s2n-bignum MULX/ADX field";
            let aw_e = std::cell::RefCell::new(awslc::KemState::new());
            let aw_d = std::cell::RefCell::new(awslc::KemState::new());
            row!("encap", "aws-lc", "reconstruction", aw_tier, move || {
                black_box(awslc::dhkem_encap(&mut aw_e.borrow_mut(), black_box(&e_be), black_box(&pk_r)));
            });
            row!("decap", "aws-lc", "reconstruction", aw_tier, move || {
                black_box(awslc::dhkem_decap(&mut aw_d.borrow_mut(), black_box(&enc), black_box(&r_be), black_box(&pk_r)));
            });
        }
        if let Some(lib) = v36 {
            let (num, _, _) = lib.version();
            let o6 = openssl_label(lib);
            let o6_tier = format!(
                "OpenSSL {}.{}.{}, EC_GFp_mont, x86_64-mont",
                num >> 28,
                (num >> 20) & 0xff,
                (num >> 4) & 0xff
            );
            let s6 = std::cell::RefCell::new(lib.scratch());
            row!("encap", o6, "reconstruction", o6_tier, move || {
                black_box(lib.recon_encap(&mut s6.borrow_mut(), black_box(&e_be), black_box(&pk_r)));
            });
            row!("decap", o6, "reconstruction", o6_tier, move || {
                black_box(lib.recon_decap(black_box(&enc), black_box(&r_be), black_box(&pk_r)));
            });
            let recip = lib.public_pkey(&pk_r).unwrap();
            let pair = lib.keypair_pkey(&r_be, &pk_r).unwrap();
            row!("encap", format!("{o6} DHKEM"), "native API (+DKP)", o6_tier, move || {
                black_box(lib.native_encap(&recip, black_box(&ikme)));
            });
            row!("decap", format!("{o6} DHKEM"), "native API", o6_tier, move || {
                black_box(lib.native_decap(&pair, black_box(&enc)));
            });
        }
    }

    // Components: each side's ExtractAndExpand alone, hpke-rs's key schedule,
    // pk(skR), and the KDF part of DeriveKeyPair.
    let dh_bytes = dhkem_ref::dh(&e_be, &pk_r).unwrap();
    let mut ctx = [0u8; 194];
    ctx[..97].copy_from_slice(&enc);
    ctx[97..].copy_from_slice(&pk_r);
    row!("kdf", "ours", "leaves", "hkdf 0.12.4 / sha2 0.10.9", move || {
        let mut c = [0u8; 194];
        p384_kem_context(&mut c, black_box(&enc), black_box(&pk_r));
        let mut prk = [0u8; 48];
        dhkem_p384_extract(&mut prk, black_box(&dh_bytes));
        let mut s = [0u8; 48];
        dhkem_p384_expand(&mut s, &prk, &c);
        black_box(s);
    });
    row!("kdf", "reference", "reconstruction", "hkdf 0.12.4 streaming", move || {
        black_box(dhkem_ref::extract_and_expand(black_box(&dh_bytes), black_box(&ctx)));
    });
    row!("kdf", "hpke-rs provider", "reconstruction", "hkdf 0.13 / sha2 0.11", move || {
        black_box(hpke_rs::extract_and_expand(black_box(&dh_bytes), black_box(&ctx)));
    });
    row!("kdf", "graviola", "reconstruction", "graviola Hmac<Sha384>", move || {
        black_box(grav::dhkem_extract_and_expand(black_box(&dh_bytes), black_box(&ctx)));
    });
    #[cfg(feature = "production")]
    {
        row!("kdf", "boringssl", "reconstruction", "HKDF_extract/expand", move || {
            black_box(bssl::dhkem_extract_and_expand(black_box(&dh_bytes), black_box(&ctx)));
        });
        row!("kdf", "openssl 3.0", "reconstruction", "EVP_KDF HKDF", move || {
            black_box(sys.extract_and_expand(black_box(&dh_bytes), black_box(&ctx)));
        });
        if awslc::available() {
            row!("kdf", "aws-lc", "reconstruction", "HKDF_extract/expand", move || {
                black_box(awslc::dhkem_extract_and_expand(black_box(&dh_bytes), black_box(&ctx)));
            });
        }
        if let Some(lib) = v36 {
            row!("kdf", openssl_label(lib), "reconstruction", "EVP_KDF HKDF", move || {
                black_box(lib.extract_and_expand(black_box(&dh_bytes), black_box(&ctx)));
            });
        }
    }
    let hpke_ks = hpke_rs::new();
    row!("part", "hpke-rs key schedule", "native API", "hkdf 0.13", move || {
        black_box(hpke_rs::key_schedule(&hpke_ks, black_box(&ss)));
    });
    row!("part", "hpke-rs pk(skR)", "provider", rc_tier, move || {
        black_box(hpke_rs::secret_to_public(black_box(&r_be)));
    });
    row!("part", "DKP KDF part (hkdf 0.12)", "reconstruction", "1 extract + 1 expand", move || {
        black_box(dhkem_ref::labeled_extract(&[], b"dkp_prk", black_box(&ikme)));
        let prk = [7u8; 48];
        let mut out = [0u8; 48];
        dhkem_ref::labeled_expand(&prk, b"candidate", &[0u8], &mut out);
        black_box(out);
    });

    let out = round_robin(&mut arms, reps, iters);
    let at = |op: &str, name: &str| -> f64 {
        let i = rows.iter().position(|r| r.op == op && r.name == name).expect("named row");
        out[i]
    };

    println!(
        "# DHKEM(P-384, HKDF-SHA384), RFC 9180 KEM 0x0011; reps={reps} iters={iters}, round-robin, median ns/op"
    );
    println!(
        "# p384_dhkem_encap emitted: {}; p384_dhkem_decap emitted: {}",
        p384_ecdsa_rust::DHKEM_ENCAP_EMITTED,
        p384_ecdsa_rust::DHKEM_DECAP_EMITTED
    );
    println!();
    let mut header = format!("{:<6} {:<20} {:<37} {:<52} {:>10}", "op", "implementation", "kind", "arithmetic", "ns/op");
    for b in backends {
        header.push_str(&format!(" {:>10}", format!("{}/this", b.name)));
    }
    println!("{header}");
    for (i, r) in rows.iter().enumerate() {
        if r.op != "encap" && r.op != "decap" {
            continue;
        }
        let mut line = format!("{:<6} {:<20} {:<37} {:<52} {:>10.0}", r.op, r.name, r.kind, r.tier, out[i]);
        for b in backends {
            let ours = at(r.op, &format!("ours/{}", b.name));
            line.push_str(&format!(" {:>10.2}", ours / out[i]));
        }
        println!("{line}");
    }
    println!();
    println!("# a ratio is ours / this row; above 1.00 means ours is slower than this row.");
    println!("# 'reconstruction' rows are DHKEM assembled by this crate from the library's");
    println!("#   ECDH and HKDF (or HMAC); no such library offers P-384 DHKEM itself.");
    println!("# hpke-rs native rows are Hpke::setup_sender / setup_receiver: encap adds");
    println!("#   DeriveKeyPair and the base-mode key schedule, decap adds pk(skR) and the");
    println!("#   key schedule; the adjusted rows below subtract them.  The openssl 3.2+");
    println!("#   DHKEM encap row adds DeriveKeyPair(ikme).");
    println!("# the aws-lc rows run ECDH_compute_key, which also copies and validates the");
    println!("#   peer point in a fresh EC_KEY on every call (EC_KEY_check_fips).");
    println!();

    println!("# HKDF share: ExtractAndExpand alone, same process");
    println!();
    println!("{:<20} {:<24} {:>10} {:>14} {:>14}", "implementation", "kdf", "kdf ns/op", "encap - kdf", "decap - kdf");
    for (i, r) in rows.iter().enumerate() {
        if r.op != "kdf" {
            continue;
        }
        let (enc_name, dec_name) = if r.name == "ours" {
            (format!("ours/{}", backends[0].name), format!("ours/{}", backends[0].name))
        } else {
            (r.name.clone(), r.name.clone())
        };
        let e = at("encap", &enc_name) - out[i];
        let d = at("decap", &dec_name) - out[i];
        println!("{:<20} {:<24} {:>10.0} {:>14.0} {:>14.0}", r.name, r.tier, out[i], e, d);
        if r.name == "ours" {
            for b in &backends[1..] {
                let e = at("encap", &format!("ours/{}", b.name)) - out[i];
                let d = at("decap", &format!("ours/{}", b.name)) - out[i];
                println!("{:<20} {:<24} {:>10} {:>14.0} {:>14.0}", format!("ours/{}", b.name), "(same leaves)", "", e, d);
            }
        }
    }
    println!();
    println!("# the 'ours' kdf row is timed once and applies to every backend, whose");
    println!("#   kdf leaves are the same functions; its first dh row is ours/{}.", backends[0].name);
    println!();

    let ks = at("part", "hpke-rs key schedule");
    let pk = at("part", "hpke-rs pk(skR)");
    let dkp = at("part", "DKP KDF part (hkdf 0.12)");
    println!("# native-API adjustments, ns/op");
    println!();
    println!("{:<52} {:>10}", "hpke-rs key schedule (base mode)", format!("{ks:.0}"));
    println!("{:<52} {:>10}", "hpke-rs pk(skR)", format!("{pk:.0}"));
    println!("{:<52} {:>10}", "DeriveKeyPair KDF part (hkdf 0.12, an estimate)", format!("{dkp:.0}"));
    let he = at("encap", "hpke-rs") - ks - dkp;
    let hd = at("decap", "hpke-rs") - ks - pk;
    #[allow(unused_mut)]
    let mut adjusted: Vec<(&str, String, f64)> = vec![
        ("encap", "hpke-rs native - key schedule - DKP KDF".to_string(), he),
        ("decap", "hpke-rs native - key schedule - pk(skR)".to_string(), hd),
    ];
    #[cfg(feature = "production")]
    if let Some(lib) = v36 {
        let label = openssl_label(lib);
        let o6 = at("kdf", &label);
        adjusted.push((
            "encap",
            format!("{label} DHKEM - its own kdf (DKP estimate)"),
            at("encap", &format!("{label} DHKEM")) - o6,
        ));
    }
    for (op, name, v) in &adjusted {
        let mut line = format!("{:<52} {:>10.0}", format!("{op} {name}"), v);
        for b in backends {
            line.push_str(&format!(" {:>10.2}", at(op, &format!("ours/{}", b.name)) / v));
        }
        println!("{line}");
    }
    println!();
    println!("# the ratio columns are ours/{} and ours/{} against the adjusted figure.",
        backends[0].name, backends.last().unwrap().name);
    println!("# subtracting separately timed arms is an estimate, not an isolated measurement.");
    println!();
}

fn main() {
    let reps: usize = std::env::var("BENCH_REPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(11);
    let iters: usize = std::env::var("BENCH_ITERS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(200);

    let backends = backend::all();
    for b in backends {
        (b.warm)();
    }

    let field_config = match p384::FIELD_CONFIG {
        "cryptopt" => "CryptOpt asm",
        "s2n-bignum" => "s2n-bignum asm",
        "s2n-montmul-encoded" => "encoded s2n montmul",
        _ => "fiat-crypto Rust",
    };

    if !section_enabled("ecdsa") {
        if section_enabled("dhkem") {
            println!("# {} ; AUCurves field = {field_config}", "DHKEM only (BENCH_SECTIONS)");
            for b in backends {
                println!("# backend {:<9} = {}", b.name, b.arithmetic);
            }
            #[cfg(feature = "production")]
            {
                let (num, text) = ossl::version();
                println!("# openssl system = {text} (0x{num:08x}); boringssl = {}", bssl::REVISION);
                match p384_ecdsa_rust::ossl_kem::v36() {
                    Some(lib) => {
                        let (num, text, path) = lib.version();
                        println!("# openssl 3.2+ = {text} (0x{num:08x}) from {path}");
                    }
                    None => println!("# openssl 3.2+ = absent at {}", p384_ecdsa_rust::ossl_kem::v36_path()),
                }
                println!("# aws-lc = {}", awslc_banner());
            }
            println!();
            dhkem_section(reps, iters, field_config);
        }
        return;
    }

    let mut rng = Rng(0x5eed_1234_9abc_def0);
    // The digest all sides work on is the one Graviola derives from
    // MESSAGE, so the verify rows check the same signature.
    let e = scalar::reduce(&grav::from_be48(&grav::sha384(MESSAGE)));
    let d = rng.scalar();
    let k = rng.scalar();

    let qpoint = p384::group::g1_scalar_mul_base(&d);
    let (qx, qy) = p384::group::g1_to_affine(&qpoint).expect("d*G is not the identity");
    let mut qxr = p384::FpRaw([0u64; 6]);
    let mut qyr = p384::FpRaw([0u64; 6]);
    p384::fp_from_montgomery(&mut qxr, &qx);
    p384::fp_from_montgomery(&mut qyr, &qy);

    // One public key per backend, in that backend's point representation.
    let qs: Vec<[u8; 144]> = backends
        .iter()
        .map(|b| (b.point_from_affine)(&qxr.0, &qyr.0))
        .collect();

    let q_rc = rc::affine_from_coords(&qxr.0, &qyr.0).expect("d*G is on the curve");
    let q_gv = grav::verifying_key_from_coords(&qxr.0, &qyr.0).expect("Graviola rejects d*G");
    let sk_gv = grav::signing_key(&d).expect("Graviola refused the private scalar");
    assert_eq!(
        grav::public_key_bytes(&sk_gv),
        grav::x962(&qxr.0, &qyr.0),
        "Graviola derives a different public key from d"
    );

    let (eb, db, kb) = (sb(&e), sb(&d), sb(&k));

    // One signature, checked by every side, so the verify rows measure an
    // accepting path on all of them.
    let (mut rb, mut sbb) = ([0u8; 48], [0u8; 48]);
    let mut signed = 0u64;
    (backends[0].sign)(&eb, &db, &kb, &mut rb, &mut sbb, &mut signed);
    assert_eq!(signed, 1, "the emitted kernel reported an out-of-range signature");
    let r = p384_ecdsa_rust::codec::limbs(&rb);
    let s = p384_ecdsa_rust::codec::limbs(&sbb);
    let (rc_r, rc_s) = rc::sign(&e, &d, &k).expect("RustCrypto signed");
    assert_eq!((r, s), (rc_r, rc_s), "the two sides disagree on (r, s)");
    assert!(rc::verify(&e, &r, &s, &q_rc), "RustCrypto rejects its own signature");
    for (b, q) in backends.iter().zip(qs.iter()) {
        let (mut r0, mut s0) = ([0u8; 48], [0u8; 48]);
        let mut ok0 = 0u64;
        (b.sign)(&eb, &db, &kb, &mut r0, &mut s0, &mut ok0);
        assert_eq!((r0, s0, ok0), (rb, sbb, 1), "backend {} signs differently", b.name);
        let mut ok = 0u64;
        (b.verify)(&eb, &rb, &sbb, q, &mut ok);
        assert_eq!(ok, 1, "backend {} rejects the signature it produced", b.name);
    }
    let sig_gv = grav::signature(&r, &s);
    assert!(
        grav::verify_message(&q_gv, MESSAGE, &sig_gv),
        "Graviola rejects the signature the emitted kernel produced"
    );

    // The production libraries: keys, a pre-built ECDSA_SIG of the kernel's
    // signature, and the same two checks — each library's nonce-supplied
    // signature is the kernel's, and each library accepts the kernel's.
    #[cfg(feature = "production")]
    let prod = {
        let digest = rc::be_from_limbs(&e);
        let (dbe, kbe) = (rc::be_from_limbs(&d), rc::be_from_limbs(&k));
        let (qxb, qyb) = (rc::be_from_limbs(&qxr.0), rc::be_from_limbs(&qyr.0));
        let (rbe, sbe) = (rc::be_from_limbs(&r), rc::be_from_limbs(&s));
        let bs_sk = bssl::signing_key(&dbe, &qxb, &qyb).expect("BoringSSL refused the key pair");
        let bs_vk = bssl::verifying_key(&qxb, &qyb).expect("BoringSSL rejects d*G");
        let os_sk = ossl::signing_key(&dbe, &qxb, &qyb).expect("OpenSSL refused the key pair");
        let os_vk = ossl::verifying_key(&qxb, &qyb).expect("OpenSSL rejects d*G");
        assert_eq!(
            bssl::sign_with_nonce(&bs_sk, &digest, &kbe),
            Some((rbe, sbe)),
            "BoringSSL's nonce-supplied signature differs from the kernel's"
        );
        assert_eq!(
            ossl::sign_with_nonce(&os_sk, &digest, &kbe),
            Some((rbe, sbe)),
            "OpenSSL's nonce-supplied signature differs from the kernel's"
        );
        let bs_sig = bssl::sig(&rbe, &sbe);
        let os_sig = ossl::sig(&rbe, &sbe);
        assert!(bssl::verify(&bs_vk, &digest, &bs_sig), "BoringSSL rejects the kernel's signature");
        assert!(ossl::verify(&os_vk, &digest, &os_sig), "OpenSSL rejects the kernel's signature");
        let aw = awslc::available().then(|| {
            let sk = awslc::signing_key(&dbe, &qxb, &qyb).expect("AWS-LC refused the key pair");
            let vk = awslc::verifying_key(&qxb, &qyb).expect("AWS-LC rejects d*G");
            assert_eq!(
                awslc::sign_with_nonce(&sk, &digest, &kbe),
                Some((rbe, sbe)),
                "AWS-LC's nonce-supplied signature differs from the kernel's"
            );
            let sig = awslc::sig(&rbe, &sbe);
            assert!(awslc::verify(&vk, &digest, &sig), "AWS-LC rejects the kernel's signature");
            (sk, vk, sig)
        });
        Prod { digest, kbe, bs_sk, bs_vk, bs_sig, os_sk, os_vk, os_sig, aw }
    };

    let config = match p384::FIELD_CONFIG {
        "cryptopt" => "AUCurves field = CryptOpt assembly (mul, square)",
        "s2n-bignum" => "AUCurves field = s2n-bignum assembly (montmul, montsqr)",
        "s2n-montmul-encoded" => {
            "AUCurves field = encoded s2n-bignum montmul, body bytes Lean-proved (square = montmul(x, x))"
        }
        _ => "AUCurves field = fiat-crypto Rust (pure Rust)",
    };
    #[cfg(not(feature = "production"))]
    println!("# p384 ECDSA: emitted orchestration vs RustCrypto p384 0.13.1 and Graviola 0.4.1");
    #[cfg(feature = "production")]
    println!(
        "# p384 ECDSA: emitted orchestration vs RustCrypto p384 0.13.1, Graviola 0.4.1, OpenSSL, BoringSSL{}",
        if prod.aw.is_some() { " and AWS-LC" } else { "" }
    );
    println!("# emitted sources in gen/: {}", p384_ecdsa_rust::EMITTED);
    println!("# {config}");
    println!("# graviola field = s2n-bignum x86-64 assembly");
    #[cfg(feature = "production")]
    {
        let (num, text) = ossl::version();
        println!(
            "# openssl = {text} (0x{num:08x}) from {}, EC_GFp_mont_method, generic bn_mul_mont",
            ossl::library_path()
        );
        println!(
            "# boringssl = {} (static), EC_GFp_mont_method, bn_mul_mont_nohw",
            bssl::REVISION
        );
        println!("# aws-lc = {}", awslc_banner());
    }
    for b in backends {
        println!("# backend {:<9} = {}", b.name, b.arithmetic);
    }
    println!("# message = {} bytes, digest = SHA-384", MESSAGE.len());
    println!();

    micro_inverse(reps, &e);
    #[cfg(feature = "s2n")]
    micro_base_multiply(reps, &kb);
    micro_lincomb(reps, &eb, &rb, &qs);

    // The whole-operation arms, interleaved: every backend's sign, then
    // RustCrypto's and Graviola's, then every backend's verify, then theirs,
    // then the three Graviola signing components.
    let d_be = grav::be48(&d);
    let e_be = grav::be48(&e);
    let random16 = [0xa5u8; 16];

    let mut names: Vec<String> = Vec::new();
    let mut arms: Vec<Arm> = Vec::new();

    for b in backends {
        names.push(format!("sign/{}", b.name));
        let f = b.sign;
        arms.push(Arm::new("", move || {
            let (mut r0, mut s0) = ([0u8; 48], [0u8; 48]);
            let mut ok0 = 0u64;
            f(black_box(&eb), black_box(&db), black_box(&kb), &mut r0, &mut s0, &mut ok0);
            black_box((r0, s0, ok0));
        }));
    }
    names.push("sign/rustcrypto".into());
    arms.push(Arm::new("", || {
        black_box(rc::sign(black_box(&e), black_box(&d), black_box(&k)));
    }));
    names.push("sign/graviola".into());
    arms.push(Arm::new("", || {
        black_box(grav::sign_message(black_box(&sk_gv), black_box(MESSAGE)));
    }));

    for (b, q) in backends.iter().zip(qs.iter()) {
        names.push(format!("verify/{}", b.name));
        let f = b.verify;
        arms.push(Arm::new("", move || {
            let mut ok = 0u64;
            f(black_box(&eb), black_box(&rb), black_box(&sbb), black_box(q), &mut ok);
            black_box(ok);
        }));
    }
    names.push("verify/rustcrypto".into());
    arms.push(Arm::new("", || {
        black_box(rc::verify(black_box(&e), black_box(&r), black_box(&s), black_box(&q_rc)));
    }));
    names.push("verify/graviola".into());
    arms.push(Arm::new("", || {
        black_box(grav::verify_message(black_box(&q_gv), black_box(MESSAGE), black_box(&sig_gv)));
    }));

    // The production libraries: nonce-supplied signing, verification, the
    // full signing API, and OpenSSL's nonce derivation on its own.
    #[cfg(feature = "production")]
    {
        let p = &prod;
        names.push("sign/boringssl".into());
        arms.push(Arm::new("", move || {
            black_box(bssl::sign_with_nonce(&p.bs_sk, black_box(&p.digest), black_box(&p.kbe)));
        }));
        names.push("sign/openssl".into());
        arms.push(Arm::new("", move || {
            black_box(ossl::sign_with_nonce(&p.os_sk, black_box(&p.digest), black_box(&p.kbe)));
        }));
        names.push("verify/boringssl".into());
        arms.push(Arm::new("", move || {
            black_box(bssl::verify(&p.bs_vk, black_box(&p.digest), black_box(&p.bs_sig)));
        }));
        names.push("verify/openssl".into());
        arms.push(Arm::new("", move || {
            black_box(ossl::verify(&p.os_vk, black_box(&p.digest), black_box(&p.os_sig)));
        }));
        names.push("signfull/boringssl".into());
        arms.push(Arm::new("", move || {
            black_box(bssl::sign(&p.bs_sk, black_box(&p.digest)));
        }));
        names.push("signfull/openssl".into());
        arms.push(Arm::new("", move || {
            black_box(ossl::sign(&p.os_sk, black_box(&p.digest)));
        }));
        names.push("boringssl/nonce-parts".into());
        let mut bst = bssl::NonceState::new();
        let priv_words = p384_ecdsa_rust::codec::bytes(&d);
        arms.push(Arm::new("", move || {
            bssl::nonce_parts(&p.bs_sk, black_box(&priv_words), black_box(&p.digest), &mut bst);
        }));
        names.push("openssl/dsa-nonce".into());
        let mut st = ossl::NonceState::new();
        arms.push(Arm::new("", move || {
            black_box(ossl::dsa_nonce(&p.os_sk, black_box(&p.digest), &mut st));
        }));
        if let Some((aw_sk, aw_vk, aw_sig)) = &p.aw {
            names.push("sign/aws-lc".into());
            arms.push(Arm::new("", move || {
                black_box(awslc::sign_with_nonce(aw_sk, black_box(&p.digest), black_box(&p.kbe)));
            }));
            names.push("verify/aws-lc".into());
            arms.push(Arm::new("", move || {
                black_box(awslc::verify(aw_vk, black_box(&p.digest), black_box(aw_sig)));
            }));
            names.push("signfull/aws-lc".into());
            arms.push(Arm::new("", move || {
                black_box(awslc::sign(aw_sk, black_box(&p.digest)));
            }));
            names.push("aws-lc/nonce-parts".into());
            let mut ast = awslc::NonceState::new();
            let priv_words = p384_ecdsa_rust::codec::bytes(&d);
            arms.push(Arm::new("", move || {
                awslc::nonce_parts(aw_sk, black_box(&priv_words), black_box(&p.digest), &mut ast);
            }));
        }
    }

    names.push("graviola/sha384".into());
    arms.push(Arm::new("", || {
        black_box(grav::sha384(black_box(MESSAGE)));
    }));
    names.push("graviola/rng16".into());
    arms.push(Arm::new("", || {
        black_box(grav::sign_rng_read());
    }));
    names.push("graviola/drbg".into());
    arms.push(Arm::new("", || {
        black_box(grav::drbg_nonce_path(
            black_box(&d_be),
            black_box(&e_be),
            black_box(&random16),
        ));
    }));

    let out = round_robin(&mut arms, reps, iters);
    let at = |needle: &str| -> f64 {
        let i = names.iter().position(|n| n == needle).expect("named arm");
        out[i]
    };

    let gv_s = at("sign/graviola");
    let gv_v = at("verify/graviola");
    let hash = at("graviola/sha384");
    let rng_read = at("graviola/rng16");
    let drbg = at("graviola/drbg");

    println!("# whole operation, reps={reps} iters={iters}, round-robin, median of per-rep ns/op");
    println!();
    // Opponent columns: always RustCrypto and Graviola, and the two
    // production libraries when they are built in.
    #[allow(unused_mut)]
    let mut opponents: Vec<(&str, &str, &str)> = vec![
        ("rustcrypto", "vs RC", "rustcrypto"),
        ("graviola", "vs GV", "graviola"),
    ];
    #[cfg(feature = "production")]
    {
        opponents.push(("openssl", "vs OS", "openssl"));
        opponents.push(("boringssl", "vs BS", "boringssl"));
        if prod.aw.is_some() {
            opponents.push(("aws-lc", "vs AW", "aws-lc"));
        }
    }
    let mut header = format!("{:<8} {:<10} {:>12}", "op", "backend", "ours ns/op");
    for (col, ratio, _) in &opponents {
        header.push_str(&format!(" {col:>12} {ratio:>7}"));
    }
    println!("{header}");
    for op in ["sign", "verify"] {
        for b in backends {
            let a = at(&format!("{op}/{}", b.name));
            let mut line = format!("{op:<8} {:<10} {a:>12.0}", b.name);
            for (_, _, arm) in &opponents {
                let theirs = at(&format!("{op}/{arm}"));
                line.push_str(&format!(" {theirs:>12.0} {:>7.2}", a / theirs));
            }
            println!("{line}");
        }
    }
    println!();
    println!("# a ratio is ours / theirs; above 1.00 means ours is slower");
    println!("# sign: ours and rustcrypto take a digest and a nonce and do only the");
    println!("#   arithmetic; graviola's column is its whole sign API, which also does");
    println!("#   SHA-384, a 16-byte system-RNG read and an RFC 6979 HMAC_DRBG nonce.");
    println!("#   The vs-GV sign ratio is therefore not a like-for-like ratio.");
    println!("# verify: every side takes the same signature and public key; graviola");
    println!("#   additionally hashes the message.  This row is like for like.");
    println!("# the s2n backend and graviola run the same arithmetic, so their two");
    println!("#   rows differ in orchestration alone.");
    #[cfg(feature = "production")]
    {
        println!("# openssl, boringssl: prehashed digest, ECDSA_do_verify on a pre-built");
        println!("#   ECDSA_SIG.  sign is nonce-supplied: boringssl's column is");
        println!("#   ECDSA_sign_with_nonce_and_leak_private_key_for_testing, like for like;");
        println!("#   openssl's is ecdsa_sign_setup after its nonce draw, rebuilt from public");
        println!("#   calls (EC_POINT_mul, get_affine, BN_nnmod, BN_mod_exp_mont to n-2),");
        println!("#   then ECDSA_do_sign_ex.  Both columns include ECDSA_SIG allocation and");
        println!("#   the conversion of (r, s) to 48-byte strings.");
        println!("# aws-lc: as boringssl, through the same testing entry point; its field is");
        println!("#   s2n-bignum assembly, the arithmetic of the s2n backend and graviola.");
    }
    println!();

    #[cfg(feature = "production")]
    {
        let bs_n = at("sign/boringssl");
        let os_n = at("sign/openssl");
        let bs_f = at("signfull/boringssl");
        let os_f = at("signfull/openssl");
        let os_nonce = at("openssl/dsa-nonce");
        let bs_nonce = at("boringssl/nonce-parts");
        // (nonce supplied, full API, nonce derivation) per library column.
        let mut cols: Vec<(&str, f64, f64, f64)> = vec![
            ("boringssl", bs_n, bs_f, bs_nonce),
            ("openssl", os_n, os_f, os_nonce),
        ];
        if prod.aw.is_some() {
            cols.push(("aws-lc", at("sign/aws-lc"), at("signfull/aws-lc"), at("aws-lc/nonce-parts")));
        }
        println!("# production signing, full API (ECDSA_do_sign, the library's own nonce)");
        println!();
        let row = |label: &str, f: &dyn Fn(&(&str, f64, f64, f64)) -> f64, prec: usize| {
            let mut line = format!("{label:<44}");
            for c in &cols {
                line.push_str(&format!(" {:>12.prec$}", f(c)));
            }
            println!("{line}");
        };
        let mut header = format!("{:<44}", "arm");
        for c in &cols {
            header.push_str(&format!(" {:>12}", c.0));
        }
        println!("{header}");
        row("nonce supplied (the table above)", &|c| c.1, 0);
        row("ECDSA_do_sign, full API", &|c| c.2, 0);
        row("difference, full minus nonce supplied", &|c| c.2 - c.1, 0);
        row("nonce derivation alone", &|c| c.3, 0);
        for b in backends {
            let a = at(&format!("sign/{}", b.name));
            row(&format!("{} sign / full API", b.name), &|c| a / c.2, 2);
        }
        println!();
        println!("# boringssl's full sign adds a SHA-512 of the private key and digest and a");
        println!("#   rejection-sampled DRBG draw (ecdsa_sign_fixed); its row above is that");
        println!("#   pair rebuilt from SHA512 and BN_rand_range_ex.  openssl's adds");
        println!("#   BN_generate_dsa_nonce, called directly.  aws-lc's ECDSA_do_sign has");
        println!("#   boringssl's structure, and its row is the same rebuilt pair.");
        println!("#   The difference row subtracts");
        println!("#   two separately timed arms of several hundred microseconds and is");
        println!("#   noisier than the component it would measure.  The ratios against the");
        println!("#   full API are not like for like.");
        println!();
    }

    println!("# graviola signing decomposition, same reps and iters, median ns/op");
    println!();
    println!("{:<40} {:>12} {:>10}", "component", "ns/op", "of sign");
    for (name, v) in [
        ("SHA-384 of the message", hash),
        ("system RNG, 16 bytes", rng_read),
        ("RFC 6979 HMAC_DRBG, 7 x HMAC-SHA-384", drbg),
    ] {
        println!("{name:<40} {v:>12.0} {:>9.1}%", 100.0 * v / gv_s);
    }
    let overhead = hash + rng_read + drbg;
    let bound = gv_s - overhead;
    println!(
        "{:<40} {:>12.0} {:>9.1}%",
        "subtotal, not done by our kernel",
        overhead,
        100.0 * overhead / gv_s
    );
    println!("{:<40} {:>12.0} {:>10}", "full sign, measured", gv_s, "100.0%");
    println!(
        "{:<40} {:>12.0} {:>10}",
        "arithmetic only, upper bound", bound, "-"
    );
    println!();
    println!("# the three components are timed separately, not isolated inside sign:");
    println!("#   rfc6979_sign_with_random is private and the Hash parameter cannot be");
    println!("#   instantiated downstream, so sign cannot be called without them.  The");
    println!("#   DRBG row is a reconstruction over graviola's own public Hmac<Sha384>,");
    println!("#   following high/hmac_drbg.rs: four invocations to seed and three to");
    println!("#   draw one 48-byte candidate.  Anything sign does beyond these three and");
    println!("#   the curve arithmetic is unaccounted, so the last row is an upper bound");
    println!("#   on graviola's arithmetic-only signing cost.");
    for b in backends {
        println!(
            "#   {} sign / that bound is at most {:.2}.",
            b.name,
            at(&format!("sign/{}", b.name)) / bound
        );
    }
    println!();
    println!(
        "# the hash is {:.2}% of graviola's verify row ({hash:.0} of {gv_v:.0} ns);",
        100.0 * hash / gv_v
    );
    for b in backends {
        let v = at(&format!("verify/{}", b.name));
        println!(
            "#   removing it puts {}'s verify ratio at {:.3} instead of {:.3}.",
            b.name,
            v / (gv_v - hash),
            v / gv_v
        );
    }
    println!();

    if section_enabled("dhkem") {
        dhkem_section(reps, iters, field_config);
    }
}
