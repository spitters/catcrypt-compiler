//! Google Wycheproof's adversarial ECDSA-verify vectors for
//! secp384r1 / SHA-384, IEEE P1363 encoding, once per leaf backend.
//!
//! These are NOT NIST CAVP SigVer vectors; no CAVP `.rsp` for ECDSA P-384
//! is present on this machine.  They are the negative-verification corpus
//! that is present: BoringSSL's converted copy of Wycheproof's
//! `ecdsa_secp384r1_sha384_p1363_test.json`, in the `key = value` text
//! format `convert_wycheproof.go` produces.  Point `WYCHEPROOF_DIR` at a
//! directory holding it; the test reports a skip when the file is absent.
//!
//! The harness splits the 96-byte P1363 signature into `r || s` and calls
//! the emitted kernel with them unchanged — the harness applies no range
//! check and no decoder beyond the length split, so the kernel's own
//! behaviour on each adversarial case is what is scored.  A signature whose
//! encoded length is not 96 bytes is rejected by the harness before the
//! kernel sees it and is counted separately.
//!
//! Every verdict is also taken from RustCrypto, so the run reports three
//! numbers per vector class: what Wycheproof expects, what the kernel
//! returns, and what RustCrypto returns.  The public key is encoded into
//! the backend's own point representation for each pass.

mod common;
use common::{backend, sb, Backend};

use sha2::{Digest, Sha384};
use std::path::PathBuf;

use p384_ecdsa_rust::{rc, scalar};

const FILE: &str = "ecdsa_secp384r1_sha384_p1363_test.txt";

fn vectors_path() -> PathBuf {
    let dir = std::env::var("WYCHEPROOF_DIR").unwrap_or_else(|_| {
        format!(
            "{}/Claude/bench_refs/boringssl/third_party/wycheproof_testvectors",
            std::env::var("HOME").unwrap_or_default()
        )
    });
    PathBuf::from(dir).join(FILE)
}

/// Bytes from a hex string of even length.
fn hex(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).ok())
        .collect()
}

/// Canonical limbs from a big-endian hex coordinate, tolerating a stripped
/// or an extra leading zero byte.
fn coord(s: &str) -> Option<[u64; 6]> {
    let raw = hex(s)?;
    let mut be = [0u8; 48];
    if raw.len() <= 48 {
        be[48 - raw.len()..].copy_from_slice(&raw);
    } else {
        if raw[..raw.len() - 48].iter().any(|&b| b != 0) {
            return None;
        }
        be.copy_from_slice(&raw[raw.len() - 48..]);
    }
    Some(rc::limbs_from_be(&be))
}

struct Group {
    q_bytes: [u8; 144],
    q_rc: p384_rc::AffinePoint,
}

#[derive(Default)]
struct Score {
    valid_ok: usize,
    valid_bad: usize,
    invalid_ok: usize,
    invalid_accepted: usize,
    acceptable: usize,
    bad_length: usize,
    rc_disagreements: Vec<String>,
    accepted_invalid: Vec<String>,
}

fn score_case(
    b: &Backend,
    tc: usize,
    res: &str,
    fl: &str,
    m: &[u8],
    sg: &[u8],
    g: &Group,
    sc: &mut Score,
) {
    let digest: [u8; 48] = Sha384::digest(m).into();
    let e = scalar::reduce(&rc::limbs_from_be(&digest));

    if sg.len() != 96 {
        sc.bad_length += 1;
        assert_ne!(res, "valid", "tcId {tc}: a valid vector has a 96-byte P1363 signature");
        return;
    }
    let mut rb = [0u8; 48];
    let mut sbytes = [0u8; 48];
    rb.copy_from_slice(&sg[..48]);
    sbytes.copy_from_slice(&sg[48..]);
    let r = rc::limbs_from_be(&rb);
    let s = rc::limbs_from_be(&sbytes);

    let mut ok = 0u64;
    (b.verify)(&sb(&e), &sb(&r), &sb(&s), &g.q_bytes, &mut ok);
    let emitted = ok == 1;
    let rc_ok = rc::verify(&e, &r, &s, &g.q_rc);

    if emitted != rc_ok {
        sc.rc_disagreements.push(format!(
            "tcId {tc} ({res}, {fl}): kernel {emitted}, RustCrypto {rc_ok}"
        ));
    }

    match res {
        "valid" => {
            if emitted {
                sc.valid_ok += 1;
            } else {
                sc.valid_bad += 1;
                panic!("[{}] tcId {tc}: the kernel rejected a valid signature ({fl})", b.name);
            }
        }
        "invalid" => {
            if emitted {
                sc.invalid_accepted += 1;
                sc.accepted_invalid.push(format!("tcId {tc} ({fl})"));
            } else {
                sc.invalid_ok += 1;
            }
        }
        _ => sc.acceptable += 1,
    }
}

/// One pass over the corpus for one backend.
fn run(b: &Backend, text: &str) -> Score {
    let mut sc = Score::default();
    let mut group: Option<Group> = None;
    let (mut wx, mut wy): (Option<[u64; 6]>, Option<[u64; 6]>) = (None, None);
    let (mut msg, mut result, mut sig, mut flags, mut tc_id) =
        (None::<Vec<u8>>, None::<String>, None::<Vec<u8>>, String::new(), 0usize);

    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix('[') {
            let rest = rest.trim_end_matches(']');
            if let Some((k, v)) = rest.split_once(" = ") {
                match k {
                    "publicKey.wx" => wx = coord(v),
                    "publicKey.wy" => wy = coord(v),
                    _ => {}
                }
                if let (Some(x), Some(y)) = (wx, wy) {
                    if let Some(q_rc) = rc::affine_from_coords(&x, &y) {
                        group = Some(Group {
                            q_bytes: (b.point_from_affine)(&x, &y),
                            q_rc,
                        });
                    }
                }
            }
            continue;
        }
        if let Some(rest) = line.strip_prefix("# tcId = ") {
            tc_id = rest.trim().parse().unwrap_or(0);
            continue;
        }
        if line.is_empty() {
            if let (Some(m), Some(res), Some(sg), Some(g)) =
                (msg.as_ref(), result.as_ref(), sig.as_ref(), group.as_ref())
            {
                score_case(b, tc_id, res, &flags, m, sg, g, &mut sc);
            }
            msg = None;
            result = None;
            sig = None;
            flags.clear();
            continue;
        }
        if let Some((k, v)) = line.split_once(" = ") {
            match k {
                "msg" => msg = hex(v),
                "result" => result = Some(v.to_string()),
                "sig" => sig = hex(v),
                "flags" => flags = v.to_string(),
                _ => {}
            }
        }
    }
    if let (Some(m), Some(res), Some(sg), Some(g)) =
        (msg.as_ref(), result.as_ref(), sig.as_ref(), group.as_ref())
    {
        score_case(b, tc_id, res, &flags, m, sg, g, &mut sc);
    }
    sc
}

#[test]
fn wycheproof_secp384r1_sha384() {
    let path = vectors_path();
    let text = match std::fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) => {
            println!("SKIP: {} ({e})", path.display());
            return;
        }
    };

    let mut first: Option<(usize, usize, usize)> = None;
    for b in backend::all() {
        let sc = run(b, &text);

        println!("Wycheproof {FILE} [{}]", b.name);
        println!("  valid accepted          : {}", sc.valid_ok);
        println!("  valid rejected          : {}", sc.valid_bad);
        println!("  invalid rejected        : {}", sc.invalid_ok);
        println!("  invalid ACCEPTED        : {}", sc.invalid_accepted);
        println!("  acceptable (unscored)   : {}", sc.acceptable);
        println!("  rejected on length      : {}", sc.bad_length);
        println!("  kernel != RustCrypto    : {}", sc.rc_disagreements.len());
        for d in &sc.rc_disagreements {
            println!("    {d}");
        }
        for a in &sc.accepted_invalid {
            println!("  accepted invalid: {a}");
        }

        assert_eq!(sc.valid_bad, 0, "{}", b.name);
        assert!(sc.valid_ok > 0, "no vectors were scored; check the file format");

        // Every backend must score the corpus identically: same arithmetic
        // relation, same checks, so the same verdict on every vector.
        let counts = (sc.valid_ok, sc.invalid_ok, sc.invalid_accepted);
        match first {
            None => first = Some(counts),
            Some(f) => assert_eq!(counts, f, "{} scored the corpus differently", b.name),
        }
    }
}
