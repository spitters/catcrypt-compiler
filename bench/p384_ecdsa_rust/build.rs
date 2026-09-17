//! Detects the compiler-emitted sources under `gen/`.
//!
//! Every `gen/*.rs` file is collected, in sorted order, into
//! `$OUT_DIR/emitted_includes.rs` as a list of `include!` directives, and
//! `cfg(p384_emitted)` is set when the list is non-empty.  `src/generated.rs`
//! includes that file inside a module that has the leaf shims in scope; when
//! the cfg is unset it uses the hand-written transcription instead.
//!
//! Three further cfgs record which entry points those files define:
//! `p384_ecdsa_emitted` for the three ECDSA kernels, and
//! `p384_dhkem_encap_emitted` and `p384_dhkem_decap_emitted` for the two
//! DHKEM(P-384) kernels.  Each entry point `gen/` does not define is taken
//! from the transcription, so the DHKEM kernels fall back independently of
//! the ECDSA ones.
//!
//! The `force-fallback` feature suppresses the detection.
//!
//! Under the `s2n` feature this also links the AWS s2n-bignum archive, which
//! the third leaf backend calls.  The archive is `x86/libs2nbignum.a` under
//! the s2n-bignum checkout named by `S2N_BIGNUM_DIR`; unset, the checkout is
//! `../../../SSProve-lean/bench/reference_install/s2n-bignum` relative to
//! this crate, the one in the sibling SSProve-lean tree.  Nothing is built here — the
//! checkout is read, never modified, and a missing archive is a hard error
//! rather than a silent fallback, because a backend that does not link is
//! not a backend that was measured.
//!
//! Under the `production` feature it links BoringSSL's `libcrypto.a`
//! statically and records the path of OpenSSL's `libcrypto.so.3`, which
//! `src/ossl.rs` opens at run time; see [`link_production`].

use std::env;
use std::fs;
use std::path::PathBuf;

/// Emits the link directives for the s2n-bignum archive.
///
/// `S2N_BIGNUM_DIR` names the s2n-bignum checkout, the directory holding
/// `x86/` and `x86_att/`; the archive is `$S2N_BIGNUM_DIR/x86/libs2nbignum.a`.
fn link_s2n_bignum(manifest: &PathBuf) {
    println!("cargo:rerun-if-env-changed=S2N_BIGNUM_DIR");

    let root = env::var_os("S2N_BIGNUM_DIR").map(PathBuf::from).unwrap_or_else(|| {
        manifest.join("../../../SSProve-lean/bench/reference_install/s2n-bignum")
    });
    let dir = root.join("x86");
    let archive = dir.join("libs2nbignum.a");
    assert!(
        archive.is_file(),
        "feature `s2n` needs {}; set S2N_BIGNUM_DIR to an s2n-bignum checkout \
         whose x86/libs2nbignum.a is built",
        archive.display()
    );

    println!("cargo:rerun-if-changed={}", archive.display());
    println!("cargo:rustc-link-search=native={}", dir.display());
    println!("cargo:rustc-link-lib=static=s2nbignum");
}

/// Hands the two CatCrypt-emitted P-384 field kernels to the linker of the
/// `fieldbench` binary.
///
/// The `.s` files live in sibling bench directories and are untracked build
/// output of their Lean emitters; they are read here, never written, and
/// never regenerated (that is `lake` work, and it belongs to whoever records
/// a figure).  Their writers are `emitMainP384` in
/// `CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6MontMulProvenEmit` and
/// `emitP384` in `CatCrypt.Crypto.SecureCompilation.X86Backend.P384FieldKernel`,
/// which write paths relative to the working directory; the README lists the
/// commands.  `P384_EMIT_MONTMUL_S` and `P384_EMIT_SOLINAS_S` override the
/// two paths.  They are passed as link arguments, so the linker driver
/// assembles them; nothing is spawned from this script.
fn link_emitted_field_kernels(manifest: &PathBuf) {
    let sources = [
        (
            "P384_EMIT_MONTMUL_S",
            manifest.join("../p384_compare/gen/p384_montmul_proven.s"),
        ),
        (
            "P384_EMIT_SOLINAS_S",
            manifest.join("../p384_fieldmul_compare/gen_com/p384_mul_x86_from_lean.s"),
        ),
    ];
    for (var, default) in sources {
        println!("cargo:rerun-if-env-changed={var}");
        let path = env::var_os(var).map(PathBuf::from).unwrap_or(default);
        assert!(
            path.is_file(),
            "feature `emit-field` needs {}; emit it with lake or set {var}",
            path.display()
        );
        println!("cargo:rerun-if-changed={}", path.display());
        println!("cargo:rustc-link-arg-bin=fieldbench={}", path.display());
    }
}

/// Links BoringSSL's `libcrypto.a` statically and records the OpenSSL
/// library path for `src/ossl.rs` to `dlopen`.
///
/// Both are read in place, never built or modified.  The BoringSSL archive
/// is passed as `static:-bundle`, so it reaches the final link of each
/// binary instead of being copied into this crate's rlib; its search
/// directory precedes the system ones, which also hold an OpenSSL
/// `libcrypto.a` of the same name.  OpenSSL is not linked at all: the two
/// libraries export the same C names.  The BoringSSL revision is read from
/// the checkout's `.git/HEAD`, following one loose ref, so the benchmark can
/// print what it measured.
fn link_production(manifest: &PathBuf) {
    println!("cargo:rerun-if-env-changed=BORINGSSL_LIB_DIR");
    println!("cargo:rerun-if-env-changed=P384_OPENSSL_LIBCRYPTO");

    let bssl_root = manifest.join("../../../bench_refs/boringssl");
    let lib_dir = env::var_os("BORINGSSL_LIB_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| bssl_root.join("build-ct"));
    let archive = lib_dir.join("libcrypto.a");
    assert!(
        archive.is_file(),
        "feature `production` needs BoringSSL's {}; build it in the checkout or set BORINGSSL_LIB_DIR",
        archive.display()
    );
    println!("cargo:rerun-if-changed={}", archive.display());
    println!("cargo:rustc-link-search=native={}", lib_dir.display());
    println!("cargo:rustc-link-lib=static:-bundle=crypto");

    let is_commit = |s: &String| s.len() == 40 && s.bytes().all(|b| b.is_ascii_hexdigit());
    let git = bssl_root.join(".git");
    let revision = fs::read_to_string(git.join("HEAD"))
        .ok()
        .map(|s| s.trim().to_string())
        .and_then(|head| match head.strip_prefix("ref: ") {
            None => Some(head),
            Some(r) => fs::read_to_string(git.join(r)).ok().map(|s| s.trim().to_string()),
        })
        .filter(is_commit)
        .unwrap_or_else(|| "unknown".to_string());
    println!("cargo:rustc-env=P384_BORINGSSL_REVISION={revision}");

    let ossl = env::var("P384_OPENSSL_LIBCRYPTO")
        .unwrap_or_else(|_| "/usr/lib/x86_64-linux-gnu/libcrypto.so.3".to_string());
    assert!(
        PathBuf::from(&ossl).is_file(),
        "feature `production` needs OpenSSL's {ossl}; set P384_OPENSSL_LIBCRYPTO"
    );
    println!("cargo:rustc-env=P384_OPENSSL_LIBCRYPTO={ossl}");
}

fn main() {
    println!("cargo:rustc-check-cfg=cfg(p384_emitted)");
    println!("cargo:rerun-if-changed=gen");

    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let gen_dir = manifest.join("gen");

    if env::var_os("CARGO_FEATURE_S2N").is_some() {
        link_s2n_bignum(&manifest);
    }
    if env::var_os("CARGO_FEATURE_EMIT_FIELD").is_some() {
        link_emitted_field_kernels(&manifest);
    }
    if env::var_os("CARGO_FEATURE_PRODUCTION").is_some() {
        link_production(&manifest);
    }

    let forced_off = env::var_os("CARGO_FEATURE_FORCE_FALLBACK").is_some();

    let mut sources: Vec<PathBuf> = Vec::new();
    if !forced_off {
        if let Ok(entries) = fs::read_dir(&gen_dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().and_then(|e| e.to_str()) == Some("rs") {
                    println!("cargo:rerun-if-changed={}", path.display());
                    sources.push(path);
                }
            }
        }
    }
    sources.sort();

    let mut body = String::new();
    let mut defined = String::new();
    for path in &sources {
        body.push_str(&format!("include!(r\"{}\");\n", path.display()));
        defined.push_str(&fs::read_to_string(path).unwrap_or_default());
    }
    fs::write(out_dir.join("emitted_includes.rs"), body).expect("write emitted_includes.rs");

    if !sources.is_empty() {
        println!("cargo:rustc-cfg=p384_emitted");
    }

    // Which entry points `gen/` defines, so that each one missing from it
    // falls back to its hand-written transcription on its own.  The ECDSA
    // three are one group, as they have always been emitted together; the
    // two DHKEM kernels are decided separately.
    let defines = |name: &str| defined.contains(&format!("fn {name}("));
    for (name, cfg) in [
        ("p384_ecdsa_verify", "p384_ecdsa_emitted"),
        ("p384_dhkem_encap", "p384_dhkem_encap_emitted"),
        ("p384_dhkem_decap", "p384_dhkem_decap_emitted"),
    ] {
        println!("cargo:rustc-check-cfg=cfg({cfg})");
        if defines(name) {
            println!("cargo:rustc-cfg={cfg}");
        }
    }
}
