//! Build script for `catcrypt-mpn`.
//!
//! Archives the CatCrypt-emitted mpn kernels into a static archive and links it
//! into the crate. All eight objects in `obj/` are ELF64 relocatables produced
//! by the translation-validated byte encoder, not assembled from text: the five
//! equal-length loops by
//! `CatCrypt/Crypto/SecureCompilation/X86Backend/MpnLoopBytesEmit.lean`, whose
//! `.text` is byte-identical to the `renderLprogAtt` + `as` route (checked by
//! `make -C bench/integration_owned diff-bytes` in the dev repository), and the
//! three runtime-trip
//! kernels `mpn_shift_rt_owned.o`, `mpn_cmp_ct_owned.o` and
//! `mpn_mul_basecase_rt_owned.o` by `MpnRuntimeBytesEmit.lean`, written by
//! `lake env lean --run ../catcrypt-compiler/crates/catcrypt-mpn/emit_rt_objs.lean`
//! from the dev root.
//!
//! This step is purely "archive": it invokes only `ar`, so the build pulls in
//! zero crates.io dependencies and works fully offline. The extern signatures
//! in `src/mpn_ffi.rs` are generated from the same `Lprog` values, so they
//! cannot drift from the objects.

use std::env;
use std::path::PathBuf;
use std::process::Command;

const KERNELS: [&str; 8] = [
    "mpn_add_n_loop_owned",
    "mpn_sub_n_loop_owned",
    "mpn_and_n_loop_owned",
    "mpn_ior_n_loop_owned",
    "mpn_xor_n_loop_owned",
    "mpn_shift_rt_owned",
    "mpn_cmp_ct_owned",
    "mpn_mul_basecase_rt_owned",
];

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR not set"));
    let lib = out_dir.join("libmpn_catcrypt.a");

    // Allow overriding the archiver (e.g. cross-compilation).
    let ar_tool = env::var("AR").unwrap_or_else(|_| "ar".to_string());

    let mut objs = Vec::new();
    for k in KERNELS {
        let obj = format!("obj/{k}.o");
        println!("cargo:rerun-if-changed={obj}");
        objs.push(obj);
    }

    // Archive the encoder objects into a static lib the linker resolves
    // against. No assembly hop: the objects are the encoder's output.
    let mut ar = Command::new(&ar_tool);
    ar.arg("crs").arg(&lib);
    for obj in &objs {
        ar.arg(obj);
    }
    let status = ar
        .status()
        .unwrap_or_else(|e| panic!("failed to spawn archiver `{ar_tool}`: {e}"));
    assert!(status.success(), "archiving into {} failed", lib.display());

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static=mpn_catcrypt");
}
