// Assemble the reg-ptr jasminc-emitted 12-function tower subset
// (gen/tower_regptr_12.s, produced by `make compile-12`) and link it.
//
// The reg-ptr tower exports are renamed j_bn254_* (a post-assemble symbol
// rename is awkward, so the Makefile target keeps the names and we rename at
// the jazz level here via the generated subset) so they do not collide with
// the Rust tower's tower::bn254_* symbols. The KAT calls the j_* externs.
//
// reg ptr u64[N] parameters use the same C pointer ABI (RDI/RSI/RDX) as the
// reg-u64 byte-pointer params, so the Rust extern signatures are unchanged
// (*mut u64 / *const u64).
use std::path::Path;
use std::process::Command;

fn main() {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let asm_src = format!("{manifest}/gen/tower_regptr_12.s");
    if !Path::new(&asm_src).exists() {
        panic!(
            "{asm_src} not found — run `make compile-12` in jasmin_tower/regptr/ \
             first (jasminc the reg-ptr tower 12-function subset)."
        );
    }
    let out_dir = std::env::var("OUT_DIR").unwrap();

    // Rename the tower export symbols to j_* so they don't clash with the Rust
    // bn254 tower at link time. The verified-leaf symbols are stubs internal to
    // the subset object, so only the tower exports need renaming.
    let asm = std::fs::read_to_string(&asm_src).unwrap();
    let renamed = asm
        .replace("bn254_Fp2_", "j_bn254_Fp2_")
        .replace("bn254_Fp6_", "j_bn254_Fp6_");
    let asm_r = format!("{out_dir}/tower_regptr_12_renamed.s");
    std::fs::write(&asm_r, renamed).unwrap();

    let obj = format!("{out_dir}/tower_regptr_12.o");
    let status = Command::new("as")
        .args([&asm_r, "-o", &obj])
        .status()
        .expect("failed to run `as`");
    assert!(status.success(), "as failed on {asm_r}");

    let lib_dir = format!("{out_dir}/lib");
    std::fs::create_dir_all(&lib_dir).unwrap();
    let archive = format!("{lib_dir}/libbn254_jasmin_tower_regptr.a");
    let status = Command::new("ar")
        .args(["rcs", &archive, &obj])
        .status()
        .expect("failed to run `ar`");
    assert!(status.success(), "ar failed");

    println!("cargo:rustc-link-search=native={lib_dir}");
    println!("cargo:rustc-link-lib=static=bn254_jasmin_tower_regptr");
    println!("cargo:rerun-if-changed={asm_src}");
}
