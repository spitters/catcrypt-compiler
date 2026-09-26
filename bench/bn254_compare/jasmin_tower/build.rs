// Assemble the OWNED front-emitted Fp2 tower leaves (gen_com/tower_owned.s,
// produced by `make emit` — CatCrypt's verified front + owned x86 backend,
// no jasminc) and link them.
//
// The owned exports are named j_bn254_* so they do not collide with the Rust
// tower's tower::bn254_* symbols; the KAT calls the j_* externs.
use std::path::Path;
use std::process::Command;

fn main() {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let asm = format!("{manifest}/gen_com/tower_owned.s");
    if !Path::new(&asm).exists() {
        panic!(
            "{asm} not found — run `make emit` in jasmin_tower/ first \
             (front-compile + owned-render the Fp2 tower leaves)."
        );
    }
    let out_dir = std::env::var("OUT_DIR").unwrap();
    let obj = format!("{out_dir}/tower_owned.o");
    let status = Command::new("as")
        .args([&asm, "-o", &obj])
        .status()
        .expect("failed to run `as`");
    assert!(status.success(), "as failed on {asm}");

    let lib_dir = format!("{out_dir}/lib");
    std::fs::create_dir_all(&lib_dir).unwrap();
    let archive = format!("{lib_dir}/libbn254_jasmin_tower.a");
    let status = Command::new("ar")
        .args(["rcs", &archive, &obj])
        .status()
        .expect("failed to run `ar`");
    assert!(status.success(), "ar failed");

    println!("cargo:rustc-link-search=native={lib_dir}");
    println!("cargo:rustc-link-lib=static=bn254_jasmin_tower");
    println!("cargo:rerun-if-changed={asm}");
}
