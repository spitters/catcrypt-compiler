//! KAT cross-check harness for the emitted Plonky3 STARK prover chain.
//!
//! Each emitted layer's Lean model (`CatCrypt/Crypto/SecureCompilation/VIR/
//! Plonky3*Emit.lean`) reproduces a fixed reference value from the plonky3-hax
//! crate. This harness recomputes the SAME reference values directly from the
//! plonky3-hax spec functions and prints them, so the Lean KAT theorems
//! (which pin these same constants via `native_decide`) and this harness check
//! byte-identity against one common oracle.
//!
//! The plonky3-hax test suite itself (`plonky3-hax/tests/kat_vectors.rs`) is the
//! canonical regression: `cargo test --test kat_vectors` (33 tests) asserts
//! exactly these values. This harness is the human-readable per-layer crosswalk.
//!
//! Build (from plonky3-hax/, with this file copied into tests/ or run as an
//! example):  cargo run --example plonky3_kat   (after adding to Cargo.toml),
//! or simply read it alongside `cargo test --test kat_vectors`.
//!
//! Layer -> Lean KAT theorem -> plonky3-hax reference:
//!
//!   1 Merkle : Plonky3MerkleEmit.kat_root_four_prefix
//!             <-> merkle::merkle_build_root([H(1)..H(4)], 4) = 00e1d700..
//!             ; kat_compress_const_prefix <-> hash_two_to_one(..) = b5fd0238..
//!             ; kat_leaf_*_prefix <-> hash_field_elem(0/42)
//!   2 LDE   : Plonky3LdeEmit.kat_poly_eval_horner
//!             <-> baby_bear::bb_poly_eval([7,11,13,17], 3) = 616
//!             ; kat_domain_element_zero <-> fri::domain_element(8,0) = 1
//!   3 FRI   : Plonky3FriEmit.kat_fri_fold_specific
//!             <-> fri::fri_fold(100,50,7,3) = 287609503
//!             ; kat_fold_polynomial_linear <-> fri::fold_polynomial([3,5],11)
//!   4 AIR   : Plonky3AirEmit.kat_fibonacci_trace_values
//!             <-> air::fib_trace(10) column 1 = [1,1,2,3,5,8,13,21,34,55]
//!             ; kat_air_max_degree <-> air::air_max_degree(fib_air()) = 1

use plonky3_hax::air::{air_max_degree, fib_air, fib_trace};
use plonky3_hax::fri::{domain_element, fold_polynomial, fri_fold};
use plonky3_hax::specs::baby_bear::bb_poly_eval;
use plonky3_hax::specs::merkle::{hash_field_elem, hash_two_to_one, merkle_build_root, MerkleHash};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

fn main() {
    println!("== Plonky3 chain KAT crosswalk (plonky3-hax reference) ==");

    // Layer 1: Merkle.
    let leaves: Vec<MerkleHash> = (1u64..=4u64).map(hash_field_elem).collect();
    let root = merkle_build_root(&leaves, 4);
    println!("[L1] merkle_build_root([H(1)..H(4)],4) = {}", hex(&root));
    println!("     (Lean kat_root_four_prefix pins 00 e1 d7 00)");
    let c = hash_two_to_one([0x01u8; 32], [0x02u8; 32]);
    println!("[L1] hash_two_to_one([1;32],[2;32]) = {}", hex(&c));
    println!("     (Lean kat_compress_const_prefix pins b5 fd 02 38)");
    println!("[L1] hash_field_elem(0)  = {}", hex(&hash_field_elem(0)));
    println!("[L1] hash_field_elem(42) = {}", hex(&hash_field_elem(42)));

    // Layer 2: LDE.
    println!("[L2] bb_poly_eval([7,11,13,17],3) = {}  (Lean: 616)",
             bb_poly_eval(&[7, 11, 13, 17], 3));
    println!("[L2] domain_element(8,0) = {}  (Lean: 1)", domain_element(8, 0));

    // Layer 3: FRI.
    println!("[L3] fri_fold(100,50,7,3) = {}  (Lean: 287609503)",
             fri_fold(100, 50, 7, 3));
    println!("[L3] fold_polynomial([3,5],11) = {:?}", fold_polynomial(&[3, 5], 11));

    // Layer 4: AIR.
    let trace = fib_trace(10);
    let col1: Vec<u64> = (0..10).map(|i| trace.get(i, 1)).collect();
    println!("[L4] fib_trace(10) col1 = {:?}", col1);
    println!("     (Lean kat_fibonacci_trace_values: [1,1,2,3,5,8,13,21,34,55])");
    println!("[L4] air_max_degree(fib_air()) = {}  (Lean: 1)",
             air_max_degree(&fib_air()));
}
