# #219 spill-policy re-test: BN254 tower benched against the pp_module_nospill
# leaf emit. Sets BN254_LEAVES=nospill, which the AUCurves bn254-safe-rust
# build.sh reads to select generated/bn254_leaves_nospill.jazz instead of the
# default generated/bn254_leaves.jazz.
#
# This is a SEPARATE crate from ../ so cargo links a fresh libbn254_leaves.a
# built from the nospill jazz. Run ../ (default #[spill]) and this (nospill)
# back-to-back, pinned to the same core, to read the closure ratio.
#
#   make PIN="taskset -c 2" bench   # nospill cyc/op (compare vs ../ bn254-vale-bench)

PIN ?=

.PHONY: bench clean
bench: bn254_nospill_bench.rs Cargo.toml
	BN254_LEAVES=nospill $(PIN) cargo run --release --bin bn254_nospill_bench

clean:
	cargo clean 2>/dev/null || true
