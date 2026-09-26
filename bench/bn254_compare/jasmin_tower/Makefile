# BN254 tower variant (#222) — OWNED Fp2 leaves (no jasminc).
#
# The three Fp2 tower leaves the KAT/bench link (j_bn254_Fp2_add /
# j_bn254_Fp2_sub / j_bn254_Fp2_felem_copy) are FRONT-COMPILED and rendered
# through CatCrypt's own x86 backend (LowCT carry-chain bodies ->
# translateDialectControl -> Com catCryptDialect -> cryptoDialectToJasminCom
# -> Com.toLprogPhysAbi -> renderLprogAtt), emitted by
# CatCrypt/Crypto/SecureCompilation/Bn254TowerFrontEmit.lean.  jasminc is not
# on the artifact path.
#
# Faithfulness KAT: the owned Fp2_add / Fp2_sub / felem_copy leaves are
# byte-identical to the AUCurves verified-bedrock2 Rust tower's
# tower::bn254_Fp2_add / bn254_Fp2_sub / bn254_Fp2_felem_copy on the published
# EIP-197 G2 generator coordinates (Montgomery form).  No fabricated vectors.
#
# The stackalloc-typing gap that limited the jasminc route to the 12 leaf-level
# tower functions (see ../JASMIN_TOWER_222.md) is moot on this path; the
# heavier tower ops (Fp2_mul etc.) ride the #260 reg-ptr re-emit in the parent
# bn254_compare bench.

COMPILER := $(abspath $(CURDIR)/../../..)
DEV      := $(abspath $(COMPILER)/../SSProve-lean)
# lake env/build from the dev root (one-root rule); the command runs in the compiler tree
LEAN_IN_COMPILER := cd $(DEV) && lake env sh -c 'cd $(COMPILER) && exec "$$@"' sh

.PHONY: kat bench emit compile clean

# OWNED emit (no jasminc): the three Fp2 leaves as one .s, rendered by the
# verified front.  In-model gates (front compiles, renders clean, denote =
# independent (x +- y) mod p spec on the EIP-197 anchor + edges) live in
# Bn254TowerFrontEmit.lean; this artifact is gated by the byte KAT below.
gen_com/tower_owned.s: $(COMPILER)/CatCrypt/Crypto/SecureCompilation/Bn254TowerFrontEmit.lean tower_owned_emit.lean
	$(LEAN_IN_COMPILER) lean --run bench/bn254_compare/jasmin_tower/tower_owned_emit.lean

emit: gen_com/tower_owned.s
compile: gen_com/tower_owned.s

# Byte-identical KAT: owned Fp2_add/sub/copy vs the Rust tower (AUCurves
# verified bedrock2), plus the jasmin-only add/sub round-trip.
kat: gen_com/tower_owned.s
	cargo run --release --bin bn254_tower_kat

# Perf parity bench (owned Fp2 ops vs Rust tower Fp2 ops), MIN-of-3, $(PIN) core pinning.
PIN ?= taskset -c 2
bench: gen_com/tower_owned.s
	$(PIN) cargo run --release --bin bn254_tower_bench

clean:
	rm -f gen_com/tower_owned.s gen/tower_subset.jazz gen/leaf_stubs.jazz \
	  gen/combined.jazz gen/tower_subset.s gen/tower_subset_renamed.jazz
	cargo clean 2>/dev/null || true
